{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}

module Utils where

import           Control.Lens ((<&>), makeLenses)
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Bifunctor (first, second)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import qualified Data.Set as S
import           Data.Traversable (for)
import           Debug.Trace  (trace)
import           Types


showTrace :: Show b => b -> b
showTrace = trace =<< show


data TIState = TIState
  { _tiVNames :: Int
  , _tiTNames :: Int
  , _tiSubst  :: Subst
  }

makeLenses ''TIState

type TI = ExceptT String (State TIState)


unravel :: Exp a -> Maybe (VName, [Exp a])
unravel = go []
  where
    go acc (LCon a) = pure (a, acc)
    go acc (a :@ b) = go (b : acc) a
    go _ _ = Nothing


letters :: [String]
letters = do
  b <- "":letters
  a <- ['a'..'z']
  pure $ a : b


runTI :: TI a -> Either String a
runTI = flip evalState (TIState 0 0 mempty) . runExceptT


kind :: Type -> TI Kind
kind (TVar x)  = pure $ tKind x
kind (TCon x)  = pure $ tKind x
kind (a :@@ b) = do
  ka <- kind a
  kb <- kind b
  let kerr kk = throwE $ mconcat
        [ "kind mismatch: '"
        , show b
        , " :: "
        , show kb
        , "' vs '"
        , show kk
        , "'\nwhen trying to apply '"
        , show a
        , " :: "
        , show ka
        , "'\n"
        ]
  case ka of
    kal :>> kar -> do
      when (kal /= kb) $ kerr kal
      pure kar
    KStar -> kerr KStar


data GenDataCon = GenDataCon
  { gdcName      :: VName
  , gdcConType   :: Qual Type
  , gdcFinalType :: Qual Type
  , gdcCon       :: Exp VName
  } deriving (Eq, Show)


buildDataCon
    :: VName
    -> [Type]
    -> Maybe Type
    -> GenDataCon
buildDataCon n@(VName s) ts t' =
  let ks = fmap (either error id . runTI . kind) ts
      k  = foldr (:>>) KStar ks
      tr = maybe (foldl (:@@) (TCon $ TName s k)
         . fmap TVar
         $ S.toList $ free ts) id t'
      t  = foldr (:->) tr ts
      ls = fmap fst $ zip (fmap VName letters) ts
   in GenDataCon n ([] :=> t) ([] :=> tr)
    . foldr lam
            (foldl (:@) (LCon n) $ fmap V ls)
    $ ls


buildRecord
    :: VName
    -> [(VName, Type)]
    -> Maybe Type
    -> (GenDataCon, [(VName, (Qual Type, Exp VName))])
buildRecord n fs t =
  let gen@(GenDataCon _ _ t' _) = buildDataCon n (fmap snd fs) t
   in (gen, )
    $ zip [0..] fs <&> \(fn, (f, ft)) ->
        let p = take (length fs) $ putBack $ splitAt fn $ repeat PWildcard
            putBack (as, bs) = as <> [PVar "p"] <> bs
         in (f,)
          $ ([] :=> unqualType t' :-> ft,)
          $ lam "z"
          $ case_ "z"
          $ [(PCon n p, "p")]


getDictName :: CName -> String
getDictName n = "@" <> unCName n

getDict :: Pred -> String
getDict (IsInst c t) = "@" <> show c <> "@" <> show t


buildDictType
    :: Class
    -> (GenDataCon, [(VName, (Qual Type, Exp VName))])
buildDictType (Class _ n ms) =
  buildRecord
    (VName name)
    -- TODO(sandy): there is a bug here if there is a constraint on the method
    (fmap (second unqualType . first ("@" <>)) $ M.assocs ms)
    Nothing
    -- (Just $ TCon (TName name KStar))
  where
    name = getDictName n


buildDict :: GenDataCon -> InstRep Pred -> (VName, (Qual Type, Exp VName))
buildDict gdc (InstRep (qs :=> i@(IsInst c t)) impls) =
    (VName dict,)
      -- TODO(sandy): buggy; doesn't do nested dicts
      -- TODO(sandy): also buggy. we should just run the type checker on this
      $ (sub (Subst $ M.fromList [("a", t)] ) $ gdcFinalType gdc,)
      $ foldl (:@) (LCon (VName dname)) $ M.elems impls
  where
    dict = getDict i
    dname = getDictName c

