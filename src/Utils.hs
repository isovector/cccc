{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}

module Utils where

import           Control.Lens ((<&>), makeLenses)
import           Control.Monad.State
import           Control.Monad.Trans.Except
import qualified Data.Map as M
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
kind TInt      = pure KStar
kind TUnit     = pure KStar
kind TVoid     = pure KStar
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


buildDataCon
    :: VName
    -> [Type]
    -> Maybe Type
    -> (Qual Type, Exp VName)
buildDataCon n@(VName s) ts t' =
  let ks = fmap (either error id . runTI . kind) ts
      k  = foldr (:>>) KStar ks
      tr = TCon $ TName s k
      t  = foldr (:->) (maybe (foldl (:@@) tr ts) id t') ts
      ls = fmap fst $ zip (fmap VName letters) ts
   in ([] :=> t,)
    . foldr lam
            (foldl (:@) (LCon n) $ fmap V ls)
    $ ls


buildDict :: InstRep a -> Exp VName
buildDict ir =
  lam "m" $ case_ "m" $
    (M.assocs $ irImpls ir) <&> \(VName m, e) ->
      (PLit (LitString m), e)

