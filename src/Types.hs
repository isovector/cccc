{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wall                   #-}

module Types where

import           Bound hiding (instantiate)
import           Bound.Scope hiding (instantiate)
import           Control.Arrow (first, second)
import           Control.Lens ((<&>))
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Char (isUpper)
import           Data.Eq.Deriving (deriveEq1)
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           Data.Set (Set)
import qualified Data.Set as S
import           GHC.Exts (IsString (..))
import           Prelude hiding (exp)
import           Text.Show.Deriving (deriveShow1)


type TI = ExceptT String (State (Int, Int))

letters :: [String]
letters = do
  b <- "":letters
  a <- ['a'..'z']
  pure $ a : b

runTI :: TI a -> Either String a
runTI = flip evalState (0, 0) . runExceptT

newTyVar :: TI Type
newTyVar = do
  n <- fst <$> get
  modify $ first (+1)
  pure . TVar . TName $ letters !! n

newVName :: (Int -> a) -> TI a
newVName f = do
  n <- snd <$> get
  modify $ second (+1)
  pure $ f n


type Name = String

infixl 9 :@
data Exp a
  = V a
  | Lit Lit
  | Exp a :@ Exp a
  | Lam (Scope () Exp a)
  | Let (Scope () Exp a) (Scope () Exp a)
  | Assert (Exp a) Type
  deriving (Functor, Foldable, Traversable)

instance IsString a => IsString (Exp a) where
  fromString = V . fromString

pattern TProd :: Type -> Type -> Type
pattern TProd a b = TCon "*" :@@ a :@@ b

pattern TSum :: Type -> Type -> Type
pattern TSum a b = TCon "+" :@@ a :@@ b

pattern TArr :: Type -> Type -> Type
pattern TArr a b = TCon "->" :@@ a :@@ b

infixl 9 :@@
data Type
  = TVar TName
  | TInt
  | TUnit
  | TVoid
  | TCon TName
  | Type :@@ Type
  deriving (Eq, Ord)

instance IsString Type where
  fromString x =
    case isUpper $ head x of
      True  -> TCon $ fromString x
      False -> TVar $ fromString x

instance Show Type where
  showsPrec x (TArr a b)  = showParen (x > 0)
    $ showsPrec 1 a
    . showString " -> "
    . showsPrec 0 b
  showsPrec _ (TSum TUnit TUnit) = showString "Bool"
  showsPrec x (TProd a b) = showParen (x > 3)
    $ showsPrec 3 a
    . showString " * "
    . showsPrec 3 b
  showsPrec x (TSum a b)  = showParen (x > 5)
    $ showsPrec 5 a
    . showString " + "
    . showsPrec 5 b
  showsPrec _ (TVar n)    = showString $ unTName n
  showsPrec _ (TCon n)    = showString $ unTName n
  showsPrec x (a :@@ b)   = showParen (x > 9)
    $ showsPrec 9 a
    . showString " "
    . showsPrec 10 b
  showsPrec _ TInt        = showString "Int"
  showsPrec _ TUnit       = showString "1"
  showsPrec _ TVoid       = showString "0"

newtype TName = TName { unTName :: String }
  deriving (Eq, Ord, IsString)

newtype VName = VName { unVName :: String }
  deriving (Eq, Ord, IsString)

instance Show TName where
  show = unTName

instance Show VName where
  show = unVName

data Scheme = Scheme
  { schemeVars :: [TName]
  , schemeType :: Type
  }
  deriving (Eq, Ord, Show)

data Lit
  = LInt Int
  | LBool Bool
  -- | LPair (Exp VName) (Exp VName)

instance Applicative Exp where
  pure  = V
  (<*>) = ap

instance Monad Exp where
  return       = pure
  V a        >>= f = f a
  Lit x      >>= _ = Lit x
  (x :@ y)   >>= f = (x >>= f) :@ (y >>= f)
  Lam e      >>= f = Lam (e >>>= f)
  Let bs b   >>= f = Let (bs >>>= f) (b >>>= f)
  Assert e t >>= f = Assert (e >>= f) t


deriveEq1 ''Exp
deriveShow1 ''Exp

deriving instance Eq Lit
deriving instance Show Lit
deriving instance Eq a   => Eq (Exp a)
deriving instance Show a => Show (Exp a)


instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- traverse (const newTyVar) vars
  pure $ apply (Subst $ M.fromList (zip vars nvars)) t

unify :: Type -> Type -> TI Subst
unify (l :@@ r) (l' :@@ r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  pure $ s1 <> s2
unify (TCon a) (TCon b)
  | a == b  = pure mempty
unify (TVar u) t  = varBind u t
unify t (TVar u)  = varBind u t
unify TInt TInt   = pure mempty
unify t1 t2       = throwE $
  mconcat
    [ "types don't unify: '"
    , show t1
    , "' vs '"
    , show t2
    , "'"
    ]

varBind :: TName -> Type -> TI Subst
varBind u t
  | t == TVar u = pure mempty
  | S.member u (free t) = throwE
      $ mconcat
        [ "occurs check: '"
        , show u
        , "' vs '"
        , show t
        , "'"
        ]
  | otherwise = pure $ Subst [(u, t)]


splatter :: Monad f => c -> Scope b f c -> f c
splatter name = splat pure (const $ pure name)

infer
    :: (Show a, Ord a)
    => (Int -> a)
    -> SymTable a
    -> Exp a
    -> TI (Subst, Type)
infer f env (Assert e t) = do
  (s1, t1) <- infer f env e
  s2       <- unify t t1
  pure (s1 <> s2, t)
infer _ (SymTable env) (V a) =
  case M.lookup a env of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> (,) <$> pure mempty <*> instantiate sigma
infer f env (Let bs b) = do
  name <- newVName f
  let e1 = splatter name bs
      e2 = splatter name b
  (s1, t1) <- infer f env e1
  let t' = generalize (apply s1 env) t1
      env' = SymTable $ M.insert name t' $ unSymTable env
  (s2, t2) <- infer f (apply s1 env') e2
  pure (s1 <> s2, t2)
infer _ _ (Lit (LInt _))  = pure (mempty, TInt)
infer _ _ (Lit (LBool _)) = pure (mempty, TBool)
infer f (SymTable env) (Lam x) = do
  name <- newVName f
  tv <- newTyVar
  let env' = SymTable $ env <> [(name, Scheme [] tv)]
      e = splatter name x
  (s1, t1) <- infer f env' e
  pure (s1, TArr (apply s1 tv) t1)

infer f env exp@(e1 :@ e2) =
  do
    tv <- newTyVar
    (s1, t1) <- infer f env e1
    (s2, t2) <- infer f (apply s1 env) e2
    s3 <- unify (apply s2 t1) (TArr t2 tv)
    pure (s1 <> s2 <> s3, apply s3 tv)
  `catchE` \e -> throwE $
    mconcat
      [ e
      , "\n in "
      , show exp
      , "\n\ncontext: \n"
      , foldMap ((<> "\n") . show) . M.assocs $ unSymTable env
      ]

typeInference :: Map VName Scheme -> Exp VName -> TI Type
typeInference env e = do
  (s, t) <- infer (VName . ("!!!v" <>) . show) (SymTable env) e
  pure $ apply s t

pattern (:->) :: Type -> Type -> Type
pattern (:->) a b = TArr a b
infixr 1 :->

pattern TBool :: Type
pattern TBool = TSum TUnit TUnit

class Types a where
  free :: a -> Set TName
  apply :: Subst -> a -> a


flatten :: Subst -> Subst
flatten (Subst x) = fix $ \(Subst final) ->
  Subst $ M.fromList $ M.assocs x <&> \(a, b) -> (a,) $
    apply (Subst final) $ case b of
      TVar n -> maybe (TVar n) id $ M.lookup n final
      z      -> z



instance Types Type where
  free (TVar a)    = [a]
  free (TCon _)    = [] -- ?
  free TInt        = []
  free TBool       = []
  free TUnit       = []
  free TVoid       = []
  free (a :@@ b)   = free a <> free b

  apply s (TVar n)    = maybe (TVar n) id $ M.lookup n $ unSubst s
  apply _ (TCon n)    = TCon n
  apply s (a :@@ b)   = apply s a :@@ apply s b
  apply _ TInt        = TInt
  apply _ TUnit       = TUnit
  apply _ TBool       = TBool
  apply _ TVoid       = TVoid

instance Types Scheme where
  free (Scheme vars t) = free t S.\\ S.fromList vars

  -- apply all `s` that are not quantified?
  apply s (Scheme vars t) =
    Scheme vars $ apply (Subst $ foldr M.delete (unSubst s) vars) t

newtype Subst = Subst
  { unSubst :: Map TName Type }
  deriving (Eq, Show)

instance Monoid Subst where
  mempty = Subst mempty
  mappend s1 (Subst s2) =
    Subst $ fmap (apply s1) s2 <> unSubst s1

newtype SymTable a = SymTable
  { unSymTable :: Map a Scheme
  }

instance Types (SymTable a) where
  free = mconcat . fmap free . M.elems . unSymTable
  apply s = SymTable . fmap (apply s) . unSymTable

generalize :: SymTable a -> Type -> Scheme
generalize env t =
  Scheme (S.toList $ free t S.\\ free env) t

normalizeType :: Type -> Type
normalizeType = schemeType . normalize . Scheme mempty

normalize :: Scheme -> Scheme
normalize (Scheme _ body) = Scheme (map snd ord) (normtype body)
  where
    ord = zip (nub $ S.toList $ free body) (fmap TName letters)

    normtype (TCon a)    = TCon a
    normtype (a :@@ b)   = normtype a :@@ normtype b
    normtype TInt        = TInt
    normtype TBool       = TBool
    normtype TUnit       = TUnit
    normtype TVoid       = TVoid
    normtype (TVar a)    =
      case Prelude.lookup a ord of
        Just x -> TVar x
        Nothing -> error "type variable not in signature"



-- freeVars :: Ord a => Exp a -> Set a
-- freeVars (V a)    = [a]
-- freeVars (Lit _)  = []
-- freeVars (a :@ b) = freeVars a <> freeVars b
-- freeVars (Lam x)  = S.fromList $ foldMapScope (const []) pure x


lam :: Eq a => a -> Exp a -> Exp a
lam x e = Lam (abstract1 x e)

let_ :: Eq a => a -> Exp a -> Exp a -> Exp a
let_ x v e = Let (abstract1 x v) (abstract1 x e)


whnf :: Exp a -> Exp a
whnf (f :@ a) =
  case whnf f of
    Lam b -> whnf (instantiate1 a b)
    f' -> f' :@ a
whnf e = e


test :: Exp VName -> IO ()
test x =
  case runTI $ typeInference stdLib x of
    Left e -> putStrLn e
    Right t -> putStrLn $ show $ normalizeType t

main :: IO ()
main = do
  print $ whnf $ lam 'x' (V 'x' :@ V 'x')
              :@ lam 'x' (V 'x' :@ V 'x')


stdLib :: Map VName Scheme
stdLib = fmap (generalize $ SymTable @VName mempty) stdLib'

stdLib' :: Map VName Type
stdLib' =
  [ ("fst", TProd "a" "b" :-> "a")
  , ("snd", TProd "a" "b" :-> "b")
  , ("inl", "a" :-> TSum "a" "b")
  , ("inr", "b" :-> TSum "a" "b")
  , ("proj", ("a" :-> "c") :-> ("b" :-> "c") :-> TSum "a" "b" :-> "c")
  , (".", ("b" :-> "c") :-> ("a" :-> "b") :-> "a" :-> "c")
  , ("unit", TUnit)
  , ("==", "a" :-> "a" :-> TBool)
  , (",", "a" :-> "b" :-> TProd "a" "b")
  , ("bool", "a" :-> "a" :-> TBool :-> "a")
  , ("id", "a" :-> "a")
  , ("ccc", ("a" :-> "b") :-> "k" :@@ "a" :@@ "b")
  ]


