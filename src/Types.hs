{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wall                   #-}

module Types where

import Control.Arrow (first, second)
import Prelude hiding (exp)
import Control.Monad.Trans.Except
import Control.Monad.State
import           Bound hiding (instantiate)
import           Bound.Scope hiding (instantiate)
import           Data.Eq.Deriving (deriveEq1)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           Data.Set (Set)
import qualified Data.Set as S
import           GHC.Exts (IsString)
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
  deriving (Functor, Foldable, Traversable)

data Type
  = TVar TName
  | TInt
  | TBool
  | TArr Type Type
  deriving (Eq, Ord)

instance Show Type where
  show (TVar x) = show x
  show TInt = "Int"
  show TBool = "Bool"
  show (TArr a b) = show a <> " -> " <> show b

newtype TName = TName { unTName :: String }
  deriving (Eq, Ord, IsString)

instance Show TName where
  show = unTName

data Scheme = Scheme [TName] Type
  deriving (Eq, Ord, Show)

data Lit
  = LInt Int
  | LBool Bool
  deriving (Eq, Ord, Show)


makeBound ''Exp
deriveEq1 ''Exp
deriveShow1 ''Exp

deriving instance Eq a   => Eq (Exp a)
deriving instance Show a => Show (Exp a)


instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- traverse (const newTyVar) vars
  pure $ apply (M.fromList (zip vars nvars)) t

mgu :: Type -> Type -> TI Subst
mgu (TArr l r) (TArr l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  pure $ composeSubst s1 s2
mgu (TVar u) t  = varBind u t
mgu t (TVar u)  = varBind u t
mgu TInt TInt   = pure mempty
mgu TBool TBool = pure mempty
mgu t1 t2       = throwE $
  mconcat
  [ "types don't unify: '"
  , show t1
  , "' vs '"
  , show t2
  , "'"
  ]

varBind :: TName -> Type -> TI Subst
varBind u t | t == TVar u
              = pure mempty
            | S.member u (free t)
              = throwE
                $ mconcat
                  [ "occurs check: '"
                  , show u
                  , "' vs '"
                  , show t
                  , "'"
                  ]
            | otherwise = pure [(u, t)]

tiLit :: Lit -> TI (Subst, Type)
tiLit (LInt _)  = pure (mempty, TInt)
tiLit (LBool _) = pure (mempty, TBool)

ti :: (Show a, Ord a) => (Int -> a) -> TypeEnv a -> Exp a -> TI (Subst, Type)
ti _ (TypeEnv env) (V a) =
  case M.lookup a env of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> do
      (,) <$> pure mempty <*> instantiate sigma
ti _ _ (Lit l) = tiLit l
ti f (TypeEnv env) (Lam x) = do
  name <- newVName f
  tv <- newTyVar
  let env' = TypeEnv $ env <> [(name, Scheme [] tv)]
      e = splat pure (const $ pure name) x
  (s1, t1) <- ti f env' e
  pure (s1, TArr (apply s1 tv) t1)
ti f env exp@(e1 :@ e2) =
  do
    tv <- newTyVar
    (s1, t1) <- ti f env e1
    (s2, t2) <- ti f (apply s1 env) e2
    s3 <- mgu (apply s2 t1) (TArr t2 tv)
    pure (composeSubst s3 $ composeSubst s2 s1, apply s3 tv)
  `catchE` \e -> throwE $ e <> "\n in " <> show exp

typeInference :: Map String Scheme -> Exp String -> TI Type
typeInference env e = do
  (s, t) <- ti (("v" <>) . show) (TypeEnv env) e
  pure $ apply s t


class Types a where
  free :: a -> Set TName
  apply :: Map TName Type -> a -> a

instance Types Type where
  free (TVar a)   = [a]
  free TInt       = []
  free TBool      = []
  free (TArr a b) = free a <> free b

  apply s (TVar n)   = maybe (TVar n) id $ M.lookup n s
  apply s (TArr a b) = TArr (apply s a) (apply s b)
  apply _ t          = t

instance Types Scheme where
  free (Scheme vars t) = free t S.\\ S.fromList vars

  -- apply all `s` that are not quantified?
  apply s (Scheme vars t) =
    Scheme vars $ apply (foldr M.delete s vars) t

instance (Types a) => Types [a] where
  free    = foldr (<>) S.empty . fmap free
  apply s = fmap $ apply s

type Subst = Map TName Type

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = fmap (apply s1) s2 <> s1

newtype TypeEnv a = TypeEnv { unTypeEnv :: Map a Scheme }

remove :: Ord a => TypeEnv a -> a -> TypeEnv a
remove (TypeEnv env) var = TypeEnv $ M.delete var env

instance Types (TypeEnv a) where
  free = free . M.elems . unTypeEnv
  apply s = TypeEnv . fmap (apply s) . unTypeEnv

generalize :: TypeEnv a -> Type -> Scheme
generalize env t =
  Scheme (S.toList $ free t S.\\ free env) t


freeVars :: Ord a => Exp a -> Set a
freeVars (V a)    = [a]
freeVars (Lit _)  = []
freeVars (a :@ b) = freeVars a <> freeVars b
freeVars (Lam x)  = S.fromList $ foldMapScope (const []) pure x


lam :: Eq a => a -> Exp a -> Exp a
lam x e = Lam (abstract1 x e)


whnf :: Exp a -> Exp a
whnf (f :@ a) =
  case whnf f of
    Lam b -> whnf (instantiate1 a b)
    f' -> f' :@ a
whnf e = e


main :: IO ()
main = do
  print $ whnf $ lam 'x' (V 'x' :@ V 'x')
              :@ lam 'x' (V 'x' :@ V 'x')

