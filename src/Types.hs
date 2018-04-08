{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# OPTIONS_GHC -Wall                   #-}

module Types where

import           Bound hiding (instantiate)
import           Control.Monad.State
import           Data.Char (isLower)
import           Data.Eq.Deriving (deriveEq1)
import           Data.List (intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Semigroup (Semigroup (..))
import           Data.Set (Set)
import qualified Data.Set as S
import           GHC.Exts (IsString (..))
import           Prelude hiding (exp)
import           Text.Show.Deriving (deriveShow1)


infixl 9 :@@
data Type
  = TVar TName
  | TInt
  | TUnit
  | TVoid
  | TCon TName
  | Type :@@ Type
  deriving (Eq, Ord)


pattern TProd :: Type -> Type -> Type
pattern TProd a b = TCon "*" :@@ a :@@ b


pattern TSum :: Type -> Type -> Type
pattern TSum a b = TCon "+" :@@ a :@@ b


pattern TArr :: Type -> Type -> Type
pattern TArr a b = TCon "->" :@@ a :@@ b


pattern TBool :: Type
pattern TBool = TSum TUnit TUnit


pattern TCat :: Type -> Type -> Type -> Type
pattern TCat k a b = k :@@ a :@@ b


instance IsString Type where
  fromString x =
    case isLower $ head x of
      False -> TCon $ fromString x
      True  -> TVar $ fromString x


instance Show Type where
  showsPrec x (TArr a b)  = showParen (x > 0)
    $ showsPrec 1 a
    . showString " -> "
    . showsPrec 0 b
  showsPrec _ (TSum TUnit TUnit) = showString "2"
  showsPrec x (TProd a b) = showParen (x > 3)
    $ showsPrec 4 a
    . showString " * "
    . showsPrec 3 b
  showsPrec x (TSum a b)  = showParen (x > 5)
    $ showsPrec 6 a
    . showString " + "
    . showsPrec 5 b
  showsPrec _ (TVar n)    = showString $ unTName n
  showsPrec _ (TCon n)    = showString $ unTName n <> "!"
  showsPrec x (a :@@ b)   = showParen (x > 9)
    $ showsPrec 9 a
    . showString " "
    . showsPrec 10 b
  showsPrec _ TInt        = showString "Int"
  showsPrec _ TUnit       = showString "1"
  showsPrec _ TVoid       = showString "0"


newtype TName = TName { unTName :: String }
  deriving (Eq, Ord, IsString)

instance Show TName where
  show = unTName


infixl 9 :@
data Exp a
  = V a
  | LInt Int
  | LBool Bool
  | LUnit
  | LProd (Exp a) (Exp a)
  | LInj Bool (Exp a)
  | Exp a :@ Exp a
  | Lam (Scope () Exp a)
  | Let (Scope () Exp a) (Scope () Exp a)
  -- TODO(sandy): doesn't work for polymorphic assertions (occurs checks)
  | Assert (Exp a) Type
  deriving (Functor, Foldable, Traversable)


instance IsString a => IsString (Exp a) where
  fromString = V . fromString


instance Applicative Exp where
  pure  = V
  (<*>) = ap


instance Monad Exp where
  return       = pure
  V a        >>= f = f a
  LInt i     >>= _ = LInt i
  LBool i    >>= _ = LBool i
  LUnit      >>= _ = LUnit
  LProd a b  >>= f = LProd (a >>= f) (b >>= f)
  LInj x a   >>= f = LInj x (a >>= f)
  (x :@ y)   >>= f = (x >>= f) :@ (y >>= f)
  Lam e      >>= f = Lam (e >>>= f)
  Let bs b   >>= f = Let (bs >>>= f) (b >>>= f)
  Assert e t >>= f = Assert (e >>= f) t


deriveEq1 ''Exp
deriveShow1 ''Exp

deriving instance Eq a   => Eq (Exp a)
deriving instance Show a => Show (Exp a)


infixr 0 :=>
data Qual t = (:=>)
  { qualPreds  :: [Pred]
  , unqualType :: t
  } deriving (Eq, Ord, Functor, Traversable, Foldable)


instance Show t => Show (Qual t) where
  show (a :=> b) =
    case length a of
      0 -> show b
      1 -> show (head a) <> " => " <> show b
      _ -> mconcat
             [ "("
             , intercalate ", " $ fmap show a
             , ") => "
             , show b
             ]

data Pred = IsInst
  { predCName :: CName
  , predInst  :: Type
  } deriving (Eq, Ord)


instance Show Pred where
  show (IsInst a b) = show a <> " (" <> show b <> ")"


newtype CName = CName { unCName :: String }
  deriving (Eq, Ord, IsString)


instance Show CName where
  show = unCName


newtype VName = VName { unVName :: String }
  deriving (Eq, Ord, IsString)


instance Show VName where
  show = unVName


data Scheme = Scheme
  { schemeVars :: [TName]
  , schemeType :: Qual Type
  }
  deriving (Eq, Ord, Show)


pattern (:->) :: Type -> Type -> Type
pattern (:->) a b = TArr a b
infixr 1 :->


class Types a where
  free :: a -> Set TName
  apply :: Subst -> a -> a


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


instance Types a => Types [a] where
  free = mconcat . fmap free
  apply s = fmap (apply s)


instance Types a => Types (Qual a) where
  free (a :=> b)    = free a <> free b
  apply s (a :=> b) = apply s a :=> apply s b


instance Types Pred where
  free (IsInst _ a)    = free a
  apply s (IsInst a b) = IsInst a (apply s b)


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


newtype ClassEnv = ClassEnv
  { unClassEnv :: Set (Qual Pred)
  } deriving (Eq, Ord, Show, Monoid)


newtype SymTable a = SymTable
  { unSymTable :: Map a Scheme
  } deriving (Eq, Ord, Show)


instance Types (SymTable a) where
  free = free . M.elems . unSymTable
  apply s = SymTable . fmap (apply s) . unSymTable


pattern CCat :: Type -> Pred
pattern CCat t = IsInst "Category" t


whnf :: Map VName (Exp VName) -> Exp VName -> Exp VName
whnf std (V name) =
  case M.lookup name std of
    Just x -> x
    Nothing -> V name
whnf std (f :@ a) =
  case whnf std f of
    Lam b -> whnf std (instantiate1 a b)
    f' -> f' :@ a
whnf _ e = e


lam :: Eq a => a -> Exp a -> Exp a
lam x e = Lam (abstract1 x e)


let_ :: Eq a => a -> Exp a -> Exp a -> Exp a
let_ x v e = Let (abstract1 x v) (abstract1 x e)

