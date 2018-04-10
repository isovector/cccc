{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# OPTIONS_GHC -Wall                   #-}

module Types where

import           Bound hiding (instantiate)
import           Control.Monad.State
import           Data.Bool (bool)
import           Data.Char (isLower, isSymbol, isPunctuation)
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
  | TCon TName
  | TInt
  | TUnit
  | TVoid
  | Type :@@ Type
  deriving (Eq, Ord)



infixr 9 :>>
data Kind
  = KStar
  | Kind :>> Kind
  deriving (Eq, Ord)


instance Show Kind where
  showsPrec _ KStar  = showString "*"
  showsPrec x (a :>> b)  = showParen (x > 0)
    $ showsPrec 1 a
    . showString " -> "
    . showsPrec 0 b


pattern TK2 :: String -> Type -> Type -> Type
pattern TK2 c a b = TVar (TName c K2) :@@ a :@@ b

pattern K2 :: Kind
pattern K2 = KStar :>> KStar :>> KStar


pattern TProd :: Type -> Type -> Type
pattern TProd a b = TProdCon :@@ a :@@ b

pattern TProdCon :: Type
pattern TProdCon = TCon (TName "*" K2)

pattern TSum :: Type -> Type -> Type
pattern TSum a b = TSumCon :@@ a :@@ b

pattern TSumCon :: Type
pattern TSumCon = TCon (TName "+" K2)

pattern TArr :: Type -> Type -> Type
pattern TArr a b = TArrCon :@@ a :@@ b

pattern TArrCon :: Type
pattern TArrCon = TCon (TName "->" K2)


pattern TBool :: Type
pattern TBool = TSum TUnit TUnit


pattern TCat :: String -> Type -> Type -> Type
pattern TCat k a b = TK2 k a b


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
    . showsPrec 4 b
  showsPrec x (TSum a b)  = showParen (x > 5)
    $ showsPrec 6 a
    . showString " + "
    . showsPrec 6 b
  showsPrec _ (TVar n)    = showString $ unTName n
  showsPrec _ (TCon n)    = showString $ unTName n <> "!"
  showsPrec x (a :@@ b)   = showParen (x > 9)
    $ showsPrec 9 a
    . showString " "
    . showsPrec 10 b
  showsPrec _ TInt        = showString "Int"
  showsPrec _ TUnit       = showString "1"
  showsPrec _ TVoid       = showString "0"


data TName
  = TName      String Kind
  | TFreshName String Kind
  deriving (Eq, Ord)


instance IsString TName where
  fromString = flip TName KStar


instance Show TName where
  show = unTName


unTName :: TName -> String
unTName (TName a _)      = a
unTName (TFreshName a _) = a


tKind :: TName -> Kind
tKind (TName _ k)      = k
tKind (TFreshName _ k) = k


infixl 9 :@
data Exp a
  = V a
  | LInt Int
  | LBool Bool
  | LUnit
  | LProd (Exp a) (Exp a)
  | LInj Bool (Exp a)
  | Exp a :@ Exp a
  | Lam VName (Scope () Exp a)
  | Let VName (Exp a) (Scope () Exp a)
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
  Lam n e    >>= f = Lam n (e >>>= f)
  Let n bs b >>= f = Let n (bs >>= f) (b >>>= f)
  Assert e t >>= f = Assert (e >>= f) t


newtype VName = VName { unVName :: String }
  deriving (Eq, Ord, IsString)


instance Show VName where
  show = unVName


deriveEq1 ''Exp
deriveShow1 ''Exp

deriving instance Eq a   => Eq (Exp a)
deriving instance {-# OVERLAPPABLE #-} Show a => Show (Exp a)

instance Show (Exp VName) where
  showsPrec x (V a) =
    showParen (all ((||) <$> isSymbol <*> isPunctuation) $ unVName a)
      $ showsPrec x a
  showsPrec x (V "." :@ a :@ b) =
    showParen (x >= 9)
      $ showsPrec 9 a
      . showString " . "
      . showsPrec 9 b
  showsPrec x (a :@ b) =
    showParen (x >= 10)
      $ showsPrec 9 a
      . showString " "
      . showsPrec 10 b
  showsPrec _ (LInt z)  = showString $ show z
  showsPrec _ (LBool z) = showString $ show z
  showsPrec _ LUnit     = showString "unit"
  showsPrec x (Lam n z) = showParen (x >= 2)
    $ showString "\\"
    . showString (show n)
    . showString ". "
    . showsPrec 1 (instantiate1 (V n) z)
  showsPrec x (Let n b e) = showParen (x > 0)
    $ showString "let "
    . showString (show n)
    . showString " = "
    . showsPrec 0 b
    . showString " in "
    . showsPrec 0 (instantiate1 (V n) e)
  showsPrec _ (LProd a b) = showParen True
    $ showsPrec 0 a
    . showString ", "
    . showsPrec 0 b
  showsPrec x (LInj b v) = showParen (x >= 10)
    $ showString (bool "inl" "inr" b)
    . showString " "
    . showsPrec 10 v
  showsPrec x (Assert e t) = showParen (x > 0)
    $ showsPrec 0 e
    . showString " :: "
    . showsPrec 0 t


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


pattern CCat :: String -> Pred
pattern CCat t = IsInst "Category" (TVar (TName t K2))

pattern CCart :: String -> Pred
pattern CCart t = IsInst "Cartesian" (TVar (TName t K2))

pattern CTerm :: String -> Pred
pattern CTerm t = IsInst "Terminal" (TVar (TName t K2))

pattern CClosed :: String -> Pred
pattern CClosed t = IsInst "Closed" (TVar (TName t K2))


whnf :: Map VName (Exp VName) -> Exp VName -> Exp VName
whnf std (V name) =
  case M.lookup name std of
    Just x -> x
    Nothing -> V name
whnf std (f :@ a) =
  case whnf std f of
    Lam _ b -> whnf std (instantiate1 a b)
    f' -> f' :@ a
whnf _ e = e


lam :: VName -> Exp VName -> Exp VName
lam x e = Lam x (abstract1 x e)


let_ :: VName -> Exp VName -> Exp VName -> Exp VName
let_ x v e = Let x v (abstract1 x e)

