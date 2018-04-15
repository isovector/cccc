{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# OPTIONS_GHC -Wall                   #-}

module Types where

import           Bound
import           Control.Lens ((<&>))
import           Control.Monad.State
import           Data.Bifunctor (second)
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
  | Type :@@ Type
  deriving (Eq, Ord)



infixr 9 :>>
data Kind
  = KStar
  | KConstraint
  | Kind :>> Kind
  deriving (Eq, Ord)


instance Show Kind where
  showsPrec _ KStar  = showString "*"
  showsPrec _ KConstraint  = showString "Constraint"
  showsPrec x (a :>> b)  = showParen (x > 0)
    $ showsPrec 1 a
    . showString " -> "
    . showsPrec 0 b


pattern TK2 :: String -> Type -> Type -> Type
pattern TK2 c a b = TVar (TName c K2) :@@ a :@@ b

pattern K2 :: Kind
pattern K2 = KStar :>> KStar :>> KStar


pattern TProd :: Type -> Type -> Type
pattern TProd a b = TCon (TName "," K2) :@@ a :@@ b

pattern TSum :: Type -> Type -> Type
pattern TSum a b = TCon (TName "+" K2) :@@ a :@@ b

pattern TArr :: Type -> Type -> Type
pattern TArr a b = TArrCon :@@ a :@@ b

pattern TArrCon :: Type
pattern TArrCon = TCon (TName "->" K2)

pattern TBool :: Type
pattern TBool = "2"

pattern TUnit :: Type
pattern TUnit = "1"

pattern TString :: Type
pattern TString = "String"

pattern TInt :: Type
pattern TInt = "Int"


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
  showsPrec x (TProd a b) = showParen (x > 3)
    $ showsPrec 4 a
    . showString " * "
    . showsPrec 4 b
  showsPrec x (TSum a b)  = showParen (x > 5)
    $ showsPrec 6 a
    . showString " + "
    . showsPrec 6 b
  showsPrec _ (TVar n)    = showString $ unTName n
  showsPrec _ (TCon n)    =
    showParen (all ((||) <$> isSymbol <*> isPunctuation) $ unTName n)
    $ showString $ unTName n
  showsPrec x (a :@@ b)   = showParen (x > 9)
    $ showsPrec 9 a
    . showString " "
    . showsPrec 10 b


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


data Pat
  = PVar VName
  | PWildcard
  | PAs VName Pat
  | PCon VName [Pat]
  | PLit Lit
  deriving (Eq, Ord)


instance IsString Pat where
  fromString = PVar . fromString


pattern PFalse :: Pat
pattern PFalse = PCon "False" []


pattern PTrue :: Pat
pattern PTrue = PCon "True" []


instance Show Pat where
  showsPrec _ PWildcard  = showString "_"
  showsPrec _ (PVar x)   = showString $ show x
  showsPrec _ (PAs x p)  =
      showString (show x)
    . showString "@"
    . showsPrec 10 p
  showsPrec _ (PLit l) = showString $ show l
  showsPrec x (PCon n ps)  = showParen (x > 0)
    $ showString (show $ V n)
    . foldl (.) id (fmap ((showString " " .) . showsPrec 10) ps)


-- | a new variable to introduce
data Assump a = (:>:)
  { assumpName :: VName
  , assumpVal :: a
  }
  deriving (Eq, Ord, Show)


data Scheme = Scheme
  { schemeVars :: [TName]
  , schemeType :: Qual Type
  }
  deriving (Eq, Ord)


mkScheme :: Type -> Scheme
mkScheme t = Scheme mempty $ [] :=> t


infixr 0 :=>
data Qual t = (:=>)
  { qualPreds  :: [Pred]
  , unqualType :: t
  } deriving (Eq, Ord, Functor, Traversable, Foldable)

data Pred = IsInst
  { predCName :: TName
  , predInst  :: Type
  } deriving (Eq, Ord)


infixl 9 :@
data Exp a
  = V a
  | Lit Lit
  | LCon VName
  | Exp a :@ Exp a
  | Lam VName (Scope () Exp a)
  | Let VName (Exp a) (Scope () Exp a)
  | Case (Exp a) [(Pat, Scope VName Exp a)]
  | Assert (Exp a) Type
  deriving (Functor, Foldable, Traversable)


data Lit
  = LitInt Int
  | LitString String
  deriving (Eq, Ord)

instance Show Lit where
  show (LitInt i) = show i
  show (LitString i) = show i


instance IsString a => IsString (Exp a) where
  fromString x =
    case isLower $ head x of
      False -> LCon $ fromString x
      True  -> V $ fromString x


instance Applicative Exp where
  pure  = V
  (<*>) = ap


instance Monad Exp where
  return       = pure
  V a        >>= f = f a
  LCon a     >>= _ = LCon a
  Lit  i     >>= _ = Lit i
  (x :@ y)   >>= f = (x >>= f) :@ (y >>= f)
  Lam n e    >>= f = Lam n (e >>>= f)
  Let n bs b >>= f = Let n (bs >>= f) (b >>>= f)
  Assert e t >>= f = Assert (e >>= f) t
  Case e p   >>= f = Case (e >>= f) $ fmap (second (>>>= f)) p


pattern LInt :: Int -> Exp a
pattern LInt i = Lit (LitInt i)

pattern LString :: String -> Exp a
pattern LString s = Lit (LitString s)

pattern LProd :: Exp a -> Exp a -> Exp a
pattern LProd a b = LCon "," :@ a :@ b


newtype VName = VName { unVName :: String }
  deriving (Eq, Ord, IsString, Monoid)


instance Show VName where
  show = unVName


deriveEq1 ''Exp
deriveShow1 ''Exp

deriving instance Eq a   => Eq (Exp a)
deriving instance {-# OVERLAPPABLE #-} Show a => Show (Exp a)
deriving instance Show Scheme

instance Show (Exp VName) where
  showsPrec x (V a) =
    showParen ((||) <$> all ((||) <$> isSymbol <*> isPunctuation) <*> elem ' ' $ unVName a)
      $ showsPrec x a
  showsPrec x (LCon a) =
    showsPrec x $ TCon (TName (unVName a) KStar)
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
  showsPrec _ (Lit l)   = showString $ show l
  showsPrec x (Lam n z) = showParen (x >= 2)
    $ showString "λ"
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
  showsPrec x (Assert e t) = showParen (x > 0)
    $ showsPrec 0 e
    . showString " :: "
    . showsPrec 0 t
  showsPrec x (Case e ps) = showParen (x >= 2)
    $ showString "case "
    . showsPrec 0 e
    . showString " of {"
    . (drop 1 . foldl (.) id
        (ps <&> \(p, pe) ->
          showString "; "
            . showsPrec 0 p
            . showString " -> "
            . showsPrec 0 (instantiate V pe)))
    . showString " }"



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


instance Show Pred where
  show (IsInst a b) = show a <> " (" <> show b <> ")"



data Class = Class
  { cVars    :: [TName]
  , cName    :: TName
  , cMethods :: Map VName (Qual Type)
  } deriving (Eq, Ord, Show)


pattern (:->) :: Type -> Type -> Type
pattern (:->) a b = TArr a b
infixr 1 :->


class Types a where
  free :: a -> Set TName
  sub :: Subst -> a -> a


instance Types a => Types (Assump a) where
  free (_ :>: a)  = free a
  sub s (x :>: a) = x :>: sub s a


instance Types Type where
  free (TVar a)    = S.fromList [a]
  free (TCon _)    = S.fromList [] -- ?
  free (a :@@ b)   = free a <> free b

  sub s (TVar n)    = maybe (TVar n) id $ M.lookup n $ unSubst s
  sub _ (TCon n)    = TCon n
  sub s (a :@@ b)   = sub s a :@@ sub s b


instance Types a => Types [a] where
  free = mconcat . fmap free
  sub s = fmap (sub s)


instance Types a => Types (Qual a) where
  free (a :=> b)    = free a <> free b
  sub s (a :=> b) = sub s a :=> sub s b


instance Types Pred where
  free (IsInst _ a)    = free a
  sub s (IsInst a b) = IsInst a (sub s b)


instance Types Scheme where
  free (Scheme vars t) = free t S.\\ S.fromList vars

  -- sub all `s` that are not quantified?
  sub s (Scheme vars t) =
    Scheme vars $ sub (Subst $ foldr M.delete (unSubst s) vars) t


newtype Subst = Subst
  { unSubst :: Map TName Type }
  deriving (Eq, Show)


instance Monoid Subst where
  mempty = Subst mempty
  mappend s1 (Subst s2) =
    Subst $ fmap (sub s1) s2 <> unSubst s1


newtype ClassEnv = ClassEnv
  { unClassEnv :: Map Pred (InstRep ())
  } deriving (Eq, Show, Monoid)


data InstRep a = InstRep
  { irQuals :: Qual a
  , irImpls :: Map VName (Exp VName)
  } deriving (Eq, Show, Functor)


getQuals :: ClassEnv -> [Qual Pred]
getQuals = fmap (\(a, b) -> a <$ irQuals b) . M.assocs . unClassEnv

getInstReps :: ClassEnv -> [InstRep Pred]
getInstReps = fmap (\(p, i) -> p <$ i) . M.assocs . unClassEnv


newtype SymTable a = SymTable
  { unSymTable :: Map a Scheme
  } deriving (Eq, Ord, Show)


instance Types (SymTable a) where
  free = free . M.elems . unSymTable
  sub s = SymTable . fmap (sub s) . unSymTable


pattern CCat :: String -> Pred
pattern CCat t = IsInst "Category" (TVar (TName t K2))

pattern CCart :: String -> Pred
pattern CCart t = IsInst "Cartesian" (TVar (TName t K2))

pattern CTerm :: String -> Pred
pattern CTerm t = IsInst "Terminal" (TVar (TName t K2))

pattern CClosed :: String -> Pred
pattern CClosed t = IsInst "Closed" (TVar (TName t K2))


lam :: VName -> Exp VName -> Exp VName
lam x e = Lam x (abstract1 x e)

case_ :: Exp VName -> [(Pat, Exp VName)] -> Exp VName
case_ e ps
  = Case e
  . flip fmap ps
  $ \(p, ep) -> (p, abstract
  (\x -> bool Nothing (Just x) $ elem x $ pVars p) ep)

pVars :: Pat -> [VName]
pVars PWildcard  = []
pVars (PVar i)   = pure i
pVars (PAs i p)  = i : pVars p
pVars (PCon _ p) = foldMap pVars p
pVars (PLit _)   = []

let_ :: VName -> Exp VName -> Exp VName -> Exp VName
let_ x v = Let x v . abstract1 x

