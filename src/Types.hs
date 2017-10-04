{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Types where

import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Control.Monad.Trans.Except
import qualified Data.Map as M
import Control.Monad.State

type Name = String

data Expr
  = Var Name
  | App Expr Expr
  | Lam Name Expr
  -- | Let Name Expr Expr
  | Lit Lit
  deriving (Show, Eq, Ord)

data Lit
  = LInt Integer
  | LBool Bool
  deriving (Show, Eq, Ord)

data Value
  = Closure Name Expr (M.Map Name Value)
  | VLit Lit
  deriving (Show, Eq, Ord)

makeBaseFunctor ''Expr

eval :: M.Map Name Value -> Expr -> Value
eval scope (Var n) = scope M.! n
eval scope (Lam n x) = Closure n x scope
eval scope (App a b) = apply (eval scope a) (eval scope b)
eval scope (Lit l) = VLit l

apply :: Value -> Value -> Value
apply (Closure n x scope) z = eval (M.insert n z scope) x
apply _ z = error "can't apply a non closure"


i :: Expr
i = λ"x" --> Var "x"

k :: Expr
k = λλ"a" "b" --> Var "a"

s :: Expr
s = λλλ"a" "b" "c" --> (Var "a" `App` Var "c")
                 `App` (Var "b" `App` Var "c")

λ :: Name -> Expr -> Expr
λ = Lam

λλ :: Name -> Name -> Expr -> Expr
λλ a b e = λ a --> λ b --> e

λλλ :: Name -> Name -> Name -> Expr -> Expr
λλλ a b c e = λ a --> λ b --> λ c --> e

(-->) :: (a -> b) -> a -> b
(-->) = ($)

infixr 0 -->

ski :: M.Map Name Value
ski = [ ("s", eval M.empty s)
      , ("k", eval M.empty k)
      , ("i", eval M.empty i)
      ]

apping :: String -> Expr
apping = foldl (\b a -> App b (Var $ pure a)) (Var "i")

