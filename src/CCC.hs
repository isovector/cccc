{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module CCC where

import Data.Monoid ((<>))
import TypeChecking
import Data.Bool (bool)
import Types
import Bound
import Control.Monad.State

toCCC :: Exp VName -> Exp VName
toCCC = flip evalState 0 . toCCC'


toCCC' :: Exp VName -> State Int (Exp VName)
toCCC' (Lam _ x) =
  case unscope x of
    V (B ())    -> pure $ "id"
    V (F (V a)) -> pure $ "const" :@ V a
    V (F _)     -> error "this should never be hit"
    u :@ v      -> do
      u' <- toCCC' $ anonLam u
      v' <- toCCC' $ anonLam v
      pure $ foldl1 (:@)
        [ "."
        , "apply"
        , foldl1 (:@)
          [ "fork"
          , u'
          , v'
          ]
        ]
    Lam _ _    -> do
      name <- VName . ("!!!" <>) . show <$> get
      modify (+1)
      toCCC' . lam name
             . unsafeInst1  ("snd" :@ V name)
             $ instantiate1 ("fst" :@ V name) x
    LInt i     -> pure $ "const" :@ LInt i
    LBool b    -> pure $ "const" :@ LBool b
    LProd a b  -> toCCC' . anonLam $ (V $ F ",") :@ a :@ b
    LInj a b   -> toCCC' . anonLam $ (V $ F $ bool "inl" "inr" a) :@ b
    LUnit      -> pure $ "const" :@ LUnit
    -- TODO(sandy): is this right? it discards info
    Assert a _ -> toCCC' $ anonLam a
    Let _ b e  -> toCCC' . anonLam $ instantiate1 b e
  where
    anonLam = Lam "eta" . Scope
-- eta abstract a point-free function
toCCC' z = toCCC' $ lam "!!!!z" $ z :@ "!!!!z"


unsafeInst1 :: Exp VName -> Exp VName -> Exp VName
unsafeInst1 z (Lam _ x) = instantiate1 z x
unsafeInst1 _ _ = error "unsafeInst1"

