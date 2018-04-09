{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module CCC where

import Data.Bool (bool)
import Types
import Bound


toCCC :: Exp VName -> Exp VName
toCCC x =
  Assert
    (maybe ("inr" :@ LUnit) ("inl" :@) $ toCCC' x)
    (TSum "a" TUnit)


toCCC' :: Exp VName -> Maybe (Exp VName)
toCCC' (Lam x) =
  case unscope x of
    V (B ())    -> pure "id"
    V (F (V a)) -> pure $ "const" :@ V a
    V (F _)     -> error "this should never be hit"
    u :@ v      -> do
      u' <- toCCC' $ Lam $ Scope u
      v' <- toCCC' $ Lam $ Scope v
      pure $ foldl1 (:@)
        [ "."
        , "apply"
        , foldl1 (:@)
          [ "fork"
          , u'
          , v'
          ]
        ]
    Lam _      -> toCCC'
                . lam "!!!z"
                . unsafeInst1  ("snd" :@ "!!!z")
                $ instantiate1 ("fst" :@ "!!!z") x
    LInt i     -> pure $ "const" :@ LInt i
    LBool b    -> pure $ "const" :@ LBool b
    LProd a b  -> toCCC' . Lam . Scope $ (V $ F ",") :@ a :@ b
    LInj a b   -> toCCC' . Lam . Scope $ (V $ F $ bool "inl" "inr" a) :@ b
    LUnit      -> pure $ "const" :@ LUnit
    -- TODO(sandy): is this right? it discards info
    Assert a _ -> toCCC' . Lam $ Scope a
    Let b e    -> toCCC' . Lam . Scope $ instantiate1 b e
toCCC' _ = Nothing


unsafeInst1 :: Exp VName -> Exp VName -> Exp VName
unsafeInst1 z (Lam x) = instantiate1 z x
unsafeInst1 _ _ = error "unsafeInst1"

