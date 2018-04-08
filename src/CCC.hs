{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module CCC where

import TypeChecking
import Types
import Bound



toCCC :: Exp VName -> Exp VName
toCCC (Lam x) =
  case unscope x of
    V (B ()) -> "id"
    V (F a)  -> a
    u :@ v   ->
      foldl1 (:@)
        [ "o"
        , "apply"
        , foldl1 (:@)
          [ "fork"
          , toCCC . Lam $ Scope u
          , toCCC . Lam $ Scope v
          ]
        ]
    Lam _    -> error "hmm"
    LInt i   -> "const" :@ LInt i
    LBool b  -> "const" :@ LBool b
    LProd a b -> toCCC $ Lam $ Scope $ (V $ F ",") :@ a :@ b
    LUnit    -> "const" :@ LUnit
toCCC x = x

