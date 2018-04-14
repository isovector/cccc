{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module CCC where

import Bound
import Control.Arrow ((&&&))
import Data.Bool (bool)
import Data.Monoid ((<>))
import TypeChecking
import Types


fork :: (a -> b) -> (a -> c) -> (a -> (b, c))
fork = (&&&)

apply :: (a -> b, a) -> b
apply = uncurry ($)


simplify :: Exp VName -> Exp VName
simplify ("." :@ "apply" :@ ("fork" :@ ("curry" :@ h) :@ g)) =
  simplify $ "." :@ h :@ ("fork" :@ "id" :@ g)
simplify (V n)       = V n
simplify (LCon c)    = LCon c
simplify (a :@ b)    = simplify a :@ simplify b
simplify _           = error "simplify can only be done on pointfree exps"


toCCC :: Exp VName -> Exp VName
toCCC (Lam n x) =
  case unscope x of
    V (B ())    -> "id"
    V (F (V a)) ->
      (case a of
         -- TODO(sandy): more generally we should look at the SymTable and see
         -- if there is a categorical context in order to return id here
        "id"  -> id
        ","   -> id
        "fst" -> id
        "snd" -> id
        "inr" -> id
        "inl" -> id
        "."   -> id
        _ -> \z -> ("." :@ z :@ "shouldInline")
      ) "const" :@ V a
    V (F _)     -> error "this should never be hit"
    LProd a b  -> anonLam $ (V $ F ",") :@ a :@ b
    LInl b   -> anonLam $ (V $ F $ "inl") :@ b
    LInr b   -> anonLam $ (V $ F $ "inr") :@ b
    u :@ v      ->
      foldl1 (:@)
        [ "."
        , "apply"
        , foldl1 (:@)
          [ "fork"
          , anonLam u
          , anonLam v
          ]
        ]
    Lam n2 y    ->
      let name = VName $ unVName n <> "+" <> unVName n2
       in
        ( case unscope y of
            V (F _) -> ("curry" :@)
            _       -> id
        ) . toCCC
          . lam name
          . unsafeInst1  ("snd" :@ V name)
          . instantiate1 ("fst" :@ V name)
          $ x
    LInt i     -> "const" :@ LInt i
    LTrue      -> "const" :@ LTrue
    LFalse     -> "const" :@ LFalse
    -- TODO(sandy): these are icky
    LUnit      -> "const" :@ LUnit
    LCon l -> error $ show l
    -- TODO(sandy): is this right? it discards info
    Assert a _ -> anonLam a
    Let _ b e  -> anonLam $ instantiate1 b e
  where
    anonLam = toCCC . Lam n . Scope
-- eta abstract a point-free function
toCCC z = toCCC $ lam "!!!!z" $ z :@ "!!!!z"


unsafeInst1 :: Exp VName -> Exp VName -> Exp VName
unsafeInst1 z (Lam _ x) = instantiate1 z x
unsafeInst1 _ _ = error "unsafeInst1"

