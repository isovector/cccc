{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wall          #-}

module Evaluation where

import           Bound
import           Control.Lens ((<&>))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           TypeChecking
import           Types


extract :: Pat -> Exp VName -> Maybe [(VName, Exp VName)]
extract (PVar i)  a      = pure $ pure (i, a)
extract (PAs i p) a      = (:) <$> pure (i, a) <*> extract p a
extract PWildcard _      = pure []
extract (PCon "*" [p1, p2])
        (LProd a b)      = (++) <$> extract p1 a <*> extract p2 b
extract (PCon "*" [_, _])
        _                = Nothing
extract (PCon "*" _) _   = error "bad number of pattern ctors to *"
extract (PCon "inl" [p])
        (LInj False a)   = extract p a
extract (PCon "inl" [_])
        (LInj True _)    = Nothing
extract (PCon "inl" _) _ = error "bad number of pattern ctors to inl"
extract (PCon "inr" [p])
        (LInj True a)    = extract p a
extract (PCon "inr" [_])
        (LInj False _)   = Nothing
extract (PCon "inr" _) _ = error "bad number of pattern ctors to inr"
extract (PCon _ _) _     = error "bad constructor!"
extract (PLit l) (Lit l')
    | l == l'            = Just []
    | otherwise          = Nothing
extract (PLit _) _       = Nothing



whnf :: Map VName (Exp VName) -> Exp VName -> Exp VName
whnf std (V name) =
  case M.lookup name std of
    Just x  -> x
    Nothing -> V name
whnf std (f :@ a) =
  case whnf std f of
    Lam _ b -> whnf std (instantiate1 a b)
    f' -> f' :@ a
whnf _ z@(Lit _)      = z
whnf _ z@(LProd _ _)  = z
whnf _ z@(LInj _ _)   = z
whnf std (Let _ v e)  = whnf std $ instantiate1 v e
whnf std (Assert e _) = whnf std e
whnf std (Case e ps)  =
  let e'              = whnf std e
   in whnf std $ head $ flip mapMaybe ps $ \(p, v) ->
     extract p e' <&> \(M.fromList -> vs) ->
       instantiate (vs M.!) v
whnf _ z@(Lam _ _)    = z

