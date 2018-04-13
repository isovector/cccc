{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wall          #-}

module Evaluation where

import           Bound
import           Control.Lens ((<&>))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Monoid ((<>))
import           StdLib
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
extract (PCon "inl" [p])
        (LBool False)    = extract p LUnit
extract (PCon "inl" [_])
        _                = Nothing
extract (PCon "inl" _) _ = error "bad number of pattern ctors to inl"
extract (PCon "inr" [p])
        (LInj True a)    = extract p a
extract (PCon "inr" [p])
        (LBool True)     = extract p LUnit
extract (PCon "inr" [_])
        _                = Nothing
extract (PCon "inr" _) _ = error "bad number of pattern ctors to inr"
extract (PCon _ _) _     = error "bad constructor!"
extract (PLit l) (Lit l')
    | l == l'            = Just []
    | otherwise          = Nothing
extract (PLit _) _       = Nothing



whnf :: ClassEnv -> Map VName (Exp VName) -> Exp VName -> Exp VName
whnf _ std (V name) =
  case M.lookup name std of
    Just x  -> x
    Nothing -> V name
whnf cenv std (V "error" :@ a) =
  error $ "error: " <> show (whnf cenv std a)
whnf cenv std (V m :@ LDict t) =
  whnf cenv std $ irImpls (unClassEnv cenv M.! t) M.! m
whnf cenv std (f :@ a) =
  case whnf cenv std f of
    Lam _ b -> whnf cenv std (instantiate1 a b)
    f' -> f' :@ a
whnf _ _ z@(Lit _)      = z
whnf _ _ z@(LProd _ _)  = z
whnf _ _ z@(LInj _ _)   = z
whnf cenv std (Let _ v e)  = whnf cenv std $ instantiate1 v e
whnf cenv std (Assert e _) = whnf cenv std e
whnf cenv std (Case e ps)  =
  let e'              = whnf cenv std e
   in whnf cenv std $ head $ flip mapMaybe ps $ \(p, v) ->
     extract p e' <&> \(M.fromList -> vs) ->
       instantiate (vs M.!) v
whnf _ _ z@(Lam _ _)    = z
whnf _ _ z@(LDict _)    = z

