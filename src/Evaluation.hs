{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wall          #-}

module Evaluation where

import           Bound
import           Control.Lens ((<&>))
import           Control.Monad (join)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Monoid ((<>))
import           TypeChecking
import           Types
import           Utils


extract :: Pat -> Exp VName -> Maybe [(VName, Exp VName)]
extract (PVar i)  a      = pure $ pure (i, a)
extract (PAs i p) a      = (:) <$> pure (i, a) <*> extract p a
extract PWildcard _      = pure []
extract (PCon c ps) a
  | Just (c', as) <- unravel a
  , c == c'              =
      if length ps /= length as
         then error $ "bad number of pattern ctors to " <> show c
         else fmap join
            . traverse (uncurry extract)
            $ zip ps as
extract (PCon _ _) _     = Nothing
extract (PLit l) (Lit l')
    | l == l'            = Just []
    | otherwise          = Nothing
extract (PLit _) _       = Nothing



whnf :: Map VName (Exp VName) -> Exp VName -> Exp VName
whnf std (V name) =
  case M.lookup name std of
    Just x  -> x
    Nothing -> V name
whnf _ z@(LCon _) = z
whnf std (f :@ a) =
  case whnf std f of
    Lam _ b -> whnf std (instantiate1 a b)
    f' -> f' :@ a
whnf _ z@(Lit _)      = z
whnf std (Let _ v e)  = whnf std $ instantiate1 v e
whnf std (Assert e _) = whnf std e
whnf std (Case e ps)  =
  let e'              = whnf std e
   in whnf std $ head $ flip mapMaybe ps $ \(p, v) ->
     extract p e' <&> \(M.fromList -> vs) ->
       instantiate (vs M.!) v
whnf _ z@(Lam _ _)    = z

