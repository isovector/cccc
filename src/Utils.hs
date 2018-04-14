{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Utils where

import           Control.Lens ((<&>))
import qualified Data.Map as M
import           Data.Traversable (for)
import           Types
import TypeChecking


-- buildDataCon
--     :: VName
--     -> [Type]
--     -> (Qual Type, Exp VName)
-- buildDataCon n@(VName s) ts =
--   let ks = fmap (either error id . runTI . kind) ts
--       k = foldr (:>>) KStar ks
--       t = TCon (TName s k)
--       ls = zip (fmap VName letters) ts
--    in ([] :=> t,)
--     $ foldr (\l e -> lam l e)
--             (foldl _ (L) _)
--     $ fmap fst ls


buildDict :: InstRep a -> Exp VName
buildDict ir =
  lam "m" $ case_ "m" $
    (M.assocs $ irImpls ir) <&> \(VName m, e) ->
      (PLit (LitString m), e)

