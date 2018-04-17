{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wall          #-}

module Compiler where

import           Control.Lens ((<&>))
import           Control.Monad (join)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           Data.Traversable (for)
import           TypeChecking
import           Types
import           Utils


getGDCBinding :: GenDataCon -> (VName, (Qual Type, Exp VName))
getGDCBinding gdc = (gdcName gdc, (gdcConType gdc, gdcCon gdc))


compile :: CompUnit -> TI (Map VName (Exp VName), (ClassEnv, SymTable VName))
compile cu = do
  -- build classes
  let classes = cuClasses cu
      allCGdcs = M.fromList
               . zip (fmap cName classes)
               $ fmap buildDictType classes
      cgdcs = fmap fst allCGdcs
      classMethods = M.fromList
                   . join
                   . M.elems
                   $ fmap snd allCGdcs

  -- build instances + dicts
  let instances = cuInsts cu
      instDicts =
        instances <&> \c ->
          let cname = predCName . unqualType $ irQuals c
           in buildDict (cgdcs M.! cname) c

  -- build class env
  let cenv = ClassEnv
           . M.fromList
           $ instances <&> \i ->
               (unqualType $ irQuals i, () <$ i)

  -- build defs
  let allDefs = mconcat $
        [ M.fromList . fmap getGDCBinding $ mconcat
          [ M.elems cgdcs
          , cuGDCs cu
          , fmap fst $ cuRecords cu
          ]
        , classMethods
        , M.fromList instDicts
        , cuDecls cu
        , M.fromList . join . fmap snd $ cuRecords cu
        ]

  -- build initial symbol table
  let sym = SymTable $ fmap (generalize (SymTable @VName mempty) . fst) allDefs

  defs <- for (fmap snd allDefs) $ \i -> do
    (_, e) <- typeInference cenv sym i
    pure e

  pure (defs, (cenv, sym))

