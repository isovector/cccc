{-# LANGUAGE TupleSections #-}

module Compiler where

import           Control.Lens ((<&>))
import           Control.Monad (join)
import           Data.Bifunctor (second)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           Data.Traversable (for)
import           TypeChecking
import           Types
import           Utils

prelude :: Map VName (Exp VName)
Right (prelude, _, _) = runTI $ compile preludeSource

preludeSource :: CompUnit
preludeSource = CompUnit
  { cuClasses =
    [ Class "a" "Eq"
      $ M.fromList [("==", [] :=> "a" :-> "a" :-> TBool)]
    ]

  , cuInsts =
    [ InstRep ([] :=> IsInst "Eq" TBool) $ M.fromList
      [ ( "=="
        , lam "x" $ lam "y" $
            case_ "x"
              [ ( PFalse
                , case_ "y"
                  [ ( PFalse
                    , "True"
                    )
                  , ( PWildcard
                    , "False"
                    )
                  ]
                )
              , ( PTrue
                , case_ "y"
                  [ ( PTrue
                    , "True"
                    )
                  , ( PWildcard
                    , "False"
                    )
                  ]
                )
              ])
      ]
    , InstRep ([IsInst "Eq" "a", IsInst "Eq" "b"] :=> IsInst "Eq" (TSum "a" "b"))
      $ M.fromList
      [ ( "=="
        , lam "x" $ lam "y" $
            case_ "x"
              [ ( PCon "Inl" ["x1"]
                , case_ "y"
                  [ ( PCon "Inl" ["y1"]
                    , "==" :@ "x1" :@ "y1"
                    )
                  , ( PWildcard
                    , "False"
                    )
                  ]
                )
              , ( PCon "Inr" ["x1"]
                , case_ "y"
                  [ ( PCon "Inr" ["y1"]
                    , "==" :@ "x1" :@ "y1"
                    )
                  , ( PWildcard
                    , "False"
                    )
                  ]
                )
              ])
      ]
    ]

  , cuGDCs =
    [ buildDataCon "Inl" ["a"] . Just $ TSum "a" "b"
    , buildDataCon "Inr" ["b"] . Just $ TSum "a" "b"
    , buildDataCon "False" []  . Just $ TBool
    , buildDataCon "True" []   . Just $ TBool
    , buildDataCon "Unit" []   . Just $ TUnit
    ]

  , cuRecords =
    [ buildRecord "," [("fst", "a"), ("snd", "b")] Nothing
    ]

  , cuDecls = M.fromList
    [ ( "eq"
      , ( [IsInst "Eq" "a"] :=> "a" :-> "a" :-> TBool
        , "=="
        )
      )
    ]
  }


getGDCBinding :: GenDataCon -> (VName, (Qual Type, Exp VName))
getGDCBinding gdc = (gdcName gdc, (gdcConType gdc, gdcCon gdc))


genMethods :: Class -> Map VName (Qual Type, Exp VName)
genMethods c = flip M.mapWithKey (cMethods c) $ \k m ->
  ( IsInst (cName c) (TCon $ cVars c) : qualPreds m :=> unqualType m
  , V k
  )


compile :: CompUnit -> TI (Map VName (Exp VName), ClassEnv, SymTable VName)
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

        ] <> fmap genMethods classes

  -- build initial symbol table
  let sym = SymTable $ fmap (generalize (SymTable @VName mempty) . fst) allDefs

  defs <- for (fmap snd allDefs) $ \i -> do
    (_, e) <- typeInference cenv (unSymTable sym) i
    pure e

  pure (defs, cenv, sym)

