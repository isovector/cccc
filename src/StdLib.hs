{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module StdLib where

import           Control.Arrow ((***))
import           Control.Monad (join)
import           Data.Bifunctor (first, second)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           TypeChecking
import           Types
import           Evaluation
import           Utils


classes :: [Class]
classes =
  [ Class ["a"]
          "Eq"
        $ M.fromList [("==", [] :=> "a" :-> "a" :-> TBool)]
  , Class ["a"] "Category" []
  ]

classGDCs :: Map TName (GenDataCon, [(VName, (Qual Type, Exp VName))])
classGDCs = M.fromList $ zip (fmap cName classes) $ fmap buildDictType classes


classEnv :: ClassEnv
classEnv = ClassEnv
  [ ( IsInst "Eq" TBool
    , InstRep ([] :=> ())
    $ [ ( "=="
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
              ]
        )
      ]
    )
  , ( IsInst "Eq" TUnit
    , InstRep ([] :=> ())
    $ [ ( "=="
        , lam "x" $ lam "y" "True"
        )
      ]
    )
  , ( IsInst "Eq" TInt
    , InstRep ([] :=> ())
    $ [ ( "==", "undefined" )
      ]
    )
  , ( IsInst "Eq" TString
    , InstRep ([] :=> ())
    $ [ ( "==", "undefined" )
      ]
    )
  , ( IsInst "Eq" (TProd "a" "b")
    , InstRep ([IsInst "Eq" "a", IsInst "Eq" "b"] :=> ())
    $ [ ( "==", "undefined" )
      ]
    )
  , ( IsInst "Eq" (TSum "a" "b")
    , InstRep ([IsInst "Eq" "a", IsInst "Eq" "b"] :=> ())
    $ [ ( "=="
        , lam "x" $ lam "y" $
            case_ "x"
              [ ( PCon "inl" ["x1"]
                , case_ "y"
                  [ ( PCon "inl" ["y1"]
                    , "==" :@ "x1" :@ "y2"
                    )
                  , ( PWildcard
                    , "False"
                    )
                  ]
                )
              , ( PCon "inr" ["x1"]
                , case_ "y"
                  [ ( PCon "inr" ["y1"]
                    , "==" :@ "x1" :@ "y2"
                    )
                  , ( PWildcard
                    , "False"
                    )
                  ]
                )
              ]
        ) ]
    )

  , ( IsInst "Category" TArrCon
    , InstRep ([] :=> ())
    $ []
    )
  ]


stdLib :: Map VName Scheme
stdLib = fmap (generalize $ SymTable @VName mempty) $ fmap fst stdLib'

evalLib :: Map VName (Exp VName)
evalLib = fmap snd stdLib'


toStdLib :: GenDataCon -> (VName, (Qual Type, Exp VName))
toStdLib g = (gdcName g, (gdcConType g, gdcCon g))


stdLib' :: Map VName (Qual Type, Exp VName)
stdLib' =
  [ ("swap",
      ( [] :=> TProd "a" "b" :-> TProd "b" "a"
      , lam "z" $ LProd ("snd" :@ "z") ("fst" :@ "z")
      ))
  , ("shouldInline",
      ( [IsInst "ToInline" "a"] :=> "a" :-> "a"
      , "id"
      ))
  , ( toStdLib $ buildDataCon "Inl" ["a"] $ Just $ TSum "a" "b" )
  , ( toStdLib $ buildDataCon "Inr" ["b"] $ Just $ TSum "a" "b" )
  , ( toStdLib $ buildDataCon "False" [] $ Just $ TBool )
  , ( toStdLib $ buildDataCon "True" [] $ Just $ TBool )
  , ( toStdLib $ buildDataCon "Unit" [] $ Just TUnit )
  , ("proj",
      ( []
          :=> ("a" :-> "c")
          :-> ("b" :-> "c")
          :-> TSum "a" "b"
          :-> "c"
      , lam "f" $ lam "g" $ lam "e" $
          case_ "e"
            [ ( PCon "Inl" [PVar "x"], "f" :@ "x")
            , ( PCon "Inr" [PVar "y"], "g" :@ "y")
            ]
      ))
  , (".",
      ( [CCat "k"]
          :=> TCat "k" "b" "c"
          :-> TCat "k" "a" "b"
          :-> TCat "k" "a" "c"
      , lam "g" . lam "f" . lam "x" $ "g" :@ ("f" :@ "x")
      ))
  , ("apply",
      ( [CCat "k"]
          :=> (TCat "k" (TProd ("a" :-> "b") "a") "b")
      , "undefined"
      ))
  , ("curry",
      ( [CCat "k"]
          :=> TCat "k" (TProd "a" "b") "c"
          :-> TCat "k" "a" ("b" :-> "c")
      , "undefined"
      ))
  , ("fork",
      ( [CCat "k"]
          :=> TCat "k" "a" "c"
          :-> TCat "k" "a" "d"
          :-> TCat "k" "a" (TProd "c" "d")
      , "undefined"
      ))
  , ("==",
      ( [IsInst "Eq" "a"] :=> "a" :-> "a" :-> TBool
      , "undefined"
      ))
  , ("id",
      ( [CCat "k"] :=> TCat "k" "a" "a"
      , lam "x" "x"
      ))
  , ("const",
      ( [CCat "k"]
          :=> "b"
          :-> TCat "k" "a" "b"
      , lam "x" $ lam "y" $ "x"
      ))
  , ("ccc",
      ( [CCat "k"]
          :=> ("a" :-> "b") :-> TSum (TCat "k" "a" "b") TUnit
      , "undefined"
      ))
  , ("error",
      ( [] :=> TString :-> "a"
      , "undefined"
      ))
  , ("undefined",
      ( [] :=> "a"
      , "error" :@ LString "undefined"
      ))
  ] <>
  M.fromList ( join $ fmap (\(gdc, zs) -> toStdLib gdc : zs) $
    [ buildRecord "," [("fst", "a"), ("snd", "b")] Nothing
    ] <> fmap buildDictType classes
    )
  <> M.fromList
      (fmap (\c@(InstRep (_ :=> IsInst cname _) _) ->
            buildDict (fst $ classGDCs M.! cname) c)
        $ getInstReps classEnv)


test'' :: Exp VName -> Either String ((Qual Type, Type), Exp VName)
test'' = second (first (first normalizeType))
      . runTI
      . typeInference classEnv stdLib


test' :: Exp VName -> Either String (Qual Type)
test' = fmap (fst . fst) . test''


test :: Exp VName -> IO ()
test x =
  case test'' x of
    Left e  -> putStrLn e
    Right ((t, t'), e) -> do
      putStrLn $ show t
      putStrLn $ show t'
      putStrLn $ show e

