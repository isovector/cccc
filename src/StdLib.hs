{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wall          #-}

module StdLib where

import           Compiler
import           Data.Bifunctor (first, second)
import           Data.Map (Map)
import qualified Data.Map as M
import           Evaluation
import           TypeChecking
import           Types
import           Utils


prelude :: Map VName (Exp VName)
preludeEnv :: (ClassEnv, SymTable VName)
Right (prelude, preludeEnv) = runTI $ compile preludeSource


pattern CK3 :: String -> TName
pattern CK3 str = TName str ((KStar :>> KStar :>> KStar) :>> KStar)

pattern CK2 :: String -> TName
pattern CK2 str = TName str ((KStar :>> KStar) :>> KStar)

pattern CKArr :: String -> TName
pattern CKArr str = TName str (KStar :>> KStar :>> KStar)

pattern CK1 :: String -> TName
pattern CK1 str = TName str (KStar :>> KStar)


preludeSource :: CompUnit
preludeSource = CompUnit
  { cuClasses =
    [ Class "a" (CK1 "Eq")
      $ M.fromList [("==", [] :=> "a" :-> "a" :-> TBool)]

    , let func = CK1 "f"
       in Class func (CK2 "Functor")
        $ M.fromList

        [("fmap", []
            :=> ("a" :-> "b") :-> TVar func :@@ "a" :-> TVar func :@@ "b")]

    , Class (TName "k" K2) (CK3 "Category") $ M.fromList
        [ ( "."
          , [] :=> TCat "k" "b" "c"
               :-> TCat "k" "a" "b"
               :-> TCat "k" "a" "c"
          )
        , ( "id"
          , [] :=> TCat "k" "a" "a"
          )
        ]
    ]

  , cuInsts =
    [ InstRep ([] :=> IsInst (CK2 "Functor") (TCon $ CK1 "Maybe")) $ M.fromList
      [ ( "fmap"
        , lam "f" $ lam "ma" $
            case_ "ma"
              [ (PCon "Just" ["a"], "Just" :@ ("f" :@ "a"))
              , (PCon "Nothing" [], "Nothing")
              ]
        )
      ]

    , InstRep ([] :=> IsInst (CK2 "Functor") (TCon $ CK1 "List")) $ M.fromList
      [ ( "fmap"
        , lam "f" $ lam "la" $
            case_ "la"
              [ ( PCon "Cons" ["a", "as"]
                , "Cons" :@ ("f" :@ "a")
                         :@ ("fmap" :@ "f" :@ "as"))
              , (PCon "Nil" [], "Nil")
              ]
        )
      ]

    , InstRep ([] :=> IsInst (CK2 "Functor")
        ((TCon $ CK3 "Coyoneda") :@@ TVar (CK1 "f")) ) $ M.fromList
      [ ( "fmap"
        , lam "f" $ lam "c" $
            "Coyoneda"
              :@ ("." :@ "f" :@ ("coFn" :@ "c"))
              :@ ("coFm" :@ "c")
        )
      ]

    , InstRep ([] :=> IsInst (CK1 "Eq") TBool) $ M.fromList
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

    , InstRep ([IsInst (CK1 "Eq") "a", IsInst (CK1 "Eq") "b"]
        :=> IsInst (CK1 "Eq") (TProd "a" "b"))
      $ M.fromList
      [ ( "=="
        , lam "x" $ lam "y" $
            case_ (LProd "x" "y")
              [ ( PProd (PProd "l1" "r1") (PProd "l2" "r2")
                , "&&" :@ ("==" :@ "l1" :@ "l2")
                       :@ ("==" :@ "r1" :@ "r2")
                )
              ])
      ]

    , InstRep ([IsInst (CK1 "Eq") "a", IsInst (CK1 "Eq") "b"]
        :=> IsInst (CK1 "Eq") (TSum "a" "b"))
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

    , InstRep ([] :=> IsInst (CK1 "Eq") TUnit)
      $ M.fromList
      [ ( "=="
        , lam "x" $ lam "y" "True"
        )
      ]

    , InstRep ([] :=> IsInst (CK1 "Eq") TInt)
      $ M.fromList
      [ ( "=="
        , lam "x" $ lam "y" $
            Lit (LitNative "eqInt" $ TInt :-> TInt :-> TBool)
              :@ "x" :@ "y"
        )
      ]

    , InstRep ([] :=> IsInst (CK1 "Eq") TString)
      $ M.fromList
      [ ( "=="
        , lam "x" $ lam "y" $
            Lit (LitNative "eqString" $ TString :-> TString :-> TBool)
              :@ "x" :@ "y"
        )
      ]

    , InstRep ([] :=> IsInst (CK3 "Category") TArrCon) $ M.fromList
      [ ( "id"
        , lam "x" "x"
        )
      , ( "."
        , lam "f" $ lam "g" $ lam "x" $ "f" :@ ("g" :@ "x")
        )
      ]

    ]

  , cuGDCs =
    [ buildDataCon "Inl" ["a"] . Just $ TSum "a" "b"
    , buildDataCon "Inr" ["b"] . Just $ TSum "a" "b"
    , buildDataCon "False" []  . Just $ TBool
    , buildDataCon "True" []   . Just $ TBool
    , buildDataCon "Unit" []   . Just $ TUnit
    , buildDataCon "Nothing" []  . Just $
        TCon (TName "Maybe" $ KStar :>> KStar) :@@ "a"
    , buildDataCon "Just" ["a"]   . Just $
        TCon (TName "Maybe" $ KStar :>> KStar) :@@ "a"
    , buildDataCon "Nil" []  . Just $
        TCon (TName "List" $ KStar :>> KStar) :@@ "a"
    , buildDataCon "Cons" ["a", TCon (TName "List" $ KStar :>> KStar) :@@ "a"]   . Just $
        TCon (TName "List" $ KStar :>> KStar) :@@ "a"
    ]

  , cuRecords =
    [ buildRecord "," [("fst", "a"), ("snd", "b")] Nothing

    , let f = TVar (TName "f" $ KStar :>> KStar)
       in buildRecord
            "Coyoneda"
            [ ("coFn", "b" :-> "a")
            , ("coFm", f :@@ "b")
            ]
            $ Just
            $ TCon (TName "Coyoneda" $ (KStar :>> KStar) :>> KStar :>> KStar)
                :@@ f
                :@@ "a"
    ]

  , cuDecls = M.fromList
    [ ( "undefined"
      , ( [] :=> "a"
        , "error" :@ LString "undefined"
        )
      )

    , ( "&&"
      , ( [] :=> TBool :-> TBool :-> TBool
        , lam "x" $ lam "y" $ case_ "x"
            [ (PTrue,     "y")
            , (PWildcard, "False")
            ]
        )
      )

    , ( "swap"
      , ( [] :=> TProd "a" "b" :-> TProd "b" "a"
        , lam "z" $ LProd ("snd" :@ "z") ("fst" :@ "z")
        )
      )

    , ( "proj"
      , ( []
            :=> ("a" :-> "c")
            :-> ("b" :-> "c")
            :-> TSum "a" "b"
            :-> "c"
        , lam "f" $ lam "g" $ lam "e" $
            case_ "e"
              [ ( PCon "Inl" [PVar "x"], "f" :@ "x")
              , ( PCon "Inr" [PVar "y"], "g" :@ "y")
              ]
        )
      )

    , ( "const"
      , ( [CCat "k"]
            :=> "b"
            :-> TCat "k" "a" "b"
        , lam "x" $ lam "y" $ "x"
        )
      )

    , ("error"
      , ( [] :=> TString :-> "a"
        , lam "x" $
            Lit (LitNative "error" $ TString :-> "a")
              :@ "x"
        )
      )

    , ( "liftCoyoneda"
      , ( [] :=> TK1 "f" "a"
             :-> TCon (CK3 "Coyoneda")
                    :@@ TVar (TName "f" K1)
                    :@@ "a"
        , "Coyoneda" :@ "id"
        )
      )

    , ( "lowerCoyoneda"
      , ( [IsInst (CK2 "Functor") (TVar $ CK1 "f") ]
             :=> TCon (CK3 "Coyoneda") :@@ (TVar $ CK1 "f") :@@ "a"
             :-> (TVar $ CK1 "f") :@@ "a"
        , lam "c" $ "fmap" :@ ("coFn" :@ "c") :@ ("coFm" :@ "c")
        )
      )

    , ( "head"
      , ( [] :=> TCon (CK1 "List") :@@ "a"
             :-> "a"
        , lam "c" $ case_ "c" [(PCon "Cons" ["a", PWildcard], "a")]
        )
      )

    ]
  }



test'' :: Exp VName -> Either String ((Qual Type, Type), Exp VName)
test'' = second (first (first normalizeType))
      . runTI
      . uncurry typeInference preludeEnv


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

