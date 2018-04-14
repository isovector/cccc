{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module StdLib where

import           Control.Monad (join)
import           Data.Bifunctor (first, second)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           TypeChecking
import           Types
import           Utils


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
                    , LBool True
                    )
                  , ( PWildcard
                    , LBool False
                    )
                  ]
                )
              , ( PTrue
                , case_ "y"
                  [ ( PTrue
                    , LBool True
                    )
                  , ( PWildcard
                    , LBool False
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
        , lam "x" $ lam "y" $ LBool True
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
  , ( IsInst "Eq" TVoid
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
    $ [ ( "==", "undefined" )
      ]
    )

  , ( IsInst "Category" TArrCon
    , InstRep ([] :=> ())
    $ []
    )
  , ( IsInst "Cartesian" TArrCon
    , InstRep ([] :=> ())
    $ []
    )
  , ( IsInst "Terminal" TArrCon  -- const
    , InstRep ([] :=> ())
    $ []
    )
  , ( IsInst "Closed" TArrCon
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
  , ( toStdLib $ buildDataCon "inl" ["a"] $ Just $ TSum "a" "b"
    )
  , ( toStdLib $ buildDataCon "inr" ["b"] $ Just $ TSum "a" "b"
    )
  , ("proj",
      ( []
          :=> ("a" :-> "c")
          :-> ("b" :-> "c")
          :-> TSum "a" "b"
          :-> "c"
      , lam "f" $ lam "g" $ lam "e" $
          case_ "e"
            [ ( PCon "inl" [PVar "x"], "f" :@ "x")
            , ( PCon "inr" [PVar "y"], "g" :@ "y")
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
      , undefined
      ))
  , ("curry",
      ( [CCat "k"]
          :=> TCat "k" (TProd "a" "b") "c"
          :-> TCat "k" "a" ("b" :-> "c")
      , undefined
      ))
  , ("fork",
      ( [CCat "k"]
          :=> TCat "k" "a" "c"
          :-> TCat "k" "a" "d"
          :-> TCat "k" "a" (TProd "c" "d")
      , undefined
      ))
  , ("unit",
      ( [] :=> TUnit
      , LUnit
      ))
  , ("==",
      ( [IsInst "Eq" "a"] :=> "a" :-> "a" :-> TBool
      , undefined
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
      , undefined
      ))
  , ("error",
      ( [] :=> TString :-> "a"
      , undefined
      ))
  , ("undefined",
      ( [] :=> "a"
      , "error" :@ LString "undefined"
      ))
  ] <>
  M.fromList ( join $ fmap (\(gdc, zs) -> toStdLib gdc : zs) $
    [ buildRecord "," [("fst", "a"), ("snd", "b")] Nothing
    ])

test' :: Exp VName -> Either String (Qual Type)
test' = second normalizeType
      . runTI
      . typeInference classEnv stdLib


test :: Exp VName -> IO ()
test x =
  case test' x of
    Left e  -> putStrLn e
    Right t -> putStrLn $ show t

