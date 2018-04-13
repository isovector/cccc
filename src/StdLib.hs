{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module StdLib where

import Data.Bifunctor (second)
import Data.Map (Map)
import Types
import TypeChecking


classEnv :: ClassEnv
classEnv = ClassEnv
  [ ( [] :=> IsInst "Eq" TInt
    , []
    )
  , ( [] :=> IsInst "Eq" TUnit
    , []
    )
  , ( [] :=> IsInst "Eq" TVoid
    , []
    )
  , ( [IsInst "Eq" "a", IsInst "Eq" "b"] :=> IsInst "Eq" (TProd "a" "b")
    , []
    )
  , ( [IsInst "Eq" "a", IsInst "Eq" "b"] :=> IsInst "Eq" (TSum "a" "b")
    , []
    )

  , ( [] :=> IsInst "Category"  TArrCon
    , []
    )
  , ( [] :=> IsInst "Cartesian" TArrCon
    , []
    )
  , ( [] :=> IsInst "Terminal"  TArrCon  -- const
    , []
    )
  , ( [] :=> IsInst "Closed"    TArrCon
    , []
    )
  ]


stdLib :: Map VName Scheme
stdLib = fmap (generalize $ SymTable @VName mempty) $ fmap fst stdLib'


stdLib' :: Map VName (Qual Type, Exp VName)
stdLib' =
  [ ("fst",
      ( [] :=> TProd "a" "b" :-> "a"
      , lam "z" $ case_ "z" [(PCon "*" [PVar "x", PWildcard], "x")]
      ))
  , ("snd",
      ( [] :=> TProd "a" "b" :-> "b"
      , lam "z" $ case_ "z" [(PCon "*" [PWildcard, PVar "x"], "x")]
      ))
  , ("swap",
      ( [] :=> TProd "a" "b" :-> TProd "b" "a"
      , lam "z" $ LProd ("snd" :@ "z") ("fst" :@ "z")
      ))
  , ("shouldInline",
      ( [IsInst "ToInline" "a"] :=> "a" :-> "a"
      , "id"
      ))
  , ("inl",
      ( [] :=> "a" :-> TSum "a" "b"
      , lam "x" $ LInj False "x"
      ))
  , ("inr",
      ( [] :=> "b" :-> TSum "a" "b"
      , lam "x" $ LInj True "x"
      ))
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
  , (",",
      ( [] :=> "a" :-> "b" :-> TProd "a" "b"
      , lam "a" $ lam "b" $ LProd "a" "b"
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
  , ("undefined",
      ( [] :=> "a"
      , case_ "unit" []
      ))
  ]


test' :: Exp VName -> Either String (Qual Type)
test' = second normalizeType
      . runTI
      . typeInference classEnv stdLib


test :: Exp VName -> IO ()
test x =
  case test' x of
    Left e  -> putStrLn e
    Right t -> putStrLn $ show t
