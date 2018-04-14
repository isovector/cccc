{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EvalSpec where

import           Data.Foldable (for_)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import           Evaluation
import           StdLib
import           Test.Hspec
import           TypeChecking
import           Types
import           Utils


eval :: Exp VName -> Exp VName -> SpecWith ()
eval v e = it (show e <> " |=> " <> show v) $
  whnf (fmap snd stdLib') e `shouldBe` v


getDef :: VName -> Exp VName
getDef n = fmap snd stdLib' M.! n


spec :: Spec
spec = do
  describe "evaluation" $ do
    eval (LInt 5) $ LInt 5
    eval (LString "hello") $ LString "hello"

    eval (LBool False) $ LBool False
    eval (LProd "fst" "snd") $ LProd "fst" "snd"
    eval (getDef "fst") $ "fst" :@ LProd "fst" "snd"

    let myPats =
          [ ( PCon "inl" [PLit (LitInt 5)]
            , LInt 1
            )
          , ( PCon "inl" [PVar "z"]
            , "z"
            )
          , ( PCon "inr" [PWildcard]
            , LInt $ -15
            )
          ]

    eval (LInt 1) $ case_ ("inl" :@ LInt 5) myPats
    eval (LInt 2) $ case_ ("inl" :@ LInt 2) myPats
    eval (LInt 3) $ case_ ("inl" :@ LInt 3) myPats
    eval (LInt $ -15) $ case_ ("inr" :@ LInt 3) myPats

    eval (LString "yo") $ case_ (LString "hello")
      [ ( PLit (LitString "hello"), LString "yo" )
      , ( PWildcard, LString "bad" )
      ]

    let prod = LProd (LInt 1) (LInt 2)
    eval prod $ case_ prod
      [( PAs "i" $ PCon "," [PVar "x", PVar "y"], "i")]
    eval (LInt 2) $ case_ prod
      [( PAs "i" $ PCon "," [PVar "x", PVar "y"], "y")]

    let idF = lam "x" "x"
    eval idF idF

    eval (LBool True) $ let_ "x" (LBool True) "x"
    eval (LInt 7) $ let_ "x" (LBool True) $
      "fst" :@ LProd (LInt 7) "x"
    eval (LBool True) $ let_ "x" (LBool True) $
      "snd" :@ ("," :@ LInt 7 :@ "x")

    eval idF $ Assert idF $ TInt :-> TInt


    let getMethod m c t =
          (V $ VName $ "@" <> m) :@ V (VName $ getDict $ IsInst c t)
    let apps :: [(Bool, Bool)] = do
          a <- [False, True]
          b <- [False, True]
          pure (a, b)
    for_ apps $ \(a, b) ->
      eval (LBool $ a == b) $ getMethod "==" "Eq" TBool :@ LBool a :@ LBool b

