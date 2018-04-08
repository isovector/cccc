{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module TypeCheckingSpec where

import Test.Hspec
import TypeChecking
import Types
import Data.Monoid ((<>))

fromRight (Right a) = a


typeCheck :: Exp VName -> Qual Type -> SpecWith ()
typeCheck e t = it (show t) $ test' e `shouldBe` Right t


typeError :: Exp VName -> SpecWith ()
typeError e = it ("type error: " <> show e) $ do
  let Left z = test' e
  z `shouldContain` "types don't unify"


ambiguous :: Exp VName -> SpecWith ()
ambiguous e = it ("ambiguous: " <> show e) $ do
  let Left z = test' e
  z `shouldContain` "is ambiguous"


spec :: Spec
spec = describe "type checking" $ do
  let idT = [] :=> "a" :-> "a"
  typeCheck "id" idT
  typeCheck ("id" :@ "id") idT
  typeCheck (lam "x" "x") idT
  typeCheck (let_ "x" "id" "x") idT
  typeCheck (Assert "id" $ unqualType idT) idT
  typeCheck (Assert "id" $ "b" :-> "b") idT

  typeCheck ("." :@ "inl") $
    [] :=> ("a" :-> "b") :-> "a" :-> TSum "b" "c"

  typeCheck "==" $
    [IsInst "Eq" "a"] :=> "a" :-> "a" :-> TBool

  let eqIntT = TInt :-> TInt :-> TBool
  typeCheck (Assert "==" eqIntT) $ [] :=> eqIntT
  typeCheck (let_ "x" "==" $ Assert "x" eqIntT) $ [] :=> eqIntT
  typeCheck (let_ "x" (Assert "==" eqIntT) "x") $ [] :=> eqIntT


  -- should not occurs check
  -- expectationFailure $ do
  --   let eqAxBT = TProd "a" "b" :-> TProd "a" "b" :-> TBool
  --   typeCheck (Assert "==" eqAxBT) $
  --     [IsInst "Eq" "x", IsInst "Eq" "y"] :=> eqAxBT

  typeCheck "unit" $ [] :=> TUnit
  typeCheck ("inl" :@ "unit") $ [] :=> TSum TUnit "a"
  typeCheck (Assert ("inl" :@ "unit") TBool) $ [] :=> TBool
  typeCheck (LInt 5) $ [] :=> TInt
  typeCheck (LProd "id" "id") $
    [] :=> TProd ("a" :-> "a") ("b" :-> "b")
  typeCheck (LProd "==" "==") $
    [IsInst "Eq" "a", IsInst "Eq" "b"]
      :=> TProd ("a" :-> "a" :-> TBool) ("b" :-> "b" :-> TBool)

  typeError $ "fst" :@ "inl"

  ambiguous $ "==" :@ "==" :@ "=="

