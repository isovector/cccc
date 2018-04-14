{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module TypeCheckingSpec where

import Data.Monoid ((<>))
import StdLib
import Test.Hspec
import TypeChecking
import Types
import Utils

fromRight (Right a) = a


typeCheck :: Exp VName -> Qual Type -> SpecWith ()
typeCheck e t = it (show t) $ test' e `shouldBe` Right t


typeError :: Exp VName -> SpecWith ()
typeError e = it ("type error: " <> show e) $ do
  let Left z = test' e
  z `shouldContain` "types don't unify"


kindError :: Type -> SpecWith ()
kindError t = it ("kind error: " <> show t) $ do
  let Left z = runTI $ kind t
  z `shouldContain` "kind mismatch"


ambiguous :: Exp VName -> SpecWith ()
ambiguous e = it ("ambiguous: " <> show e) $ do
  let Left z = test' e
  z `shouldContain` "is ambiguous"


spec :: Spec
spec = do
  describe "type checking" $ do
    let idCT = [CCat "b"] :=> TCat "b" "a" "a"
        idT = [] :=> "a" :-> "a"
    typeCheck "id" idCT
    typeCheck ("id" :@ "id") idCT
    typeCheck (lam "x" "x") idT
    typeCheck (let_ "x" "id" "x") idCT
    typeCheck (Assert "id" $ unqualType idT) idT
    typeCheck (Assert "id" $ "b" :-> "b") idT

    typeCheck ("." :@ "Inl") $
      [] :=> ("a" :-> "b") :-> "a" :-> TSum "b" "c"

    typeCheck "==" $
      [IsInst "Eq" "a"] :=> "a" :-> "a" :-> TBool

    let eqIntT = TInt :-> TInt :-> TBool
    typeCheck (Assert "==" eqIntT) $ [] :=> eqIntT
    typeCheck (let_ "x" "==" $ Assert "x" eqIntT) $ [] :=> eqIntT
    typeCheck (let_ "x" (Assert "==" eqIntT) "x") $ [] :=> eqIntT

    typeCheck (lam "x" $ "==" :@ "x" :@ LInt 5) $
      [] :=> TInt :-> TBool

    let eqAxBT = TProd "a" "b" :-> TProd "a" "b" :-> TBool
    typeCheck (Assert "==" eqAxBT) $
      [IsInst "Eq" "a", IsInst "Eq" "b"] :=> eqAxBT

    typeCheck "Unit" $ [] :=> TUnit
    typeCheck ("Inl" :@ "Unit") $ [] :=> TSum TUnit "a"
    typeCheck (LInt 5) $ [] :=> TInt
    typeCheck (LProd "id" "id") $
      [CCat "b", CCat "d"] :=> TProd (TCat "b" "a" "a") (TCat "d" "c" "c")
    typeCheck (LProd "==" "==") $
      [IsInst "Eq" "a", IsInst "Eq" "b"]
        :=> TProd ("a" :-> "a" :-> TBool) ("b" :-> "b" :-> TBool)

    typeCheck (
      case_ "Unit"
        [ (PWildcard, "Unit")
        , (PWildcard, "Unit")
        ]
      ) $ [] :=> TUnit

    typeCheck (
      case_ "Unit"
        [ (PVar "x",  "x")
        , (PWildcard, "Unit")
        ]
      ) $ [] :=> TUnit

    typeCheck (
      lam "z" $
        case_ "z"
          [ (PCon "Inl" [PVar "x"],  "x")
          , (PCon "Inr" [PCon "Unit" []], "Unit")
          ]
      ) $ [] :=> TSum TUnit TUnit :-> TUnit

    let lamCase =
          lam "z" $ case_ "z" [ (PCon "Inl" [PVar "x"], "x") , (PCon "Inr" [PVar "z"], "z") ]

    typeCheck lamCase $
      [] :=> TSum "a" "a" :-> "a"

    -- TODO(sandy): THERE IS A BUG HERE MY DUDE -- this gets inferred as having type `a`
    -- typeCheck (lamCase :@ ("Inr" :@ "Unit")) $
    --   [] :=> TUnit

    typeCheck (LString "hello") $ [] :=> TString

    let getMethod m c t =
          (V $ VName $ "@" <> m) :@ V (VName $ getDict $ IsInst c t)

    typeCheck (getMethod "==" "Eq" TBool) $
      [] :=> TBool :-> TBool :-> TBool
    typeCheck (getMethod "==" "Eq" TInt) $
      [] :=> TInt :-> TInt :-> TBool

    typeError $ "fst" :@ "Inl"
    typeError $
      case_ "Unit"
        [ (PWildcard, "Unit")
        , (PWildcard, LInt 5)
        ]
    typeError $
      case_ "Unit"
        [ (PVar "x", "x")
        , (PWildcard, LInt 5)
        ]

    ambiguous $ "==" :@ "==" :@ "=="

  describe "kind checking" $ do
    kindError $ TInt :@@ TBool
    kindError $ TCon (TName "+" K2) :@@ TCon (TName "+" K2)
    kindError $ TCon (TName "+" K2) :@@ TInt :@@ TCon (TName "," K2)

