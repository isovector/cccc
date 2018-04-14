{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module CCCSpec where

import CCC
import Data.List (partition)
import Data.Monoid ((<>))
import StdLib
import Test.Hspec
import TypeChecking
import Types

fromRight (Right a) = a


cccType :: Exp VName -> Qual Type -> SpecWith ()
cccType e (q :=> t) = it (show e) $
  test' (toCCC e) `shouldBe` Right (q :=> t)

cccDidntInline :: Exp VName -> Qual Type -> SpecWith ()
cccDidntInline e (q :=> t) = it ("to inline: " <> show e) $ do
  let Right (q' :=> t') = test' $ toCCC e
      (i, q'')          = partition ((== "ToInline") . predCName) q'
  (q'' :=> t') `shouldBe` (q :=> t)
  i `shouldNotBe` []


spec :: Spec
spec = do
  pure ()
  -- describe "type checking" $ do
  --   cccType (lam "x" "x") $
  --     [CCat "b"] :=> TCat "b" "a" "a"

  --   cccType (lam "x" $ lam "y" $ "," :@ "x" :@ "y") $
  --     [CCat "c"]
  --       :=> TCat "c" (TProd "a" "b") (TProd "a" "b")

  --   cccType (lam "x" $ lam "y" $ LProd "x" "y") $
  --     [CCat "c"]
  --       :=> TCat "c" (TProd "a" "b") (TProd "a" "b")

  --   cccType (lam "x" $ lam "y" $ LProd "y" "x") $
  --     [CCat "c"]
  --       :=> TCat "c" (TProd "a" "b") (TProd "b" "a")
  --   cccType (lam "z" $ LProd ("snd" :@ "z") ("fst" :@ "z")) $
  --     [CCat "c"]
  --       :=> TCat "c" (TProd "a" "b") (TProd "b" "a")
  --   cccDidntInline "swap" $
  --     [CCat "c"]
  --       :=> TCat "c" (TProd "a" "b") (TProd "b" "a")


  --   cccType (lam "x" $ lam "y" $ LProd (LInt 5) LTrue) $
  --     [CCat "b"]
  --       :=> TCat "b" "a" (TProd TInt TBool)

  --   cccType (lam "x" $ "fst") $
  --     [CCat "b"]
  --       :=> TCat "b" "a" (TProd "c" "d" :-> "c")

  --   cccType "fst" $
  --     [CCat "c"]
  --       :=> TCat "c" (TProd "a" "b") "a"

