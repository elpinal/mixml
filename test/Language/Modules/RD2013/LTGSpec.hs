module Language.Modules.RD2013.LTGSpec where

import Test.Hspec

import Data.Text.Prettyprint.Doc

import Language.Modules.RD2013.LTG

infixr 7 ^>
(^>) :: Kind -> Kind -> Kind
(^>) = KFun

infixr 7 +>
(+>) :: MType -> MType -> Type
(+>) = TFun

spec :: Spec
spec = do
  describe "pretty" $ do
    it "pretty-prints kinds" $ do
      show (pretty $ Prec Type)                     `shouldBe` "*"
      show (pretty $ Prec $ Type ^> Type)           `shouldBe` "* -> *"
      show (pretty $ Prec $ Type ^> Type ^> Type)   `shouldBe` "* -> * -> *"
      show (pretty $ Prec $ (Type ^> Type) ^> Type) `shouldBe` "(* -> *) -> *"

    it "pretty-prints types" $ do
      show (pretty $ Named $ TVar $ variable 80) `shouldBe` "v[80]"
      show (pretty $ Named $ TVar $ global 79)   `shouldBe` "g79"

      let v1 = TVar $ global 3
      let v2 = TVar $ global 47

      show (pretty $ Named $ un v1 +> un v2)               `shouldBe` "g3 -> g47"
      show (pretty $ Named $ un v2 +> un (un v1 +> un v2)) `shouldBe` "g47 -> g3 -> g47"
      show (pretty $ Named $ un (un v1 +> un v2) +> un v1) `shouldBe` "(g3 -> g47) -> g3"

      show (pretty $ Named $ lin v1 +> lin v2)                 `shouldBe` "g3@L -> g47@L"
      show (pretty $ Named $ lin v2 +> lin (lin v1 +> lin v2)) `shouldBe` "g47@L -> (g3@L -> g47@L)@L"
      show (pretty $ Named $ lin (lin v1 +> lin v2) +> lin v1) `shouldBe` "(g3@L -> g47@L)@L -> g3@L"

      show (pretty $ Named $ un v1 +> lin v2) `shouldBe` "g3 -> g47@L"

      show (pretty $ Named $ TRecord [])                                `shouldBe` "{}"
      show (pretty $ Named $ TRecord [("a", un $ v1)])                  `shouldBe` "{a = g3}"
      show (pretty $ Named $ TRecord [("a", un $ v1), ("b", lin $ v2)]) `shouldBe` "{a = g3; b = g47@L}"

      show (pretty $ Named $ Forall Index (un Type) $ un v1) `shouldBe` "∀t0 : *. g3"

      let v3 = TVar $ variable 0
      let v4 = TVar $ variable 1

      show (pretty $ Named $ Forall Index (un Type) $ un v3)                                         `shouldBe` "∀t0 : *. t0"
      show (pretty $ Named $ Forall Index (un Type) $ un v4)                                         `shouldBe` "∀t0 : *. v[1]"
      show (pretty $ Named $ Forall Index (un Type) $ un $ Forall Index (un $ Type ^> Type) $ un v3) `shouldBe` "∀t0 : *. ∀t1 : * -> *. t1"
      show (pretty $ Named $ Forall Index (un Type) $ un $ Forall Index (un $ Type ^> Type) $ un v4) `shouldBe` "∀t0 : *. ∀t1 : * -> *. t0"

      let ty1 = Forall Index (un Type) $ un v3

      show (pretty $ Named $ un ty1 +> un ty1)  `shouldBe` "(∀t0 : *. t0) -> ∀t0 : *. t0"
      show (pretty $ Named $ lin ty1 +> un ty1) `shouldBe` "(∀t0 : *. t0)@L -> ∀t0 : *. t0"
      show (pretty $ Named $ un ty1 +> lin ty1) `shouldBe` "(∀t0 : *. t0) -> (∀t0 : *. t0)@L"

      show (pretty $ Named $ Some Index (un Type) $ un v3) `shouldBe` "∃t0 : *. t0"
      show (pretty $ Named $ TAbs Index Type $ v3)         `shouldBe` "λt0 : *. t0"

      show (pretty $ Named $ Ref v1)                      `shouldBe` "?g3"
      show (pretty $ Named $ Ref $ Ref v1)                `shouldBe` "?(?g3)"
      show (pretty $ Named $ Ref ty1)                     `shouldBe` "?(∀t0 : *. t0)"
      show (pretty $ Named $ Ref $ TApp v1 v2)            `shouldBe` "?(g3 g47)"
      show (pretty $ Named $ un (Ref v1) +> un (Ref v1))  `shouldBe` "?g3 -> ?g3"
      show (pretty $ Named $ un (Ref v1) +> lin (Ref v1)) `shouldBe` "?g3 -> (?g3)@L"

      show (pretty $ Named $ TApp v1 v2)                           `shouldBe` "g3 g47"
      show (pretty $ Named $ v1 `TApp` v2 `TApp` v1)               `shouldBe` "g3 g47 g3"
      show (pretty $ Named $ TApp v1 $ v2 `TApp` v1)               `shouldBe` "g3 (g47 g3)"
      show (pretty $ Named $ un (TApp v1 v2) +> un (TApp v2 v1))   `shouldBe` "g3 g47 -> g47 g3"
      show (pretty $ Named $ lin (TApp v1 v2) +> lin (TApp v2 v1)) `shouldBe` "(g3 g47)@L -> (g47 g3)@L"
