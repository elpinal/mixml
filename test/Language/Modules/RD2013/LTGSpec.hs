module Language.Modules.RD2013.LTGSpec where

import Test.Hspec

import Data.Text.Prettyprint.Doc

import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State

import Language.Modules.RD2013.LTG
import Shift

infixr 7 ^>
(^>) :: Kind -> Kind -> Kind
(^>) = KFun

infixr 7 +>
(+>) :: MType -> MType -> Type
(+>) = TFun

computeKind :: TEnv -> Type -> Either KindError MKind
computeKind e = run . runError . evalState e . kindOf

runEqEnv :: EqEnv -> Eff '[Reader EqEnv] a -> a
runEqEnv e = run . runReader e

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
      show (pretty $ Named $ TAbs Index Type v3)           `shouldBe` "λt0 : *. t0"
      show (pretty $ Named $ TAbs (Bind 8) Type v3)        `shouldBe` "λg8 : *. v[0]"

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

    it "pretty-prints terms" $ do
      show (pretty $ Named $ Var $ variable 80) `shouldBe` "v[80]"
      show (pretty $ Named $ Var $ global 79)   `shouldBe` "g79"

      let v = un $ TVar $ global 41

      show (pretty $ Named $ Abs Index v $ Var $ global 79)                 `shouldBe` "λv0 : g41. g79"
      show (pretty $ Named $ Abs Index (un $ v +> v) $ Var $ global 79)     `shouldBe` "λv0 : g41 -> g41. g79"
      show (pretty $ Named $ Abs Index (lin $ v +> v) $ Var $ global 79)    `shouldBe` "λv0 : (g41 -> g41)@L. g79"
      show (pretty $ Named $ Abs Index (un $ v +> v) $ Var $ variable 0)    `shouldBe` "λv0 : g41 -> g41. v0"
      show (pretty $ Named $ Abs Index (un $ v +> v) $ Var $ variable 1)    `shouldBe` "λv0 : g41 -> g41. v[1]"
      show (pretty $ Named $ Abs (Bind 8) (un $ v +> v) $ Var $ variable 0) `shouldBe` "λg8 : g41 -> g41. v[0]"

      let t = Var $ global 3

      show (pretty $ Named $ App t t)               `shouldBe` "g3 g3"
      show (pretty $ Named $ App t $ App t t)       `shouldBe` "g3 (g3 g3)"
      show (pretty $ Named $ App (App t t) t)       `shouldBe` "g3 g3 g3"
      show (pretty $ Named $ App (Abs Index v t) t) `shouldBe` "(λv0 : g41. g3) g3"
      show (pretty $ Named $ App t (Abs Index v t)) `shouldBe` "g3 (λv0 : g41. g3)"

      show (pretty $ Named $ Let [] (Var $ global 1) (Var $ global 33))                              `shouldBe` "let {} = g1 in g33"
      show (pretty $ Named $ Let [("xy", Bind 20)] (Var $ global 1) (Var $ global 33))               `shouldBe` "let {xy = g20} = g1 in g33"
      show (pretty $ Named $ Let [("xy", Bind 20), ("z", Index)] (Var $ global 5) (Var $ global 39)) `shouldBe` "let {xy = g20; z = v0} = g5 in g39"

      show (pretty $ Named $ App t $ Let [] (Var $ global 1) (Var $ global 33))      `shouldBe` "g3 (let {} = g1 in g33)"
      show (pretty $ Named $ flip App t $ Let [] (Var $ global 1) (Var $ global 33)) `shouldBe` "(let {} = g1 in g33) g3"

      show (pretty $ Named $ Let [] (Var $ global 1) $ Let [] (Var $ global 5) $ Var $ global 33)  `shouldBe` "let {} = g1 in let {} = g5 in g33"
      show (pretty $ Named $ Let [] (Let [] (Var $ global 5) $ Var $ global 33) $ Var $ global 40) `shouldBe` "let {} = let {} = g5 in g33 in g40"

      show (pretty $ Named $ Let [("xy", Bind 20)] (Var $ global 1) $ Var $ variable 0)                              `shouldBe` "let {xy = g20} = g1 in v[0]"
      show (pretty $ Named $ Let [("xy", Index)] (Var $ global 1) $ Var $ variable 0)                                `shouldBe` "let {xy = v0} = g1 in v0"
      show (pretty $ Named $ Let [("xy", Index), ("xyz", Index)] (Var $ global 1) $ Var $ variable 0)                `shouldBe` "let {xy = v0; xyz = v1} = g1 in v1"
      show (pretty $ Named $ Let [("xy", Index), ("xyz", Bind 5), ("B", Index)] (Var $ global 1) $ Var $ variable 1) `shouldBe` "let {B = v0; xy = v1; xyz = g5} = g1 in v0"
      show (pretty $ Named $ Let [("xy", Index), ("xyz", Bind 5), ("z", Index)] (Var $ global 1) $ Var $ variable 1) `shouldBe` "let {xy = v0; xyz = g5; z = v1} = g1 in v0"

      show (pretty $ Named $ LetN [] $ Var $ global 33)                                                    `shouldBe` "let in g33"
      show (pretty $ Named $ LetN [(Index, Var $ global 7)] $ Var $ global 33)                             `shouldBe` "let v0 = g7 in g33"
      show (pretty $ Named $ LetN [(Index, Var $ global 7), (Index, Var $ global 8)] $ Var $ global 33)    `shouldBe` "let v0 = g7; v1 = g8 in g33"
      show (pretty $ Named $ LetN [(Bind 9, Var $ global 7), (Index, Var $ global 8)] $ Var $ variable 0)  `shouldBe` "let g9 = g7; v0 = g8 in v0"
      show (pretty $ Named $ LetN [(Bind 9, Var $ global 7), (Index, Var $ global 8)] $ Var $ variable 1)  `shouldBe` "let g9 = g7; v0 = g8 in v[1]"
      show (pretty $ Named $ LetN [(Bind 9, Var $ global 7), (Bind 1, Var $ global 8)] $ Var $ variable 0) `shouldBe` "let g9 = g7; g1 = g8 in v[0]"

      show (pretty $ Named $ LetN [(Bind 9, Var $ global 7), (Index, Var $ variable 0), (Bind 1, Var $ global 8)] $ Var $ variable 0)  `shouldBe` "let g9 = g7; v0 = v[0]; g1 = g8 in v0"
      show (pretty $ Named $ LetN [(Bind 9, Var $ global 7), (Index, Var $ variable 0), (Index, Var $ variable 0)] $ Var $ variable 0) `shouldBe` "let g9 = g7; v0 = v[0]; v1 = v[0] in v1"

      show (pretty $ Named $ New $ TVar $ global 6)               `shouldBe` "new g6"
      show (pretty $ Named $ App t $ New $ TVar $ global 6)       `shouldBe` "g3 (new g6)"
      show (pretty $ Named $ App (New $ TVar $ global 6) t)       `shouldBe` "(new g6) g3"
      show (pretty $ Named $ Abs Index v $ New $ TVar $ global 6) `shouldBe` "λv0 : g41. new g6"

      show (pretty $ Named $ Def t t)               `shouldBe` "def g3 := g3"
      show (pretty $ Named $ Def t $ Abs Index v t) `shouldBe` "def g3 := λv0 : g41. g3"

      let t1 = Var $ global 20

      show (pretty $ Named $ Read t)                 `shouldBe` "!g3"
      show (pretty $ Named $ Read $ Read t)          `shouldBe` "!(!g3)"
      show (pretty $ Named $ App (Read t1) (Read t)) `shouldBe` "!g20 !g3"
      show (pretty $ Named $ Read $ App t t1)        `shouldBe` "!(g3 g20)"

      let k = un Type

      show (pretty $ Named $ Poly Index k t)                                      `shouldBe` "Λt0 : *. g3"
      show (pretty $ Named $ Abs Index (un $ TVar $ variable 0) t)                `shouldBe` "λv0 : v[0]. g3"
      show (pretty $ Named $ Poly Index k $ Abs Index (un $ TVar $ variable 0) t) `shouldBe` "Λt0 : *. λv0 : t0. g3"
      show (pretty $ Named $ Read $ Poly Index k t)                               `shouldBe` "!(Λt0 : *. g3)"

      show (pretty $ Named $ Inst t $ TVar $ global 9)                           `shouldBe` "g3 [g9]"
      show (pretty $ Named $ App t $ Inst t $ TVar $ global 9)                   `shouldBe` "g3 (g3 [g9])"
      show (pretty $ Named $ flip App t $ Inst t $ TVar $ global 9)              `shouldBe` "g3 [g9] g3"
      show (pretty $ Named $ Inst (Inst t $ TVar $ global 9) $ TVar $ global 10) `shouldBe` "g3 [g9] [g10]"
      show (pretty $ Named $ Inst (Inst t $ TVar $ global 9) $ v +> v)           `shouldBe` "g3 [g9] [g41 -> g41]"

      show (pretty $ Named $ Pack (TVar $ global 15) t $ TVar $ global 7)              `shouldBe` "pack <g15, g3> as g7"
      show (pretty $ Named $ App t $ Pack (TVar $ global 15) t $ TVar $ global 7)      `shouldBe` "g3 (pack <g15, g3> as g7)"
      show (pretty $ Named $ flip App t $ Pack (TVar $ global 15) t $ TVar $ global 7) `shouldBe` "(pack <g15, g3> as g7) g3"
      show (pretty $ Named $ Def t $ Pack (TVar $ global 15) t $ TVar $ global 7)      `shouldBe` "def g3 := pack <g15, g3> as g7"

      let v = Var $ variable 0
      let t2 = Abs Index (un $ TVar $ variable 0) v

      show (pretty $ Named $ Unpack Index Index t t1)  `shouldBe` "unpack <t0, v0> = g3 in g20"
      show (pretty $ Named $ Unpack Index Index v v)   `shouldBe` "unpack <t0, v0> = v[0] in v0"
      show (pretty $ Named $ Unpack Index Index t2 t2) `shouldBe` "unpack <t0, v0> = λv0 : v[0]. v0 in λv1 : t0. v1"

      show (pretty $ Named $ Unpack Index (Bind 7) t2 t2)    `shouldBe` "unpack <t0, g7> = λv0 : v[0]. v0 in λv0 : t0. v0"
      show (pretty $ Named $ Unpack (Bind 4) (Bind 7) t2 t2) `shouldBe` "unpack <g4, g7> = λv0 : v[0]. v0 in λv0 : v[0]. v0"

      show (pretty $ Named $ NewIn Index Type v)  `shouldBe` "new t0 : * in v[0]"
      show (pretty $ Named $ NewIn Index Type t2) `shouldBe` "new t0 : * in λv0 : t0. v0"
      show (pretty $ Named $ App t $ NewIn Index Type t2) `shouldBe` "g3 (new t0 : * in λv0 : t0. v0)"
      show (pretty $ Named $ flip App t $ NewIn Index Type t2) `shouldBe` "(new t0 : * in λv0 : t0. v0) g3"

      show (pretty $ Named $ NewInN [] v)                                     `shouldBe` "new in v[0]"
      show (pretty $ Named $ NewInN [(Index, Type)] v)                        `shouldBe` "new t0 : * in v[0]"
      show (pretty $ Named $ NewInN [(Index, Type), (Index, Type ^> Type)] v) `shouldBe` "new t0 : *; t1 : * -> * in v[0]"

      show (pretty $ Named $ NewInN [] $ Abs Index (un $ TVar $ variable 0) v)               `shouldBe` "new in λv0 : v[0]. v0"
      show (pretty $ Named $ NewInN [(Index, Type)] $ Abs Index (lin $ TVar $ variable 0) v) `shouldBe` "new t0 : * in λv0 : t0@L. v0"

      let ty1 = TVar $ global 27
      let ty2 = TVar $ global 40

      show (pretty $ Named $ DefIn ty1 ty2 t2 $ un ty1) `shouldBe` "def g27 := g40 in (λv0 : v[0]. v0) : g27"

      show (pretty $ Named $ DefInN [] t2 $ un ty1)                       `shouldBe` "def in (λv0 : v[0]. v0) : g27"
      show (pretty $ Named $ DefInN [(ty1, ty2)] t2 $ un ty1)             `shouldBe` "def g27 := g40 in (λv0 : v[0]. v0) : g27"
      show (pretty $ Named $ DefInN [(ty1, ty2), (ty2, ty1)] t2 $ un ty1) `shouldBe` "def g27 := g40; g40 := g27 in (λv0 : v[0]. v0) : g27"

      show (pretty $ Named $ Proj t "a")               `shouldBe` "g3.a"
      show (pretty $ Named $ Proj (App t t1) "a")      `shouldBe` "(g3 g20).a"
      show (pretty $ Named $ Proj (Proj t "w") "a")    `shouldBe` "g3.w.a"
      show (pretty $ Named $ App t1 $ Proj t "w")      `shouldBe` "g20 g3.w"
      show (pretty $ Named $ flip App t1 $ Proj t "w") `shouldBe` "g3.w g20"

      show (pretty $ Named $ Restrict t [])                      `shouldBe` "restrict g3 to []"
      show (pretty $ Named $ Restrict t ["a"])                   `shouldBe` "restrict g3 to [a]"
      show (pretty $ Named $ Restrict t ["a", "z", "k"])         `shouldBe` "restrict g3 to [a, k, z]"
      show (pretty $ Named $ Restrict (App t t) ["a", "z", "k"]) `shouldBe` "restrict g3 g3 to [a, k, z]"

  describe "kindOf" $ do
    it "computes a kind for a type" $ do
      computeKind emptyTEnv (tvar 0)                                  `shouldBe` Left (UnboundTypeVariable $ variable 0)
      computeKind emptyTEnv (Forall Index (un Type) $ un $ tvar 0)    `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (lin Type) $ un $ tvar 0)   `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (un Type) $ un $ tvar 1)    `shouldBe` Left (UnboundTypeVariable $ variable 1)
      computeKind emptyTEnv (Forall (Bind 0) (un Type) $ un $ tvar 0) `shouldBe` Left (UnboundTypeVariable $ variable 0)

      computeKind emptyTEnv (Forall Index (lin Type) $ un $ Forall Index (lin $ Type ^> Type) $ un $ tvar 1) `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (lin Type) $ un $ Forall Index (lin $ Type ^> Type) $ un $ tvar 0) `shouldBe` Left (UnexpectedHigherKind (Type ^> Type) (tvar 0) Any)

      computeKind emptyTEnv (Forall Index (un Type) $ un $ un (tvar 0) +> un (tvar 0))  `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (lin Type) $ un $ un (tvar 0) +> un (tvar 0)) `shouldBe` return (un Type)

      computeKind (fromGTEnv [(0, lin Type)]) (TVar $ global 0)                                            `shouldBe` return (lin Type)
      computeKind (fromGTEnv [(0, lin Type)]) (un (TVar $ global 0) +> un (TVar $ global 0))               `shouldBe` Left (UnexpectedLinearKind (TVar $ global 0) Any)
      computeKind (fromGTEnv [(0, lin Type), (8, un Type)]) (un (TVar $ global 8) +> un (TVar $ global 0)) `shouldBe` Left (UnexpectedLinearKind (TVar $ global 0) Any)

      computeKind emptyTEnv (Some Index (un Type) $ un $ tvar 0) `shouldBe` return (un Type)

      computeKind emptyTEnv (TAbs Index Type $ tvar 0)                       `shouldBe` return (un $ Type ^> Type)
      computeKind emptyTEnv (TAbs Index Type $ un (tvar 0) +> un (tvar 0))   `shouldBe` return (un $ Type ^> Type)
      computeKind emptyTEnv (TAbs Index Type $ lin (tvar 0) +> lin (tvar 0)) `shouldBe` return (un $ Type ^> Type)

      computeKind emptyTEnv (TAbs Index (Type ^> Type) $ tvar 0) `shouldBe` return (un $ (Type ^> Type) ^> Type ^> Type)

      computeKind emptyTEnv (TAbs Index Type $ TAbs Index Type $ tvar 0)           `shouldBe` return (un $ Type ^> Type ^> Type)
      computeKind emptyTEnv (TAbs Index Type $ TAbs Index (Type ^> Type) $ tvar 0) `shouldBe` return (un $ Type ^> (Type ^> Type) ^> Type ^> Type)
      computeKind emptyTEnv (TAbs Index Type $ TAbs Index (Type ^> Type) $ tvar 1) `shouldBe` return (un $ Type ^> (Type ^> Type) ^> Type)

      computeKind emptyTEnv (Forall Index (un Type) $ un $ TRecord [])                             `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (un Type) $ un $ TRecord [("a", un $ tvar 0)])           `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (lin Type) $ lin $ TRecord [("a", lin $ tvar 0)])        `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (un $ Type ^> Type) $ un $ TRecord [("a", un $ tvar 0)]) `shouldBe` Left (UnexpectedHigherKind (Type ^> Type) (tvar 0) Any)

      computeKind emptyTEnv (Forall Index (un Type) $ un $ tvar 0 @@ tvar 0) `shouldBe` Left (NotHigherKind (tvar 0) (tvar 0) Any)

      computeKind emptyTEnv (Forall Index (un $ Type ^> Type) $ un $ Forall Index (un Type) $ un $ tvar 1 @@ tvar 0)         `shouldBe` return (un Type)
      computeKind emptyTEnv (Forall Index (un $ Type ^> Type ^> Type) $ un $ Forall Index (un Type) $ un $ tvar 1 @@ tvar 0) `shouldBe` Left (UnexpectedHigherKind (Type ^> Type) (tvar 1 @@ tvar 0) Any)

      computeKind emptyTEnv (Forall Index (un $ Type ^> Type ^> Type) $ un $ Forall Index (un Type) $ un $ tvar 1 @@ tvar 0 @@ tvar 0) `shouldBe` return (un Type)

  describe "shift" $ do
    it "shifts variables in a type" $ do
      shift 1 (variable 0)        `shouldBe` variable 1
      shift 1 (global 0)          `shouldBe` global 0
      shiftAbove 3 1 (variable 0) `shouldBe` variable 0
      shiftAbove 0 1 (variable 0) `shouldBe` variable 1

      shift 1 (tvar 0)                                  `shouldBe` tvar 1
      shift 1 (Forall Index (un Type) $ un $ tvar 0)    `shouldBe` Forall Index (un Type) (un $ tvar 0)
      shift 1 (Forall (Bind 1) (un Type) $ un $ tvar 0) `shouldBe` Forall (Bind 1) (un Type) (un $ tvar 1)

  describe "subst" $ do
    it "substitutes types" $ do
      subst (variable 0) (tvar 0) (tvar 0)                               `shouldBe` tvar 0
      subst (variable 0) (un (tvar 11) +> un (tvar 17)) (tvar 1)         `shouldBe` tvar 1
      subst (variable 1) (un (tvar 11) +> un (tvar 17)) (tvar 1)         `shouldBe` (un (tvar 11) +> un (tvar 17))
      subst (variable 1) (tvar 8) (Forall Index (un Type) $ un $ tvar 0) `shouldBe` (Forall Index (un Type) $ un $ tvar 0)
      subst (variable 0) (tvar 8) (Forall Index (un Type) $ un $ tvar 0) `shouldBe` (Forall Index (un Type) $ un $ tvar 0)
      subst (variable 0) (tvar 8) (Forall Index (un Type) $ un $ tvar 1) `shouldBe` (Forall Index (un Type) $ un $ tvar 9)

      subst (global 5) (tvar 8) (Forall Index (un Type) $ un $ TVar $ global 5)             `shouldBe` (Forall Index (un Type) $ un $ tvar 9)
      subst (global 5) (tvar 8) (Forall (Bind 5) (un Type) $ un $ TVar $ global 5)          `shouldBe` (Forall (Bind 5) (un Type) $ un $ tvar 8) -- Be careful with this behavior.
      subst (global 5) (TVar $ global 3) (Forall (Bind 3) (un Type) $ un $ TVar $ global 5) `shouldBe` (Forall (Bind 3) (un Type) $ un $ TVar $ global 3) -- Be careful with this behavior.

      subst (global 5) (tvar 8) (localize $ Forall (Bind 5) (un Type) $ un $ TVar $ global 5)          `shouldBe` (Forall Index (un Type) $ un $ tvar 0)
      subst (global 5) (TVar $ global 3) (localize $ Forall (Bind 3) (un Type) $ un $ TVar $ global 5) `shouldBe` (Forall Index (un Type) $ un $ TVar $ global 3)

  describe "localize" $ do
    it "localizes a type" $ do
      localize (Forall (Bind 3) (un Type) $ un $ tvar 0) `shouldBe` (Forall Index (un Type) $ un $ tvar 1)

  describe "reduce" $ do
    it "reduces a type to its weak-head normal form (up to alpha-equivalence)" $ do
      runEqEnv emptyEqEnv (reduce $ tvar 0)                                                                             `shouldBe` tvar 0
      runEqEnv emptyEqEnv (reduce $ Forall Index (un Type) $ un $ tvar 0)                                               `shouldBe` Forall Index (un Type) (un $ tvar 0)
      runEqEnv emptyEqEnv (reduce $ TApp (TAbs Index Type $ tvar 0) $ tvar 66)                                          `shouldBe` tvar 66
      runEqEnv emptyEqEnv (reduce $ TApp (TAbs (Bind 6) Type $ tvar 0) $ tvar 66)                                       `shouldBe` tvar 0
      runEqEnv emptyEqEnv (reduce $ TApp (TAbs (Bind 6) Type $ TVar $ global 6) $ tvar 66)                              `shouldBe` tvar 66
      runEqEnv emptyEqEnv (reduce $ TApp (TAbs (Bind 6) Type $ TAbs (Bind 6) Type $ TVar $ global 6) $ tvar 66)         `shouldBe` TAbs Index Type (tvar 0)
      runEqEnv emptyEqEnv (reduce $ TApp (TAbs (Bind 6) Type $ TAbs (Bind 9) Type $ TVar $ global 6) $ TVar $ global 9) `shouldBe` TAbs Index Type (TVar $ global 9)
      runEqEnv emptyEqEnv (reduce $ tvar 0 @@ (TAbs Index Type (tvar 0) @@ tvar 65))                                    `shouldBe` tvar 0 @@ (TAbs Index Type (tvar 0) @@ tvar 65)

      runEqEnv [(variable 0, tvar 79)] (reduce $ tvar 0) `shouldBe` tvar 79

      -- The following will not terminate as expected.
      -- runEqEnv [(variable 0, tvar 79), (variable 79, tvar 0)] (reduce $ tvar 0) `shouldBe` tvar 79

      runEqEnv [(variable 0, tvar 1), (variable 1, tvar 2)] (reduce $ tvar 0) `shouldBe` tvar 2
      runEqEnv [(variable 0, tvar 1), (variable 1, tvar 2)] (reduce $ tvar 1) `shouldBe` tvar 2
      runEqEnv [(variable 0, tvar 1), (variable 1, tvar 2)] (reduce $ tvar 2) `shouldBe` tvar 2
      runEqEnv [(variable 0, tvar 1), (variable 1, tvar 2)] (reduce $ tvar 3) `shouldBe` tvar 3

      runEqEnv [(variable 0, TAbs Index Type (tvar 0) @@ tvar 80)] (reduce $ tvar 0)                                `shouldBe` tvar 80
      runEqEnv [(variable 0, TAbs Index Type (tvar 0) @@ tvar 80)] (reduce $ TAbs Index Type (tvar 1) @@ tvar 65)   `shouldBe` tvar 80
      runEqEnv [(variable 0, TAbs Index Type $ tvar 0)] (reduce $ tvar 0 @@ tvar 65)                                `shouldBe` tvar 65
      runEqEnv [(variable 0, TAbs Index Type $ tvar 0)] (reduce $ tvar 0 @@ (TAbs Index Type (tvar 0) @@ tvar 65))  `shouldBe` tvar 65
      runEqEnv [(variable 0, TAbs Index Type $ tvar 0)] (reduce $ tvar 0 @@ (TAbs Index Type (tvar 33) @@ tvar 65)) `shouldBe` tvar 32

  describe "equalType" $ do
    it "tests whether two types (of the 'type' kind) are equivalent" $ do
      equalType (Forall Index (un Type) $ un $ tvar 0) (Forall Index (un Type) $ un $ tvar 0)    `shouldBe` return ()
      equalType (Forall Index (lin Type) $ un $ tvar 0) (Forall Index (un Type) $ un $ tvar 0)   `shouldBe` Left (ModedKindMismatch (lin Type) (un Type) Any)
      equalType (Forall Index (lin Type) $ un $ tvar 0) (Forall Index (lin Type) $ lin $ tvar 0) `shouldBe` Left (ModeMismatch Unrestricted Linear (tvar 0) (tvar 0) Any)

      equalType (Forall Index (un Type) $ un $ tvar 0) (Forall Index (un Type) $ un $ TAbs Index Type (tvar 0) @@ tvar 0) `shouldBe` return ()
