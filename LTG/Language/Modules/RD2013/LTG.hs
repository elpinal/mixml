module Language.Modules.RD2013.LTG
  (
  -- * Modes
    Mode(..)
  , Moded(..)
  , un
  , lin

  -- * Variables
  , Variable
  , variable
  , global

  -- * Labels
  , Label

  -- * Records
  , Record

  -- * Kinds
  , Kind(..)
  , MKind

  -- * Binders
  , Binder(..)

  -- * Types
  , Type(..)
  , MType
  , tvar
  , (@@)

  -- * Terms
  , Term(..)
  , seq_

  -- * Pretty-printing
  , Prec(..)
  , Named(..)

  -- * Linearity
  , close

  -- * Kinding
  , Kinded(..)

  -- * Typing
  , Typed(..)

  -- * Environments
  , TEnv
  , emptyTEnv
  , fromGTEnv
  , EqEnv
  , emptyEqEnv

  -- * Failure
  , Failure(..)
  , Evidence(..)

  -- * Errors
  , KindError(..)
  , TypeError(..)

  -- * Consistency
  , Consistent(..)

  -- * Substitutions
  , Subst(..)
  , Substitution(..)
  , subst
  , substTop

  -- * Localization
  , Localize(..)

  -- * Reduction
  , reduce

  -- * Beta-eta equivalence
  , BetaEtaEq(..)
  , equalType
  ) where

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Data.Foldable (fold)
import Data.Functor
import Data.Map.Merge.Strict
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Monoid
import Data.Monoid hiding (Any)
import Data.Semigroup hiding (Any)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import GHC.Exts
import GHC.Generics

import Shift

data Mode
  = Unrestricted
  | Linear
  deriving (Eq, Show)
  deriving Shift via Fixed Mode

instance Pretty Mode where
  pretty Unrestricted = "U"
  pretty Linear       = "L"

un :: a -> Moded a
un = Moded Unrestricted

lin :: a -> Moded a
lin = Moded Linear

data Moded a = Moded Mode a
  deriving (Eq, Show)
  deriving Functor
  deriving Generic

instance Shift a => Shift (Moded a)

-- "Unrestricted" mode is omitted for pretty-printing.
instance PrettyPrec a => PrettyPrec (Moded a) where
  prettyPrec n (Moded Unrestricted x) = prettyPrec n x
  prettyPrec n (Moded Linear x)       = prettyPrec 9 x <> "@" <> pretty Linear

-- "Unrestricted" mode is omitted for pretty-printing.
instance PrettyEnv a => PrettyEnv (Moded a) where
  prettyEnv n (Moded Unrestricted x) = prettyEnv n x
  prettyEnv n (Moded Linear x) = do
    d <- prettyEnv 9 x
    return $ d <> "@" <> pretty Linear

toUn :: Moded a -> Moded a
toUn (Moded _ x) = Moded Unrestricted x

getMode :: Moded a -> Mode
getMode (Moded m _) = m

fromModed :: Moded a -> a
fromModed (Moded _ x) = x

newtype Label = Label T.Text
  deriving (Eq, Ord, Show, Pretty, IsString)

newtype Record a = Record (Map.Map Label a)
  deriving (Eq, Show)
  deriving Functor
  deriving Generic

instance Shift a => Shift (Record a)

instance IsList (Record a) where
  type Item (Record a) = (Label, a)

  fromList = Record . Map.fromList
  toList (Record m) = Map.toList m

instance PrettyEnv a => PrettyEnv (Record a) where
  prettyEnv _ (Record m) = do
    m <- mapM prettyEnv0 m
    let x = hcat $ punctuate (semi <> line) $ (\(l, d) -> hsep [pretty l, "=", d]) <$> Map.toList m
    return $ group $ braces $ flatAlt space "" <> align x <> flatAlt (semi <> line) ""

data Kind
  = Type
  | KFun Kind Kind
  deriving (Eq, Show)
  deriving Shift via Fixed Kind

class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc ann

newtype Prec a = Prec a
  deriving (Eq, Show)

instance PrettyPrec a => Pretty (Prec a) where
  pretty (Prec x) = prettyPrec 0 x

parensWhen :: Bool -> Doc ann -> Doc ann
parensWhen True  = parens
parensWhen False = id

instance PrettyPrec Kind where
  prettyPrec _ Type         = "*"
  prettyPrec n (KFun k1 k2) = parensWhen (n >= 4) $ prettyPrec 4 k1 <+> "->" <+> prettyPrec 3 k2

instance PrettyEnv Kind where
  prettyEnv n k = return $ prettyPrec n k

type MKind = Moded Kind

data Variable
  = Variable Int
  | Global Int
  deriving (Eq, Ord, Show)

instance Shift Variable where
  shiftAbove c d (Variable n) = Variable $ coerce $ shiftAbove c d $ IndexedVariable n
  shiftAbove _ _ g            = g

variable :: Int -> Variable
variable = Variable

global :: Int -> Variable
global = Global

data NameEnv = NameEnv
  { vdepth :: Int
  , tdepth :: Int
  }

nameEnv :: NameEnv
nameEnv = NameEnv
  { vdepth = 0
  , tdepth = 0
  }

fromCTEnv :: CTEnv -> NameEnv
fromCTEnv (Consistent tenv) = nameEnv { tdepth = length $ itenv tenv }
fromCTEnv Any               = error "unexpected Any"

incValueDepth :: NameEnv -> NameEnv
incValueDepth nenv = nenv { vdepth = vdepth nenv + 1 }

incTypeDepth :: NameEnv -> NameEnv
incTypeDepth nenv = nenv { tdepth = tdepth nenv + 1 }

class PrettyEnv a where
  prettyEnv :: Member (Reader NameEnv) r => Int -> a -> Eff r (Doc ann)

prettyEnv0 :: (PrettyEnv a, Member (Reader NameEnv) r) => a -> Eff r (Doc ann)
prettyEnv0 = prettyEnv 0

newtype Named a = Named a
  deriving (Eq, Show)

instance PrettyEnv a => Pretty (Named a) where
  pretty (Named x) = run $ runReader nameEnv $ prettyEnv0 x

prettyTypeVariable :: Member (Reader NameEnv) r => Variable -> Eff r (Doc ann)
prettyTypeVariable (Global n)   = return $ "g" <> pretty n
prettyTypeVariable (Variable n) = do
  d <- asks tdepth
  let m = d - n - 1
  if m < 0
    then return $ "v" <> brackets (pretty n)
    else return $ "t" <> pretty m

prettyVariable :: Member (Reader NameEnv) r => Variable -> Eff r (Doc ann)
prettyVariable (Global n)   = return $ "g" <> pretty n
prettyVariable (Variable n) = do
  d <- asks vdepth
  let m = d - n - 1
  if m < 0
    then return $ "v" <> brackets (pretty n)
    else return $ "v" <> pretty m

data Binder
  = Index
  | Bind Int
  deriving (Eq, Show)
  deriving Shift via Fixed Binder

isIndex :: Binder -> Bool
isIndex Index    = True
isIndex (Bind _) = False

ifIndex :: Binder -> (a -> a) -> a -> a
ifIndex Index f    = f
ifIndex (Bind _) _ = id

countIndex :: [Binder] -> Int
countIndex = length . filter isIndex

prettyTypeBinder :: Member (Reader NameEnv) r => Binder -> Eff r (Doc ann)
prettyTypeBinder (Bind n) = prettyTypeVariable (Global n)
prettyTypeBinder Index    = local incTypeDepth $ prettyTypeVariable $ Variable 0

prettyBinder :: Member (Reader NameEnv) r => Binder -> Eff r (Doc ann)
prettyBinder (Bind n) = prettyVariable (Global n)
prettyBinder Index    = local incValueDepth $ prettyVariable $ Variable 0

data Type
  = TFun MType MType
  | TRecord (Record MType)
  | Forall Binder MKind MType
  | Some Binder MKind MType
  | Ref Type
  | TVar Variable
  | TAbs Binder Kind Type
  | TApp Type Type
  deriving (Eq, Show)
  deriving Generic

delta :: Binder -> Int
delta Index    = 1
delta (Bind _) = 0

tvar :: Int -> Type
tvar = TVar . variable

(@@) :: Type -> Type -> Type
(@@) = TApp

instance Shift Type where
  shiftAbove c d (Forall b k ty) = Forall b k $ shiftAbove (c + delta b) d ty
  shiftAbove c d (Some b k ty)   = Some b k $ shiftAbove (c + delta b) d ty
  shiftAbove c d (TAbs b k ty)   = TAbs b k $ shiftAbove (c + delta b) d ty
  shiftAbove c d x               = to $ gShiftAbove c d $ from x

prettyTypeBind :: (Member (Reader NameEnv) r, PrettyPrec k, PrettyEnv ty) => Int -> Binder -> k -> ty -> Doc ann -> Eff r (Doc ann)
prettyTypeBind n b k ty d = fmap (parensWhen $ n >= 4) $ f <$> prettyTypeBinder b <*> local (ifIndex b incTypeDepth) (prettyEnv0 ty)
  where f x y = d <> x <+> ":" <+> pretty (Prec k) <> "." <+> y

instance PrettyEnv Type where
  prettyEnv n (TFun ty1 ty2) = fmap (parensWhen $ n >= 4) $ f <$> prettyEnv 4 ty1 <*> prettyEnv 3 ty2
    where f d1 d2 = hsep [d1, "->", d2]
  prettyEnv n (TRecord r)     = prettyEnv n r
  prettyEnv n (Forall b k ty) = prettyTypeBind n b k ty "∀"
  prettyEnv n (Some b k ty)   = prettyTypeBind n b k ty "∃"
  prettyEnv n (Ref ty)        = parensWhen (n >= 9) <$> liftM2 (<>) (return "?") (prettyEnv 9 ty)
  prettyEnv _ (TVar v)        = prettyTypeVariable v
  prettyEnv n (TAbs b k ty)   = prettyTypeBind n b k ty "λ"
  prettyEnv n (TApp ty1 ty2)  = parenF (n >= 5) $ liftM2 (<+>) (prettyEnv 4 ty1) (prettyEnv 5 ty2)

type MType = Moded Type

data Term
  = Var Variable
  | Abs Binder MType Term
  | App Term Term
  | TmRecord (Record Term)
  | Let (Record Binder) Term Term
  | LetN [(Binder, Term)] Term
  | New Type
  | Def Term Term
  | Read Term
  | Poly Binder MKind Term
  | Inst Term Type
  | Pack Type Term Type
  | Unpack Binder Binder Term Term
  | NewIn Binder Kind Term
  | NewInN [(Binder, Kind)] Term
  | DefIn Type Type Term MType
  | DefInN [(Type, Type)] Term MType
  | Proj Term Label
  | Restrict Term (Set.Set Label)
  deriving (Eq, Show)

seq_ :: Term -> Term -> Term
seq_ t1 t2 = Let [] t1 t2

prettyBind :: (Member (Reader NameEnv) r, PrettyEnv k, PrettyEnv ty) => Int -> Binder -> k -> ty -> Doc ann -> Eff r (Doc ann)
prettyBind n b k ty d = fmap (parensWhen $ n >= 4) $ f <$> prettyBinder b <*> prettyEnv0 k <*> local (ifIndex b incValueDepth) (prettyEnv0 ty)
  where f x y z = d <> x <+> ":" <+> y <> "." <+> z

toVariable :: Member (State Int) r => Binder -> Eff r Variable
toVariable Index    = modify (subtract (1 :: Int)) >> gets variable
toVariable (Bind n) = return $ global n

ntimes :: Int -> (a -> a) -> a -> a
ntimes n = appEndo . mtimesDefault n . Endo

lineAlt :: Doc ann
lineAlt = flatAlt hardline space

parenF :: Functor f => Bool -> f (Doc ann) -> f (Doc ann)
parenF = fmap . parensWhen

instance PrettyEnv Term where
  prettyEnv _ (Var v)       = prettyVariable v
  prettyEnv n (Abs b ty t)  = prettyBind n b ty t "λ"
  prettyEnv n (App t1 t2)   = parenF (n >= 5) $ liftM2 (<+>) (prettyEnv 4 t1) (prettyEnv 5 t2)
  prettyEnv n (TmRecord r)  = prettyEnv n r
  prettyEnv n (Let r t1 t2) = do
    let nn = countIndex $ snd <$> toList r
    let f (l, b) = local (ntimes nn incValueDepth) $ toVariable b >>= prettyVariable >>= \x -> return (hsep [pretty l, "=", x])
    d <- hsep . punctuate semi <$> evalState nn (sequence $ f <$> toList r)
    d1 <- prettyEnv0 t1
    d2 <- local (ntimes nn incValueDepth) $ prettyEnv0 t2
    return $ parensWhen (n >= 4) $ hsep ["let", braces d, "=", d1, "in" <> softline <> d2]
  prettyEnv n (LetN xs t) = do
    let nn = countIndex $ fst <$> xs
    let f (b, t) = (\x y -> hsep [x, "=", y]) <$> (toVariable b >>= local (ntimes nn incValueDepth) . prettyVariable) <*> prettyEnv0 t
    ds <- evalState nn $ mapM f xs
    z <- local (ntimes nn incValueDepth) $ prettyEnv0 t
    return $ parensWhen (n >= 4) $ hsep ("let" : punctuate semi ds) <+> "in" <> softline <> z
  prettyEnv n (New ty)              = parensWhen (n >= 4) . ("new" <+>) <$> prettyEnv 9 ty
  prettyEnv n (Def t1 t2)           = (\x y -> parensWhen (n >= 4) $ hsep ["def", x, ":=", y]) <$> prettyEnv0 t1 <*> prettyEnv0 t2
  prettyEnv n (Read t)              = parensWhen (n >= 9) . ("!" <>) <$> prettyEnv 9 t
  prettyEnv n (Poly b k t)          = prettyTypeBind n b k t "Λ"
  prettyEnv n (Inst t ty)           = parenF (n >= 5) $ liftM2 (<+>) (prettyEnv 4 t) (brackets <$> prettyEnv0 ty)
  prettyEnv n (Pack ty1 t ty2)      = parenF (n >= 4) $ (\x y z -> hsep ["pack", angles $ x <> comma <+> y, "as", z]) <$> prettyEnv0 ty1 <*> prettyEnv0 t <*> prettyEnv0 ty2
  prettyEnv n (Unpack b1 b2 t1 t2)  = parenF (n >= 4) $ f <$> prettyTypeBinder b1 <*> prettyBinder b2 <*> prettyEnv0 t1 <*> local (ifIndex b2 incValueDepth . ifIndex b1 incTypeDepth) (prettyEnv0 t2)
    where
      f w x y z = align $ group (hsep ["unpack", angles $ w <> comma <+> x, nest 2 ("=" <> lineAlt <> y) <> lineAlt <> "in" <> lineAlt]) <> softline' <> z
  prettyEnv n (NewIn b k t)         = parenF (n >= 4) $ f <$> prettyTypeBinder b <*> prettyEnv0 k <*> local (ifIndex b incTypeDepth) (prettyEnv0 t)
    where
      f x y z = hsep ["new", x, ":", y, "in" <> softline <> z]
  prettyEnv n (NewInN xs t)         = parenF (n >= 4) $ local (ntimes nn incTypeDepth) $ (\x y -> hsep ("new" : punctuate semi x ++ ["in" <> softline <> y])) <$> evalState nn (mapM f xs) <*> prettyEnv0 t
    where
      f (b, k) = toVariable b >>= prettyTypeVariable >>= \x -> return $ hsep [x, ":", pretty $ Prec k]
      nn = countIndex $ fst <$> xs
  prettyEnv n (DefIn ty1 ty2 t ty3) = parenF (n >= 4) $ (\w x y z -> hsep ["def", w, ":=", x, "in" <> softline <> y, ":", z]) <$> prettyEnv0 ty1 <*> prettyEnv0 ty2 <*> prettyEnv 9 t <*> prettyEnv0 ty3
  prettyEnv n (DefInN tys t ty)     = parenF (n >= 4) $ (\x y z -> hsep ("def" : punctuate semi x ++ ["in" <> softline <> y, ":", z])) <$> mapM f tys <*> prettyEnv 9 t <*> prettyEnv0 ty
    where
      f (ty1, ty2) = (\x y -> hsep [x, ":=", y]) <$> prettyEnv0 ty1 <*> prettyEnv0 ty2
  prettyEnv n (Proj t l)            = (\x -> hcat [x, ".", pretty l]) <$> prettyEnv 9 t
  prettyEnv n (Restrict t ls)       = parenF (n >= 4) $ (\x -> hsep ["restrict", x, "to", prettyList $ Set.toAscList ls]) <$> prettyEnv0 t

data TEnv = TEnv
  { gtenv :: Map.Map Int MKind -- Global type environment.
  , itenv :: [MKind] -- Indexed type environment.
  }
  deriving (Eq, Show)

emptyTEnv :: TEnv
emptyTEnv = TEnv
  { gtenv = mempty
  , itenv = []
  }

fromGTEnv :: Map.Map Int MKind -> TEnv
fromGTEnv e = emptyTEnv { gtenv = e }

isLinear :: Moded a -> Bool
isLinear x = getMode x == Linear

findLinear :: TEnv -> Set.Set Variable
findLinear tenv =
  Set.map global (Map.keysSet $ Map.filter isLinear $ gtenv tenv)
  <>
  foldr g mempty (map f $ zip [0..] $ itenv tenv)
    where
      f (n, k)
        | isLinear k = Just $ variable n
        | otherwise  = Nothing

      g Nothing s  = s
      g (Just v) s = Set.insert v s

newtype EqEnv = EqEnv (Map.Map Variable Type)
  deriving (Eq, Show)

instance IsList EqEnv where
  type Item EqEnv = (Variable, Type)

  fromList = coerce . Map.fromList
  toList (EqEnv m) = Map.toList m

emptyEqEnv :: EqEnv
emptyEqEnv = EqEnv mempty

lookupEqEnv :: Variable -> EqEnv -> Maybe Type
lookupEqEnv v (EqEnv m) = Map.lookup v m

extensional :: Member (Reader EqEnv) r => Variable -> Eff r (Maybe Type)
extensional v = asks $ lookupEqEnv v

data Env = Env
  { tenv :: TEnv
  , eqenv :: EqEnv
  , venv :: Map.Map Variable MType
  }
  deriving (Eq, Show)

data Environmental a = Environmental Env a
  deriving (Eq, Show)

data Consistent a
  = Any
  | Consistent a

instance Eq a => Eq (Consistent a) where
  Consistent x == Consistent y = x == y
  _ == _                       = True

instance Show a => Show (Consistent a) where
  show Any            = "Any"
  show (Consistent x) = show x

type CTEnv = Consistent TEnv

data Failure = forall a. Failure a (Evidence a) (a -> LayoutOptions -> T.Text)

data Evidence a where
  EvidKind :: Evidence KindError
  EvidType :: Evidence TypeError

class Evidential a where
  evidence :: Evidence a

throwFailure :: (Member (Error Failure) r, Evidential a, Pretty a) => a -> Eff r b
throwFailure x = throwError $ Failure x evidence (\y opt -> renderStrict $ layoutSmart opt $ pretty y)

data KindError
  = UnexpectedLinearKind Type CTEnv
  | UnexpectedHigherKind Kind Type CTEnv
  | UnusedTypeVariableWithLinearKind Kind
  | EmptyITEnv
  | UnboundTypeVariable Variable
  | UnusedTypeVariables (Set.Set Variable) CTEnv
  | KindMismatch Type Type Kind Kind CTEnv
  | ModedKindMismatch MKind MKind CTEnv
  | NotHigherKind Type Type CTEnv
  | StructurallyInequivalent Type Type CTEnv
  | MissingLabelL Label (Record MType) (Record MType) CTEnv
  | MissingLabelR Label (Record MType) (Record MType) CTEnv
  | ModeMismatch Mode Mode Type Type CTEnv
  deriving (Eq, Show)

instance Evidential KindError where
  evidence = EvidKind

instance Pretty KindError where
  pretty (UnexpectedLinearKind ty env)        = "expected unrestricted kind, but got linear kind for" <+> run (runReader (fromCTEnv env) $ prettyEnv0 ty)
  pretty (UnexpectedHigherKind k ty env)      = "unexpected higher kind:" <+> pretty (Prec k) <> ", which is kind of" <+> run (runReader (fromCTEnv env) $ prettyEnv0 ty)
  pretty (UnusedTypeVariableWithLinearKind k) = "unused type variable with kind:" <+> pretty (Prec $ lin k)
  pretty (UnboundTypeVariable v)              = "unbound type variable:" <+> pretty (show v)

type WithTEnvError r = Members '[State TEnv, Error Failure] r

throw :: (WithTEnvError r, Evidential e, Pretty e) => (CTEnv -> e) -> Eff r a
throw f = do
  tenv <- get
  throwFailure $ f $ Consistent tenv

unType :: (Kinded a, WithTEnvError r) => a -> Eff r ()
unType ty = do
  k <- unKind ty
  case k of
    Type     -> pure ()
    KFun _ _ -> throw $ UnexpectedHigherKind k $ toType ty

(!?) :: [a] -> Int -> Maybe a
[] !? n       = Nothing
(x : _) !? 0  = Just x
(_ : xs) !? n = xs !? (n - 1)

close :: Member (Error Failure) r => TEnv -> Eff (State TEnv ': r) a -> Eff r a
close tenv e = do
  (x, tenv) <- runState tenv e
  let set = findLinear tenv
  when (not $ Set.null set) $
    throwFailure $ UnusedTypeVariables set $ Consistent tenv
  return x

class Kinded a where
  toType :: a -> Type

  kindOf :: WithTEnvError r => a -> Eff r MKind

instance Kinded (Moded Type) where
  toType (Moded _ ty) = ty

  kindOf (Moded _ ty) = kindOf ty

instance Kinded Variable where
  toType = TVar

  kindOf v @ (Global n) = do
    tenv <- gets gtenv
    maybe (throwFailure $ UnboundTypeVariable v) return $ Map.lookup n tenv

  kindOf v @ (Variable n) = do
    tenv <- gets itenv
    maybe (throwFailure $ UnboundTypeVariable v) return $ tenv !? n

instance Kinded Type where
  toType = id

  kindOf (TVar v)        = kindOf v
  kindOf (TFun ty1 ty2)  = unType ty1 >> unType ty2 $> un Type
  kindOf (Ref ty)        = unType ty $> un Type
  kindOf (Forall b k ty) = withTypeBinding b (toUn k) $ unType ty $> un Type
  kindOf (Some b k ty)   = withTypeBinding b (toUn k) $ unType ty $> un Type
  kindOf (TAbs b k ty)   = fmap (un . KFun k) $ withTypeBinding b (un k) $ unKind ty
  kindOf (TApp ty1 ty2)  = fmap un $ join $ kindOfTApp ty1 ty2 <$> unKind ty1 <*> unKind ty2
  kindOf (TRecord r)     = kindOf r

kindOfTApp :: WithTEnvError r => Type -> Type -> Kind -> Kind -> Eff r Kind
kindOfTApp ty1 ty2 (KFun k1 k2) k
  | k1 == k               = return k2
  | otherwise             = throw $ KindMismatch ty1 ty2 k1 k
kindOfTApp ty1 ty2 Type _ = throw $ NotHigherKind ty1 ty2

instance Kinded (Record MType) where
  toType = TRecord

  kindOf (Record m) = mapM_ unType m $> un Type

unKind :: (Kinded a, WithTEnvError r) => a -> Eff r Kind
unKind ty = do
  k <- kindOf ty
  case k of
    Moded Linear _       -> throw $ UnexpectedLinearKind $ toType ty
    Moded Unrestricted k -> return k

insertLookup :: Ord k => k -> a -> Map.Map k a -> (Maybe a, Map.Map k a)
insertLookup k x t = Map.insertLookupWithKey (\_ a _ -> a) k x t

insert :: Member (State TEnv) r => Int -> MKind -> Eff r (Maybe MKind)
insert n k = do
  tenv <- gets gtenv
  let (old, m) = insertLookup n k tenv
  modify $ replaceGTEnv m
  return old

alter :: WithTEnvError r => Maybe MKind -> Int -> Eff r ()
alter old n = do
  tenv <- gets gtenv
  case Map.lookup n tenv of
    Just (Moded Linear k) -> throwFailure $ UnusedTypeVariableWithLinearKind k
    _                     -> return ()
  modify $ replaceGTEnv $ Map.update (\_ -> old) n tenv

replaceGTEnv :: Map.Map Int MKind -> TEnv -> TEnv
replaceGTEnv m tenv = tenv { gtenv = m }

replaceITEnv :: [MKind] -> TEnv -> TEnv
replaceITEnv xs tenv = tenv { itenv = xs }

uncons []       = throwFailure EmptyITEnv
uncons (x : xs) = return $ (x, xs)

push :: Member (State TEnv) r => MKind -> Eff r ()
push k = modify f
  where
    f tenv = tenv { itenv = k : itenv tenv }

pop :: WithTEnvError r => Eff r ()
pop = do
  tenv <- gets itenv
  (x, xs) <- uncons tenv
  modify $ replaceITEnv xs
  case x of
    Moded Linear k -> throwFailure $ UnusedTypeVariableWithLinearKind k
    _              -> return ()

withTypeBinding :: WithTEnvError r => Binder -> MKind -> Eff r a -> Eff r a
withTypeBinding Index k e = do
  push k
  x <- e
  pop
  return x
withTypeBinding (Bind n) k e = do
  old <- insert n k
  x <- e
  alter old n
  return x

class Used a where
  used :: a -> a -> Bool

instance Used TEnv where
  used tenv1 tenv2 = getAny $
    fold (uncurry f <$> zip (itenv tenv1) (itenv tenv2))
    <>
    fold (Map.intersectionWith f (gtenv tenv1) (gtenv tenv2))
      where
        f (Moded Linear _) (Moded Unrestricted _) = coerce True
        f (Moded Unrestricted _) (Moded Linear _) = error "unexpected transition from unrestricted kind to linear kind"
        f _ _                                     = coerce False

newtype Subst = Subst (Map.Map Variable Type)

instance IsList Subst where
  type Item Subst = (Variable, Type)

  fromList = coerce . Map.fromList
  toList (Subst m) = Map.toList m

instance Shift Subst where
  shiftAbove c d (Subst m) = Subst $ fromList $ f <$> toList m
    where
      f (v, ty) = (shiftAbove c d v, shiftAbove c d ty)

lookupSubst :: Variable -> Subst -> Maybe Type
lookupSubst v (Subst m) = Map.lookup v m

class Substitution a where
  apply :: Subst -> a -> a

-- Notice:
-- * Bound global variables can be affected.
-- * Global variables can be captured.
instance Substitution Type where
  apply s ty @ (TVar v)     = fromMaybe ty $ lookupSubst v s
  apply s (TFun ty1 ty2)    = apply s ty1 `TFun` apply s ty2
  apply s (TRecord r)       = TRecord $ apply s r
  apply s (Forall b k ty)   = Forall b k $ apply (shift (delta b) s) ty
  apply s (Some b k ty)     = Some b k $ apply (shift (delta b) s) ty
  apply s (TAbs b k ty)     = TAbs b k $ apply (shift (delta b) s) ty
  apply s (TApp ty1 ty2)    = apply s ty1 `TApp` apply s ty2
  apply s (Ref ty)          = Ref $ apply s ty

instance Substitution a => Substitution (Record a) where
  apply s (Record m) = Record $ apply s <$> m

instance Substitution a => Substitution (Moded a) where
  apply s m = apply s <$> m

subst :: Substitution a => Variable -> Type -> a -> a
subst v by = apply $ Subst $ Map.singleton v by

substTop :: Type -> Type -> Type
substTop by = shift (-1) . subst (variable 0) (shift 1 by)

class Localize a where
  localize :: a -> a

instance Localize Type where
  localize (TVar v)          = TVar v
  localize (TFun ty1 ty2)    = localize ty1 `TFun` localize ty2
  localize (TRecord r)       = TRecord $ localize r
  localize (Forall b k ty)   = Forall Index k $ localize' b ty
  localize (Some b k ty)     = Some Index k $ localize' b ty
  localize (TAbs b k ty)     = TAbs Index k $ localize' b ty
  localize (TApp ty1 ty2)    = localize ty1 `TApp` localize ty2
  localize (Ref ty)          = Ref $ localize ty

instance Localize a => Localize (Record a) where
  localize r = localize <$> r

instance Localize a => Localize (Moded a) where
  localize m = localize <$> m

localize' :: (Shift a, Substitution a, Localize a) => Binder -> a -> a
localize' Index ty    = localize ty
localize' (Bind n) ty = subst (global n) (TVar $ variable 0) $ shift 1 $ localize ty

-- This function may not terminate since type equivalence environments are
-- allowed to have cyclic definitions. But it's OK because undecidability of
-- LTG does not affect decidability of MixML.
reduce :: Member (Reader EqEnv) r => Type -> Eff r Type
reduce (TApp ty1 ty2) = join $ reduce' <$> reduce ty1 <*> return ty2
reduce ty @ (TVar v)  = extensional v >>= maybe (return ty) reduce
reduce ty             = return ty

reduce' :: Member (Reader EqEnv) r => Type -> Type -> Eff r Type
reduce' (TAbs Index _ ty1) ty2        = reduce $ substTop ty2 ty1
reduce' ty1 @ (TAbs (Bind n) _ _) ty2 = reduce' (localize ty1) ty2
reduce' ty1 ty2                       = return $ TApp ty1 ty2

strEquiv :: (WithTEnvError r, Member (Reader EqEnv) r) => Type -> Type -> Eff r Kind
strEquiv ty1 @ (TVar v1) ty2 @ (TVar v2)
  | v1 == v2  = fromModed <$> kindOf v1
  | otherwise = throw $ StructurallyInequivalent ty1 ty2
strEquiv (TFun ty11 ty12) (TFun ty21 ty22) = do
  equal ty11 ty21 Type
  equal ty12 ty22 Type
  return Type
strEquiv (TRecord r1 @ (Record m1)) (TRecord r2 @ (Record m2)) = do
  let f l _ = throw $ MissingLabelL l r1 r2
  let g l _ = throw $ MissingLabelR l r1 r2
  let h _ ty1 ty2 = equal ty1 ty2 Type
  _ <- mergeA (traverseMissing f) (traverseMissing g) (zipWithAMatched h) m1 m2
  return Type
strEquiv (Forall Index k1 ty1) (Forall Index k2 ty2)
  | k1 == k2  = push (toUn k1) >> equal ty1 ty2 Type $> Type <* pop
  | otherwise = throw $ ModedKindMismatch k1 k2
strEquiv (Some Index k1 ty1) (Some Index k2 ty2)
  | k1 == k2  = push (toUn k1) >> equal ty1 ty2 Type $> Type <* pop
  | otherwise = throw $ ModedKindMismatch k1 k2
strEquiv ty1 @ (Forall _ _ _) ty2 @ (Forall _ _ _) = strEquiv (localize ty1) (localize ty2)
strEquiv ty1 @ (Some _ _ _) ty2 @ (Some _ _ _)     = strEquiv (localize ty1) (localize ty2)
strEquiv (TApp ty11 ty12) (TApp ty21 ty22) = do
  k <- strEquiv ty11 ty21
  case k of
    KFun k1 k2 -> do
      equal ty12 ty22 k1
      return k2
    Type -> error $ "unexpected 'type' kind, which is kind of " ++ show ty11
strEquiv (Ref ty1) (Ref ty2) = strEquiv ty1 ty2
strEquiv ty1 ty2             = throw $ StructurallyInequivalent ty1 ty2

class BetaEtaEq a where
  equal :: (WithTEnvError r, Member (Reader EqEnv) r) => a -> a -> Kind -> Eff r ()

instance BetaEtaEq Type where
  -- Assumes well-kindness of input types.
  equal ty1 ty2 Type         = void $ join $ strEquiv <$> reduce ty1 <*> reduce ty2
  equal ty1 ty2 (KFun k1 k2) = do
    push $ un k1
    equal (shift 1 ty1 @@ tvar 0) (shift 1 ty2 @@ tvar 0) k2
    pop

instance BetaEtaEq MType where
  equal (Moded m1 ty1) (Moded m2 ty2) k
    | m1 == m2  = equal ty1 ty2 k
    | otherwise = throw $ ModeMismatch m1 m2 ty1 ty2

-- Assumes input types have the 'type' kind.
equalType :: Type -> Type -> Either Failure ()
equalType ty1 ty2 = run $ runError $ runReader emptyEqEnv $ evalState emptyTEnv $ equal ty1 ty2 Type

data TypeError
  = NotFunction Type Term Term CTEnv
  deriving (Eq, Show)

instance Evidential TypeError where
  evidence = EvidType

instance Pretty TypeError where
  pretty (NotFunction ty1 t1 t2 env) = "not function type:" <+> run (runReader (fromCTEnv env) $ prettyEnv0 ty1)

type WithEnvError r = (WithTEnvError r, Members '[Reader EqEnv] r)

class Typed a where
  typeOf :: WithEnvError r => a -> Eff r MType

instance Typed Term where
  typeOf (App t1 t2) = do
    ty1 <- fromModed <$> whTypeOf t1
    ty2 <- typeOf t2
    case ty1 of
      TFun ty11 ty12 -> do
        equal ty11 ty2 Type
        return ty12
      _ -> throw $ NotFunction ty1 t1 t2
  typeOf (New ty) = do
    unType ty
    return $ lin $ Ref ty
  typeOf (Poly b k t) = do
    tenv1 <- get
    -- TODO: consider venv
    ty <- withTypeBinding b k $ typeOf t
    tenv2 <- get
    let m = if used tenv1 (tenv2 :: TEnv)
              then lin
              else un
    return $ m $ Forall b k ty

whTypeOf :: (Typed a, WithEnvError r) => a -> Eff r MType
whTypeOf t = typeOf t >>= f
  where
    f (Moded m ty) = Moded m <$> reduce ty
