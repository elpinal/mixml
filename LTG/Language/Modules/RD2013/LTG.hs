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

  -- * Environments
  , TEnv
  , emptyTEnv

  -- * Errors
  , KindError(..)
  ) where

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Data.Functor
import qualified Data.Map.Strict as Map
import Data.Monoid hiding (Any)
import Data.Semigroup hiding (Any)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc
import GHC.Exts

data Mode
  = Unrestricted
  | Linear
  deriving (Eq, Show)

instance Pretty Mode where
  pretty Unrestricted = "U"
  pretty Linear       = "L"

un :: a -> Moded a
un = Moded Unrestricted

lin :: a -> Moded a
lin = Moded Linear

data Moded a = Moded Mode a
  deriving (Eq, Show)

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

newtype Label = Label T.Text
  deriving (Eq, Ord, Show, Pretty, IsString)

newtype Record a = Record (Map.Map Label a)
  deriving (Eq, Show)

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
  , itenv :: [Maybe MKind] -- Indexed type environment.
  }
  deriving (Eq, Show)

emptyTEnv :: TEnv
emptyTEnv = TEnv
  { gtenv = mempty
  , itenv = []
  }

isLinear :: Moded a -> Bool
isLinear x = getMode x == Linear

findLinear :: TEnv -> Set.Set Variable
findLinear tenv =
  Set.map global (Map.keysSet $ Map.filter isLinear $ gtenv tenv)
  <>
  foldr g mempty (map f $ zip [0..] $ itenv tenv)
    where
      f (_, Nothing) = Nothing
      f (n, Just k)
        | isLinear k = Just $ variable n
        | otherwise  = Nothing

      g Nothing s  = s
      g (Just v) s = Set.insert v s

data Env = Env
  { tenv :: TEnv
  , eqenv :: Map.Map Variable Type
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

data KindError
  = UnexpectedLinearKind Type CTEnv
  | UnexpectedHigherKind Kind Type CTEnv
  | UnusedTypeVariableWithLinearKind Kind
  | EmptyITEnv
  | UnboundTypeVariable Variable
  | UnusedTypeVariables (Set.Set Variable) CTEnv
  deriving (Eq, Show)

type WithTEnvError r = Members '[State TEnv, Error KindError] r

throw :: WithTEnvError r => (CTEnv -> KindError) -> Eff r ()
throw f = do
  tenv <- get
  throwError $ f $ Consistent tenv

unType :: (Kinded a, WithTEnvError r) => a -> Eff r ()
unType ty = do
  k <- kindOf ty
  case k of
    Moded Linear _       -> throw $ UnexpectedLinearKind $ toType ty
    Moded Unrestricted k ->
      case k of
        Type     -> pure ()
        KFun _ _ -> throw $ UnexpectedHigherKind k $ toType ty

(!?) :: [a] -> Int -> Maybe a
[] !? n       = Nothing
(x : _) !? 0  = Just x
(_ : xs) !? n = xs !? (n - 1)

close :: Member (Error KindError) r => TEnv -> Eff (State TEnv ': r) a -> Eff r a
close tenv e = do
  (x, tenv) <- runState tenv e
  let set = findLinear tenv
  when (not $ Set.null set) $
    throwError $ UnusedTypeVariables set $ Consistent tenv
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
    maybe (throwError $ UnboundTypeVariable v) return $ Map.lookup n tenv

  kindOf v @ (Variable n) = do
    tenv <- gets itenv
    maybe (throwError $ UnboundTypeVariable v) return $ join $ tenv !? n

instance Kinded Type where
  toType = id

  kindOf (TVar v)        = kindOf v
  kindOf (TFun ty1 ty2)  = unType ty1 >> unType ty2 $> un Type
  kindOf (Ref ty)        = unType ty $> un Type
  kindOf (Forall b k ty) = withTypeBinding b (toUn k) $ unType ty $> un Type

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
    Just (Moded Linear k) -> throwError $ UnusedTypeVariableWithLinearKind k
    _                     -> return ()
  modify $ replaceGTEnv $ Map.update (\_ -> old) n tenv

replaceGTEnv :: Map.Map Int MKind -> TEnv -> TEnv
replaceGTEnv m tenv = tenv { gtenv = m }

replaceITEnv :: [Maybe MKind] -> TEnv -> TEnv
replaceITEnv xs tenv = tenv { itenv = xs }

uncons []       = throwError EmptyITEnv
uncons (x : xs) = return $ (x, xs)

push :: Member (State TEnv) r => MKind -> Eff r ()
push k = modify f
  where
    f tenv = tenv { itenv = Just k : itenv tenv }

pop :: WithTEnvError r => Mode -> Eff r ()
pop m = do
  tenv <- gets itenv
  (x, xs) <- uncons tenv
  modify $ replaceITEnv xs
  case x of
    Just (Moded Linear k) -> throwError $ UnusedTypeVariableWithLinearKind k
    _                     -> return ()

withTypeBinding :: WithTEnvError r => Binder -> MKind -> Eff r a -> Eff r a
withTypeBinding Index k e = do
  push k
  x <- e
  pop $ getMode k
  return x
withTypeBinding (Bind n) k e = do
  old <- insert n k
  x <- e
  alter old n
  return x
