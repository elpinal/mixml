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

  -- * Pretty-printing
  , Prec(..)
  , Named(..)
  ) where

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Reader
import qualified Data.Map.Strict as Map
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
    m <- mapM (prettyEnv 0) m
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

type MKind = Moded Kind

data Variable
  = Variable Int
  | Global Int
  deriving (Eq, Show)

variable :: Int -> Variable
variable = Variable

global :: Int -> Variable
global = Global

data NameEnv = NameEnv
  { ntenv :: Map.Map Int T.Text
  , nvenv :: Map.Map Int T.Text
  , count :: Int
  }

nameEnv :: NameEnv
nameEnv = NameEnv
  { ntenv = mempty
  , nvenv = mempty
  , count = 0
  }

incCount :: NameEnv -> NameEnv
incCount nenv = nenv { count = count nenv + 1 }

newTypeVariable :: NameEnv -> NameEnv
newTypeVariable nenv = (incCount nenv)
  { ntenv = Map.insert (count nenv) ("t" <> T.pack (show $ count nenv)) $ ntenv nenv
  }

class PrettyEnv a where
  prettyEnv :: Member (Reader NameEnv) r => Int -> a -> Eff r (Doc ann)

newtype Named a = Named a
  deriving (Eq, Show)

instance PrettyEnv a => Pretty (Named a) where
  pretty (Named x) = run $ runReader nameEnv $ prettyEnv 0 x

prettyTypeVariable :: Member (Reader NameEnv) r => Variable -> Eff r (Doc ann)
prettyTypeVariable (Global n)   = return $ "g" <> pretty n
prettyTypeVariable (Variable n) = do
  nenv <- asks ntenv
  c <- asks count
  return $ maybe ("v" <> brackets (pretty n)) pretty $ Map.lookup (c - n - 1) nenv

prettyVariable :: Member (Reader NameEnv) r => Variable -> Eff r (Doc ann)
prettyVariable (Global n)   = return $ "g" <> pretty n
prettyVariable (Variable n) = do
  nenv <- asks nvenv
  c <- asks count
  return $ maybe ("v" <> brackets (pretty n)) pretty $ Map.lookup (c - n - 1) nenv

data Binder
  = Index
  | Bind Int
  deriving (Eq, Show)

prettyTypeBinder :: Member (Reader NameEnv) r => Binder -> Eff r a -> Eff r (Doc ann, a)
prettyTypeBinder (Bind n) e = (,) <$> prettyTypeVariable (Global n) <*> e
prettyTypeBinder Index    e = local newTypeVariable $ (,) <$> prettyTypeVariable (Variable 0) <*> e

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

prettyBind :: (Member (Reader NameEnv) r, PrettyPrec k, PrettyEnv ty) => Int -> Binder -> k -> ty -> Doc ann -> Eff r (Doc ann)
prettyBind n b k ty d = fmap (parensWhen $ n >= 4) $ fmap f $ prettyTypeBinder b $ prettyEnv 0 ty
  where f (x, y) = d <> x <+> ":" <+> pretty (Prec k) <> "." <+> y

instance PrettyEnv Type where
  prettyEnv n (TFun ty1 ty2) = fmap (parensWhen $ n >= 4) $ f <$> prettyEnv 4 ty1 <*> prettyEnv 3 ty2
    where f d1 d2 = hsep [d1, "->", d2]
  prettyEnv n (TRecord r)     = prettyEnv n r
  prettyEnv n (Forall b k ty) = prettyBind n b k ty "∀"
  prettyEnv n (Some b k ty)   = prettyBind n b k ty "∃"
  prettyEnv n (Ref ty)        = parensWhen (n >= 9) <$> liftM2 (<>) (return "?") (prettyEnv 9 ty)
  prettyEnv _ (TVar v)        = prettyTypeVariable v
  prettyEnv n (TAbs b k ty)   = prettyBind n b k ty "λ"
  prettyEnv n (TApp ty1 ty2)  = fmap (parensWhen $ n >= 5) $ liftM2 (<+>) (prettyEnv 4 ty1) (prettyEnv 5 ty2)

type MType = Moded Type

data Env = Env
  { tenv :: Map.Map Variable MKind
  , eqenv :: Map.Map Variable Type
  , venv :: Map.Map Variable MType
  }
  deriving (Eq, Show)

data Environmental a = Environmental Env a
  deriving (Eq, Show)
