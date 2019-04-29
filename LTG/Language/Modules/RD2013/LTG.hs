module Language.Modules.RD2013.LTG
  (
  ) where

import qualified Data.Map.Strict as Map

data Mode
  = Unrestricted
  | Linear
  deriving (Eq, Show)

data Moded a = Moded Mode a
  deriving (Eq, Show)

newtype Label = Label String
  deriving (Eq, Ord, Show)

newtype Record a = Record (Map.Map Label a)
  deriving (Eq, Show)

data Kind
  = Type
  | KFun Kind Kind
  deriving (Eq, Show)

type MKind = Moded Kind

data Variable
  = Variable Int
  | Global Int
  deriving (Eq, Show)

data Binder
  = Index
  | Bind Int
  deriving (Eq, Show)

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

type MType = Moded Type

data Env = Env
  { tenv :: Map.Map Variable MKind
  , eqenv :: Map.Map Variable Type
  , venv :: Map.Map Variable MType
  }
  deriving (Eq, Show)

data Environmental a = Environmental Env a
  deriving (Eq, Show)
