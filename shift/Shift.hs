{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Shift
  ( Shift(..)
  , GShift(..)
  , Fixed(..)
  , IndexedVariable(..)
  ) where

import qualified Data.Map.Lazy as Map
import GHC.Generics

-- Shifts variables.
class Shift a where
  shiftAbove :: Int -> Int -> a -> a
  shift :: Int -> a -> a

  default shiftAbove :: (Generic a, GShift (Rep a)) => Int -> Int -> a -> a
  shiftAbove c d x = to $ gShiftAbove c d $ from x

  shift d x = shiftAbove 0 d x

class GShift f where
  gShiftAbove :: Int -> Int -> f a -> f a

instance GShift V1 where
  gShiftAbove _ _ _ = undefined

instance GShift U1 where
  gShiftAbove _ _ U1 = U1

instance (GShift a, GShift b) => GShift (a :*: b) where
  gShiftAbove c d (x :*: y) = gShiftAbove c d x :*: gShiftAbove c d y

instance (GShift a, GShift b) => GShift (a :+: b) where
  gShiftAbove c d (L1 x) = L1 $ gShiftAbove c d x
  gShiftAbove c d (R1 x) = R1 $ gShiftAbove c d x

instance GShift a => GShift (M1 i c a) where
  gShiftAbove c d (M1 x) = M1 $ gShiftAbove c d x

instance Shift a => GShift (K1 i a) where
  gShiftAbove c d (K1 x) = K1 $ shiftAbove c d x

instance Shift () where
  shiftAbove _ _ x = x

newtype Fixed a = Fixed { getFixed :: a }
  deriving (Eq, Show)

instance Shift (Fixed a) where
  shiftAbove _ _ x = x

newtype IndexedVariable = IndexedVariable { getIndexedVariable :: Int }
  deriving (Eq, Show)

instance Shift IndexedVariable where
  shiftAbove c d v @ (IndexedVariable n)
    | c <= n    = IndexedVariable $ n + d
    | otherwise = v

instance Shift a => Shift [a] where
  shiftAbove c d xs = map (shiftAbove c d) xs

instance Shift a => Shift (Map.Map k a) where
  shiftAbove c d = fmap $ shiftAbove c d

instance (Shift a, Shift b) => Shift (a, b) where
  shiftAbove c d (x, y) = (shiftAbove c d x, shiftAbove c d y)

instance (Shift a, Shift b, Shift c) => Shift (a, b, c) where
  shiftAbove c d (x, y, z) = (shiftAbove c d x, shiftAbove c d y, shiftAbove c d z)
