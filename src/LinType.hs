{-# LANGUAGE DeriveDataTypeable #-}

module LinType where

import Data.Data

data LinType
  = Bottom
  | Top
  | One
  | Zero
  | Atom Int
  | OfCourse LinType
  | WhyNot LinType
  | Perp LinType
  | Tens LinType LinType
  | Par LinType LinType
  | Plus LinType LinType
  | With LinType LinType
  deriving (Eq, Show, Ord, Typeable, Data)

isAtomic :: LinType -> Bool
isAtomic (Atom i) = True
isAtomic (Perp (Atom i)) = True
isAtomic _ = False

isAtom (Atom i) = True
isAtom _ = False

isPerp (Perp t) = True
isPerp _ = False

dual :: LinType -> LinType
dual Bottom = One
dual One = Bottom
dual Top = Zero
dual Zero = Top
dual (Atom i) = Perp (Atom i)
dual (Perp (Atom i)) = Atom i
dual (Plus a b) = With (dual a) (dual b)
dual (Tens a b) = Par (dual a) (dual b)
dual (Par a b) = Tens (dual a) (dual b)
dual (OfCourse a) = WhyNot (dual a)
dual (WhyNot a) = OfCourse (dual a)

isPositive :: LinType -> Bool
isPositive t = case t of
  -- TODO: What about Perp and Atom?
  One -> True
  Zero -> True
  OfCourse a -> True
  Tens a b -> True
  Plus a b -> True
  _ -> False

isNegative = not . isPositive

isSync :: LinType -> Bool
isSync t = case t of
  Bottom -> True
  Par a b -> True
  WhyNot a -> True
  Top -> True
  With a b -> True
  _ -> False

-- NOTE: isAsync != not . isSync
isAsync :: LinType -> Bool
isAsync t = case t of
  One -> True
  Tens a b -> True
  OfCourse a -> True
  Zero -> True
  Plus a b -> True
  _ -> False

isMultiplicative :: LinType -> Bool
isMultiplicative t = case t of
  Bottom -> True
  One -> True
  Par a b -> True
  Tens a b -> True
  WhyNot a -> True
  _ -> False

isAdditive = not . isMultiplicative
