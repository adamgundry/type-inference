%if False

> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              TemplateHaskell, ScopedTypeVariables, FlexibleContexts,
>              FlexibleInstances, MultiParamTypeClasses,
>              UndecidableInstances, StandaloneDeriving #-}

> module Units.Group where

> import Prelude hiding (null)

> import Control.Arrow

> import Data.SignedMultiset as SM (multiply, multiplicity, shadow, additiveUnion, fromList, null, toList, size)
> import Data.SignedMultiset (SignedMultiset)

> import Common.Names hiding (fromList)
> import Common.PrettyPrint
> import {-# SOURCE #-} Units.Type

%endif

I begin by introducting the semantic representation of units of
measure, along with operations on them, as described in
Section~\longref{sec:units:group-unification}.  A unit of measure is
represented as a |Unit| value with signed multisets of metavariables
and constants.  For simplicity, the type of base units is fixed.

> data Unit = Unit (SignedMultiset (Name Type)) (SignedMultiset BaseUnit)
> data BaseUnit  = METRE | SEC | KG

%if False

> deriving instance Eq Unit
> deriving instance Show Unit
> deriving instance Eq BaseUnit
> deriving instance Ord BaseUnit
> deriving instance Show BaseUnit

> instance Alpha BaseUnit
> instance Subst t BaseUnit

> instance Pretty BaseUnit where
>     pretty METRE  = return $ text "m"
>     pretty SEC    = return $ text "s"
>     pretty KG     = return $ text "kg"

%endif


The |mkUnit| function creates a unit from lists of powers of
metavariables and base units.  As a special case, |metaUnit| creates a
unit from a single metavariable.

> mkUnit :: [(Name Type, Int)] -> [(BaseUnit, Int)] -> Unit
> mkUnit vs bs = Unit (fromList vs) (fromList bs)
>
> metaUnit :: Name Type -> Unit
> metaUnit a = mkUnit [(a, 1)] []


Utility functions determine if a unit is the identity or constant, the
number of variables it contains, and the power of a metavariable in
it.

> isIdentity :: Unit -> Bool
> isIdentity (Unit vs bs)  = null vs && null bs
>
> isConstant :: Unit -> Bool
> isConstant (Unit vs bs)  = null vs
>
> numVariables :: Unit -> Int
> numVariables (Unit vs _) = size vs
>
> powerIn :: Name Type -> Unit -> Int
> alpha `powerIn` Unit vs _ = multiplicity alpha vs


The |dividesPowers| function determines if an integer divides all the
powers of metavariables and base units.

> dividesPowers :: Int -> Unit -> Bool
> n `dividesPowers` (Unit vs bs) = dividesAll vs && dividesAll bs
>   where
>     dividesAll :: SignedMultiset a -> Bool
>     dividesAll = all ((0 ==) . (`mod` n) . snd) . toList


The |notMax| function determines if the power of a variable is
less than the power of at least one other variable.

> notMax :: (Name Type, Int) -> Unit -> Bool
> notMax (alpha, n) (Unit vs _) = any bigger (toList vs)
>   where bigger (beta, m) = alpha /= beta && abs n <= abs m


The |(*~)|, |(/~)| and |(^~)| operators respectively multiply and
divide units, and raise a unit to a constant power.

> (*~) :: Unit -> Unit -> Unit
> Unit vs bs *~ Unit vs' bs' = Unit (additiveUnion vs vs') (additiveUnion bs bs')
>
> (/~) :: Unit -> Unit -> Unit
> d /~ e = d *~ invert e
>
> (^~) :: Unit -> Int -> Unit
> Unit vs bs ^~ k = Unit (multiply k vs) (multiply k bs)
>
> invert :: Unit -> Unit
> invert (Unit vs bs) = Unit (shadow vs) (shadow bs)


The |pivot| function removes the given metavariable from the unit,
inverts it and takes the quotient of its powers by the power of the
removed variable.

> pivot :: Name Type -> Unit -> Unit
> pivot alpha e = invert $ quotient $ e /~ (metaUnit alpha ^~ n)
>   where
>     n = alpha `powerIn` e
>
>     quotient (Unit vs bs) = mkUnit  (map (second (`quot` n)) (toList vs))
>                                     (map (second (`quot` n)) (toList bs))


The |substUnit| function substitutes a unit for a metavariable in
another unit.

> substUnit :: Name Type -> Unit -> Unit -> Unit
> substUnit alpha d e = ((d /~ metaUnit alpha) ^~ (alpha `powerIn` e)) *~ e


%if False

> $(derive[''BaseUnit])

%endif
