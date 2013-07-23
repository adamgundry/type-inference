> module Common.Names (module Unbound.LocallyNameless,
>                      unsafeUnbind, GenBind(..), unions, fromList,
>                      vars, notSubsetOf, o) where

> import Data.Foldable (Foldable, toList)

> import Data.Set (Set, isSubsetOf)
> import qualified Data.Set as Set (empty, singleton, union, map)

> import Unbound.LocallyNameless hiding (empty, fv, Float, rUnit, toList)
> import Unbound.LocallyNameless.Ops (unsafeUnbind)
> import Unbound.LocallyNameless.Types (GenBind(..))
> import Unbound.Util (unions, fromList)

> vars :: (Ord a, Collection c, Foldable f) => f (a, b) -> c a
> vars = fromList . map fst . toList

> notSubsetOf :: Ord a => Set a -> Set a -> Bool
> a `notSubsetOf` b = not (a `isSubsetOf` b) 


This doesn't really belong here, but is useful for having a pretty
composition operator:

> o :: (b -> c) -> (a -> b) -> (a -> c)
> (g `o` f) x = g (f x)

> infixr 9 `o`