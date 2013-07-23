> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FlexibleInstances, TypeOperators, ScopedTypeVariables, FlexibleContexts, UndecidableInstances #-}

> module Common.BwdFwd where

> import Data.Foldable
> import Data.Monoid
> import Data.Traversable

> import Generics.RepLib
> import Unbound.LocallyNameless

> data Bwd a = B0 | Bwd a :< a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> infixl 5 :<

> instance Monoid (Bwd a) where
>     mempty = B0
>     xs `mappend` B0         = xs
>     xs `mappend` (ys :< y)  = (xs `mappend` ys) :< y

> (<><) :: Bwd a -> [a] -> Bwd a
> xs <>< []       = xs 
> xs <>< (y : ys) = (xs :< y) <>< ys

> infixl 4 <><

> (<>>) :: Bwd a -> [a] -> [a]
> B0         <>> ys = ys
> (xs :< x)  <>> ys = xs <>> (x : ys)

> fwd :: Bwd a -> [a]
> fwd = (<>> [])

> bwd :: [a] -> Bwd a
> bwd = (B0 <><)

> lookupBwd :: Eq a => a -> Bwd (a, b) -> Maybe b
> lookupBwd x xs = lookup x (fwd xs)

> lengthBwd :: Bwd a -> Int
> lengthBwd B0 = 0
> lengthBwd (xs :< _) = succ (lengthBwd xs)

> (<.>) :: Monoid m => m -> m -> m
> (<.>) = mappend




> instance Alpha a => Alpha (Bwd a)

> instance Subst t a => Subst t (Bwd a)

RepLib won't automatically derive instances for data types with infix
data constructors, so here are manually created instances for Bwd
(based on the instances for list in Generics.RepLib.R).

> rBwd :: forall a. Rep a => R (Bwd a)
> rBwd = Data (DT "Bwd" ((rep :: R a) :+: MNil))
>             [ Con rB0Emb MNil, Con rBConsEmb (rBwd :+: (rep :: R a) :+: MNil) ]

> rB0Emb :: Emb Nil (Bwd a)
> rB0Emb = Emb {   to   = \Nil -> B0,
>                   from  = \x -> case x of
>                            (_:<_) -> Nothing
>                            B0    -> Just Nil,
>                   labels = Nothing,
>                   name = "B0",
> 		  fixity = Nonfix
>                  }
> 
> rBConsEmb :: Emb (Bwd a :*: a :*: Nil) (Bwd a)
> rBConsEmb =
>    Emb {
>             to   = (\ (xs :*: x :*: Nil) -> (xs :< x)),
>             from  = \x -> case x of
>                     (ys :< y) -> Just (ys :*: y :*: Nil)
>                     B0        -> Nothing,
>             labels = Nothing,
>             name = ":<",
> 	    fixity = Nonfix -- ???
>           }

> instance Rep a => Rep (Bwd a) where
>   rep = rBwd


> rBwd1 :: forall a ctx.
>   Rep a => ctx (Bwd a) -> ctx a -> R1 ctx (Bwd a)
> rBwd1 ca cl = Data1 (DT "Bwd" ((rep :: R a) :+: MNil))
>                   [ rBCons1, rB01 ] where
>    rB01  :: Con ctx (Bwd a)
>    rB01  = Con rB0Emb MNil
> 
>    rBCons1 :: Con ctx (Bwd a)
>    rBCons1 = Con rBConsEmb (ca :+: cl :+: MNil)
> 
> instance (Rep a, Sat (ctx a), Sat (ctx (Bwd a))) => Rep1 ctx (Bwd a) where
>   rep1 = rBwd1 dict dict