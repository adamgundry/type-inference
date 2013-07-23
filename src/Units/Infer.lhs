> {-# LANGUAGE FlexibleContexts #-}

> module Units.Infer (infer, metaBind) where

> import Control.Applicative
> import Control.Monad.State (modify)

> import Common.BwdFwd
> import Common.Names
> import Units.Type
> import Units.Unify

> metaUnbind :: (Alpha t, Subst Type t, Fresh m) =>
>                 Bind (Name Type) t -> m (Name Type, t)
> metaUnbind b = do
>     (a, t) <- unbind b
>     return (a, subst a (M a) t)

> specialise :: Scheme -> Contextual Type
> specialise (T tau) = return tau
> specialise (All ki b) = do
>     (beta, tau) <- metaUnbind b
>     modify (:< E beta ki HOLE)
>     specialise tau


> metaBind :: (Alpha t, Subst Type t) => Name Type -> t -> Bind (Name Type) t
> metaBind alpha = bind alpha . subst alpha (V alpha)

> (>=>) :: Suffix -> Type -> Scheme
> []                                  >=> tau = T tau
> ((alpha, ki, HOLE)          : _Xi)  >=> tau = All ki (metaBind alpha (_Xi >=> tau))
> ((alpha, _, DEFN upsilon)  : _Xi)   >=> tau = subst alpha upsilon (_Xi >=> tau)

> generaliseOver ::  Contextual Type -> Contextual Scheme
> generaliseOver mt = do
>     modify (:< Mark)
>     tau <- mt
>     _Xi <- skimContext []
>     return (_Xi >=> tau)
>   where
>     skimContext :: Suffix -> Contextual Suffix
>     skimContext _Xi = popL >>= \ e -> case e of
>         Mark          -> return _Xi
>         E alpha ki d  -> skimContext ((alpha, ki, d) : _Xi)



> infer :: Tm -> Contextual Type
>
> infer (X x) = find x >>= specialise
>
> infer (Lam b) = do
>     alpha    <- M <$> freshMeta "alpha" Star
>     (x, w)   <- unbind b
>     upsilon  <- inScope x (T alpha) $ infer w
>     return (alpha `Arr` upsilon)
>
> infer (App f s) = do
>     chi      <- infer f
>     upsilon  <- infer s
>     beta     <- M <$> freshMeta "beta" Star
>     unify chi (upsilon `Arr` beta)
>     return beta
>
> infer (Let s b) = do
>     sigma   <- generaliseOver (infer s)
>     (x, w)  <- unbind b
>     inScope x sigma $ infer w
