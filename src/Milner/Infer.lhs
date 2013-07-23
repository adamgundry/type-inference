%if False

> {-# LANGUAGE FlexibleContexts #-}

> module Milner.Infer where

> import Control.Applicative ((<$>))
> import Control.Monad.State (modify)

> import Common.BwdFwd (Bwd(..))
> import Common.Names (Name, subst, unbind, Alpha, Subst, Fresh, Bind, bind, o)

> import Milner.Type
> import Milner.Unify

%endif

Building on the implementation of unification in the previous section,
I now implement the type inference algorithm described in
Section~\longref{sec:milner:type-inference}.


The |metaBind| and |metaUnbind| functions extend the |bind| and
|unbind| functions provided by the Binders Unbound library, so that
binding a metavariable converts it into a variable, and vice versa.

> metaBind ::  (Alpha t, Subst Type t) =>
>                  Name Type -> t -> Bind (Name Type) t
> metaBind alpha = bind alpha `o` subst alpha (V alpha)
>
> metaUnbind ::  (Alpha t, Subst Type t, Fresh m) =>
>                    Bind (Name Type) t -> m (Name Type, t)
> metaUnbind b = do  (a, t) <- unbind b
>                    return (a, subst a (M a) t)


Specialisation of type schemes is implemented by the |specialise|
function, which unpacks a scheme with fresh metavariables for the
bound variables.

> specialise :: Scheme -> Contextual Type
> specialise (T tau)  = return tau
> specialise (All b)  = do  (beta, sigma) <- metaUnbind b
>                           modify (:< E beta HOLE)
>                           specialise sigma


Generalisation turns a type into a scheme by \scare{skimming} entries
off the top of the metacontext.  The |generaliseOver| control operator
runs a |Contextual| computation in a new locality (extending the
context by |Mark|), then generalises the resulting type until it finds
the |Mark| again.  This depends on the |>=>| function which
generalises a suffix of metavariables over a type to produce a scheme.

\clearpage

> generaliseOver ::  Contextual Type -> Contextual Scheme
> generaliseOver x = do  modify (:< Mark)
>                        tau <- x
>                        _Xi <- skimContext []
>                        return (_Xi >=> tau)
>   where
>     skimContext :: Suffix -> Contextual Suffix
>     skimContext _Xi = popL >>= \ e -> case e of
>         E alpha d  -> skimContext ((alpha, d) : _Xi)
>         Mark       -> return _Xi
>
> (>=>) :: Suffix -> Type -> Scheme
> []                              >=> tau = T tau
> ((alpha, HOLE)          : _Xi)  >=> tau = All (metaBind alpha (_Xi >=> tau))
> ((alpha, DEFN upsilon)  : _Xi)  >=> tau = subst alpha upsilon (_Xi >=> tau)




Finally, the |infer| function implements the type inference algorithm.
It proceeds structurally through the term, following the rules in
Figure~\longref{fig:milner:infer-rules} and using the monadic
operations defined earlier.

> infer :: Tm -> Contextual Type
>
> infer (X x)      = find x >>= specialise
>
> infer (Lam b)    = do  (x, t)   <- unbind b
>                        alpha    <- M <$> freshMeta "alpha"
>                        upsilon  <- inScope x (T alpha) $ infer t
>                        return (alpha `Arr` upsilon)
>
> infer (App f s)  = do  chi      <- infer f
>                        upsilon  <- infer s
>                        beta     <- M <$> freshMeta "beta"
>                        unify chi (upsilon `Arr` beta)
>                        return beta
>
> infer (Let s b)  = do  sigma   <- generaliseOver (infer s)
>                        (x, t)  <- unbind b
>                        inScope x sigma $ infer t
