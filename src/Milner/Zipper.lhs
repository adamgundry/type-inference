%if False

> module Milner.Zipper where

> import Control.Applicative
> import Control.Monad.Error (throwError)
> import Control.Monad.State hiding ((>=>))

> import Common.Names
> import Common.BwdFwd hiding ((<><))

> import Milner.Type hiding (find)
> import Milner.Unify
> import Milner.Infer hiding (specialise)

%endif

In this section, I implement the zipper-based elaboration algorithm
described in Section~\longref{sec:milner:zipper}.  This transforms
source language terms |Tm| (defined in
Section~\ref{sec:milner:apx:type}) into \SystemF\ terms |FTm|,
represented thus:

< data FTm  =  VarF (Name FTm) |  AppTm FTm FTm |  AppTy FTm Type
<           |  LamTm Scheme (Bind (Name FTm) FTm)
<           |  LamTy (Bind (Name Type) FTm)

As described in the text, context entries now consist of metavariables
and layers:

< data TermLayer  =  AppLeft () Tm
<                 |  AppRight (FTm, Type) ()
<                 |  LamBody (Name Tm, Type) ()
<                 |  LetBinding () (Bind (Name Tm) Tm)
<                 |  LetBody (Name Tm) (FTm, Scheme) ()
<
< data Entry      =  E (Name Type) (Decl Type)  |  Layer TermLayer


%if False

> lamTmF :: Name Tm -> Type -> FTm -> FTm
> lamTmF x tau t = LamTm (T tau) (bind x t)

> lamTmF' :: Name Tm -> Scheme -> FTm -> FTm
> lamTmF' x sigma t = LamTm sigma (bind x t)


> _Lams :: Suffix -> FTm -> FTm
> _Lams _Xi t = foldr f t _Xi
>   where 
>     f (alpha, HOLE)      t = LamTy (metaBind alpha t)
>     f (alpha, DEFN tau)  t = subst alpha tau t

%endif


Most functions from the previous sections, including the unification
algorithm, remain unchanged.  The |find| function, which looks up a
term variable in the context and returns its type scheme, is easily
adapted to the new structure:

> find :: Name Tm -> Contextual Scheme
> find x = get >>= help
>   where
>     help :: Context -> Contextual Scheme
>     help B0 = throwError $ "Out of scope: " ++ show x
>     help (mcx :< Layer (LamBody (y, tau) ()))      | x == y  = return (T tau)
>     help (mcx :< Layer (LetBody y (_, sigma) ()))  | x == y  = return sigma
>     help (mcx :< _)                                          = help mcx

The |specialise| function takes an elaborated term and its scheme, and
applies the term to fresh metavariables to produce a witness of the
specialised type.

> specialise :: FTm -> Scheme -> Contextual (FTm, Type)
> specialise t (T tau)  = return (t, tau)
> specialise t (All b)  = do  (beta, sigma) <- metaUnbind b
>                             modify (:< E beta HOLE)
>                             specialise (t `AppTy` M beta) sigma



Now elaboration can be implemented as a tail-recursive function
|elab|.  To elaborate a variable, it looks up the type scheme and
instantiates it with fresh metavariables, then calls the |next|
function to navigate the zipper structure and find the next
elaboration problem.  For $\lambda$-abstractions, applications and
let-bindings, it extends the zipper and elaborates the appropriate
subterm.

> elab :: Tm -> Contextual (FTm, Type)
> elab (X x)        = do  sigma   <- find x
>                         next [] =<< specialise (VarF x) sigma
> elab (Lam b)      = do  (x, t)  <- unbind b
>                         alpha   <- freshMeta "alpha"
>                         modify (:< Layer (LamBody (x, M alpha) ())) >> elab t
> elab (f `App` a)  = modify (:< Layer (AppLeft () a)) >> elab f
> elab (Let s b)    = modify (:< Layer (LetBinding () b)) >> elab s



The |next| function is called with the term at the current location
and its type.  It navigates through the zipper structure to find the
next elaboration problem, updating the current term and type as it
does so.  The accumulator |_Xi| collects metavariables that
encountered along the way.  These are reinserted into the context once
the new problem is found, or if a |LetBinding| layer is encountered,
|_Xi| contains exactly the metavariables to generalise over.

> next :: Suffix -> (FTm, Type) -> Contextual (FTm, Type)
> next _Xi (t, tau) = optional popL >>= \ e -> case e of
>       Just (Layer (AppLeft () a))             -> do  modify (<>< _Xi)
>                                                      modify (:< Layer (AppRight (t, tau) ()))
>                                                      elab a
>       Just (Layer (AppRight (f, sigma) ()))   -> do  modify (<>< _Xi)
>                                                      beta <- M <$> freshMeta "beta"
>                                                      unify sigma (tau `Arr` beta)
>                                                      next [] (f `AppTm` t, beta)
>       Just (Layer (LamBody (x, upsilon) ()))  -> next _Xi (lamTmF x upsilon t, upsilon `Arr` tau)
>       Just (Layer (LetBinding () b))          -> do  (x, w) <- unbind b
>                                                      let (t', sigma) = (_Lams _Xi t, _Xi >=> tau)
>                                                      modify (:< Layer (LetBody x (t', sigma) ()))
>                                                      elab w
>       Just (Layer (LetBody x (s, sigma) ()))  -> next _Xi (lamTmF' x sigma t `AppTm` s, tau)
>       Just (E alpha d)                        -> next ((alpha, d) : _Xi) (t, tau)
>       Nothing                                 -> modify (<>< _Xi) >> return (t, tau)
