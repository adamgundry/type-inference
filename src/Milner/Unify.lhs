%if False

> module Milner.Unify where

> import Prelude hiding (elem)

> import Control.Monad.Error (throwError)
> import Control.Monad.State (modify)

> import Data.Foldable (elem)

> import Common.BwdFwd (Bwd(..), (<.>))
> import Common.Names (Name, subst, o)

> import Milner.Type

%endif

Having set up the necessary data structures, I will now implement the
unification algorithm of Section~\longref{sec:milner:unification}.

The |onTop| operator delivers the typical access pattern for contexts,
locally bringing the top variable declaration into focus and working
over the remainder.  The local operation |f|, passed as an argument,
may |restore| the previous entry, or it may return a context extension
(containing at least as much information as the entry that has been
removed) with which to |replace| it.

> data Extension = Restore | Replace Suffix

> onTop ::  (Name Type -> Decl Type -> Contextual Extension)
>             -> Contextual ()
> onTop f = popL >>= \ e -> case e of
>         E alpha d -> f alpha d >>= \ m -> case m of
>             Replace _Xi  -> modify (<>< _Xi)
>             Restore      -> modify (:< e)
>         _ -> onTop f >> modify (:< e)

> restore :: Contextual Extension
> restore = return Restore
>
> replace :: Suffix -> Contextual Extension
> replace = return `o` Replace



The |unify| function actually implements unification.  This proceeds
structurally over types.  If it reaches a pair of metavariables, it
examines the context, using |onTop| to pick out a declaration to
consider.  Depending on the metavariables, it then either succeeds,
restoring the old entry or replacing it with a new one, or continues
with an updated constraint.

> unify :: Type -> Type -> Contextual ()
> unify (tau0 `Arr` tau1)  (upsilon0 `Arr` upsilon1)  = unify tau0 upsilon0 >> unify tau1 upsilon1
> unify (M alpha)        (M beta)                 = onTop $ \ gamma d -> case
>           (gamma == alpha,  gamma == beta,  d         ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          HOLE      )  ->  replace [(alpha, DEFN (M beta))]
>           (False,           True,           HOLE      )  ->  replace [(beta, DEFN (M alpha))]  
>           (True,            False,          DEFN tau  )  ->  unify (M beta)   tau       >> restore   
>           (False,           True,           DEFN tau  )  ->  unify (M alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (M alpha)  (M beta)  >> restore   
> unify (M alpha)        tau                               =   solve alpha [] tau
> unify tau              (M alpha)                         =   solve alpha [] tau    
> unify _                _                                 = throwError "Rigid-rigid mismatch"

The |solve| function is called to unify a metavariable with a rigid
type (one that is not a metavariable).  It works similarly to the way
|unify| works on pairs of metavariables, but must also accumulate a
list of the type's dependencies and push them left through the
context.  It performs the occurs check and throws an
exception if an illegal occurrence (leading to an infinite type) is
detected.

> solve :: Name Type -> Suffix -> Type -> Contextual ()
> solve alpha _Xi tau = onTop $
>   \ gamma d -> case
>     (gamma == alpha,  gamma `elem` fmvs tau,         d             ) of
>     (_,               _,                             DEFN upsilon  )  ->  modify (<>< _Xi)
>                                                                       >>  unify (subst gamma upsilon (M alpha)) (subst gamma upsilon tau)
>                                                                       >>  restore
>     (True,            True,                          HOLE          )  ->  throwError "Occurrence detected!"
>     (True,            False,                         HOLE          )  ->  replace (_Xi <.> [(alpha, DEFN tau)])
>     (False,           True,                          HOLE          )  ->  solve alpha ((gamma, HOLE) : _Xi) tau
>                                                                       >>  replace []
>     (False,           False,                         HOLE          )  ->  solve alpha _Xi tau
>                                                                       >>  restore
