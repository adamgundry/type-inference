%if False

> module Units.Unify (unify) where

> import Prelude hiding (mapM_, elem)
> import Control.Monad.Error (throwError)
> import Control.Monad.State (modify)
> import Data.Foldable (mapM_, elem)

> import Common.BwdFwd hiding ((<><))
> import Common.Names
> import Units.Type
> import Units.GroupUnify

%endif

Here I implement the type unification algorithm given in
Section~\longref{sec:units:type-unification}.  The implementation of
|unify| for types with units of measure is very similar to the version
in Section~\ref{sec:milner:apx:unify}, except that it calls
|unifyUnit| to unify the unit annotations of |Float| types, and uses
|startSolve| in place of |solve| as discussed below.

> unify :: Type -> Type -> Contextual ()
> unify (tau0 `Arr` tau1)  (upsilon0 `Arr` upsilon1)  = unify tau0 upsilon0 >> unify tau1 upsilon1
> unify (Float d)          (Float e)                  = unifyUnit d e
> unify (M alpha)          (M beta)                   = onTopTY $ \ gamma d -> case
>           (gamma == alpha,  gamma == beta,  d  ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          HOLE      )  ->  replace [(alpha, Star, DEFN (M beta))]
>           (False,           True,           HOLE      )  ->  replace [(beta, Star, DEFN (M alpha))]
>           (True,            False,          DEFN tau  )  ->  unify (M beta)   tau       >> restore   
>           (False,           True,           DEFN tau  )  ->  unify (M alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (M alpha)  (M beta)  >> restore
> unify (M alpha)        tau                               =   startSolve alpha tau
> unify tau              (M alpha)                         =   startSolve alpha tau    
> unify _                _                                 =   throwError "Rigid-rigid mismatch"

When starting to solve a flex-rigid constraint, one has to be careful
not to accidentally lose polymorphism, as explained in
Subsection~\longref{subsec:units:recover-generality}.  The syntactic
occurs check performed by |solve| is not quite right, because the
richer equational theory of abelian groups may exhibit apparent
dependency when there is in fact none.  Thus |startSolve| replaces
units in the rigid type with fresh variables, solves the flex-rigid
constraint first, then unifies the units.

> startSolve :: Name Type -> Type -> Contextual ()
> startSolve alpha tau = do  (rho, xs) <- rigidHull tau
>                            solve alpha (constraintsToSuffix xs) rho
>                            solveConstraints xs

The |rigidHull| operation computes the \scare{hull} of a type of kind
|Star|, replacing unit subexpressions with fresh variables.  Along
with the hull, it returns the constraints between the fresh variables
and the units they replaced.

\clearpage

> rigidHull :: Type -> Contextual (Type, [(Name Type, Type)])
> rigidHull (M a)                = return (M a, [])
> rigidHull (V a)                = return (V a, [])
> rigidHull (tau `Arr` upsilon)  = do  (tau',      xs  )  <- rigidHull tau
>                                      (upsilon',  ys  )  <- rigidHull upsilon
>                                      return (tau' `Arr` upsilon', xs <.> ys)
> rigidHull (Float d)            = do  beta <- fresh (s2n "beta")
>                                      return (Float (M beta), [(beta, d)])

A list of constraints can be turned into the appropriate context
suffix by discarding the types and adding unit declarations for the
metavariables:

> constraintsToSuffix :: [(Name Type, Type)] -> Suffix
> constraintsToSuffix = map (\ (alpha, _) -> (alpha, UN, HOLE))

Or they can be solved by repeatedly invoking |unifyUnit|:

> solveConstraints :: [(Name Type, Type)] -> Contextual ()
> solveConstraints = mapM_ (uncurry $ unifyUnit `o` M)

The implementation of |solve| is almost identical to the version in
Appendix~\ref{apx:milner}.

> solve :: Name Type -> Suffix -> Type -> Contextual ()
> solve alpha _Xi tau = onTopTY $
>   \ gamma d -> case
>             (gamma == alpha,  gamma `elem` fmvs tau,         d             ) of
>             (_,               _,                             DEFN upsilon  )  ->  modify (<>< _Xi)
>                                                                               >>  unify (subst gamma upsilon (M alpha)) (subst gamma upsilon tau)
>                                                                               >>  restore
>             (True,            True,                          HOLE          )  ->  throwError "Occurrence detected!"
>             (True,            False,                         HOLE          )  ->  replace $ _Xi <.> [(alpha, Star, DEFN tau)]
>             (False,           True,                          HOLE          )  ->  solve alpha ((gamma, Star, HOLE) : _Xi) tau
>                                                                               >>  replace []
>             (False,           False,                         HOLE          )  ->  solve alpha _Xi tau
>                                                                               >>  restore