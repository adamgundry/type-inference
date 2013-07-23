%if False

> {-# LANGUAGE GADTs #-}

> module Units.GroupUnify (unifyUnit) where

> import Control.Monad.Error (throwError)
> import Control.Monad.State (modify)

> import Common.BwdFwd
> import Common.Names
> import Units.Group
> import Units.Type

%endif

I now implement the abelian group unification algorithm given in
Section~\longref{sec:units:group-unification}.  This is based around
an algorithm for unifying single expressions with the group identity.
A pair of expressions can then be unified thus:

> unifyUnit :: Type -> Type -> Contextual ()
> unifyUnit d e = unifyId Nothing $ typeToUnit d /~ typeToUnit e

To unify a unit expression |e| with the identity, first check if it is
already the identity (and win) or is another constant (and lose).
Otherwise, search the context for group variables that occur in |e|.
When one is found, either substitute it into the expression (if it has
a definition) or examine the coefficients to determine how to proceed.
If its coefficient |n| divides all the others, it can be defined to
solve the equation.  Otherwise, either reduce the coefficients modulo
|n| or just collect the variable and move it back in the context.

> unifyId :: Maybe (Name Type) -> Unit -> Contextual ()
> unifyId _Psi e
>   | isIdentity e  = return ()
>   | isConstant e  = throwError "Unit mismatch!"
>   | otherwise     = onTopUN $ \ alpha d ->
>       let n = alpha `powerIn` e in
>       case d of
>             _ | n == 0                -> do  unifyId _Psi e
>                                              restore
>             DEFN x                    -> do  modify (ins _Psi)
>                                              let e' = substUnit alpha  (typeToUnit x) e
>                                              unifyId Nothing e'
>                                              restore
>             HOLE
>              | n `dividesPowers` e    -> do  modify (ins _Psi)
>                                              let p = pivot alpha e
>                                              replace [(alpha, UN, DEFN (unitToType p))]
>              | (alpha, n) `notMax` e  -> do  modify (ins _Psi)
>                                              beta <- fresh (s2n "beta")
>                                              let p = pivot alpha e *~ metaUnit beta
>                                              unifyId (Just beta) $ substUnit alpha p e
>                                              replace [(alpha, UN, DEFN (unitToType p))]
>              | numVariables e > 1     -> do  unifyId (Just alpha) e
>                                              replace []
>              | otherwise              -> throwError "No way!"

> ins :: Maybe (Name Type) -> Context -> Context
> ins Nothing       mcx = mcx
> ins (Just alpha)  mcx = mcx :< E alpha UN HOLE
