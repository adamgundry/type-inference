%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
>       FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
>       UndecidableInstances, GeneralizedNewtypeDeriving,
>       TypeSynonymInstances, ScopedTypeVariables, TupleSections #-}

> module PatternUnify.Check where

> import Prelude hiding (any)

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.Reader
> import Data.Foldable (any, foldMap)
> import Data.Traversable (traverse)

> import Common.BwdFwd
> import Common.Names
> import Common.PrettyPrint
> import PatternUnify.Tm
> import PatternUnify.Context

%endif

Here I give a typechecker and definitional equality test for the type
theory defined in Subsection~\longref{subsec:miller:typing-rules}.
With the |Contextual| monad operations, I define a bidirectional
typechecker, based on a typed definitional equality test between
$\beta\delta$-normal forms that produces an $\eta$-long standard form.
The |equalise _T s t| function implements the judgment
$[[MCx | Gam |- s =[u]= t : T]]$, defined in
Figure~\longref{fig:miller:equality}, where $[[u]]$ is the result.

> equalise :: Type -> Tm -> Tm -> Contextual Tm
> equalise TYPE  SET   SET   = return SET
> equalise TYPE  _S    _T    = equalise SET _S _T
> equalise SET   BOOL  BOOL  = return BOOL
> equalise BOOL  TT    TT    = return TT
> equalise BOOL  FF    FF    = return FF
> equalise SET   (Pi _A _B) (Pi _S _T) = do
>     _U <- equalise SET _A _S
>     Pi _U <$>   bindsInScope _U _B _T
>                    (\ x _B' _T' -> equalise SET _B' _T')
> equalise (Pi _U _V) f g =
>     L <$>  bindInScope _U _V
>                (\ x _V' -> equalise _V' (f $$ var x) (g $$ var x))
> equalise SET (Sig _A _B) (Sig _S _T) = do
>     _U <- equalise SET _A _S
>     Sig _U <$>  bindsInScope _U _B _T
>                    (\ x _B' _T' -> equalise SET _B' _T')
> equalise (Sig _U _V) s t = do
>     u0 <- equalise _U (hd s) (hd t)
>     u1 <- equalise (inst _V u0) (tl s) (tl t)
>     return (PAIR u0 u1)
> equalise _U (N h e) (N h' e') = do
>     (h'', e'', _V) <- equaliseN h e h' e'
>     equalise TYPE _U _V
>     return (N h'' e'')

%if False

> equalise SET  NAT     NAT     = return NAT
> equalise NAT  ZE      ZE      = return ZE
> equalise NAT  (SU m)  (SU n)  = SU <$> equalise NAT m n

> equalise _U s t = fail $ "Type " ++ pp _U ++ " does not make "
>                          ++ pp s ++ " equal to " ++ pp t

%endif


Similarly, the |equaliseN h e h' e'| function implements the equality judgment
$[[MCx | Gam |- h . E ==[h'' . E''] h' . E' :=> T]]$, defined in
Figure~\longref{fig:miller:equality-neu}, where $[[h'']]$, $[[E'']]$
and $[[T]]$ are the results.

\clearpage

> equaliseN ::  Head -> Bwd Elim -> Head -> Bwd Elim ->
>                   Contextual (Head, Bwd Elim, Type)
> equaliseN h B0 h' B0 | h == h'          = (h, B0,) <$> infer h
> equaliseN h (e :< A s)  h' (e' :< A t)  = do
>     (h'', e'', Pi _U _V)  <- equaliseN h e h' e'
>     u                     <- equalise _U s t
>     return (h'', e'' :< A u, inst _V u)
> equaliseN h (e :< Hd)   h' (e' :< Hd)   = do
>     (h'', e'', Sig _U _V) <- equaliseN h e h' e'
>     return (h'', e'' :< Hd, _U)
> equaliseN h (e :< Tl)   h' (e' :< Tl)   = do
>     (h'', e'', Sig _U _V) <- equaliseN h e h' e'
>     return (h'', e'' :< Tl, inst _V (N h'' (e'' :< Hd)))
> equaliseN h (e :< If _T u v) h' (e' :< If _T' u' v') = do
>     (h'', e'', BOOL)  <- equaliseN h e h' e'
>     _U''              <- bindsInScope BOOL _T _T' (\ x _U _U' -> equalise TYPE _U _U')
>     u''               <- equalise (inst _U'' TT) u u'
>     v''               <- equalise (inst _U'' FF) v v'
>     return (h'', e'' :< If _U'' u'' v'', inst _U'' (N h'' e''))

%if False

> equaliseN h e h' e' = fail $ "Neutral terms " ++ pp h ++ " . " ++ pp e
>                               ++ " and " ++ pp h' ++ " . " ++ pp e'
>                               ++ " not equal!"

%endif


The |infer| function looks up the type of a head, using |lookupVar| or
|lookupMeta| from the previous section as appropriate.

> infer :: Head -> Contextual Type
> infer (V x w)  = lookupVar x w
> infer (M x)    = lookupMeta x

The |bindInScope| and |bindsInScope| helper operations introduce a
binding or two and call the continuation with a variable of the given
type in scope.

> bindInScope ::  Type -> Bind Nom Tm ->
>                   (Nom -> Tm -> Contextual Tm) ->
>                   Contextual (Bind Nom Tm)
> bindInScope _T b f = do  (x, b') <- unbind b
>                          bind x <$> inScope x (P _T) (f x b')
>
> bindsInScope ::  Type -> Bind Nom Tm -> Bind Nom Tm -> 
>                    (Nom -> Tm -> Tm -> Contextual Tm) ->
>                    Contextual (Bind Nom Tm)
> bindsInScope _T a b f = do  Just (x, a', _, b') <- unbind2 a b
>                             bind x <$> inScope x (P _T) (f x a' b')



Equality checking can return a Boolean instead of throwing an error
when the terms are not equal.  Since typing is the diagonal of
equality, it is easy to define a typechecking function as well.

> equal :: Type -> Tm -> Tm -> Contextual Bool
> equal _T s t =  (equalise _T s t >> return True) <|> (return False)
>
> typecheck :: Type -> Tm -> Contextual Bool
> typecheck _T t = equal _T t t


Finally, a convenience function that tests if a heterogeneous equation
is reflexive, by checking that the types are equal and the terms are
equal.

> isReflexive :: Equation -> Contextual Bool
> isReflexive (EQN _S s _T t) =  optional (equalise TYPE _S _T) >>=
>                                    maybe (return False) (\ _U -> equal _U s t)


%if False

> bindInScope_ ::  Alpha t => Param -> Bind Nom t ->
>                           (Nom -> t -> Contextual ()) ->
>                           Contextual ()
> bindInScope_ p b f =  do  (x, b') <- unbind b
>                           inScope x p (f x b')

> check :: Type -> Tm -> Contextual ()
> check _T t = equalise _T t t >> return ()

> checkProb :: Problem -> Contextual ()
> checkProb (Unify (EQN _S s _T t)) = do
>    check TYPE _S  >> check _S s
>    check TYPE _T  >> check _T t
> checkProb (All p b) = do
>     checkParam p
>     bindInScope_ p b (const checkProb)

> checkParam :: Param -> Contextual ()
> checkParam (P _S)         = check TYPE _S
> checkParam (Twins _S _T)  = check TYPE _S >> check TYPE _T


> validate :: Contextual ()
> validate = local (const B0) $ do
>     _Del' <- getR
>     unless (null _Del') $ error "validate: not at far right"
>     _Del <- getL
>     validateCx _Del `catchError` (error . (++ ("\nwhen validating\n" ++ pp (_Del, _Del'))))
>     putL _Del
>   where
>     validateCx :: ContextL -> Contextual ()
>     validateCx B0 = return ()
>     validateCx _Del'@(_Del :< E x _) | x <? _Del = throwError $ "validate: dependency error: " ++ show x ++ " occurs before its declaration"
>     validateCx (_Del :< E _ (_T, HOLE))      = do  putL _Del
>                                                    check TYPE _T
>                                                    validateCx _Del
>     validateCx (_Del :< E _ (_T, DEFN v))  = do  putL _Del
>                                                  check TYPE _T
>                                                  check _T v
>                                                  validateCx _Del
>     validateCx (_Del :< Q Blocked p)       = do  putL _Del
>                                                  checkProb p
>                                                  validateCx _Del
>     validateCx (_Del :< Q Active p)       = throwError $ "validate: found active problem " ++ pp p




> mcxToSubs :: Bwd Entry -> Subs
> mcxToSubs = foldMap f
>   where
>     f (E alpha (_, DEFN t))  = [(alpha, t)]
>     f _                      = []

> anyBlocked :: ContextL -> Bool
> anyBlocked = any isBlocked
>   where
>     isBlocked (Q Blocked _)  = True
>     isBlocked (Q Active p)   = error "active problem left"
>     isBlocked (E _ _)        = False

> checkHolds :: [Problem] -> Contextual ()
> checkHolds ps = do
>     mcx <- getL
>     if anyBlocked mcx
>         then return ()
>         else do
>             theta <- mcxToSubs <$> getL
>             traverse checkHold $ substs theta ps
>             return ()
>   where
>     checkHold (All (P _T) b) = bindInScope_ (P _T) b (const checkHold)
>     checkHold (All (Twins _S _T) b) = do
>         b <- equal TYPE _S _T
>         if b then throwError "checkHolds: equal twins hanging around"
>              else throwError "checkHolds: unequal twins"
>     checkHold (Unify q) = do
>         b <- isReflexive q
>         if b then return ()
>              else throwError $ "checkHolds: not reflexive: " ++ pp q

%endif