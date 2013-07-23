%format >=> = ">=>"

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeSynonymInstances, PatternGuards #-}

> module PatternUnify.Unify where

> import Prelude hiding (elem, notElem, foldr)

> import Control.Applicative ((<$>), (<*>), optional)
> import Control.Monad ((>=>), unless)
> import Control.Monad.Error (throwError, when)
> import Control.Monad.Reader (ask, local)

> import Data.Foldable (Foldable, fold, foldr, elem, notElem, foldMap)
> import Data.Maybe (isJust)
> import Data.Monoid (Any(..), getAny)
> import Data.Set (Set, isSubsetOf, member, notMember)
> import Data.Traversable (Traversable, traverse)

> import Common.BwdFwd 
> import Common.Names
> import PatternUnify.Tm (Can(..), Tm(..), Elim(..), Head(..), Twin(..),
>            Nom, Type, Subs,
>            mapElim, foldMapElim,
>            ($$), (%%), ($*$), inst, 
>            var, meta, lam, lams, lams', _Pi, _Pis, twinL, twinR, hd, tl, 
>            (*%*), fmvs, fvs, fvrigs)
> import PatternUnify.Check (typecheck, equal, isReflexive)
> import PatternUnify.Context (Decl(..), Entry(..), Status(..), Problem(..), Equation(..),
>                 Param(..), Params, Contextual, lookupMeta,
>                 eqnProb, allProb, allTwinsProb,
>                 lookupVar, pushR, pushL, pushLs, inScope, popL, popR, goLeft, sym)

%endif

With the preliminaries out of the way, I can now present the pattern
unification algorithm as specified in
Section~\longref{sec:miller:spec}.  I begin with utilities for working
with metavariables and problems, then give the implementations of
inversion, intersection, pruning, metavariable simplification and
problem simplification.  Finally, I show how the order of constraint
solving is managed.


\subsubsection{Making and filling holes}

A telescope is a list of binding names and their types.  Any type can
be viewed as consisting of a $\Pi$-bound telescope followed by a
non-$\Pi$-type.

> type Telescope = Bwd (Nom, Type)
>
> telescope :: Type -> Contextual (Telescope, Type)
> telescope (Pi _S _T)  = do  (x, _T') <- unbind _T
>                             (_Tel, _U) <- telescope _T' 
>                             return ((B0 :< (x, _S)) <.> _Tel, _U)
> telescope _T          = return (B0, _T)

The |hole| control operator creates a metavariable of the given type
(under a telescope of parameters), and calls the continuation with the
metavariable in scope.  Finally, it moves the cursor back to the left
of the metavariable, so it will be examined again in case further
progress can be made on it.  The continuation must not move the
cursor.

> hole :: Telescope -> Type -> (Tm -> Contextual a) -> Contextual a
> hole _Gam _T f = do  alpha <- fresh (s2n "alpha")
>                      pushL $ E alpha (_Pis _Gam _T, HOLE)
>                      r <- f (meta alpha $*$ _Gam)
>                      goLeft
>                      return r

% >     check TYPE (_Pis _Gam _T) `catchError` error

Once a solution for a metavariable is found, the |define| function
adds a definition to the context.  (The declaration of the
metavariable should already have been removed.)  This also propagates
a substitution that replaces the metavariable with its value.

> define :: Telescope -> Nom -> Type -> Tm -> Contextual ()
> define _Gam alpha _S v = do  pushR $ Left [(alpha, t)]
>                              pushR $ Right $ E alpha (_T, DEFN t)
>   where  _T  = _Pis _Gam _S
>          t   = lams' _Gam v

% >   check _T t `catchError` error


\subsubsection{Postponing problems}

When a problem cannot be solved immediately, it can be postponed by
adding it to the metacontext.  The |postpone| functions wraps a
problem in the current context (as returned by |ask|) and stores it in
the metacontext with the given status.  The |active| function
postpones a problem on which progress can be made, while the |block|
function postpones a problem that cannot make progress until its type
becomes more informative, as discussed in
Subsection~\ref{subsec:miller:impl:ambulando}.

> postpone :: Status -> Problem -> Contextual ()
> postpone s p = pushR `o` Right `o` Q s `o` wrapProb p =<< ask
>   where
>     wrapProb :: Problem -> Params -> Problem
>     wrapProb = foldr (\ (x, e) p -> All e (bind x p))
>
> active, block ::  Problem -> Contextual ()
> active  = postpone Active
> block   = postpone Blocked


\subsubsection{A useful combinator}

The following combinator executes its first argument, and if this
returns |False| then it also executes its second argument.

> (<||) :: Monad m => m Bool -> m () -> m ()
> a <|| b = do  x <- a
>               unless x b

%if False

> infixr 5 <||

%endif


\subsection{Inversion}
\label{subsec:miller:impl:invert}

A flexible unification problem is one where one side is an applied
metavariable and the other is an arbitrary term.  The algorithm moves
left in the context, accumulating a list of metavariables $[[XI]]$
that the term depends on, to construct the necessary
dependency-respecting permutation.  Once the target metavariable is
reached, it can attempt to find a solution by inversion.  This
implements step \eqref{eqn:miller:unify:solve} in
Figure~\longref{fig:miller:solve}, as described in
Subsection~\longref{subsec:miller:spec:invert}.

> flexTerm ::  [Entry] -> Equation -> Contextual ()
> flexTerm _Xi q@(EQNO (N (M alpha) _) _) = do
>   _Gam <- fmap snd <$> ask
>   popL >>= \ e -> case e of
>     E beta (_T, HOLE)
>       | alpha == beta && alpha `elem` fmvs _Xi   -> do  pushLs (e:_Xi)
>                                                         block (Unify q)
>       | alpha == beta                            -> do  pushLs _Xi
>                                                         tryInvert q _T
>                                                             <|| (block (Unify q) >> pushL e)
>       | beta `elem` fmvs (_Gam, _Xi, q)          ->  flexTerm (e : _Xi) q
>     _                                            -> do  pushR (Right e)
>                                                         flexTerm _Xi q

%if False

> flexTerm _ q = error $ "flexTerm: " ++ show q

%endif


A flex-flex unification problem is one where both sides are applied
metavariables.  As in the general case above, the algorithm proceeds
leftwards through the context, looking for one of the metavariables so
it can try to solve one with the other.
If it reaches one of the metavariables and cannot solve for the
metavariable by inversion, it continues (using |flexTerm|), which
ensures it will terminate after trying to solve for both.  For
example, consider the case
$[[alpha </ ti // i /> ~~ beta </ xj // j />]]$
where only $[[</ xj // j />]]$ is a list of variables.  If it reaches
$[[alpha]]$ first then it might get stuck even if it could potentially
solve for $[[beta]]$.  This would be correct if order were important
in the metacontext, for example when implementing let-generalisation
as discussed in Chapter~\ref{chap:milner}.  Here it is not, so the
algorithm can simply pick up $[[alpha]]$ and carry on.

> flexFlex ::  [Entry] -> Equation -> Contextual ()
> flexFlex _Xi q@(EQNO (N (M alpha) ds) (N (M beta) es)) = do
>   _Gam <- fmap snd <$> ask
>   popL >>= \ e -> case e of
>     E gamma (_T, HOLE)
>       | gamma `elem` [alpha, beta] && gamma `elem` fmvs(_Xi) -> do  pushLs (e : _Xi)
>                                                                     block (Unify q)
>       | gamma == alpha                     -> do  pushLs _Xi
>                                                   tryInvert q _T <|| flexTerm [e] (sym q)
>       | gamma == beta                      -> do  pushLs _Xi
>                                                   tryInvert (sym q) _T <|| flexTerm [e] q
>       | gamma `elem` fmvs (_Gam, _Xi, q)   -> flexFlex (e : _Xi) q
>     _                                      -> do  pushR (Right e)
>                                                   flexFlex _Xi q

%if False

> flexFlex _ q = error $ "flexFlex: " ++ show q

%endif



Given a flexible equation whose head metavariable has just been found
in the context, the |tryInvert| control operator calls |invert| to
seek a solution to the equation. If it finds one, it defines the
metavariable.

> tryInvert ::  Equation -> Type -> Contextual Bool
> tryInvert q@(EQNO (N (M alpha) e) s) _T = invert alpha _T e s >>= \ m -> case m of
>         Nothing  ->  return False
>         Just v   ->  do  active (Unify q)
>                          define B0 alpha _T v
>                          return True

%if False

> tryInvert _ q = error $ "tryInvert: " ++ show q

%endif


Given a metavariable $[[alpha]]$ of type $[[T]]$, spine $[[E]]$ and
term $[[t]]$, |invert| attempts to find a value for $[[alpha]]$ that
solves the equation $[[E[alpha] ~~ t]]$.  It will throw an error if
the problem is unsolvable due to an impossible occurrence.

> invert ::  Nom -> Type -> Bwd Elim -> Tm -> Contextual (Maybe Tm)
> invert alpha _T e t  | occurCheck True alpha t = throwError "occur check"
>                      | alpha `notMember` fmvs t, Just xs <- toVars e, linearOn t xs = do
>                          b <- local (const B0) (typecheck _T (lams xs t))
>                          return $ if b then Just (lams xs t) else Nothing
>                      | otherwise = return Nothing

Note that the solution |lams xs t| is typechecked under no parameters,
so typechecking will fail if an out-of-scope variable is used.

The occur check, used to tell if an equation is definitely unsolvable,
looks for occurrences of a metavariable inside a term.  In a strong
rigid context (where the first argument is |True|), any occurrence is
fatal.  In a weak rigid context (where it is |False|), the evaluation
context of the metavariable must be a list of variables.

> occurCheck :: Bool -> Nom -> Tm -> Bool
> occurCheck w alpha (L b)           =  occurCheck w alpha t
>                                           where (_, t) = unsafeUnbind b
> occurCheck w alpha (N (V _ _) e)   =  getAny $ foldMap
>                                           (foldMapElim (Any `o` occurCheck False alpha)) e
> occurCheck w alpha (N (M beta) e)  =  alpha == beta && (w || isJust (toVars e))
> occurCheck w alpha (C c)           =  getAny $ foldMap (Any `o` occurCheck w alpha) c
> occurCheck w alpha (Pi _S _T)      =  occurCheck w alpha _S || occurCheck w alpha _T'
>                                           where (_, _T') = unsafeUnbind _T
> occurCheck w alpha (Sig _S _T)      =  occurCheck w alpha _S || occurCheck w alpha _T'
>                                           where (_, _T') = unsafeUnbind _T

Here |toVars| tries to convert a spine to a list of variables, and
|linearOn| determines if a list of variables is linear on the free
variables of a term.  Since it is enough for a term in a spine to be
$\eta$-convertible to a variable, the |etaContract| function
implements $\eta$-contraction for terms.

> linearOn :: Tm -> Bwd Nom -> Bool
> linearOn _  B0       = True
> linearOn t  (as:<a)  = not (a `elem` fvs t && a `elem` as) && linearOn t as

> etaContract :: Tm -> Tm
> etaContract (L b) = case etaContract t of
>      N x (e :< A (N (V y' _) B0)) | y == y', not (y `elem` fvs e)  -> N x e
>      t'                                                            -> lam y t'
>    where (y, t) = unsafeUnbind b
> etaContract (N x as)    = N x (fmap (mapElim etaContract) as)
> etaContract (PAIR s t)  = case (etaContract s, etaContract t) of
>     (N x (as :< Hd), N y (bs :< Tl)) | x == y, as == bs  -> N x as
>     (s', t')                                             -> PAIR s' t'
> etaContract (C c)       = C (fmap etaContract c)

> toVar :: Tm -> Maybe Nom
> toVar v = case etaContract v of  N (V x _) B0  -> Just x
>                                  _             -> Nothing
>
> toVars :: Traversable f => f Elim -> Maybe (f Nom)
> toVars = traverse (unA >=> toVar)
>   where  unA (A t)  = Just t
>          unA _      = Nothing
>


\subsection{Intersection}
\label{subsec:miller:impl:intersect}

When a flex-flex equation has the same metavariable on both
sides, i.e. it has the form
$[[alpha </ xi // i /> ~~ alpha </ yi // i />]]$ where
$[[</ xi // i />]]$ and $[[</ yi // i />]]$ are both lists of
variables, the equation can be solved by restricting $[[alpha]]$ to the
arguments on which $[[</ xi // i />]]$ and $[[</ yi // i />]]$ agree
(i.e. creating a new metavariable $[[beta]]$ and using it to solve
$[[alpha]]$).  This implements step \eqref{eqn:miller:unify:same} in
Figure~\longref{fig:miller:solve}, as described in
Subsection~\longref{subsec:miller:spec:intersect}.

The |flexFlexSame| function extracts the type of $[[alpha]]$ as a
telescope and calls |intersect| to generate a restricted telescope.
If this succeeds, it calls |instantiate| to create a new metavariable
and solve the old one. Otherwise, it leaves the equation in the
context.  Twin annotations can be ignored here here because any twins
will have definitionally equal types anyway.

> flexFlexSame ::  Equation -> Contextual ()
> flexFlexSame q@(EQNO (N (M alpha) e) (N (M alpha_) e')) = do
>     (_Tel, _T) <- telescope =<< lookupMeta alpha
>     case intersect _Tel e e' of
>         Just _Tel' | fvs _T `isSubsetOf` vars _Tel'  -> instantiate (alpha, _Pis _Tel' _T, \ beta -> lams' _Tel (beta $*$ _Tel))
>         _                                            -> block (Unify q)

Given a telescope and the two evaluation contexts, |intersect|
checks the evaluation contexts are lists of variables and produces the
telescope on which they agree.

> intersect ::  Telescope -> Bwd Elim -> Bwd Elim -> Maybe Telescope
> intersect B0                 B0          B0           = return B0
> intersect (_Tel :< (z, _S))  (e :< A s)  (e' :< A t)  = do
>     _Tel'  <- intersect _Tel e e'
>     x      <- toVar s
>     y      <- toVar t
>     if x == y then return (_Tel' :< (z, _S)) else return _Tel'
> intersect _ _ _ = Nothing


\subsection{Pruning}
\label{subsec:miller:impl:pruning}

Given a flex-rigid or flex-flex equation, it might be possible to make
some progress by pruning the metavariables contained within it, as
described in Subsection~\longref{subsec:miller:spec:prune}.  The
|tryPrune| function calls |pruneTm|: if it learns anything from
pruning, it leaves the current problem |active| and instantiates the
pruned metavariable.

> tryPrune ::  Equation -> Contextual Bool
> tryPrune q@(EQNO (N (M alpha) e) t) = pruneTm (fvs e) t >>= \ u ->  case u of
>         d:_  -> active (Unify q) >> instantiate d >> return True
>         []   -> return False

%if False

> tryPrune q = error $ "tryPrune: " ++ show q

%endif

Pruning a term requires traversing it looking for occurrences of
forbidden variables.  If any occur rigidly, the corresponding
constraint is impossible.  If a metavariable is encountered, it cannot
depend on any arguments that contain rigid occurrences of forbidden
variables, so it can be replaced by a fresh metavariable of
restricted type.  The |pruneTm| function generates a list of triples
|(beta, _U, f)| where |beta| is a metavariable, |_U| is a type for a
new metavariable |gamma| and |f gamma| is a solution for |beta|.  It
maintains the invariant that |_U| and |f gamma| depend only on
metavariables defined prior to |beta| in the context.

> pruneTm ::  Set Nom -> Tm -> Contextual [Instantiation]
> pruneTm _Vs (Pi _S _T)      = (++) <$> pruneTm _Vs _S  <*> pruneUnder _Vs _T
> pruneTm _Vs (Sig _S _T)     = (++) <$> pruneTm _Vs _S  <*> pruneUnder _Vs _T
> pruneTm _Vs (PAIR s t)      = (++) <$> pruneTm _Vs s   <*> pruneTm _Vs t
> pruneTm _Vs (L b)           = pruneUnder _Vs b
> pruneTm _Vs (N (M beta) e)  = pruneMeta _Vs beta e
> pruneTm _Vs (C _)           = return []
> pruneTm _Vs (N (V z _) e)   | z `member` _Vs    = pruneElims _Vs e
>                             | otherwise         = throwError "pruning error"
>
> pruneUnder :: Set Nom -> Bind Nom Tm -> Contextual [Instantiation]
> pruneUnder _Vs b = do  (x, t) <- unbind b
>                        pruneTm (_Vs `union` singleton x) t
>
> pruneElims :: Set Nom -> Bwd Elim -> Contextual [Instantiation]
> pruneElims _Vs e = fold <$> traverse pruneElim e
>   where
>     pruneElim (A a)        = pruneTm _Vs a
>     pruneElim (If _T s t)  = (++) <$> ((++)  <$> pruneTm _Vs s <*> pruneTm _Vs t)
>                                                  <*> pruneUnder _Vs _T
>     pruneElim _            = return []

Once a metavariable has been found, |pruneMeta| unfolds its type as a
telescope |_Pis _Tel _T|, and calls |prune| with the telescope and
list of arguments.  If the telescope is successfully pruned (|_Tel'|
is not the same as |_Tel|) and the free variables of |_T| remain in
the telescope, then an instantiation of the
metavariable is generated.

> pruneMeta :: Set Nom -> Nom -> Bwd Elim -> Contextual [Instantiation]
> pruneMeta _Vs beta e = do
>     (_Tel, _T) <- telescope =<< lookupMeta beta
>     case prune _Vs _Tel e of
>         Just _Tel'  | _Tel' /= _Tel, fvs _T `isSubsetOf` vars _Tel'
>                         -> return [(beta, _Pis _Tel' _T, \ beta' -> lams' _Tel (beta' $*$ _Tel'))]
>         _               -> return []

The |prune| function generates a restricted telescope, removing
arguments that contain a rigid occurrence of a forbidden variable.
This may fail if it is not clear which arguments must be removed.

> prune :: Set Nom -> Telescope -> Bwd Elim -> Maybe Telescope
> prune _Vs B0                 B0          = Just B0
> prune _Vs (_Del :< (x, _S))  (e :< A s)  = do
>     _Del' <- prune _Vs _Del e
>     case toVar s of
>       Just y  | y `member` _Vs, fvs _S `isSubsetOf` vars _Del'  -> Just (_Del' :< (x, _S))
>       _       | fvrigs s `notSubsetOf` _Vs                      -> Just _Del'
>               | otherwise                                       -> Nothing
> prune _ _ _ = Nothing


A metavariable |alpha| can be instantiated to a more specific type by
moving left through the context until it is found, creating a new
metavariable and solving for |alpha|.  The type must not depend on any
metavariables defined after |alpha|.

> type Instantiation = (Nom, Type, Tm -> Tm)

> instantiate :: Instantiation -> Contextual ()
> instantiate d@(alpha, _T, f) = popL >>= \ e -> case e of 
>       E beta (_U, HOLE)  | alpha == beta  ->  hole B0 _T (\ t -> define B0 beta _U (f t))
>       _                                   ->  do  pushR (Right e)
>                                                   instantiate d


\subsection{Metavariable simplification}
\label{subsec:miller:impl:metasimp}

Given the name and type of a metavariable, |lower| attempts to
simplify it by removing $\Sigma$-types, according to the metavariable
simplification steps \eqref{eqn:miller:metasimp:sigma} and
\eqref{eqn:miller:metasimp:pi-sigma} in
Figure~\longref{fig:miller:solve}, as described in
Subsection~\longref{subsec:miller:spec:metasimp}.

> lower :: Telescope -> Nom -> Type -> Contextual Bool
> lower _Phi alpha (Sig _S _T) =  hole _Phi _S $ \ s ->
>                                 hole _Phi (inst _T s) $ \ t ->
>                                 define _Phi alpha (Sig _S _T) (PAIR s t) >>
>                                 return True
>
> lower _Phi alpha (Pi _S _T) = do  x <- fresh (s2n "x")
>                                   splitSig B0 x _S >>= maybe
>                                       (lower (_Phi :< (x, _S)) alpha (inst _T (var x)))
>                                       (\ (y, _A, z, _B, s, (u, v)) ->
>                                           hole _Phi (_Pi y _A  (_Pi z _B (inst _T s))) $ \ w ->
>                                           define _Phi alpha (Pi _S _T) (lam x (w $$ u $$ v)) >>
>                                           return True)      
>             
> lower _Phi alpha _T = return False


Lowering a metavariable needs to split $\Sigma$-types (possibly
underneath a bunch of parameters) into their components.  For example,
$[[y : Pi x : X . Sigma z : S . T]]$ splits into
$[[y0 : Pi x : X . S]]$ and $[[y1 : Pi x : X . {y0 x/z} T]]$.  Given
the name of a variable and its type, |splitSig| attempts to split it,
returning fresh variables for the two components of the $\Sigma$-type,
an inhabitant of the original type in terms of the new variables and
inhabitants of the new types by projecting the original variable.

> splitSig ::  Telescope -> Nom -> Type ->
>                  Contextual (Maybe  (Nom, Type, Nom, Type, Tm, (Tm, Tm)))
> splitSig _Phi x (Sig _S _T)  = do  y  <- fresh (s2n "y")
>                                    z  <- fresh (s2n "z")
>                                    return $ Just  (y, _Pis _Phi _S, z, _Pis _Phi (inst _T (var y)),
>                                                   lams' _Phi (PAIR (var y $*$ _Phi) (var z $*$ _Phi)),
>                                                   (lams' _Phi (var x $*$ _Phi %% Hd), 
>                                                        lams' _Phi (var x $*$ _Phi %% Tl)))
> splitSig _Phi x (Pi _A _B)   = do  a <- fresh (s2n "a")
>                                    splitSig (_Phi :< (a, _A)) x (inst _B (var a))
> splitSig _ _ _ = return Nothing


\subsection{Problem simplification and unification}
\label{subsec:miller:impl:unification}

Given a problem, the |solver| simplifies it according to the rules in
Figure~\longref{fig:miller:prob-decompose}, introduces parameters and
calls |unify| defined below if it is not already reflexive.  In
particular, problem simplification removes $\Sigma$-types from
parameters, potentially eliminating projections, and replaces twins
whose types are definitionally equal with a single parameter.  This
implements the steps described in
Subsection~\longref{subsec:miller:spec:decompose}.

> solver :: Problem -> Contextual ()
> solver (Unify q) = do  b <- isReflexive q
>                        unless b (unify q)
> solver (All p b) = do
>     (x, q)  <- unbind b
>     case p of
>         _ |  x `notElem` fvs q -> active q
>         P _S         -> splitSig B0 x _S >>= \ m -> case m of
>             Just (y, _A, z, _B, s, _)  -> solver (allProb y _A  (allProb z _B (subst x s q)))
>             Nothing                    -> inScope x (P _S) $ solver q
>         Twins _S _T  -> equal SET _S _T >>= \ c ->
>             if c  then  solver (allProb x _S (subst x (var x) q))
>                   else  inScope x (Twins _S _T) $ solver q
>             

The |unify| function performs a single unification step:
$\eta$-expanding elements of $\Pi$ or $\Sigma$ types via the problem
simplification steps \eqref{eqn:miller:decompose:fun} and
\eqref{eqn:miller:decompose:pair} in
Figure~\longref{fig:miller:prob-decompose}, or invoking an auxiliary
function in order to make progress.

> unify :: Equation -> Contextual ()
>
> unify (EQN (Pi _A _B) f (Pi _S _T) g) = do
>     x <- fresh (s2n "x")
>     active $ allTwinsProb x _A _S (eqnProb (inst _B (twinL x)) (f $$ twinL x) (inst _T (twinR x)) (g $$ twinR x))
> unify (EQN (Sig _A _B) t (Sig _C _D) w) = do
>     active $ eqnProb _A (hd t) _C (hd w)
>     active $ eqnProb (inst _B (hd t)) (tl t) (inst _D (hd w)) (tl w)
>
> unify q@(EQNO (N (M alpha) e) (N (M beta) e'))
>     | alpha == beta =  tryPrune q <|| tryPrune (sym q) <|| flexFlexSame q
> unify q@(EQNO (N (M alpha) e) (N (M beta) e'))  = tryPrune q <|| tryPrune (sym q) <|| flexFlex [] q
> unify q@(EQNO (N (M alpha) e) t)                = tryPrune q <|| flexTerm [] q
> unify q@(EQNO t (N (M alpha) e))                = tryPrune (sym q) <|| flexTerm [] (sym q)
> unify q                                         = rigidRigid q

A rigid-rigid equation (between two non-metavariable terms) can either
be decomposed into simpler equations or it is impossible to solve.
For example, $[[Pi x : A . B ~~ Pi x : S . T]]$ splits into
$[[A ~~ S]], [[B ~~ T]]$, but
$[[Pi x : A . B ~~ Sigma x : S . T]]$ cannot be solved.
The |rigidRigid| function implements steps
\eqref{eqn:miller:decompose:pi}--\eqref{eqn:miller:decompose:rigid-fail}
from Figure~\longref{fig:miller:prob-decompose}, as described in
Subsection~\longref{subsec:miller:spec:decompose}.  Both |unify| and
|rigidRigid| will be called only when the equation is not already
reflexive.

> rigidRigid :: Equation -> Contextual ()
>
> rigidRigid (EQN SET (Pi _A _B) SET (Pi _S _T)) = do
>     x <- fresh (s2n "x")
>     active $ eqnProb SET _A SET _S
>     active $ allTwinsProb x _A _S (eqnProb SET (inst _B (twinL x)) SET (inst _T (twinR x)))
>
> rigidRigid (EQN SET (Sig _A _B) SET (Sig _S _T)) = do
>     x <- fresh (s2n "x")
>     active $ eqnProb SET _A SET _S
>     active $ allTwinsProb x _A _S (eqnProb SET (inst _B (twinL x)) SET (inst _T (twinR x)))
>
> rigidRigid (EQNO (N (V x w) e) (N (V x' w') e')) =
>     matchSpine x w e x' w' e' >> return ()
>
> rigidRigid q  | orthogonal q  = throwError "Rigid-rigid mismatch"
>               | otherwise     = block $ Unify q


A constraint has no solutions if it equates two |orthogonal| terms,
with different constructors or variables, as defined in
Figure~\longref{fig:miller:impossible}.

> orthogonal :: Equation -> Bool
> orthogonal (EQN SET (Pi _ _) SET (Sig _ _))     = True
> orthogonal (EQN SET (Pi _ _) SET BOOL)          = True
> orthogonal (EQN SET (Sig _ _) SET (Pi _ _))     = True
> orthogonal (EQN SET (Sig _ _) SET BOOL)         = True
> orthogonal (EQN SET BOOL SET (Pi _ _))          = True
> orthogonal (EQN SET BOOL SET (Sig _ _))         = True
> orthogonal (EQN BOOL TT BOOL FF)                = True
> orthogonal (EQN BOOL FF BOOL TT)                = True
>
> orthogonal (EQN SET (Pi _ _)  _ (N (V _ _) _))  = True
> orthogonal (EQN SET (Sig _ _) _ (N (V _ _) _))  = True
> orthogonal (EQN SET BOOL _ (N (V _ _) _))       = True
> orthogonal (EQN BOOL TT _ (N (V _ _) _))        = True
> orthogonal (EQN BOOL FF _ (N (V _ _) _))        = True
>
> orthogonal (EQN _ (N (V _ _) _) SET (Pi _ _))   = True
> orthogonal (EQN _ (N (V _ _) _) SET (Sig _ _))  = True
> orthogonal (EQN _ (N (V _ _) _) SET BOOL)       = True
> orthogonal (EQN _ (N (V _ _) _) BOOL TT)        = True
> orthogonal (EQN _ (N (V _ _) _) BOOL FF)        = True
>
> orthogonal _                                    = False


When there are rigid variables at the heads on both sides, proceed
through the evaluation contexts, demanding that projections are
identical and unifying terms in applications.  Note that |matchSpine|
returns the types of the two sides, used when unifying applications to
determine the types of the arguments.  For example, if
$[[y : Pi x : S . {x/x} T -> U]]$ then the constraint $[[y s t ~~ y u v]]$
will decompose into
$[[(s : S) ~~ (u : S) && (t : {s/x} T) ~~ (v : {u/x} T)]]$.

> matchSpine ::  Nom -> Twin -> Bwd Elim ->
>                Nom -> Twin -> Bwd Elim ->
>                    Contextual (Type, Type)
> matchSpine x w B0 x' w' B0
>   | x == x'    = (,) <$> lookupVar x w <*> lookupVar x' w'
>   | otherwise  = throwError "rigid head mismatch"
> matchSpine x w (e :< A a) x' w' (e' :< A s) = do
>     (Pi _A _B, Pi _S _T) <- matchSpine x w e x' w' e'
>     active $ eqnProb _A a _S s
>     return (inst _B a, inst _T s)
> matchSpine x w (e :< Hd) x' w' (e' :< Hd) = do
>     (Sig _A _B, Sig _S _T) <- matchSpine x w e x' w' e'
>     return (_A, _S)
> matchSpine x w (e :< Tl) x' w' (e' :< Tl) = do
>     (Sig _A _B, Sig _S _T) <- matchSpine x w e x' w' e'
>     return (inst _B (N (V x w) (e :< Hd)), inst _T (N (V x' w') (e' :< Hd)))
> matchSpine x w (e :< If _T s t) x' w' (e' :< If _T' s' t') = do
>     (BOOL, BOOL) <- matchSpine x w e x' w' e'
>     y <- fresh (s2n "y")
>     active $ allProb y BOOL (eqnProb TYPE (inst _T (var y)) TYPE (inst _T' (var y)))
>     active $ eqnProb (inst _T TT) s (inst _T' TT) s'
>     active $ eqnProb (inst _T FF) t (inst _T' FF) t'
>     return (inst _T (N (V x w) e), inst _T' (N (V x' w') e'))
> matchSpine _ _ _ _ _ _ = throwError "spine mismatch"




\subsection{Solvitur ambulando}
\label{subsec:miller:impl:ambulando}

Constraint solving is started by the |ambulando| function, which
lazily propagates a substitution rightwards through the metacontext,
making progress on problems where possible.  It maintains the
invariant that the entries to the left of the cursor include no active
problems.  This is not the only possible strategy: indeed, it is
crucial for guaranteeing most general solutions that solving the
constraints in any order would produce the same result.  However, it
is simple to implement and often works well with the heterogeneity
invariant, because the problems making a constraint homogeneous will
usually be solved before the constraint itself.

> ambulando :: Subs -> Contextual ()
> ambulando theta = optional popR >>= \ x -> case x of
>  Nothing             -> return ()
>  Just (Left theta')  -> ambulando (theta *%* theta')
>  Just (Right e)      -> case update theta e of
>     e'@(E alpha (_T, HOLE))   ->  do  lower B0 alpha _T <|| pushL e'
>                                       ambulando theta
>     Q Active p                ->  do  pushR (Left theta)
>                                       solver p
>                                       ambulando []
>     e'                        ->  do  pushL e'
>                                       ambulando theta

Each problem records its status, which is either |Active| and ready to
be worked on or |Blocked| and unable to make progress.  The |update|
function applies a substitution to an entry, updating the status of a
problem if its type changes.

> update :: Subs -> Entry -> Entry
> update theta (Q s p) = Q s' p'
>   where  p'  = substs theta p
>          s'  | p == p'    = s 
>              | otherwise  = Active
> update theta e = substs theta e

For simplicity, |Blocked| problems do not store any information about
when they may be resumed.  An optimisation would be to track the
conditions under which they should become active, typically when
particular metavariables are solved or types become definitionally
equal.
