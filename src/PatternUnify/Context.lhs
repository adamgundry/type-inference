%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
>       FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
>       UndecidableInstances, GeneralizedNewtypeDeriving,
>       TypeSynonymInstances, ScopedTypeVariables, StandaloneDeriving #-}

> module PatternUnify.Context where

> import Prelude hiding (foldr)

> import Control.Arrow (first, second)
> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Error
> import Control.Monad.Reader
> import Control.Monad.Identity
> import qualified Data.Set as Set (empty) 
> import Data.Traversable (Traversable, traverse)

> import Common.BwdFwd
> import Common.Names
> import Common.PrettyPrint hiding (first)
> import PatternUnify.Tm

%endif

I will now define unification problems, metacontexts and operations
for working on them in the |Contextual| monad.  The notions of
metacontext and context in use were given in
Subsection~\longref{subsec:miller:contexts}, and the monadic approach
develops that of the previous appendices.  Metacontext entries now
consist of metavariables, as before, or problems, which carry a status
bit used to record whether they have been solve as far as possible
given their current type (see
Subsection~\ref{subsec:miller:impl:ambulando}).  Problems are
equations under universally quantified parameters, and parameters may
include twins.

> data Decl v    =  HOLE | DEFN v
> data Entry     =  E (Name Tm) (Type, Decl Tm) | Q Status Problem
> data Status    =  Blocked | Active
>
> data Param     =  P Type | Twins Type Type
> type Params    =  Bwd (Nom, Param)
>
> data Equation  =  EQN Type Tm Type Tm
> data Problem   =  Unify Equation | All Param (Bind Nom Problem)

The |sym| function swaps the two sides of an equation:

> sym :: Equation -> Equation
> sym (EQN _S s _T t) = EQN _T t _S s


The metacontext is represented as a list zipper: a pair of lists
representing the entries before and after the cursor.  Entries after
the cursor may include substitutions, being propagated lazily.

> type ContextL  = Bwd Entry
> type ContextR  = [Either Subs Entry]
> type Context   = (ContextL, ContextR)


%if False

> deriving instance Eq Status
> deriving instance Show Status

> instance Alpha Status
> instance Subst a Status

> deriving instance Show Param

> instance Alpha Param
> instance Subst Tm Param

> instance Occurs Param where
>     free l (P _T)          = free l _T
>     free l (Twins _S _T)   = free l _S `union` free l _T

> instance Pretty Param where
>     pretty (P _T)         = pretty _T
>     pretty (Twins _S _T)  = (| (between (text "&")) (pretty _S) (pretty _T) |)


> deriving instance Eq v => Eq (Decl v)
> deriving instance Show v => Show (Decl v)

> instance Alpha v => Alpha (Decl v)
> instance Subst t v => Subst t (Decl v)

> instance Pretty v => Pretty (Decl v) where
>     pretty HOLE     = return $ text "HOLE"
>     pretty (DEFN t) = pretty t

> instance Occurs v => Occurs (Decl v) where
>     free l HOLE      = Set.empty
>     free l (DEFN t)  = free l t


> deriving instance Eq Entry
> deriving instance Show Entry

> instance Alpha Entry
> instance Subst Tm Entry

> instance Pretty Entry where
>     pretty (E alpha (_T, HOLE))    = (| (between colon) (pretty alpha) (pretty _T) |)
>     pretty (E alpha (_T, DEFN v))  = (| (between (text ":=")) (| (between colon) (pretty alpha) (pretty _T) |) (pretty v) |)
>     pretty (Q s p)                 = (| ~(text $ "?" ++ show s) <+> pretty p |)

> instance Occurs Entry where
>     free l (E _ d)  = free l d
>     free l (Q _ p)  = free l p

> deriving instance Show Equation

> pattern EQNO s t = EQN boring s boringer t

> instance Alpha Equation
> instance Subst Tm Equation

> instance Occurs Equation where
>     free l (EQN _S s _T t) = free l (_S, s, _T, t)

> instance Pretty Equation where
>   pretty (EQN _S s _T t) = (| f (pretty _S) (pretty s) (pretty _T) (pretty t) |)
>       where f _S' s' _T' t' = parens (s' <+> colon <+> _S') <+>
>                                   text "==" <+> parens (t' <+> colon <+> _T')

> deriving instance Show Problem

> instance Alpha Problem
> instance Eq Problem where
>     (==) = aeq

> instance Occurs Problem where
>     free l (Unify q)  = free l q
>     free l (All e b)  = free l (e, b)


> instance Subst Tm Problem where
>     substs s (Unify q)  = Unify (substs s q)
>     substs s (All e b)  = All (substs s e) (bind x (substs s p))
>                               where (x, p) = unsafeUnbind b

> instance Pretty Problem where
>     pretty (Unify q) = pretty q
>     pretty (All e b) = lunbind b $ \ (x, p) -> do
>         e'  <- pretty e
>         x'  <- pretty x
>         p'  <- pretty p
>         return $ parens (x' <+> colon <+> e') <+> text "->" <+> p'

> eqnProb :: Type -> Tm -> Type -> Tm -> Problem
> eqnProb _S s _T t = Unify (EQN _S s _T t)

> allProb :: Nom -> Type -> Problem -> Problem
> allProb x _T p = All (P _T) (bind x p)

> allTwinsProb :: Nom -> Type -> Type -> Problem -> Problem
> allTwinsProb x _S _T p = All (Twins _S _T) (bind x p)

%endif



The |Contextual| monad stores the current context and parameters,
generates fresh names when required for going under binders, and
handles exceptions.

> newtype Contextual a = Contextual
>   (ReaderT Params (StateT Context (FreshMT (ErrorT String Identity))) a)

%if False

> runContextual ::  ContextL -> Params -> Contextual a ->
>                       Either String (a, Context)
> runContextual mcx pars (Contextual m) =
>     runIdentity `o` runErrorT `o` runFreshMT `o`
>         flip runStateT (mcx, []) `o` flip runReaderT pars $ m

> deriving instance Applicative Contextual
> deriving instance Alternative Contextual
> deriving instance Fresh Contextual
> deriving instance Functor Contextual
> deriving instance Monad Contextual
> deriving instance MonadError String Contextual
> deriving instance MonadState Context Contextual
> deriving instance MonadReader Params Contextual

%endif


\subsubsection{Reading and modifying state}

I define versions of the usual state-manipulating |get|, |modify| and
|put| operations that act on the left or right part of the context
(before or after the cursor).

> getL :: Contextual ContextL
> getL = gets fst
>
> getR :: Contextual ContextR
> getR = gets snd
>
> modifyL :: (ContextL -> ContextL) -> Contextual ()
> modifyL = modify `o` first
>
> modifyR :: (ContextR -> ContextR) -> Contextual ()
> modifyR = modify `o` second
>
> putL :: ContextL -> Contextual ()
> putL = modifyL `o` const
>
> putR :: ContextR -> Contextual ()
> putR = modifyR `o` const

Here are operations to push to, or pop from, either side of the
cursor, or move the cursor one entry to the left:

> pushL :: Entry -> Contextual ()
> pushL e = modifyL (:< e)
>
> pushR :: Either Subs Entry -> Contextual ()
> pushR e  = modifyR (e :)
>
> pushLs :: Traversable f => f Entry -> Contextual ()
> pushLs es = traverse pushL es >> return ()
>
> popL :: Contextual Entry
> popL = do  mcx <- getL
>            case mcx of  (mcx' :< e)  -> putL mcx' >> return e
>                         B0           -> throwError "popL: out of context"
>
> popR :: Contextual (Either Subs Entry)
> popR = do  mcx <- getR
>            case mcx of  (x  : mcx')  -> putR mcx' >> return x
>                         []           -> throwError "popR: out of context"
>
> goLeft :: Contextual ()
> goLeft = popL >>= pushR `o` Right


\subsubsection{Variable and metavariable lookup}

The context of local parameters is tracked using the |ReaderT| monad
transformer, so the |local| operation can be used to bring a parameter
into scope, and the |ask| operation can be used to look up a variable.

> inScope :: Nom -> Param -> Contextual a -> Contextual a
> inScope x p = local (:< (x, p))
>
> lookupVar :: Nom -> Twin -> Contextual Type
> lookupVar x w = help w =<< ask
>   where
>     help Only   (_Gam :< (y, P _T))         | x == y  = return _T
>     help TwinL  (_Gam :< (y, Twins _S _T))  | x == y  = return _S
>     help TwinR  (_Gam :< (y, Twins _S _T))  | x == y  = return _T
>     help w      (_Gam :< _)                           = help w _Gam
>     help _      B0 = throwError $ "lookupVar: missing " ++ show x


The type of a metavariable can be determined from its name by
searching the metacontext.  Only metavariables left of the cursor are
in scope.

> lookupMeta :: Nom -> Contextual Type
> lookupMeta x = look =<< getL
>   where
>     look (mcx  :< E y (_T, _))  | x == y     = return _T
>     look (mcx  :< _)                         = look mcx
>     look B0 = error $ "lookupMeta: missing " ++ show x


%if False

> $(derive[''Problem, ''Equation, ''Param, ''Entry, ''Status, ''Decl])

%endif