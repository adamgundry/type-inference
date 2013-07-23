%if False

> {-# LANGUAGE FlexibleContexts, FlexibleInstances,  MultiParamTypeClasses,
>              TemplateHaskell, UndecidableInstances, ScopedTypeVariables,
>              GeneralizedNewtypeDeriving, StandaloneDeriving #-}

> module Milner.Type where

> import Control.Applicative
> import Control.Monad.Identity
> import Control.Monad.State
> import Control.Monad.Error

> import Data.Set as Set (Set, empty, singleton)

> import Common.BwdFwd hiding ((<><))
> import Common.Names
> import Common.PrettyPrint

%endif

This section implements type, contexts and terms, as in
Section~\longref{sec:milner:framework}.

The datatype |Type| represents types of the object language, which
may contain metavariables |M| and variables |V| as well as functions
and a base type.  The |Name| constructor is provided by the Binders
Unbound library.

> data Type  =  M (Name Type) | V (Name Type) | Type `Arr` Type

%if False

> deriving instance Eq Type
> deriving instance Show Type

> infixr 5 `Arr`

> instance Alpha Type
> instance Subst Type Type where
>     isvar (M a)  = Just (SubstName a)
>     isvar (V a)  = Just (SubstName a)
>     isvar _      = Nothing

> instance Pretty Type where
>     pretty (M x)        = pretty x
>     pretty (V x)        = pretty x
>     pretty (t `Arr` u)  = between (text "->") <$> pretty t <*> pretty u

%endif

The |fmvs| function computes the free metavariables of a type.

> fmvs :: Type -> Set (Name Type)
> fmvs (M alpha)            = Set.singleton alpha
> fmvs (V a)                = Set.empty
> fmvs (tau `Arr` upsilon)  = fmvs tau `union` fmvs upsilon


The datatype |Scheme| represents type schemes.  Binding variables
uses a locally nameless representation where bound variables have de
Bruijn indices and free variables (those bound in the context) have
names \citep{mcbride2004:not-a-number}.

> data Scheme  =  T Type | All (Bind (Name Type) Scheme)

%if False

> deriving instance Show Scheme

> instance Alpha Scheme
> instance Subst Type Scheme

> instance Eq Scheme where
>     (==) = aeq

> instance Pretty Scheme where
>     pretty (T t)      = pretty t
>     pretty (All b)  = lunbind b $ \ (a, s) -> do
>                           a' <- pretty a
>                           s' <- pretty s
>                           return $ text "all" <+> a' <+> text "." <+> s'

%endif
 

|Bwd| is the type of backwards lists with |B0| for the empty list and
|:<| for snoc.  Lists are traversable functors, and monoids under
concatenation |(<.>)|, in the usual way.  Datatype declarations are
cheap, so rather than reusing the forwards list type |[]|, I prefer to
make the code closer to the specification.

< data Bwd a = B0 | Bwd a :< a


Contexts are backwards lists of entries, which are either
metavariables |E| (possibly carrying a definition), term variables |Z|
or generalisation markers |Mark|.  A context suffix contains only
metavariable entries, and can be appended to a context with the
\scare{fish} operator |(<><)|.

> type Context  =  Bwd Entry
> type Suffix   =  [(Name Type, Decl Type)]
> data Decl v   =  HOLE |  DEFN v
> data Entry    =  E (Name Type) (Decl Type) | Z (Name Tm) Scheme | Mark

%if False

This is introduced in Milner.Zipper, but is defined here to save
redoing everything with an alternate definition of Entry:

>                | Layer TermLayer

> data FTm  =  VarF (Name Tm)
>           |  AppTm FTm FTm
>           |  AppTy FTm Type
>           |  LamTm Scheme (Bind (Name Tm) FTm)
>           |  LamTy (Bind (Name Type) FTm)

> deriving instance Show FTm
> instance Alpha FTm
> instance Subst Type FTm
> instance Eq FTm where
>   (==) = aeq

> instance Pretty FTm where
>     pretty (VarF x) = pretty x
>     pretty (f `AppTm` s) = (<+>) <$> pretty f <*> pretty s
>     pretty (f `AppTy` s) = (<+>) <$> pretty f <*> (brackets <$> pretty s)
>     pretty (LamTm tau b) = lunbind b $ \ (x, t) -> do
>                        x' <- pretty x
>                        tau' <- pretty tau
>                        t' <- pretty t
>                        return $ parens $ text "\\" <+> x' <+> colon <+> tau' <+> text "." <+> t'
>     pretty (LamTy b) = lunbind b $ \ (x, t) -> do
>                        x' <- pretty x
>                        t' <- pretty t
>                        return $ parens $ text "/\\" <+> x' <+> text "." <+> t'


> data TermLayer  =  AppLeft () Tm
>                 |  AppRight (FTm, Type) ()
>                 |  LamBody (Name Tm, Type) ()
>                 |  LetBinding () (Bind (Name Tm) Tm)
>                 |  LetBody (Name Tm) (FTm, Scheme) ()

> deriving instance Show TermLayer

> instance Alpha TermLayer

> instance Eq TermLayer where
>   (==) = aeq

> deriving instance Eq Entry

> instance Pretty Entry where
>     pretty (E a d)   = (<+>) <$> pretty a <*> pretty d
>     pretty (Z x sc)  = between colon <$> pretty x <*> pretty sc
>     pretty Mark      = return $ text ";"
>     pretty (Layer l) = return $ text $ show l

> deriving instance Eq v => Eq (Decl v)
> deriving instance Show v => Show (Decl v)

> instance Alpha v => Alpha (Decl v)
> instance Subst t v => Subst t (Decl v)

> instance Pretty v => Pretty (Decl v) where
>     pretty HOLE     = return $ text "?"
>     pretty (DEFN t) = (text ":=" <+>) <$> pretty t

%endif

> (<><) :: Context -> Suffix -> Context
> mcx <>< ((alpha, d) : es)  = (mcx :< E alpha d) <>< es
> mcx <>< []                 = mcx


The |Contextual| monad represents computations that can mutate the
context, generate fresh names and throw exceptions.  It thus
encapsulates the effects needed to implement unification and type
inference.  I will use the |throwError| operation in the monad to
abort due to \scare{expected} errors, such as impossible unification
problems, and the Haskell built-in |error| for violations of
invariants that would indicate bugs in the implementation itself.

> newtype Contextual a = Contextual
>     (StateT Context (FreshMT (ErrorT String Identity)) a)

%if False

> deriving instance Applicative Contextual
> deriving instance Alternative Contextual
> deriving instance Functor Contextual
> deriving instance Monad Contextual
> deriving instance MonadState Context Contextual
> deriving instance MonadError String Contextual
> deriving instance Fresh Contextual

> runContextual :: Context -> Contextual a -> Either String (a, Context)
> runContextual mcx (Contextual m) = runIdentity . runErrorT . runFreshMT . flip runStateT mcx $ m

%endif


The |popL| function removes and returns an entry from the metacontext.

> popL :: Contextual Entry
> popL = do  mcx :< e <- get
>            put mcx
>            return e


The |freshMeta| function generates a fresh metavariable name and
appends a |HOLE| to the context.

> freshMeta :: String -> Contextual (Name Type)
> freshMeta a = do  alpha <- fresh (s2n a)
>                   modify (:< E alpha HOLE)
>                   return alpha



The datatype |Tm| represents terms in the object language.  As with
type schemes, it uses a locally nameless representation.

> data Tm  =  X (Name Tm)              |  App Tm Tm 
>          |  Lam (Bind (Name Tm) Tm)  |  Let Tm (Bind (Name Tm) Tm)

%if False

> deriving instance Show Tm

> instance Alpha Tm

> instance Eq Tm where
>     (==) = aeq

> instance Pretty Tm where
>     pretty (X x) = pretty x
>     pretty (f `App` s) = (<+>) <$> pretty f <*> pretty s
>     pretty (Lam b) = lunbind b $ \ (x, t) -> do
>                        x' <- pretty x
>                        t' <- pretty t
>                        return $ parens $ text "\\" <+> x' <+> text "." <+> t'
>     pretty (Let s b) = do
>         s' <- pretty s
>         lunbind b $ \ (x, t) -> do
>             x' <- pretty x
>             t' <- pretty t
>             return $ text "let" <+> x' <+> text "=" <+> s' <+> text "in" <+> t'

%endif


The |Contextual| monad supports the |find| function, which looks up a
term variable in the context and returns its scheme.

> find     :: Name Tm -> Contextual Scheme
> find x = get >>= help
>   where
>     help :: Context -> Contextual Scheme
>     help B0                           = throwError $ "Out of scope: " ++ show x
>     help (mcx :< Z y sigma) | x == y  = return sigma
>     help (mcx :< _)                   = help mcx

The |inScope| operator runs a |Contextual| computation with an
additional term variable in scope, then removes the variable
afterwards.

> inScope  :: Name Tm -> Scheme -> Contextual a -> Contextual a
> inScope x sigma m = do  modify (:< Z x sigma)
>                         a <- m
>                         modify dropVar
>                         return a
>   where
>     dropVar B0                       = error "Invariant violation"
>     dropVar (mcx :< Z y _) | x == y  = mcx
>     dropVar (mcx :< e)               = dropVar mcx :< e

%if False

The iterated version of this operator is used only for testing.

> inScopes :: Bwd (Name Tm, Scheme) -> Contextual a -> Contextual a
> inScopes B0                    m = m
> inScopes (_Gam :< (x, sigma))  m = inScopes _Gam (inScope x sigma m)

%endif


%if False

> $(derive[''Decl, ''Type, ''Scheme, ''Tm, ''FTm, ''TermLayer])

%endif