%if False

> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              TypeOperators, FlexibleInstances, GADTs,
>              StandaloneDeriving, TemplateHaskell,
>              MultiParamTypeClasses, FlexibleContexts,
>              UndecidableInstances, ScopedTypeVariables,
>              GeneralizedNewtypeDeriving #-}

> module Units.Type where

> import Prelude hiding (foldr)

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Identity
> import Control.Monad.State (StateT(..), MonadState(..), modify)
> import Data.SignedMultiset (foldr)
> import Data.Set as Set (Set, singleton, empty)

> import Common.BwdFwd hiding ((<><))
> import Common.Names
> import Common.PrettyPrint
> import Units.Group

%endif

Now I extend the representation of types and contexts from
Section~\ref{sec:milner:apx:type} to include units of measure, as
described in Subsection~\longref{subsec:units:framework}.
The datatype of types retains metavariables, variables and functions,
and gains syntax for units (types of kind |UN|): the identity,
multiplication, constant expontentiation and base units.  The |Float|
constructor is an example of a type parameterised by a unit.

> data Kind  = Star | UN
> data Type  =  M (Name Type) | V (Name Type) | Type `Arr` Type
>            |  Float Type | One |  Type `Times` Type |  Type `Pow` Int | Base BaseUnit

%if False

> deriving instance Eq Kind
> deriving instance Show Kind

> instance Alpha Kind
> instance Subst t Kind

> instance Pretty Kind where
>     pretty Star  = return $ text "*"
>     pretty UN    = return $ text "UN"


> deriving instance Show Type

> infixr 5 `Arr`

> instance Alpha Type
> instance Subst Type Type where
>     isvar (M a)  = Just (SubstName a)
>     isvar (V a)  = Just (SubstName a)
>     isvar _      = Nothing

> instance Eq Type where
>     M x == M y = x == y
>     V x == V y = x == y
>     (t1 `Arr` t2) == (u1 `Arr` u2) = t1 == u1 && t2 == u2
>     Float d == Float e = typeToUnit d == typeToUnit e
>     s == t = unitLike s && unitLike t && typeToUnit s == typeToUnit t

> unitLike :: Type -> Bool
> unitLike (_ `Arr` _)  = False
> unitLike (Float _)    = False
> unitLike _            = True

> instance Pretty Type where
>     pretty (M a)          = braces <$> pretty a
>     pretty (V a)          = brackets <$> pretty a
>     pretty (s `Arr` t)    = parens <$> (between (text "->") <$> pretty s <*> pretty t)
>     pretty (Float t)      = ((text "F" <+>) . parens) <$> pretty t
>     pretty One            = return $ text "1"
>     pretty (s `Times` t)  = between (text "*") <$> pretty s <*> pretty t
>     pretty (t `Pow` k)    = parens <$> (between (text "^") <$> pretty t <*> pretty k)
>     pretty (Base u)       = pretty u

%endif


The set of free metavariables is computed in the obvious way.

> fmvs :: Type -> Set (Name Type)
> fmvs (M alpha)            = Set.singleton alpha
> fmvs (V a)                = Set.empty
> fmvs (tau `Arr` upsilon)  = fmvs tau `union` fmvs upsilon
> fmvs (Float nu)           = fmvs nu
> fmvs One                  = Set.empty
> fmvs (nu `Times` nu')     = fmvs nu `union` fmvs nu'
> fmvs (nu `Pow` _)         = fmvs nu
> fmvs (Base _)             = Set.empty



It is easy to convert a semantic |Unit| to a syntactic expression
|Type|, while the other direction may fail if the type is not
well-kinded.

> unitToType :: Unit -> Type
> unitToType (Unit xs ys)  =        foldr (\ alpha k tau -> (M alpha `Pow` k) `Times` tau) One xs
>                          `Times`  foldr (\ u k tau -> (Base u `Pow` k) `Times` tau) One ys
>
> typeToUnit :: Type -> Unit
> typeToUnit (M alpha)         = metaUnit alpha
> typeToUnit One               = mkUnit [] []
> typeToUnit (nu `Times` nu')  = typeToUnit nu *~ typeToUnit nu'
> typeToUnit (nu `Pow` k)      = typeToUnit nu ^~ k
> typeToUnit (Base b)          = mkUnit [] [(b, 1)]
> typeToUnit _                 = error "typeToUnit: kind error"



Type schemes are defined as in Appendix~\ref{apx:milner}, except that
each $\forall$ quantifier carries a kind.

> data Scheme  =  T Type | All Kind (Bind (Name Type) Scheme)

%if False

> deriving instance Show Scheme

> instance Alpha Scheme
> instance Subst Type Scheme

> instance Eq Scheme where
>     (==) = aeq

> instance Pretty Scheme where
>     pretty (T t)      = pretty t
>     pretty (All k b)  = lunbind b $ \ (a, s) -> do
>                           k' <- pretty k
>                           a' <- pretty a
>                           s' <- pretty s
>                           return $ text "all" <+> a' <+> colon <+> k' <+> text "." <+> s'

%endif


Similarly, contexts are generalised to record the kinds of metavariables:

> type Context  = Bwd Entry
> type Suffix   = [(Name Type, Kind, Decl Type)]
> data Entry    =  E (Name Type) Kind (Decl Type)
>               |  Z (Name Tm) Scheme
>               |  Mark
> data Decl v   =  HOLE |  DEFN v

%if False

> deriving instance Eq Entry

> instance Pretty Entry where
>     pretty (E a k d) = do  a' <- pretty a
>                            k' <- pretty k
>                            d' <- pretty d
>                            return $ a' <+> colon <+> k' <+> text ":=" <+> d'
>     pretty (Z x sc)  = between colon <$> pretty x <*> pretty sc
>     pretty Mark      = return $ text ";"

> deriving instance Eq v => Eq (Decl v)
> deriving instance Show v => Show (Decl v)

> instance Alpha v => Alpha (Decl v)
> instance Subst t v => Subst t (Decl v)

> instance Pretty v => Pretty (Decl v) where
>     pretty HOLE     = return $ text "HOLE"
>     pretty (DEFN t) = pretty t

> (<><) :: Context -> Suffix -> Context
> mcx <>< ((alpha, k, d) : es)  = (mcx :< E alpha k d) <>< es
> mcx <>< []                 = mcx


> data Tm  =  X (Name Tm)
>          |  App Tm Tm 
>          |  Lam (Bind (Name Tm) Tm)
>          |  Let Tm (Bind (Name Tm) Tm)
>   deriving Show

> instance Alpha Tm

> instance Pretty Tm where
>     pretty (X x) = pretty x
>     pretty (f `App` s) = (<+>) <$> pretty f <*> pretty s
>     pretty (Lam b) = lunbind b $ \ (x, t) -> do
>                        x' <- pretty x
>                        t' <- pretty t
>                        return $ text "\\" <+> x' <+> text "." <+> t'
>     pretty (Let s b) = do
>         s' <- pretty s
>         lunbind b $ \ (x, t) -> do
>             x' <- pretty x
>             t' <- pretty t
>             return $ text "let" <+> x' <+> text "=" <+> s' <+> text "in" <+> t'


> newtype Contextual a = Contextual
>     (StateT Context (FreshMT (ErrorT String Identity)) a)

> deriving instance Functor Contextual
> deriving instance Monad Contextual
> deriving instance MonadState Context Contextual
> deriving instance MonadError String Contextual
> deriving instance Fresh Contextual

> runContextual :: Context -> Contextual a -> Either String (a, Context)
> runContextual mcx (Contextual m) = runIdentity . runErrorT . runFreshMT . flip runStateT mcx $ m

> popL        :: Contextual Entry
> popL = do
>     mcx :< e <- get
>     put mcx
>     return e

> find     :: Name Tm -> Contextual Scheme
> find x = get >>= help
>   where
>     help :: Context -> Contextual Scheme
>     help B0 = throwError $ "Out of scope: " ++ show x
>     help (mcx :< Z y sc) | x == y = return sc
>     help (mcx :< _) = help mcx

> inScope  :: Name Tm -> Scheme -> Contextual a -> Contextual a
> inScope x sc m = do
>     modify (:< Z x sc)
>     a <- m
>     modify dropVar
>     return a
>   where
>     dropVar B0 = error "inScope: something went badly wrong"
>     dropVar (mcx :< Z y _) | x == y  = mcx
>     dropVar (mcx :< e)               = dropVar mcx :< e

%endif


The type |Tm| of terms is unchanged from Appendix~\ref{apx:milner}.
Likewise, the |Contextual| monad and |popL|, |find| and |inScope|
operations use the new definition of |Context| but are otherwise
identical.  The |freshMeta| operation is parameterised over the kind
of the metavariable to create:

> freshMeta   :: String -> Kind -> Contextual (Name Type)
> freshMeta a kappa = do  alpha <- fresh (s2n a)
>                         modify (:< E alpha kappa HOLE)
>                         return alpha

\clearpage

The unification algorithm must searching the context for metavariable
declarations (perhaps of a particular kind), make some changes and
either choose to |restore| the existing declaration or |replace| it
with a new one.  As before, the |onTop| function captures this
pattern, and it is used to implement |onTopTY| and |onTopUN| that look
for a metavariable of the corresponding kind.

> data Extension = Restore | Replace Suffix
>
> restore :: Contextual Extension
> restore = return Restore
>
> replace :: Suffix -> Contextual Extension
> replace = return `o` Replace
>
> onTop ::  (Name Type -> Kind -> Decl Type -> Contextual Extension) ->
>               Contextual ()
> onTop f = popL >>= \ e -> case e of
>         E alpha kappa d  ->  f alpha kappa d >>= \ m -> case m of
>                                  Replace _Xi  -> modify (<>< _Xi)
>                                  Restore      -> modify (:< e)
>         _                -> onTop f >> modify (:< e)

> onTopTY ::  (Name Type -> Decl Type -> Contextual Extension) ->
>                 Contextual ()
> onTopTY f = onTop $ \ alpha kappa d -> case kappa of
>         Star  -> f alpha d
>         UN    -> onTopTY f >> restore
>
> onTopUN ::  (Name Type -> Decl Type -> Contextual Extension) ->
>                 Contextual ()
> onTopUN f = onTop $ \ alpha kappa d -> case kappa of
>         UN    -> f alpha d
>         Star  -> onTopUN f >> restore


%if False

> $(derive[''Decl, ''Type, ''Tm, ''Scheme, ''Kind])

%endif