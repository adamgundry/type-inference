> {-# LANGUAGE FlexibleContexts #-}

> module Common.PrettyPrint (Size(..), prettyAt, prettyLow, prettyHigh,
>                     wrapDoc, runPretty, pp, ppWith, lubpretty, Pretty(..),
>                     between, commaSep, semiSep, angles, prettyVert,
>                     module Text.PrettyPrint.HughesPJ) where

> import Control.Applicative
> import Control.Monad.Reader
> import Data.Foldable
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Text.PrettyPrint.HughesPJ hiding (($$))

> import Common.BwdFwd
> import Common.Names


> data Size = ArgSize | AppSize | PiSize | LamSize
>     deriving (Bounded, Enum, Eq, Ord, Show)

> prettyAt ::
>     (Pretty a, Applicative m, LFresh m, MonadReader Size m) => Size -> a -> m Doc
> prettyAt sz = local (const sz) . pretty

> prettyLow, prettyHigh ::
>     (Pretty a, Applicative m, LFresh m, MonadReader Size m) => a -> m Doc
> prettyLow   a = prettyAt minBound a
> prettyHigh  a = prettyAt maxBound a

> wrapDoc :: MonadReader Size m => Size -> m Doc -> m Doc
> wrapDoc dSize md = do
>     d <- md
>     curSize <- ask
>     return $ if dSize > curSize then parens d else d

> runPretty :: ReaderT Size LFreshM a -> a
> runPretty = runLFreshM . flip runReaderT maxBound

> pp :: Pretty a => a -> String
> pp = render . runPretty . pretty

> ppWith :: (a -> ReaderT Size LFreshM Doc) -> a -> String
> ppWith f = render . runPretty . f

> lubpretty :: (Applicative m, LFresh m, MonadReader Size m, Pretty a, Pretty t, Alpha t, Alpha a) => Size -> Bind a t -> (Doc -> Doc -> m Doc) -> m Doc
> lubpretty sz b f = lunbind b $ \ (x, v) -> do
>                      x' <- pretty x
>                      v' <- prettyAt sz v
>                      f x' v'

> class Pretty a where
>     pretty :: (Applicative m, LFresh m, MonadReader Size m) => a -> m Doc

> instance Pretty Int where
>     pretty = return . text . show

> instance Pretty Integer where
>     pretty = return . text . show

> instance Pretty (Name x) where
>     pretty = return . text . show

> instance Pretty a => Pretty [a] where
>     pretty xs = commaSep <$> mapM pretty xs

> instance Pretty a => Pretty (Bwd a) where
>     pretty xs = pretty (fwd xs)

> instance (Pretty a, Pretty b) => Pretty (Either a b) where
>     pretty (Left x)   = (text "Left" <+>) <$> pretty x
>     pretty (Right y)  = (text "Right" <+>) <$> pretty y

> instance Pretty a => Pretty (Maybe a) where
>     pretty Nothing   = return $ text "Nothing"
>     pretty (Just x)  = pretty x 

> instance (Pretty a, Pretty b) => Pretty (a, b) where
>     pretty (a, b) = parens <$> (between comma <$> pretty a <*> pretty b)

> instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
>     pretty (a, b, c) = do
>         a' <- pretty a
>         b' <- pretty b
>         c' <- pretty c
>         return $ parens $ a' <> comma <+> b' <> comma <+> c'

> instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where
>     pretty (a, b, c, d) = do
>         a' <- pretty a
>         b' <- pretty b
>         c' <- pretty c
>         d' <- pretty d
>         return $ parens $ a' <> comma <+> b' <> comma <+> c' <> comma <+> d'


> instance Pretty () where
>     pretty () = return $ text "()"

> instance (Pretty a, Pretty b) => Pretty (Map a b) where
>     pretty m = do
>         xs <- mapM pretty $ Map.toList m
>         return $ braces $ commaSep xs

> between :: Doc -> Doc -> Doc -> Doc
> between d x y = x <+> d <+> y

> commaSep :: [Doc] -> Doc
> commaSep = hsep . punctuate comma

> semiSep :: [Doc] -> Doc
> semiSep = hsep . punctuate semi

> angles :: Doc -> Doc
> angles d = text "<" <> d <> text ">"

> prettyVert :: (Pretty a, Applicative m, LFresh m, MonadReader Size m, Foldable f) => f a -> m Doc
> prettyVert xs = vcat <$> mapM pretty (toList xs)