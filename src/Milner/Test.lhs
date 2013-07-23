> module Milner.Test where

> import Common.BwdFwd
> import Common.Names
> import Common.PrettyPrint

> import Milner.Type
> import Milner.Unify
> import Milner.Infer
> import Milner.Zipper

> findIt :: Context -> Name Type -> Decl Type
> findIt B0            x           = error $ "findIt: missing " ++ show x
> findIt (_ :< E y o)  x | x == y  = o
> findIt (c :< _)      x           = findIt c x


The |normalise| function returns the normal form (i.e.\ with all type
variables expanded as far as possible) of the given type within the
given context.

> normalise :: Context -> Type -> Type
> normalise _Gamma tau = normalStep (normaliseContext B0 (fwd _Gamma)) tau
>     where
>         normalStep :: Context -> Type -> Type
>         normalStep c (M x) = case findIt c x of
>                                  HOLE    -> M x
>                                  DEFN t  -> t
>         normalStep _ (V x)          = V x
>         normalStep c (s `Arr` t)    = normalStep c s `Arr` normalStep c t
>
>         normaliseContext :: Context -> [Entry] -> Context
>         normaliseContext c [] = c
>         normaliseContext c (E x (DEFN t) : es) = 
>             normaliseContext (c :< E x (DEFN (normalStep c t))) es
>         normaliseContext c (e : es) = normaliseContext (c :< e) es


We implement a bunch of unit tests, which allow the algorithms to be
tested with

> milner :: IO ()
> milner = mapM_ putStrLn $
>     map unifyTest unifyTests
>     ++ map (inferTest (fmap ((,) ()) . infer) . ins B0) inferTests
>     ++ map (inferTest elab . ins B0) inferTests
>   where ins c (a, b) = (a, b, c)


Note that equality of normalised types is syntactic (it does not
perform renaming) so changing the algorithm may sometimes cause
spurious failures as the fresh variable numbers may be different.

> unifyTest :: (Type, Type, Context, Maybe Context) -> String
> unifyTest (sigma, tau, c0, mc) = case (runContextual c0 (unify sigma tau), mc) of
>     (Right ((), c1), Just c2)
>         | c1 == c2   -> unlines ["OKAY: unified " ++ pp sigma ++ " and " ++ pp tau, "in context " ++ pp c0, "giving " ++ pp c1]
>         | otherwise  -> unlines ["FAIL: unexpected result context", 
>                                  pp c1, "not", pp c2, "when unifying",
>                                  pp sigma, "with", pp tau]
>     (Right ((), c1), Nothing) -> unlines ["FAIL: unexpected success with", pp c1,
>                                                 "when unifying", pp sigma, "with", pp tau]
>     (Left s, Nothing)  -> unlines ["OKAY: " ++ s, "when unifying " ++ pp sigma ++ " and " ++ pp tau, "in context " ++ pp c0]
>     (Left s, Just _)   -> unlines ["FAIL: " ++ s, "when unifying " ++ pp sigma ++ " and " ++ pp tau]

> inferTest ::  Pretty a => (Tm -> Contextual (a, Type)) -> 
>               (Tm, Maybe Type, Bwd (Name Tm, Scheme)) -> String
> inferTest f (t, expected, p) = case (runContextual B0 (inScopes p $ f t), expected) of
>     (Right ((a, tau), mcx), Just sigma)
>         | sigma == normalise mcx tau -> unlines ["OKAY: " ++ pp t, "has type " ++ pp tau, "in context " ++ pp mcx, "with annotation " ++ pp a]
>         | otherwise -> unlines ["FAIL: unexpected result type",
>                                 show (normalise mcx tau), "not", show sigma,
>                                        "when inferring", pp t,
>                                        "in", pp mcx]
>     (Right (tau, c), Nothing) -> unlines ["FAIL: unexpected success: inferring type of", pp t, "under parameters", pp p, "succeeded with type", pp tau, "and context", pp c]
>     (Left s, Nothing)   -> unlines ["OKAY: " ++ s, "when inferring " ++ pp t]
>     (Left s, Just tau)  -> unlines ["FAIL: " ++ s, "Term " ++ pp t ++ " should have type",pp tau]

> (*=) :: Name Type -> Decl Type -> Entry
> alpha *= d = E alpha d

> unifyTests :: [(Type, Type, Context, Maybe Context)]
> unifyTests = [
>     (M (s2n "a"), M (s2n "b"),
>         B0 :< ((s2n "a") *= HOLE) :< ((s2n "b") *= HOLE),
>         Just (B0 :< (s2n "a") *= HOLE :< (s2n "b") *= DEFN (M (s2n "a")))),
>     (M (s2n "a"), M (s2n "b") `Arr` M (s2n "c"), 
>         B0 :< (s2n "a") *= HOLE :< (s2n "b") *= HOLE :< s2n "c" *= HOLE,
>         Just (B0 :< (s2n "b") *= HOLE :< s2n "c" *= HOLE :< (s2n "a") *= DEFN (M (s2n "b") `Arr` M (s2n "c")))),
>     (M (s2n "a"), M (s2n "b") `Arr` M (s2n "c"),
>         B0 :< (s2n "a") *= HOLE :< s2n "c" *= DEFN (M (s2n "a")) :< (s2n "b") *= DEFN (M (s2n "a")),
>         Nothing),
>     (M (s2n "a") `Arr` M (s2n "a"), M (s2n "b") `Arr` M (s2n "b"),
>         B0 :< (s2n "b") *= HOLE :< (s2n "a") *= HOLE,
>         Just (B0 :< (s2n "b") *= HOLE :< (s2n "a") *= DEFN (M (s2n "b")))),
>     (M (s2n "a"), M (s2n "b") `Arr` M (s2n "c"),
>        B0 :< (s2n "b") *= HOLE :< (s2n "a") *= DEFN (M (s2n "b") `Arr` M (s2n "b")) :< s2n "c" *= HOLE,
>        Just (B0 :< (s2n "b") *= HOLE :< s2n "c" *= DEFN (M (s2n "b")) :< (s2n "a") *= DEFN (M (s2n "b") `Arr` M (s2n "b")))),
>     (M (s2n "a") `Arr` M (s2n "b"), M (s2n "b") `Arr` M (s2n "a"),
>        B0 :< (s2n "a") *= HOLE :< (s2n "b") *= HOLE,
>        Just (B0 :< (s2n "a") *= HOLE :< (s2n "b") *= DEFN (M (s2n "a")))),
>     (M (s2n "a") `Arr` M (s2n "b") `Arr` M (s2n "c"), M (s2n "b") `Arr` M (s2n "a") `Arr` M (s2n "a"),
>        B0 :< s2n "c" *= HOLE :< (s2n "a") *= HOLE :< (s2n "b") *= HOLE,
>        Just (B0 :< s2n "c" *= HOLE :< (s2n "a") *= DEFN (M (s2n "c")) :< (s2n "b") *= DEFN (M (s2n "a"))))
>     ]


> var :: String -> Tm
> var = X . s2n

> lam :: String -> Tm -> Tm
> lam x t = Lam (bind (s2n x) t)

> letIn :: String -> Tm -> Tm -> Tm
> letIn x s t = Let s (bind (s2n x) t)


> alphas, betas :: [Name Type]
> Right (alphas, _) = runContextual B0 (mapM (const (freshMeta "alpha")) ([1..10] :: [Integer]))
> Right (betas, _) = runContextual B0 (mapM (const (freshMeta "beta")) ([1..10] :: [Integer]))


> inferTests :: [(Tm, Maybe Type)]
> inferTests = [
>     (var "u", 
>          Nothing),
>     (lam "x" (var "x"),
>          Just (M (alphas !! 1) `Arr` M (alphas !! 1))),
>     (lam "x" (var "x" `App` var "x"),
>          Nothing),
>     (lam "x" (lam "y" (var "x" `App` var "x")),
>          Nothing),
>     (lam "x" (lam "y" (var "y")),
>          Just (M (alphas !! 1) `Arr` M (alphas !! 3) `Arr` M (alphas !! 3))),
>     (lam "x" (lam "y" (var "x")),
>          Just (M (alphas !! 1) `Arr` M (alphas !! 3) `Arr` M (alphas !! 1))),
>     (lam "x" (lam "y" (var "y") `App` var "x"),
>          Just (M (alphas !! 1) `Arr` M (alphas !! 1))),
>     (lam "x" (lam "y" (var "x") `App` var "x"),
>          Just (M (alphas !! 1) `Arr` M (alphas !! 1))),
>     (letIn "m" (lam "a" (var "a")) (var "m" `App` var "m"),
>          Just (M (alphas !! 4) `Arr` M (alphas !! 4))),
>     (letIn "s" (letIn "m" (lam "a" (var "a")) (var "m" `App` var "m")) (var "s"), 
>          Just (M (alphas !! 7) `Arr` M (alphas !! 7))),
>     (lam "x" (lam "y" (var "x")),
>          Just (M (alphas !! 1) `Arr` (M (alphas !! 3) `Arr` M (alphas !! 1)))),
>     (lam "x" (lam "y" (var "x" `App` var "y")),
>          Just ((M (alphas !! 3) `Arr` M (betas !! 4)) `Arr` (M (alphas !! 3) `Arr` M (betas !! 4)))),
>     (letIn "I" (lam "x" (var "x")) (var "I"),
>          Just (M (alphas !! 3) `Arr` M (alphas !! 3)))
>   ]