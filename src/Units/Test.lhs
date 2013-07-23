> module Units.Test where

> import Common.BwdFwd
> import Common.Names
> import Common.PrettyPrint
> import Units.Group
> import Units.Type
> import Units.Unify
> import Units.Infer


> type Param        = (Name Tm, Scheme)
> type Params       = Bwd Param

> inScopes :: Params -> Contextual a -> Contextual a
> inScopes B0 m = m
> inScopes (_Gam :< (x, sc)) m = inScopes _Gam (inScope x sc m)



> findIt :: Context -> Name Type -> Decl Type
> findIt B0              x           = error $ "findIt: missing " ++ show x
> findIt (_ :< E y _ d)  x | x == y  = d
> findIt (c :< _)        x           = findIt c x


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
>         normalStep c (Float t)      = Float (normalStep c t)
>         normalStep _ One            = One
>         normalStep c (s `Times` t)  = normalStep c s `Times` normalStep c t
>         normalStep c (Pow t k)      = Pow (normalStep c t) k
>         normalStep _ (Base u)       = Base u

>
>         normaliseContext :: Context -> [Entry] -> Context
>         normaliseContext c [] = c
>         normaliseContext c (E x ki (DEFN t) : es) = 
>             normaliseContext (c :< E x ki (DEFN (normalStep c t))) es
>         normaliseContext c (e : es) = normaliseContext (c :< e) es

> normaliseCx :: Context -> Context
> normaliseCx B0 = B0
> normaliseCx (_Gam :< E a k HOLE) = normaliseCx _Gam :< E a k HOLE
> normaliseCx (_Gam :< E a k (DEFN v)) = normaliseCx _Gam :< E a k (DEFN (normalise _Gam v))
> normaliseCx (_Gam :< Z x s) = normaliseCx _Gam :< Z x s
> normaliseCx (_Gam :< Mark) = normaliseCx _Gam :< Mark


We implement a bunch of unit tests, which allow the algorithms to be
tested with

> units :: IO ()
> units = mapM_ putStrLn $
>     map unifyTest unifyTests
>     ++ map (inferTest . ins B0) inferTests
>     ++ map (inferTest . ins floatParams) inferFloatTests
>   where ins c (a, b) = (a, b, c)

Note that equality of normalised types is syntactic (it does not
perform renaming) so changing the algorithm may sometimes cause
spurious failures as the fresh variable numbers may be different.

> unifyTest :: (Type, Type, Context, Maybe Context) -> String
> unifyTest (sigma, tau, c0, mc) = case (runContextual c0 (unify sigma tau), mc) of
>     (Right ((), c1), Just c2)
>         | normaliseCx c1 == normaliseCx c2   -> "OKAY"
>         | otherwise  -> unlines ["FAIL: unexpected result context", 
>                                  pp (normaliseCx c1), "not", pp (normaliseCx c2), "when unifying",
>                                  pp sigma, "with", pp tau]
>     (Right ((), c1), Nothing) -> unlines ["FAIL: unexpected success with", pp c1,
>                                                 "when unifying", pp sigma, "with", pp tau]
>     (Left s, Nothing)  -> "OKAY (" ++ s ++ ")"
>     (Left s, Just _)   -> "FAIL (" ++ s ++ ") " ++ pp sigma ++ " /= " ++ pp tau

> inferTest :: (Tm, Maybe Type, Params) -> String
> inferTest (t, expected, p) = case (runContextual B0 (inScopes p $ infer t), expected) of
>     (Right (tau, c), Just sigma)
>         | sigma == normalise c tau -> "OKAY"
>         | otherwise -> unlines ["FAIL: unexpected result type",
>                                 pp (normalise c tau), "not", pp sigma,
>                                        "when inferring", pp t,
>                                        "in", pp c]
>     (Right (tau, c), Nothing) -> unlines ["FAIL: unexpected success: inferring type of", pp t, "under parameters", pp p, "succeeded with type", pp tau, "and context", pp c]
>     (Left s, Nothing)   -> "OKAY (" ++ s ++ ")"
>     (Left s, Just tau)  -> "FAIL (" ++ s ++ "): " ++ pp t ++ " should have type " ++ pp tau




> (*=) :: Name Type -> Decl Type -> Entry
> alpha *= d = E alpha Star d

> (#=) :: Name Type -> Decl Type -> Entry
> alpha #= d = E alpha UN d

> gexp :: [(Name Type, Int)] -> [(BaseUnit, Int)] -> Type
> gexp xs ys = unitToType (mkUnit xs ys)

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
>        Just (B0 :< s2n "c" *= HOLE :< (s2n "a") *= DEFN (M (s2n "c")) :< (s2n "b") *= DEFN (M (s2n "a")))),
>     (Float (gexp [] []), Float (gexp [] []),
>         B0,
>         Just B0),
>     (Float (gexp [] [(SEC, 1)]), Float (gexp [] [(SEC, 1)]),
>         B0,
>         Just B0),
>     (Float (gexp [] [(SEC, 1)]), Float (gexp [] []),
>         B0,
>         Nothing),
>     (Float (gexp [(s2n "m", 1)] []), Float (gexp [(s2n "m", 1)] []),
>         B0 :< s2n "m" #= HOLE,
>         Just (B0 :< s2n "m" #= HOLE)),
>     (Float (gexp [(s2n "m", 1)] []), Float (gexp [] [(SEC, 2)]),
>         B0 :< s2n "m" #= HOLE,
>         Just (B0 :< s2n "m" #= DEFN (gexp [] [(SEC, 2)]))),
>     (Float (gexp [(s2n "m", 1)] [(SEC, 3)]), Float (gexp [] [(SEC, 2)]),
>         B0 :< (s2n "m" #= HOLE),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -1)])))),
>     (Float (gexp [(s2n "m", 1)] [(KG, -1), (SEC, 3)]), Float (gexp [] [(SEC, 2)]),
>         B0 :< (s2n "m" #= HOLE),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -1), (KG, 1)])))),
>     (Float (gexp [(s2n "m", 1)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [])))),
>     (Float (gexp [(s2n "m", 2)] []), Float (gexp [] [(METRE, 2)]),
>         B0 :< (s2n "m" #= HOLE),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(METRE, 1)])))),
>     (Float (gexp [(s2n "m", 2)] [(SEC, 4), (KG, 6)]), Float (gexp [] [(METRE, 2)]),
>         B0 :< (s2n "m" #= HOLE),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(METRE, 1), (KG, -3), (SEC, -2)])))),
>     (Float (gexp [(s2n "m", 2)] [(SEC, 1)]), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE),
>         Nothing),
>     (Float (gexp [(s2n "m", 1), (s2n "n", 1)] []), Float (gexp [(s2n "n", 2)] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE),
>         Just (B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= DEFN (gexp [(s2n "m", 1)] [])))),
>     (Float (gexp [(s2n "m", 1)] []), Float (gexp [] [(METRE, 1), (SEC, -2)]),
>         B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -2), (METRE, 1)])),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -2), (METRE, 1)])))),
>     (Float (gexp [(s2n "m", 1), (s2n "n", 2)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE),
>         Just (B0 :< (s2n "n" #= HOLE) :< (s2n "m" #= DEFN (gexp [(s2n "n", -2)] [])))),
>     (Float (gexp [(s2n "m", 2), (s2n "n", 3)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE),
>         Just (B0 :< (s2n "beta" #= HOLE) :< (s2n "n" #= DEFN (gexp [(s2n "beta", -2)] [])) :< (s2n "m" #= DEFN (gexp [(s2n "beta", 1), (s2n "n", -1)] [])))),
>     (Float (gexp [(s2n "m", 2), (s2n "n", 3)] [(KG, 6)]), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE),
>         Just (B0 :< (s2n "beta" #= HOLE) :< (s2n "n" #= DEFN (gexp [(s2n "beta", -2)] [])) :< (s2n "m" #= DEFN (gexp [(s2n "beta", 1), (s2n "n", -1)] [(KG, -3)])))),
>     (Float (gexp [(s2n "m", 1)] [(SEC, 1)]), Float (gexp [] []),
>         B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -1)])),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -1)])))),
>     (Float (gexp [(s2n "m", 1), (s2n "n", 2)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= DEFN (gexp [] [(SEC, 1)])),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -2)])) :< (s2n "n" #= DEFN (gexp [] [(SEC, 1)])))),
>     (Float (gexp [(s2n "m", 2), (s2n "n", 1)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= DEFN (gexp [] [(SEC, 1)])),
>         Nothing),
>     (Float (gexp [(s2n "m", 2), (s2n "n", 1)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= DEFN (gexp [] [(SEC, 2)])),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [(SEC, -1)])) :< (s2n "n" #= DEFN (gexp [] [(SEC, 2)])))),
>     (Float (gexp [(s2n "m", 3), (s2n "k", 2)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE) :< (s2n "k" #= DEFN (gexp [(s2n "n", 1)] [])),
>         Just (B0 :< (s2n "beta" #= HOLE) :< (s2n "m" #= DEFN (gexp [(s2n "beta",-2)] [])) :< (s2n "n" #= DEFN (gexp [(s2n "m",-1),(s2n "beta",1)] [])) :< (s2n "k" #= DEFN (gexp [(s2n "n",1)] [])))),
>     (Float (gexp [(s2n "m", 1), (s2n "k", 2)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE) :< (s2n "k" #= DEFN (gexp [(s2n "n", 1)] [])),
>         Just (B0 :< (s2n "n" #= HOLE) :< (s2n "m" #= DEFN (gexp [(s2n "n", -2)] [])) :< (s2n "k" #= DEFN (gexp [(s2n "n", 1)] [])))),
>     (Float (gexp [(s2n "m", 1), (s2n "n", 2)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= DEFN (gexp [(s2n "m", 1)] [])),
>         Just (B0 :< (s2n "m" #= DEFN (gexp [] [])) :< (s2n "n" #= DEFN (gexp [(s2n "m", 1)] [])))),
>     (Float (gexp [(s2n "m", 1), (s2n "n", 2), (s2n "k", 3)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE) :< (s2n "k" #= HOLE),
>         Just (B0 :< (s2n "m" #= HOLE) :< (s2n "beta" #= HOLE) :< (s2n "k" #= DEFN (gexp [(s2n "m", -1), (s2n "beta", -2)] [])) :< (s2n "n" #= DEFN (gexp [(s2n "beta", 1), (s2n "k", -1)] [])))),
>     (Float (gexp [(s2n "m", 1), (s2n "n", 2), (s2n "k", 2)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE) :< (s2n "k" #= HOLE),
>         Just (B0 :< (s2n "beta" #= HOLE) :< (s2n "m" #= DEFN (gexp [(s2n "beta", -2)] [])) :< (s2n "n" #= HOLE) :< (s2n "k" #= DEFN (gexp [(s2n "beta", 1), (s2n "n", -1)] [])))),
>     (Float (gexp [] []), (Float (gexp [] []) `Arr` Float (gexp [] [])),
>         B0,
>         Nothing),
>     (Float (gexp [(s2n "m", 1), (s2n "n", -3)] []), Float (gexp [] []),
>         B0 :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE),
>         Just (B0 :< (s2n "n" #= HOLE) :< (s2n "m" #= DEFN (gexp [(s2n "n", 3)] [])))),
>     (M (s2n "x"), M (s2n "y") `Arr` M (s2n "y"), 
>         B0 :< (s2n "x") *= HOLE :< Mark :< (s2n "n" #= HOLE) :< (s2n "m" #= HOLE)
>              :< (s2n "y") *= DEFN (Float (gexp [(s2n "n", 1), (s2n "m", 1)] [])),
>         Just (B0 :< (s2n "beta") #= HOLE :< beta1 #= (DEFN (M (s2n "beta"))) :< (s2n "x") *= (DEFN ((Float (gexp [(s2n "beta",1)] [])) `Arr` (Float (gexp [(s2n "beta",1)] [])))) :< Mark :< s2n "n" #= HOLE :< s2n "m" #= (DEFN (gexp [(s2n "beta",1),(s2n "n",-1)] [])) :< (s2n "y") *= (DEFN (Float (gexp [(s2n "beta",1)] []))))),
>     (M (s2n "x"), Float (gexp [(s2n "beta", 1)] []),
>         B0 :< (s2n "x") *= HOLE :< Mark :< (s2n "m" #= HOLE) :< (s2n "n" #= HOLE)
>             :< (s2n "beta" #= DEFN (gexp [(s2n "m", 1), (s2n "n", 1)] [])),
>         Just (B0 :< (s2n "beta") #= HOLE
>                  :< (s2n "x") *= (DEFN (Float (gexp [(s2n "beta",1)] []))) :< Mark
>                  :< s2n "m" #= HOLE
>                  :< s2n "n" #= HOLE
>                  :< s2n "beta" #= (DEFN (gexp [(s2n "n",1),(s2n "m",1)] []))))
>     ]



> allBind :: String -> Kind -> Scheme -> Scheme
> allBind x ki s = All ki (metaBind (s2n x) s)

> var :: String -> Tm
> var = X . s2n

> lam :: String -> Tm -> Tm
> lam x t = Lam (bind (s2n x) t)

> letIn :: String -> Tm -> Tm -> Tm
> letIn x s t = Let s (bind (s2n x) t)



> alphas, betas :: [Name Type]
> Right (alphas, _) = runContextual B0 (mapM (const (freshMeta "alpha" Star)) ([1..10] :: [Integer]))
> Right (betas, _) = runContextual B0 (mapM (const (freshMeta "beta" Star)) ([1..10] :: [Integer]))

> beta1 = betas !! 1


> inferTests :: [(Tm, Maybe Type)]
> inferTests = [
>     (var "u", 
>          Nothing),
>     (lam "x" (var "x"),
>          Just (M (alphas !! 0) `Arr` M (alphas !! 0))),
>     (lam "x" (var "x" `App` var "x"),
>          Nothing),
>     (lam "x" (lam "y" (var "y")),
>          Just (M (alphas !! 0) `Arr` M (alphas !! 2) `Arr` M (alphas !! 2))),
>     (lam "x" (lam "y" (var "x")),
>          Just (M (alphas !! 0) `Arr` M (alphas !! 2) `Arr` M (alphas !! 0))),
>     (lam "x" (lam "y" (var "y") `App` var "x"),
>          Just (M (s2n "alpha") `Arr` M (s2n "alpha"))),
>     (lam "x" (lam "y" (var "x") `App` var "x"),
>          Just (M (s2n "alpha") `Arr` M (s2n "alpha"))),
>     (letIn "m" (lam "a" (var "a")) (var "m" `App` var "m"),
>          Just (M (alphas !! 4) `Arr` M (alphas !! 4))),
>     (letIn "s" (letIn "m" (lam "a" (var "a")) (var "m" `App` var "m")) (var "s"), 
>          Just (M (alphas !! 7) `Arr` M (alphas !! 7))),
>     (lam "x" (lam "y" (var "x")),
>          Just (M (alphas !! 0) `Arr` (M (alphas !! 2) `Arr` M (alphas !! 0)))),
>     (lam "x" (lam "y" (var "x" `App` var "y")),
>          Just ((M (alphas !! 2) `Arr` M (betas !! 4)) `Arr` (M (alphas !! 2) `Arr` M (betas !! 4)))),
>     (letIn "I" (lam "x" (var "x")) (var "I"),
>          Just (M (alphas !! 3) `Arr` M (alphas !! 3)))
>   ]

> floatParams :: Params
> floatParams = B0
>   :< (s2n "zero", allBind "x" UN (T (Float (gexp [(s2n "x", 1)] []))))
>   :< (s2n "one", T (Float (gexp [] [])))
>   :< (s2n "mass", T (Float (gexp [] [(KG, 1)])))
>   :< (s2n "time", T (Float (gexp [] [(SEC, 1)])))
>   :< (s2n "times", allBind "a" UN (allBind "b" UN (T (Float (gexp [(s2n "a", 1)] []) `Arr` Float (gexp [(s2n "b", 1)] []) `Arr` Float (gexp [(s2n "a", 1), (s2n "b", 1)] [])))))
>   :< (s2n "plus", allBind "a" UN (T (Float (gexp [(s2n "a", 1)] []) `Arr` Float (gexp [(s2n "a", 1)] []) `Arr` Float (gexp [(s2n "a", 1)] []))))
>   :< (s2n "sect", T (Float (gexp [] [(SEC, 2)]) `Arr` Float (gexp [] [(SEC, 3)])))
>   :< (s2n "div", allBind "a" UN (allBind "b" UN (T (Float (gexp [(s2n "b", 1), (s2n "a", 1)] []) `Arr` Float (gexp [(s2n "a", 1)] []) `Arr` Float (gexp [(s2n "b", 1)] [])))))
>   :< (s2n "pair", allBind "a" Star (allBind "b" Star (T (M (s2n "a") `Arr` M (s2n "b") `Arr` M (s2n "a") `Arr` M (s2n "b")))))

> inferFloatTests :: [(Tm, Maybe Type)]
> inferFloatTests = [
>     (var "zero",
>        Just (Float (M (s2n "x")))),
>     (var "times" `App` var "mass" `App` var "mass",
>        Just (Float (gexp [] [(KG, 2)]))),
>     (var "times" `App` (var "sect" `App` var "zero") `App` var "mass",
>        Just (Float (gexp [] [(SEC, 3), (KG, 1)]))), 
>     (lam "a" (lam "b" (var "plus" `App` var "a" `App` var "b")),
>        Just (Float (gexp [(betas !! 6, 1)] []) `Arr` Float (gexp [(betas !! 6, 1)] []) `Arr` Float (gexp [(betas !! 6, 1)] []))),
>     (lam "x" (letIn "d" (var "div" `App` var "x") (var "pair" `App` (var "d" `App` var "mass") `App` (var "d" `App` var "time"))),
>        Just (Float (gexp [(betas !! 5, 1)] []) `Arr` Float (gexp [(betas !! 5, 1)] [(KG, -1)]) `Arr` Float (gexp [(betas !! 5, 1)] [(SEC, -1)]))),
>     (letIn "recip" (var "div" `App` var "one") (var "pair" `App` (var "recip" `App` var "mass") `App` (var "recip" `App` var "time")),
>        Just (Float (gexp [] [(KG, -1)]) `Arr` Float (gexp [] [(SEC, -1)])))
>   ]
