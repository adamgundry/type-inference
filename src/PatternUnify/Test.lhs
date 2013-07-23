> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
>       FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
>       UndecidableInstances, GeneralizedNewtypeDeriving,
>       TypeSynonymInstances, ScopedTypeVariables #-}

This module defines test cases for the unification algorithm, divided
into those which must succeed, those which should block (possibly
succeeding partially), and those which must fail.

> module PatternUnify.Test where

> import Control.Applicative
> import Data.Foldable (foldMap)

> import Unbound.LocallyNameless

> import Common.BwdFwd
> import Common.PrettyPrint
> import PatternUnify.Tm
> import PatternUnify.Context
> import PatternUnify.Check
> import PatternUnify.Unify

> if' :: String -> Type -> Tm -> Tm -> Tm -> Tm
> if' s b x t f = x %% If (bind (s2n s) b) t f

> if'' :: Type -> Tm -> Tm -> Tm -> Tm
> if'' = if' "_x"

> (&&&) :: Tm -> Tm -> Tm
> x &&& y = if'' BOOL x y FF

> ($$$) :: Tm -> [Tm] -> Tm
> ($$$) = foldl ($$)


> data TestType = Succeed | Stuck | Fail


Allocate a fresh name so the counter starts from 1, to avoid clashing
with s2n (which generates names with index 0):

> initialise :: Contextual ()
> initialise = (fresh (s2n "init") :: Contextual (Name Tm)) >> return ()

The |test| function executes the constraint solving algorithm on the
given metacontext.

> test :: TestType -> [Entry] -> IO ()
> test tt ezs = do
>     putStrLn $ "\n\nInitial context:\n" ++ pp ezs
>     let r = runContextual (bwd ezs) B0 $
>                 (initialise >> many goLeft >> ambulando [] >> validate >> checkHolds (probs ezs))
>     case (r, tt) of
>         (Left err,  Fail)  -> putStrLn $ "OKAY: expected failure:\n" ++ err
>         (Left err,  _)     -> putStrLn $ "FAIL: unexpected failure:\n" ++ err
>         (Right x,   Fail)  -> putStrLn $ "FAIL: unexpected success:\n" ++ showX x
>         (Right x,   Succeed) | succeeded x  -> putStrLn $ "OKAY: succeeded:\n" ++ showX x
>                              | otherwise    -> putStrLn $ "FAIL: did not succeed:\n" ++ showX x
>         (Right x,   Stuck)   | succeeded x  -> putStrLn $ "FAIL: did not get stuck:\n" ++ showX x
>                              | otherwise    -> putStrLn $ "OKAY: stuck:\n" ++ showX x
>   where
>     showX ((), (cxL, [])) = "Final context:\n" ++ pp cxL
>     succeeded ((), (cxL, [])) = not (anyBlocked cxL)
>     probs = foldMap foo 
>     foo (E _ _) = []
>     foo (Q _ p) = [p]

> runTestSolved, runTestStuck, runTestFailed, patternUnify :: IO ()
> runTestSolved = mapM_ (test Succeed) tests
> runTestStuck  = mapM_ (test Stuck) stucks
> runTestFailed = mapM_ (test Fail) fails
> patternUnify = runTestSolved >> runTestStuck >> runTestFailed

> lifted :: Nom -> Type -> [Entry] -> [Entry]
> lifted x _T es = lift [] es
>    where
>      lift :: Subs -> [Entry] -> [Entry]
>      lift g (E a (_A, d) : as)  = E a (_Pi x _T (substs g _A), d) :
>                                          lift ((a, meta a $$ var x) : g) as
>      lift g (Q s p : as)        = Q s (allProb x _T (substs g p)) : lift g as
>      lift _ [] = []

> boy :: String -> Type -> [Entry] -> [Entry]
> boy = lifted . s2n

> gal :: String -> Type -> Entry
> gal x _T = E (s2n x) (_T, HOLE)

> eq :: String -> Type -> Tm -> Type -> Tm -> Entry
> eq x _S s _T t = Q Active $ Unify $ EQN _S s _T t





> tests, stucks, fails :: [[Entry]]
> tests = [ 

>           -- test 0: solve B with A
>           ( gal "A" SET
>           : gal "B" SET
>           : eq "p" SET (mv "A") SET (mv "B")
>           : [])

>           -- test 1: solve B with \ _ . A
>         , ( gal "A" BOOL
>           : gal "B" (BOOL --> BOOL)
>           : boy "x" BOOL 
>             ( eq "p" BOOL (mv "A") BOOL (mv "B" $$ vv "x")
>             : [])
>           )

>           -- test 2: restrict B to second argument
>         , ( gal "A" SET
>           : gal "B" (mv "A" --> mv "A" --> BOOL)
>           : eq "p" (mv "A" --> mv "A" --> BOOL)
>                        (lam (s2n "x") (lam (s2n "y") (mv "B" $$$ [vv "y", vv "x"])))
>                    (mv "A" --> mv "A" --> BOOL)
>                        (lam (s2n "x") (lam (s2n "y") (mv "B" $$$ [vv "x", vv "x"])))
>           : [])

>           -- test 3: X unchanged
>         , [ gal "X" (_PI "A" BOOL (if'' SET (vv "A") BOOL BOOL --> BOOL)) 
>           , eq "p" BOOL (mv "X" $$$ [TT, TT])
>                    BOOL (mv "X" $$$ [TT, TT])
>           ]

>           -- test 4: solve A with BOOL
>         , [ gal "A" SET
>           , eq "p" SET (mv "A") SET BOOL
>           ]

>           -- test 5: solve A with B -> B
>         , [ gal "A" SET
>           , gal "B" SET
>           , gal "C" SET
>           , eq "p" SET (mv "A") SET (mv "B" --> mv "B")
>           ]

>           -- test 6: solve A with \ X . B && X
>         , ( gal "A" (BOOL --> BOOL) 
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A" $$ vv "X") BOOL (mv "B" &&& vv "X")
>             : [])
>           )

>           -- test 7: solve A with \ _ X _ . B X &&& X
>         , ( gal "A" (BOOL --> BOOL --> BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               (eq "p" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                       BOOL (mv "B" $$ vv "X" &&& vv "X")
>               : [])
>             )
>           )

>           -- test 8: solve S with A and T with B
>         , [ gal "A" SET
>           , gal "S" SET
>           , gal "B" (mv "A" --> BOOL)
>           , gal "T" (mv "S" --> BOOL)
>           , eq "p" (mv "A" --> BOOL) (ll "x" (mv "B" $$ vv "x"))
>                    (mv "S" --> BOOL) (ll "x" (mv "T" $$ vv "x"))
>           , eq "q" SET (mv "A") SET (mv "S")
>           ]

>           -- test 9: solve M with \ y . y
>         , [ gal "M" (BOOL --> BOOL)
>           , eq "p" (BOOL --> BOOL) (ll "y" (vv "y"))
>                    (BOOL --> BOOL) (ll "y" (mv "M" $$ vv "y"))
>           ]

>           -- test 10: solve A with \ _ X _ . X &&& X and B with \ X _ _ . X &&& X
>         , ( gal "A" (BOOL --> BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( gal "B" (BOOL --> BOOL)
>               : eq "q" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                        BOOL (mv "B" $$ vv "Y")
>               : eq "p" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                        BOOL (vv "X" &&& vv "X")
>               : [])
>             )
>           )

>           -- test 11: solve A with \ _ y . y
>         , [ gal "A" (_PI "X" BOOL (if'' SET (vv "X") NAT BOOL --> if'' SET (vv "X") NAT BOOL))
>           , eq "p" (_PI "X" BOOL (if'' SET (vv "X") NAT BOOL --> if'' SET (vv "X") NAT BOOL))
>                        (ll "X" (ll "y" (vv "y")))
>                    (_PI "X" BOOL (if'' SET (vv "X") NAT BOOL --> if'' SET (vv "X") NAT BOOL))
>                        (ll "X" (mv "A" $$ vv "X"))
>           ]

>           -- test 12: solve f with \ _ y . y after lifting type
>         , ( gal "f" (_PI "Y" BOOL (if'' SET (vv "Y") NAT BOOL --> if'' SET (vv "Y") NAT BOOL))
>           : boy "X" BOOL
>             ( eq "p" (if'' SET (vv "X") NAT BOOL --> if'' SET (vv "X") NAT BOOL) (ll "y" (vv "y"))
>                      (if'' SET (vv "X") NAT BOOL --> if'' SET (vv "X") NAT BOOL) (mv "f" $$ vv "X")
>             : [])
>           )

>           -- test 13: intersection with nonlinearity, restrict F to first two args
>         , ( gal "F" (BOOL --> BOOL --> BOOL --> BOOL) 
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" BOOL (mv "F" $$$ [vv "X", vv "X", vv "Y"])
>                        BOOL (mv "F" $$$ [vv "X", vv "X", vv "X"])
>               : [])
>             )
>           )

>           -- test 14: heterogeneous equality
>         , [ gal "A" SET
>           , gal "B" SET
>           , eq "q" SET (mv "A") SET (mv "B")
>           , eq "p" (mv "A" --> BOOL) (ll "a" TT)
>                    (mv "B" --> BOOL) (ll "b" TT)
>           ]

>           -- test 15: sigma metavariable; solve A with ((?, TT), ?)
>         , [ gal "A" (_SIG "X" (NAT *: BOOL) (if'' SET (vv "X" %% Tl) NAT BOOL))
>           , eq "p" BOOL TT BOOL (mv "A" %% Hd %% Tl)
>           ]

>           -- test 16: sigma variable; solve A with \ X Y . X &&& Y
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "B" (_SIG "X" BOOL (if'' SET (vv "X") NAT BOOL *: BOOL))
>             ( eq "p" BOOL (mv "A" $$ (vv "B" %% Hd) $$ (vv "B" %% Tl %% Tl))
>                      BOOL ((vv "B" %% Hd) &&& (vv "B" %% Tl %% Tl))
>             : [])
>           )

>           -- test 17: sigma variable; restrict A to \ _ X . ?A' X
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "B" (_SIG "X" BOOL (if'' SET (vv "X") NAT BOOL *: BOOL))
>             ( eq "p" BOOL (mv "A" $$$ [vv "B" %% Hd, vv "B" %% Tl %% Tl])
>                      BOOL (mv "A" $$$ [vv "B" %% Tl %% Tl, vv "B" %% Tl %% Tl])
>             : [])
>           )

>           -- test 18: sigma variable; solve B with \ X z . ?A X (z -)
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : gal "B" (_PI "X" BOOL (NAT *: BOOL --> BOOL))
>           : boy "C" (_SIG "X" BOOL (NAT *: BOOL))
>             ( eq "p" BOOL (mv "A" $$$ [vv "C" %% Hd, vv "C" %% Tl %% Tl])
>                      BOOL (mv "B" $$$ [vv "C" %% Hd, vv "C" %% Tl])
>             : [])
>           )

>           -- test 19: sigma metavariable and equation; solve A
>         , [ gal "A" (_SIG "X" BOOL (if'' SET (vv "X") NAT BOOL))
>           , eq "p" (_SIG "X" BOOL (if'' SET (vv "X") NAT BOOL *: BOOL))
>                        (PAIR (mv "A" %% Hd) (PAIR (mv "A" %% Tl) TT))
>                    (_SIG "X" BOOL (if'' SET (vv "X") NAT BOOL *: BOOL))
>                        (PAIR TT (PAIR (SU ZE) (mv "A" %% Hd)))
>           ]

>           -- test 20: solve A with X ! and a with X -
>         , ( boy "X" (_SIG "Y" BOOL (if'' SET (vv "Y") NAT BOOL))
>             ( gal "A" BOOL
>             : gal "a" (if'' SET (mv "A") NAT BOOL)
>             : eq "p" (_SIG "Y" BOOL (if'' SET (vv "Y") NAT BOOL)) (vv "X")
>                      (_SIG "Y" BOOL (if'' SET (vv "Y") NAT BOOL)) (PAIR (mv "A") (mv "a"))
>             : [])
>           )

>           -- test 21: solve A with f
>         , ( boy "f" (BOOL --> BOOL)
>             ( gal "A" (BOOL --> BOOL)
>             : eq "p" (BOOL --> BOOL) (vv "f")
>                      (BOOL --> BOOL) (ll "x" (mv "A" $$ vv "x"))
>             : [])
>           )

>           -- test 22: solve A with TT
>         , ( boy "X" ((BOOL --> BOOL) *: BOOL)
>             ( gal "A" BOOL
>             : eq "p" BOOL (vv "X" %% Hd $$ TT) BOOL (vv "X" %% Hd $$ mv "A")
>             : [])
>           )

>           -- test 23: solve SS with [S', S']
>         , ( gal "SS" (BOOL *: BOOL)
>           : boy "f" (BOOL --> BOOL --> BOOL)
>             ( eq "p" BOOL (vv "f" $$$ [mv "SS" %% Tl, mv "SS" %% Hd])
>                      BOOL (vv "f" $$$ [mv "SS" %% Hd, mv "SS" %% Tl])
>             : [])
>           )

>           -- test 24: solve A with TT
>         , [ gal "A" BOOL
>           , eq "q" SET (if'' SET (mv "A") NAT BOOL) SET NAT
>           , eq "p" (if'' SET (mv "A") NAT BOOL --> BOOL) (ll "a" (mv "A"))
>                    (NAT --> BOOL) (ll "a" TT)
>           ]

>           -- test 25: fill a gap
>         , ( eq "p" SET (BOOL --> BOOL) SET (BOOL --> BOOL)
>           : [])

>           -- test 26: solve A with \ _ Y . Y
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Z" BOOL      
>               ( eq "p" (if'' SET (mv "A" $$ vv "X" $$ vv "X") BOOL NAT --> BOOL)
>                            (ll "Y" (mv "A" $$ vv "X" $$ vv "Z"))
>                        (if'' SET (vv "X") BOOL NAT --> BOOL)
>                            (ll "Y" (vv "X"))
>               : [])
>             )
>           )

>           -- test 27: solve A with TT
>         , [ gal "A" BOOL
>           , eq "p" ((BOOL --> BOOL) --> BOOL) (ll "X" (vv "X" $$ mv "A"))
>                    ((BOOL --> BOOL) --> BOOL) (ll "X" (vv "X" $$ TT))
>           ]

>           -- test 28: prune and solve A with \ _ . B -> B
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : boy "x" (BOOL *: BOOL)  
>             ( eq "p" BOOL (mv "A" $$ (vv "x" %% Hd))
>                      BOOL (mv "B" $$ TT)
>             : [])
>           )

>           -- test 29: prune A and solve B with A
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" BOOL
>           : eq "p" (BOOL --> BOOL) (ll "X" (mv "A" $$ (vv "X" &&& vv "X")))
>                    (BOOL --> BOOL) (ll "X" (mv "B"))
>           : [])

>           -- test 30: prune A and solve B with A
>         , ( gal "B" BOOL
>           : gal "A" (BOOL --> BOOL)
>           : eq "p" (BOOL --> BOOL) (ll "X" (mv "A" $$ (vv "X" &&& vv "X")))
>                    (BOOL --> BOOL) (ll "X" (mv "B"))
>           : [])

>           -- test 31: solve A with BOOL and f with \ x . x
>         , ( gal "A" SET
>           : gal "f" (mv "A" --> BOOL)
>           : eq "p" (mv "A" --> BOOL) (mv "f")
>                    (mv "A" --> mv "A") (ll "x" (vv "x"))
>           : eq "q" SET (mv "A" --> BOOL) SET (mv "A" --> mv "A")
>           : [])

>           -- test 32: prune B and solve A with f B B 
>         , ( boy "f" (BOOL --> BOOL --> BOOL)
>             ( gal "A" BOOL
>             : gal "B" (BOOL --> BOOL)
>             : eq "p" (BOOL --> BOOL) (ll "Y" (mv "A"))
>                      (BOOL --> BOOL) (ll "X" (vv "f" $$ (mv "B" $$ vv "X")
>                                                      $$ (mv "B" $$ mv "A")))
>             : [])
>           )

>           -- test 33: eta-contract pi
>         , ( gal "A" ((BOOL --> BOOL) --> BOOL)
>           : boy "f" (BOOL --> BOOL)
>             ( eq "p" BOOL (mv "A" $$ (ll "y" (vv "f" $$ vv "y")))
>                      BOOL (vv "f" $$ TT)
>             : [])
>           )

>           -- test 34: eta-contract sigma
>         , ( gal "A" (BOOL *: BOOL --> BOOL)
>           : boy "b" (BOOL *: BOOL)
>             ( eq "p" BOOL (mv "A" $$ (PAIR (vv "b" %% Hd) (vv "b" %% Tl)))
>                      BOOL (vv "b" %% Hd)
>             : [])
>           )

>           -- test 35: eta-contract pi and sigma
>         , ( gal "A" ((BOOL *: BOOL --> BOOL) --> BOOL)
>           : boy "f" (BOOL *: BOOL --> BOOL)
>             ( eq "p" BOOL (mv "A" $$ (ll "b" (vv "f" $$ PAIR (vv "b" %% Hd) (vv "b" %% Tl))))
>                      BOOL (vv "f" $$ PAIR TT FF)
>             : [])
>           )

>           -- test 36: A/P Flattening Sigma-types
>         , ( gal "u" ((BOOL --> BOOL *: BOOL) --> BOOL)
>           : boy "z1" (BOOL --> BOOL)
>             ( boy "z2" (BOOL --> BOOL)
>               ( eq "p" BOOL (mv "u" $$ (ll "x" (PAIR (vv "z1" $$ vv "x") (vv "z2" $$ vv "x"))))
>                        BOOL TT
>               : [])
>             )
>           )

>           -- test 37: A/P Eliminating projections
>         , ( gal "u" ((BOOL --> BOOL) --> BOOL)
>           : boy "y" (BOOL --> BOOL *: BOOL)
>             ( eq "p" BOOL (mv "u" $$ (ll "x" (vv "y" $$ vv "x" %% Hd)))
>                      BOOL (vv "y" $$ TT %% Hd)
>             : [])
>           )

>           -- test 38: prune A and solve B with A
>         , ( gal "B" BOOL
>           : gal "A" (BOOL --> BOOL)
>           : eq "p" (BOOL --> BOOL) (ll "X" (mv "B"))
>                    (BOOL --> BOOL) (ll "X" (mv "A" $$ (vv "X" &&& vv "X")))
>                    
>           : [])

>           -- test 39: solve u with \ _ x . x
>         , ( gal "u" (_PI "v" (_SIG "S" BOOL (if'' SET (vv "S") BOOL NAT *: (if'' SET (vv "S") BOOL NAT --> BOOL)))
>                         (if'' SET (vv "v" %% Tl %% Tl $$ (vv "v" %% Tl %% Hd)) BOOL NAT --> if'' SET (vv "v" %% Tl %% Tl $$ (vv "v" %% Tl %% Hd)) BOOL NAT))
>           : boy "A" BOOL
>             ( boy "a" (if'' SET (vv "A") BOOL NAT)
>               ( boy "f" (if'' SET (vv "A") BOOL NAT --> BOOL)
>                 ( eq "p" (if'' SET (vv "f" $$ vv "a") BOOL NAT --> if'' SET (vv "f" $$ vv "a") BOOL NAT)
>                              (mv "u" $$ PAIR (vv "A") (PAIR (vv "a") (vv "f")))
>                          (if'' SET (vv "f" $$ vv "a") BOOL NAT --> if'' SET (vv "f" $$ vv "a") BOOL NAT)
>                              (ll "x" (vv "x"))
>                 : [])
>               )
>             )
>           )

>           -- test 40: restrict A to second argument
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" (BOOL --> BOOL) (mv "A" $$ vv "X")
>                        (BOOL --> BOOL) (ll "Z" (mv "A" $$ vv "Y" $$ vv "Z"))
>               : [])
>             )
>           )

>           -- test 41: solve A with [ TT , TT ]
>         , ( gal "A" (BOOL *: BOOL)
>           : eq "p" (BOOL *: BOOL) (mv "A")
>                    (BOOL *: BOOL) (PAIR (mv "A" %% Tl) TT)
>           : [])

>           -- test 42
>         , ( gal "T" (BOOL --> BOOL)
>           : gal "A" (_PI "Y" BOOL (if'' SET (mv "T" $$ vv "Y") BOOL NAT --> BOOL))
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( boy "t" (if'' SET (mv "T" $$ vv "X") BOOL NAT)
>               ( eq "p" BOOL (mv "B") BOOL (mv "A" $$ vv "X" $$ vv "t")
>               : [])
>             )
>           )

>           -- test 43
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "F" (BOOL --> BOOL)
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" (BOOL *: BOOL) (PAIR (mv "B") (mv "B"))
>                      (BOOL *: BOOL) (PAIR (mv "A" $$ (mv "F" $$ vv "X")) (mv "A" $$ vv "X"))
>             : [])
>           )

>           -- test 44: false occurrence
>         , ( gal "A" BOOL
>           : gal "B" BOOL
>           : gal "C" SET
>           : eq "p" (mv "C" --> BOOL) (lamK (mv "B"))
>                    (mv "C" --> BOOL) (lamK (mv "A"))
>           : [])

>           -- test 45
>         , ( gal "A" SET
>           : gal "B" (mv "A" --> BOOL)
>           : gal "C" (mv "A" --> BOOL)
>           : boy "x" (mv "A")
>             ( boy "y" (mv "A")
>               ( eq "p" BOOL (mv "B" $$ vv "x")
>                        BOOL (mv "C" $$ vv "x")
>               : [])
>             )
>           )

>           -- test 46: prune p to learn B doesn't depend on its argument
>         , ( gal "A" (BOOL --> BOOL)
>           : boy "Z" BOOL
>             ( gal "B" (BOOL --> BOOL)
>             : gal "C" BOOL
>             : boy "X" BOOL
>               ( boy "Y" BOOL
>                 ( eq "p" BOOL (mv "A" $$ (mv "B" $$ mv "C"))
>                          BOOL (mv "B" $$ vv "Y")
>                 : eq "q" BOOL (mv "B" $$ mv "C") BOOL (vv "Z")
>                 : [])
>               )
>             )
>           )

>           -- test 47
>         , ( gal "A" (_PI "X" BOOL (BOOL --> BOOL))
>           : gal "B" BOOL
>           : boy "Y" BOOL
>             ( boy "y" BOOL
>               ( eq "p" BOOL (mv "B")
>                        BOOL (mv "A" $$ vv "Y" $$ vv "y")
>               : [])
>             )
>           )

>           -- test 48
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" SET
>           : eq "p" SET (mv "B")
>                    SET (_PI "X" BOOL (if'' SET (mv "A" $$ vv "X") BOOL BOOL))
>                    
>           : [])

>           -- test 49: don't prune A too much
>         , ( gal "F" (BOOL --> BOOL --> BOOL)
>           : gal "A" (_PI "X" BOOL (if'' SET (mv "F" $$ TT $$ vv "X") BOOL NAT --> BOOL))
>           : gal "B" (BOOL --> BOOL)
>           : boy "Y" BOOL
>             ( eq "p" (BOOL --> BOOL) (mv "B")
>                      (if'' SET (mv "F" $$ TT $$ vv "Y") BOOL NAT --> BOOL) (mv "A" $$ vv "Y")
>             : boy "y" (if'' SET (mv "F" $$ TT $$ vv "Y") BOOL NAT)
>               ( eq "q" BOOL (mv "F" $$ vv "Y" $$ vv "Y") BOOL TT
>               : eq "r" BOOL (mv "A" $$ vv "Y" $$ vv "y")
>                        (if'' SET (mv "F" $$ TT $$ vv "Y") BOOL NAT) (vv "y")
>               : [])
>             )
>           )

>           -- test 50: Miller's nasty non-pruning example
>         , ( boy "a" BOOL
>             ( gal "X" ((BOOL --> BOOL) --> BOOL --> BOOL)
>             : boy "y" BOOL
>               ( eq "p" BOOL (mv "X" $$ (ll "z" (vv "a")) $$ vv "y")
>                        BOOL (vv "a")
>               : eq "q" ((BOOL --> BOOL) --> BOOL --> BOOL) (mv "X")
>                        ((BOOL --> BOOL) --> BOOL --> BOOL) (ll "z1" (ll "z2" (vv "z1" $$ vv "z2")))
>               : [])
>             )
>           )

>           -- test 51
>         , ( gal "A" (_PI "X" BOOL (_PI "x" BOOL BOOL))
>           : gal "B" SET
>           : eq "p" SET (mv "B")
>                    SET (_PI "X" BOOL (_PI "x" BOOL (if'' SET (mv "A" $$ vv "X" $$ vv "x") BOOL BOOL)))
>           : [])

>           -- test 52
>         , ( gal "b" BOOL
>           : eq "p" BOOL (mv "b") BOOL TT
>           : [])

>           -- test 53
>         , ( gal "b" BOOL
>           : gal "X" (if'' SET (mv "b") BOOL (BOOL --> BOOL))
>           : eq "p" (BOOL --> BOOL) (ll "Y" (vv "Y"))
>                    (if'' SET (mv "b") BOOL (BOOL --> BOOL)) (mv "X")
>           : eq "q" BOOL (mv "b") BOOL FF
>           : [])

>           -- test 54: twins with matching spines
>         , ( gal "A" SET
>           : gal "B" (BOOL --> mv "A" --> BOOL)
>           : gal "S" SET
>           : gal "T" (BOOL --> mv "S" --> BOOL)
>           : eq "p" (_SIG "x" (mv "A") BOOL --> mv "A")
>                         (ll "x" (vv "x" %% Hd))
>                     (_SIG "x" (mv "S") BOOL --> mv "S")
>                         (ll "x" (vv "x" %% Hd))
>           : eq "q" SET (mv "A") SET (mv "S")
>           : [])

>           -- test 55
>         , ( gal "a" BOOL
>           : gal "b" (if'' SET (mv "a") BOOL BOOL)
>           : gal "c" (if'' SET (mv "a") BOOL BOOL)
>           : eq "p" (if'' SET (mv "a") BOOL BOOL) (mv "b")
>                    (if'' SET (mv "a") BOOL BOOL) (mv "c")
>           : [])

>           -- test 56: double meta
>         , [ gal "A" (BOOL --> BOOL)
>           , gal "B" (BOOL --> BOOL)
>           , gal "D" BOOL
>           , gal "C" BOOL
>           , eq "p" BOOL (mv "A" $$ (mv "B" $$ mv "C")) BOOL (mv "D")
>           ]

>           -- test 57: rigid-rigid mismatch disappears after eta (good order)
>         , ( gal "a" BOOL
>           : eq "q" SET (if'' SET (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) SET (BOOL *: BOOL)
>           : boy "X" (if'' SET (mv "a") (BOOL *: BOOL) (BOOL *: BOOL))
>             ( gal "b" BOOL
>             : gal "c" BOOL
>             : eq "r" BOOL (mv "a") BOOL TT
>             : eq "p" (if'' SET (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) (vv "X") (BOOL *: BOOL) (PAIR (mv "b") (mv "c"))
>             : [])
>           )

>           -- test 58: rigid-rigid mismatch disappears after eta (bad order)
>         , ( gal "a" BOOL
>           : eq "q" SET (if'' SET (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) SET (BOOL *: BOOL)
>           : boy "X" (if'' SET (mv "a") (BOOL *: BOOL) (BOOL *: BOOL))
>             ( gal "b" BOOL
>             : gal "c" BOOL
>             : eq "p" (if'' SET (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) (vv "X") (BOOL *: BOOL) (PAIR (mv "b") (mv "c"))
>             : eq "r" BOOL (mv "a") BOOL TT
>             : [])
>           )

>         ]


> stucks = [ 

>           -- stuck 0: nonlinear
>           ( gal "A" (BOOL --> BOOL --> BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                        BOOL (mv "B" $$ vv "Y" &&& vv "X")
>               : [])
>             )
>           )

>           -- stuck 1: nonlinear
>         , ( gal "F" (BOOL --> BOOL --> BOOL) 
>           : gal "G" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "F" $$$ [vv "X", vv "X"])
>                      BOOL (mv "G" $$$ [vv "X", vv "X"])
>             : [])
>           )

>           -- stuck 2: nonlinear
>         , ( gal "f" (BOOL --> BOOL --> BOOL)
>           : boy "x" BOOL
>                 ( eq "p" (BOOL --> BOOL) (ll "y" (mv "f" $$ vv "x" $$ vv "x"))
>                          (BOOL --> BOOL) (ll "y" (vv "x"))
>                 : [])
>            )

>           -- stuck 3: nonlinear
>         , ( gal "B" (BOOL --> BOOL --> BOOL)
>           : gal "A" SET
>           : boy "X" BOOL
>             ( eq "p" (mv "A" --> BOOL) (ll "a" (mv "B" $$ vv "X" $$ vv "X"))
>                      (mv "A" --> BOOL) (ll "a" (vv "X"))
>             : [])
>           )

>           -- stuck 4: solution does not typecheck 
>         , ( gal "A" SET
>           : gal "f" (mv "A" --> BOOL)
>           : eq "p" (mv "A" --> BOOL) (mv "f")
>                    (mv "A" --> mv "A") (ll "x" (vv "x"))
>           : [])

>           -- stuck 5: weak rigid occurrence should not cause failure
>         , ( gal "A" ((NAT --> NAT) --> NAT)
>           : boy "f" (NAT --> NAT)
>             ( eq "p" NAT (mv "A" $$ vv "f")
>                      NAT (SU (vv "f" $$ (mv "A" $$ (ll "X" (vv "X")))))
>             : [])
>           )

>           -- stuck 6: cannot safely prune second argument of B
>         , ( gal "A" BOOL
>           : gal "B" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A")
>                      BOOL (mv "B" $$ mv "A" $$ vv "X")
>             : [])
>           )

>           -- stuck 7 (requires sigma-splitting of twins)
>         , ( gal "A" SET
>           : gal "B" (BOOL --> mv "A" --> BOOL)
>           : gal "S" SET
>           : gal "T" (BOOL --> mv "S" --> BOOL)
>           : eq "p" (_SIG "x" (mv "A") BOOL --> BOOL)
>                         (ll "x" (mv "B" $$ TT $$ (vv "x" %% Hd)))
>                     (_SIG "x" (mv "S") BOOL --> BOOL)
>                         (ll "x" (mv "T" $$ TT $$ (vv "x" %% Hd)))
>           : [])

>           -- stuck 8: awkward occurrence
>         , ( gal "A" SET
>           : gal "a" (mv "A")
>           : gal "f" (mv "A" --> BOOL)
>           : eq "p" SET (mv "A") SET (if'' SET (mv "f" $$ mv "a") NAT BOOL --> BOOL)
>           : [])

>           -- stuck 9
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : gal "a" (if'' SET (mv "A" $$ TT) NAT BOOL)
>           : gal "b" (if'' SET (mv "B" $$ TT) NAT BOOL)
>           : eq "p" (_SIG "x" BOOL (if'' SET (mv "B" $$ vv "x") NAT BOOL))
>                        (PAIR TT (mv "b"))
>                    (if'' SET (mv "A" $$ TT) NAT BOOL)
>                        (mv "a")
>           : eq "q" SET (_SIG "x" BOOL (if'' SET (mv "B" $$ vv "x") NAT BOOL))
>                    SET (if'' SET (mv "A" $$ TT) NAT BOOL)
>           : [])

>           -- stuck 10
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A" $$ (mv "A" $$ vv "X"))
>                      BOOL (mv "B")
>             : [])
>           )

>           -- stuck 11
>         , ( gal "F" (BOOL --> BOOL)
>           : gal "A" (_PI "X" BOOL (if'' SET (mv "F" $$ vv "X") BOOL BOOL))
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" (if'' SET (mv "F" $$ vv "X") BOOL BOOL) (mv "A" $$ vv "X")
>                        (if'' SET (mv "F" $$ vv "Y") BOOL BOOL) (mv "A" $$ vv "Y")
>               : [])
>             )
>           )

>           -- stuck 12
>         , ( gal "B" (BOOL --> BOOL)
>           : gal "F" (if'' SET (mv "B" $$ TT) BOOL BOOL --> BOOL)
>           : eq "p" (if'' SET (mv "B" $$ TT) BOOL BOOL --> BOOL)
>                        (ll "Y" (mv "F" $$ vv "Y"))
>                    (BOOL --> BOOL) 
>                        (ll "Y" (vv "Y"))
>           : [])

>           -- test 54: solve C with A despite B being in the way
>         , ( gal "A" BOOL
>           : gal "C" BOOL
>           : gal "B" (BOOL --> BOOL)
>           : gal "F" (if'' SET (mv "B" $$ TT) BOOL BOOL --> BOOL)
>           : eq "p" (_PI "X" (if'' SET (mv "B" $$ TT) BOOL BOOL) (if'' SET (mv "F" $$ vv "X") BOOL BOOL --> BOOL))
>                        (ll "X" (ll "x" (mv "A")))
>                    (_PI "X" BOOL (if'' SET (vv "X") BOOL BOOL --> BOOL))
>                        (ll "X" (ll "x" (mv "C")))
>           : eq "q" SET (_PI "X" (if'' SET (mv "B" $$ TT) BOOL BOOL) (if'' SET (mv "F" $$ vv "X") BOOL BOOL --> BOOL)) SET (_PI "X" BOOL (if'' SET (vv "X") BOOL BOOL --> BOOL))
>           : [])

>           -- test 25: solve with extensionality and refl
>         , [ gal "A" BOOL
>           , eq "p" (if'' SET (mv "A") NAT BOOL --> BOOL) (ll "x" TT)
>                    (NAT --> BOOL) (ll "x" TT)
>           , eq "q" SET (if'' SET (mv "A") NAT BOOL) SET NAT
>           ]

>         ]

> fails = [ 

>           -- fail 0: occur check failure (A occurs in suc A)
>           [ gal "A" NAT
>           , eq "p" NAT (mv "A") NAT (SU (mv "A"))
>           ]

>           -- fail 1: flex-rigid fails because A cannot depend on X
>         , ( gal "A" BOOL
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A") BOOL (vv "X" &&& mv "B")
>             : [])
>           )

>           -- fail 2: rigid-rigid clash
>         , ( boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" BOOL (vv "X") BOOL (vv "Y")
>               : [])
>             )
>           )

>           -- fail 3: spine mismatch
>         , ( boy "X" (BOOL *: BOOL)
>             ( eq "p" BOOL (vv "X" %% Hd) BOOL (vv "X" %% Tl)
>             : [])
>           )

>           -- fail 4: rigid-rigid constant clash
>         , ( eq "p" BOOL TT BOOL FF
>           : [])

>           -- fail 5: spine mismatch
>         , ( eq "p" (BOOL --> BOOL) (ll "x" (vv "x"))
>                    ((BOOL --> BOOL) --> BOOL) (ll "f" (vv "f" $$ TT))
>           : [])

>           -- fail 6
>         , ( eq "p" SET BOOL SET (BOOL --> BOOL)
>           : [])

>           -- fail 7
>         , ( gal "A" SET
>           : boy "x" (mv "A")
>             ( boy "y" (mv "A")
>               ( eq "p" (mv "A") (vv "x") (mv "A") (vv "y")
>               : [])
>             )
>           )

>           -- fail 8
>         , ( gal "A" SET
>           : boy "x" (mv "A")
>             ( eq "p" (mv "A") (vv "x") BOOL TT
>             : [])
>           )

>           -- fail 9: occur check
>         , ( boy "f" (BOOL --> BOOL)
>             ( gal "A" (BOOL --> BOOL)
>             : boy "X" BOOL
>               ( boy "Y" BOOL
>                 ( eq "p" BOOL (mv "A" $$ vv "X")
>                          BOOL (vv "f" $$ (mv "A" $$ vv "Y"))
>                 : [])
>               )
>             )
>           )


>         ]
