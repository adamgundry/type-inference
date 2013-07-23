> module Main where

> import Milner.Test
> import Units.Test
> import PatternUnify.Test

> main :: IO ()
> main = milner >> units >> patternUnify