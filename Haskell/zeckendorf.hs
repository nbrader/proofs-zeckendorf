#!/usr/bin/env stack
-- stack --resolver lts-12.21 ghci

import Data.List

fibs = 0 : 1 : fibs `add` tail fibs
  where add = zipWith (+)

-- F(x) = 0 + 1*x^1 + 1*x^2 + 2*x^3 + 3*x^4 + 5*x^5 + 8*x^6 + ...
-- F(x) =  x*F(x)    +    x^2*F(x)    +      x
-- fibs = (0:fibs) `add` (0:0:fibs) `add` (0:1:repeat 0)
  -- where add = zipWith (+)


zeckendorf :: Int -> [Int]
zeckendorf 0 = []
zeckendorf n = let glbFib = last $ takeWhile (<=n) (fibs) in glbFib : zeckendorf (n - glbFib)
-- The above algorithm cannot produce a sum with 2 fibonacci numbers that are "consecutive" (adjacent in the fibonacci sequence) because it always takes the largest fibonacci number not greater than n and then recurses but if two consecutive fibonacci numbers were taken then the sum of these two for the n at this part of the algorithm is a larger fibanacci number than each of them and must still be less than n if their sum was, and yet it wasn't taken.