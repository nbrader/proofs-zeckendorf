#!/usr/bin/env stack
-- stack --resolver lts-12.21 ghci

import Data.List

fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

zeck_lists :: Int -> [[Int]]
zeck_lists 0 = [[]]
zeck_lists 1 = [[], [1]]
zeck_lists n =
  let n' = n - 2
  in zeck_lists (n' + 1) ++
     [ fib (n' + 3) : xs
     | xs <- zeck_lists n'
     ]

main = print $ map sum (zeck_lists 10)