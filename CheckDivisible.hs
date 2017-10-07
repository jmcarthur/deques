{-# LANGUAGE OverlappingInstances #-}

module CheckDivisible where

import Divisible
import TarjanMihaescu
import DivisibleTest

import Test.QuickCheck
import Deque

checkDiv = quickCheck $ checkArb (empty :: DD TM Int)
