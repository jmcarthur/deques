{-# LANGUAGE OverlappingInstances #-}

module CheckDivisible where

import Divisible
import TarjanMihaesau
import DivisibleTest

import Test.QuickCheck
import Deque

checkDiv = quickCheck $ checkArb (empty :: DD TM Int)
