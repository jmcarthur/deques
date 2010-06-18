{-# LANGUAGE OverlappingInstances #-}

module CheckOkasaki where

import LazyRealTimeDeque
import DequeTest

import Test.QuickCheck
import Deque

checkLRT = quickCheck $ checkArb (empty :: LRT Int)
