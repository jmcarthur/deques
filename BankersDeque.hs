-- Source code from
--   Purely Functional Data Structures
--   Chris Okasaki
--   Cambridge University Press, 1998
--
-- Copyright (c) 1998 Cambridge University Press

module BankersDeque (module Deque, BankersDeque) where

import Prelude hiding (head,tail,last,init)
import Deque

c = 3
    
data BankersDeque a = BD Int [a] Int [a] deriving (Show,Eq)

check lenf f lenr r =
    if lenf > c*lenr + 1 
    then let i = (lenf+lenr) `div` 2
             j = lenf+lenr-i
             f' = take i f
             r' = r ++ reverse (drop i f)
         in BD i f' j r'
    else if lenr > c*lenf + 1 
         then let j = (lenf+lenr) `div` 2
                  i = lenf+lenr-j
                  r' = take j r
                  f' = f ++ reverse (drop j r)
              in BD i f' j r'
         else BD lenf f lenr r

instance Empty BankersDeque where
    empty = BD 0 [] 0 []

instance Deque BankersDeque where

--    isEmpty (BD lenf f lenr r) = (lenf+lenr == 0)

    push x (BD lenf f lenr r) = check (lenf+1) (x:f) lenr r

    pop (BD lenf [] lenr (r:rs)) = Just (r,empty)
    pop (BD lenf [] lenr r) = Nothing
    pop (BD lenf (x:f') lenr r) = Just (x,check (lenf-1) f' lenr r)

    inject (BD lenf f lenr r) x = check lenf f (lenr+1) (x:r)

    eject (BD lenf [f] lenr []) = Just(empty,f)
    eject (BD lenf f lenr []) = Nothing
    eject (BD lenf f lenr (x:r')) = Just (check lenf f (lenr-1) r',x)
    