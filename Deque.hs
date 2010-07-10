module Deque where

import qualified Data.Sequence as S

class Deque d where
    push :: a -> d a -> d a
    pop :: d a -> Maybe (a, d a)
    inject :: d a -> a -> d a
    eject :: d a -> Maybe (d a, a)

class Empty d where
    empty :: d a

instance Deque [] where
    push = (:)
    pop [] = Nothing
    pop (x:xs) = Just (x,xs)
    inject xs x = xs ++ [x]
    eject x = 
        do (y,ys) <- pop (reverse x)
           return (reverse ys,y)
                
instance Empty [] where
    empty = []

instance Deque S.Seq where
    push = (S.<|)
    pop xs = 
        case S.viewl xs of
          S.EmptyL -> Nothing
          y S.:< ys -> Just (y,ys)
    inject = (S.|>)
    eject xs = 
        case S.viewr xs of
          S.EmptyR -> Nothing
          ys S.:> y -> Just (ys,y)
                
instance Empty S.Seq where
    empty = S.empty