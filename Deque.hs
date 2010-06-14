module Deque where

class Deque d where
    empty :: d a
    push :: a -> d a -> d a
    pop :: d a -> Maybe (a, d a)
    inject :: d a -> a -> d a
    eject :: d a -> Maybe (d a, a)

instance Deque [] where
    empty = []
    push = (:)
    pop [] = Nothing
    pop (x:xs) = Just (x,xs)
    inject xs x = xs ++ [x]
    eject x = 
        do (y,ys) <- pop (reverse x)
           return (reverse ys,y)
                
