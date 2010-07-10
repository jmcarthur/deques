module Beque where

import qualified Deque as D

data Many a = Many a a a deriving (Eq)
data Digit a = D1 a
             | D2 a a
             | D3 a a a
             | D4 a a a a 
             | D5 a a a a a
data Beque d a = Empty
               | One a
               | Deep !(Digit a) !(d (Many a)) !(Digit a)

instance (D.Deque d, D.Empty d, Eq a) => Eq (Beque d a) where
    xs == ys =
        case (pop xs,pop ys) of
          (Nothing,Nothing) -> True
          (Just (a,as), Just (b,bs)) -> a == b && as == bs
          _ -> False

empty = Empty

push x Empty = One x
push x (One y) = Deep (D1 x) D.empty (D1 y)
push x (Deep (D1 p) y z) = Deep (D2 x p) y z
push x (Deep (D2 p q) y z) = Deep (D3 x p q) y z
push x (Deep (D3 p q r) y z) = Deep (D4 x p q r) y z
push x (Deep (D4 p q r s) y z) = Deep (D5 x p q r s) y z
push x (Deep (D5 p q r s t) y z) = Deep (D3 x p q) (D.push (Many r s t) y) z

--pop :: (D.Deque d, D.Empty d) => Beque d a -> Maybe (a,Beque d a)
pop Empty = Nothing
pop (One y) = Just (y,Empty)
pop (Deep (D1 p) y z) = Just (p,
    case D.pop y of
      Nothing -> splitD z
      Just (Many q r s,ys) -> Deep (D3 q r s) ys z)
pop (Deep (D2 p q) y z) = Just (p,Deep (D1 q) y z)
pop (Deep (D3 p q r) y z) = Just (p,Deep (D2 q r) y z)
pop (Deep (D4 p q r s) y z) = Just (p,Deep (D3 q r s) y z)
pop (Deep (D5 p q r s t) y z) = Just (p,Deep (D4 q r s t) y z)

splitD (D1 x) = One x
splitD (D2 x y) = Deep (D1 x) D.empty (D1 y)
splitD (D3 x y z) = Deep (D1 x) D.empty (D2 y z)
splitD (D4 w x y z) = Deep (D2 w x) D.empty (D2 y z)
splitD (D5 v w x y z) = Deep (D3 v w x) D.empty (D2 y z)

inject Empty x = One x
inject (One y) x = Deep (D1 y) D.empty (D1 x)
inject (Deep z y (D1 p)) x = Deep z y (D2 p x)
inject (Deep z y (D2 p q)) x = Deep z y (D3 p q x)
inject (Deep z y (D3 p q r)) x = Deep z y (D4 p q r x)
inject (Deep z y (D4 p q r s)) x = Deep z y (D5 p q r s x)
inject (Deep z y (D5 p q r s t)) x = Deep z (D.inject y (Many p q r)) (D3 s t x)

eject Empty = Nothing
eject (One y) = Just (Empty,y)
eject (Deep z y (D1 p)) = Just (
    case D.eject y of
      Nothing -> splitD z
      Just (ys,Many q r s) -> Deep z ys (D3 q r s),p)
eject (Deep z y (D2 q p)) = Just (Deep z y (D1 q),p)
eject (Deep z y (D3 q r p)) = Just (Deep z y (D2 q r),p)
eject (Deep z y (D4 q r s p)) = Just (Deep z y (D3 q r s),p)
eject (Deep z y (D5 q r s t p)) = Just (Deep z y (D4 q r s t),p)

instance D.Empty (Beque d) where
    empty = Empty

instance (D.Empty d, D.Deque d) => D.Deque (Beque d) where
    push = Beque.push
    pop = Beque.pop
    inject = Beque.inject
    eject = Beque.eject