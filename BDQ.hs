module BDQ where

import qualified Deque as D
import qualified Digit as G

data BDQ d a = Empty
               | One a
               | Deep !(G.Digit a) !(d (G.Half a)) !(G.Digit a)

empty = Empty

push x Empty = One x
push x (One y) = Deep (G.single x) D.empty (G.single y) 
push x (Deep p q r) =
    case G.push x p of
      Left p -> Deep p q r
      Right (p1,p2) -> Deep p1 (D.push p2 q) r

splitD x = 
    case G.splitD x of
      Left x -> One x
      Right (x1,x2) -> Deep x1 D.empty x2


pop Empty = Nothing
pop (One y) = Just (y,Empty)
pop (Deep p q r) = Just $
    case G.pop p of
      (a,Nothing) -> (a,
          case D.pop q of
            Nothing -> splitD r
            Just (q,qs) -> Deep (G.fromHalf q) qs r)
      (a,Just as) -> (a,Deep as q r)

inject Empty x = One x
inject (One x) y = Deep (G.single x) D.empty (G.single y) 
inject (Deep p q r) x =
    case G.inject r x of
      Left r -> Deep p q r
      Right (r1,r2) -> Deep p (D.inject q r1) r2

eject Empty = Nothing
eject (One y) = Just (Empty,y)
eject (Deep p q r) = Just $
    case G.eject r of
      (Nothing,a) ->
          (case D.eject q of
             Nothing -> splitD p
             Just (qs,q) -> Deep p qs (G.fromHalf q),a)
      (Just as,a) -> (Deep p q as,a)

instance D.Empty (BDQ d) where
    empty = Empty

instance (D.Empty d, D.Deque d) => D.Deque (BDQ d) where
    push = BDQ.push
    pop = BDQ.pop
    inject = BDQ.inject
    eject = BDQ.eject

instance (D.Deque d, D.Empty d, Eq a) => Eq (BDQ d a) where
    xs == ys =
        case (pop xs,pop ys) of
          (Nothing,Nothing) -> True
          (Just (a,as), Just (b,bs)) -> a == b && as == bs
          _ -> False