{-# LANGUAGE GADTs, KindSignatures #-}

module IterDeque where

data Digit v f z a b where
    D1 :: v f z a b -> Digit v f z a b
    D2 :: v f z a b -> v f z b c -> Digit v f z a c
    D3 :: v f z a b -> v f z b c -> v f z c d -> Digit v f z a d
    D4 :: v f z a b -> v f z b c -> v f z c d -> v f z d e -> Digit v f z a e

data Node v f z a b where
    N2 :: v f z a b -> v f z b c -> Node v f z a c
    N3 :: v f z a b -> v f z b c -> v f z c d -> Node v f z a d

data Seq v f z a b where
    Empty :: Seq v f z a a
    Single :: v f z a b -> Seq v f z a b
    Deep :: Digit v f z a b -> Seq (Node v) f z b c -> Digit v f z c d -> Seq v f z a d

data Two w f z a b where
    Two :: w z a -> Two w f z a (f z a)

cons :: v f z a b -> Seq v f z b c -> Seq v f z a c
cons x Empty = Single x
cons x (Single y) = Deep (D1 x) Empty (D1 y)
cons x (Deep (D1 y) c r) = Deep (D2 x y) c r
cons x (Deep (D2 y z) c r) = Deep (D3 x y z) c r
cons x (Deep (D3 y z p) c r) = Deep (D4 x y z p) c r
cons x (Deep (D4 y z p q) c r) = Deep (D2 x y) (cons (N3 z p q) c) r

{-
type Deque = Seq One

(<|) :: a -> Deque f (f a) b -> Deque f a b
x <| y = cons (One x) y

lview :: Deque f a b -> Maybe (a, Deque f (f a) b)
lview x = 
    case viewl x of
      EmptyL -> Nothing
      FullL (One y) ys -> Just (y,ys)
-}


type Deque2 w = Seq (Two w)

(<|) :: w z a -> Deque2 w f z (f z a) b -> Deque2 w f z a b
x <| y = cons (Two x) y

lview :: Deque2 w f z a b -> Maybe (w z a, Deque2 w f z (f z a) b)
lview x = 
    case viewl x of
      EmptyL -> Nothing
      FullL (Two y) ys -> Just (y,ys)

data ViewL v f z a b where
    EmptyL :: ViewL v f z a a
    FullL :: v f z a b -> Seq v f z b c -> ViewL v f z a c

viewl :: Seq v f z a b -> ViewL v f z a b
viewl Empty = EmptyL
viewl (Single x) = FullL x Empty
viewl (Deep (D1 x) c r) = 
    case viewl c of
      EmptyL -> 
          case r of
            D1 y -> FullL x (Single y)
            D2 y z -> FullL x (Deep (D1 y) Empty (D1 z))
            D3 y z p -> FullL x (Deep (D2 y z) Empty (D1 p))
            D4 y z p q -> FullL x (Deep (D2 y z) Empty (D2 p q))
      FullL y ys ->
          case y of
            N2 p q -> FullL x (Deep (D2 p q) ys r)
            N3 p q s -> FullL x (Deep (D3 p q s) ys r)

