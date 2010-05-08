{-# LANGUAGE GADTs, KindSignatures #-}

data Digit v (f :: * -> *) a b where
    D1 :: v f a b -> Digit v f a b
    D2 :: v f a b -> v f b c -> Digit v f a c
    D3 :: v f a b -> v f b c -> v f c d -> Digit v f a d
    D4 :: v f a b -> v f b c -> v f c d -> v f d e -> Digit v f a e

data Node v f a b where
    N2 :: v f a b -> v f b c -> Node v f a c
    N3 :: v f a b -> v f b c -> v f c d -> Node v f a d

data Seq v f a b where
    Empty :: Seq v f a a
    Single :: v f a b -> Seq v f a b
    Deep :: Digit v f a b -> Seq (Node v) f b c -> Digit v f c d -> Seq v f a d

data One f a b where
    One :: a -> One f a (f a)

cons :: v f a b -> Seq v f b c -> Seq v f a c
cons x Empty = Single x
cons x (Single y) = Deep (D1 x) Empty (D1 y)
cons x (Deep (D1 y) c r) = Deep (D2 x y) c r
cons x (Deep (D2 y z) c r) = Deep (D3 x y z) c r
cons x (Deep (D3 y z p) c r) = Deep (D4 x y z p) c r
cons x (Deep (D4 y z p q) c r) = Deep (D2 x y) (cons (N3 z p q) c) r

data ViewL v f a b where
    EmptyL :: ViewL v f a a
    FullL :: v f a b -> Seq v f b c -> ViewL v f a c

viewl :: Seq v f a b -> ViewL v f a b
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

