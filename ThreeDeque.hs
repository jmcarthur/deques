{- 
This is an implementation of worst-case constant-time deques. 
It is modified from the course notes of Robert Tarjan and Radu Mihaesau:

http://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/Notes%20on%20Catenable%20Deques.doc

This deque can also support O(lg(min(n-i,i))) indexing.
With an accumulation measure like Hinze & Paterson's finger trees, indexing can be on quantities other than position.

-}

module ThreeDeque where

import Monad
import Maybe
import Data.List
import Test.QuickCheck

-- TODO: Deque type class
-- TODO: separate tests
-- TODO: more equality tests on other deque operations
-- TODO: indexing
-- TODO: measure
-- TODO: GADT to ensure some functions are total
-- TODO: Coq proof of correctness
-- TODO: divisible version
-- TODO: written proof on fast indexing

data Buffer a = B0
              | B1 !a
              | B2 !a !a deriving (Show)

data Tree a = Leaf !a
            | Node !(Tree a) !(Tree a) deriving (Show)

data SP x y = SP !x !y deriving (Show)

type PB a = SP (Buffer (Tree a)) (Buffer (Tree a))

data SL t = Nil
          | Cons !t !(SL t) deriving (Show)

type NEL a = SP a (SL a)

data SM t = None
          | Some !t deriving (Show)

data Deque a = Deque (SL (PB a)) (SL (NEL (NEL (PB a)))) (SM (Tree a)) deriving (Show)

data Top = Prefix | Suffix | Both deriving (Show)

topCheck (SP B1{} B1{}) = Nothing
topCheck (SP B0{} B1{}) = Just Prefix
topCheck (SP B2{} B1{}) = Just Prefix
topCheck (SP B1{} B0{}) = Just Suffix
topCheck (SP B1{} B2{}) = Just Suffix
topCheck _ = Just Both

nextTop1 Prefix Prefix = True
nextTop1 Suffix Suffix = True
nextTop1 _ _ = False

cons13 :: PB a -> SL (PB a) -> SL (NEL (NEL (PB a))) -> SL (NEL (NEL (PB a)))
cons13 x xs Nil = Cons (SP (SP x xs) Nil) Nil
cons13 x xs r@(Cons (SP (SP c cs) bs) as) = 
    let Just p = topCheck x
        Just q = topCheck c
    in if nextTop1 p q
       then Cons (SP (SP x xs)  (Cons (SP c cs) bs)) as
       else Cons (SP (SP x xs) Nil) r

empty = Deque Nil Nil None

npush x (Deque Nil Nil None) = Deque Nil Nil (Some x) 
npush x (Deque Nil Nil (Some y)) = Deque (Cons (SP (B1 x) (B1 y)) Nil) Nil None 
npush x (Deque Nil (Cons (SP (SP (SP B0 (B1 z)) zs) Nil) xs) q) = Deque (Cons (SP (B1 x) (B1 z)) zs) xs q
npush x (Deque Nil (Cons (SP (SP (SP B0 (B1 z)) zs) (Cons y ys)) xs) q) = Deque (Cons (SP (B1 x) (B1 z)) zs) (Cons (SP y ys) xs) q
npush x (Deque Nil (Cons (SP (SP (SP B0 z) zs) Nil) xs) q) = Deque Nil (cons13 (SP (B1 x) z) zs xs) q 
npush x (Deque Nil (Cons (SP (SP (SP (B1 y) z) zs) Nil) xs) q) = Deque Nil (Cons (SP (SP (SP (B2 x y) z) zs) Nil) xs) q 
npush x (Deque Nil (Cons (SP (SP (SP (B1 y) z) zs) (Cons r rs)) xs) q) = Deque Nil (Cons (SP (SP (SP (B2 x y) z) zs) Nil) (Cons (SP r rs) xs)) q 
npush x (Deque (Cons (SP (B1 y) z) zs) rs q) = Deque Nil (cons13 (SP (B2 x y) z) zs rs) q

ninject (Deque Nil Nil None) x = Deque Nil Nil (Some x)
ninject (Deque Nil Nil (Some y)) x = Deque (Cons (SP (B1 y) (B1 x)) Nil) Nil None
ninject (Deque Nil (Cons (SP (SP (SP (B1 z) B0) zs) Nil) xs) q) x = Deque (Cons (SP (B1 z) (B1 x)) zs) xs q
ninject (Deque Nil (Cons (SP (SP (SP (B1 z) B0) zs) (Cons y ys)) xs) q) x = Deque (Cons (SP (B1 z) (B1 x)) zs) (Cons (SP y ys) xs) q
ninject (Deque Nil (Cons (SP (SP (SP z B0) zs) Nil) xs) q) x = Deque Nil (cons13 (SP z (B1 x)) zs xs) q 
ninject (Deque Nil (Cons (SP (SP (SP z (B1 y)) zs) Nil) xs) q) x = Deque Nil (Cons (SP (SP (SP z (B2 y x)) zs) Nil) xs) q 
ninject (Deque Nil (Cons (SP (SP (SP z (B1 y)) zs) (Cons r rs)) xs) q) x = Deque Nil (Cons (SP (SP (SP z (B2 y x)) zs) Nil) (Cons (SP r rs) xs)) q
ninject (Deque (Cons (SP z (B1 y)) zs) rs q) x = Deque Nil (cons13 (SP z (B2 y x)) zs rs) q

npop (Deque Nil Nil None) = None
npop (Deque Nil Nil (Some y)) =  Some (SP y empty)
npop (Deque Nil (Cons (SP (SP (SP (B2 y x) (B1 z)) zs) Nil) xs) q) = Some (SP y (Deque (Cons (SP (B1 x) (B1 z)) zs) xs q))
npop (Deque Nil (Cons (SP (SP (SP (B2 y x) (B1 z)) zs) (Cons r rs)) xs) q) = Some (SP y (Deque (Cons (SP (B1 x) (B1 z)) zs) (Cons (SP r rs) xs) q))
npop (Deque Nil (Cons (SP (SP (SP (B2 y x) z) zs) Nil) xs) q) = Some (SP y (Deque Nil (cons13 (SP (B1 x) z) zs xs) q))
npop (Deque Nil (Cons (SP (SP (SP (B1 y) (B2 x z)) Nil) Nil) Nil) None) = Some (SP y (Deque (Cons (SP (B1 x) (B1 z)) Nil) Nil None))
npop (Deque Nil (Cons (SP (SP (SP (B1 y) B0) Nil) Nil) Nil) (Some (Node x z))) = Some (SP y (Deque (Cons (SP (B1 x) (B1 z)) Nil) Nil None))
npop (Deque Nil (Cons (SP (SP (SP (B1 y) z) zs) Nil) xs) q) = Some (SP y (Deque Nil (Cons (SP (SP (SP B0 z) zs) Nil) xs) q))
npop (Deque Nil (Cons (SP (SP (SP (B1 y) z) zs) (Cons r rs)) xs) q) = Some (SP y (Deque Nil (Cons (SP (SP (SP B0 z) zs) Nil) (Cons (SP r rs) xs)) q))
npop (Deque (Cons (SP (B1 y) (B1 z)) Nil) Nil None) = Some (SP y (Deque Nil Nil (Some z)))
npop (Deque (Cons (SP (B1 y) z) zs) rs q) = Some (SP y (Deque Nil (cons13 (SP B0 z) zs rs) q))

neject (Deque Nil Nil None) = None
neject (Deque Nil Nil (Some y)) =  Some (SP empty y)
neject (Deque Nil (Cons (SP (SP (SP (B1 x) (B2 z y)) zs) Nil) xs) q) = Some (SP (Deque (Cons (SP (B1 x) (B1 z)) zs) xs q) y)
neject (Deque Nil (Cons (SP (SP (SP (B1 x) (B2 z y)) zs) (Cons r rs)) xs) q) = Some (SP (Deque (Cons (SP (B1 x) (B1 z)) zs) (Cons (SP r rs) xs) q) y)
neject (Deque Nil (Cons (SP (SP (SP z (B2 x y)) zs) Nil) xs) q) = Some (SP (Deque Nil (cons13 (SP z (B1 x)) zs xs) q) y)
neject (Deque Nil (Cons (SP (SP (SP (B2 x z) (B1 y)) Nil) Nil) Nil) None) = Some (SP (Deque (Cons (SP (B1 x) (B1 z)) Nil) Nil None) y)
neject (Deque Nil (Cons (SP (SP (SP (B0) (B1 y)) Nil) Nil) Nil) None) = Some (SP empty y)
neject (Deque Nil (Cons (SP (SP (SP B0 (B1 y)) Nil) Nil) Nil) (Some (Node x z))) = Some (SP (Deque (Cons (SP (B1 x) (B1 z)) Nil) Nil None) y)
neject (Deque Nil (Cons (SP (SP (SP z (B1 y)) zs) Nil) xs) q) = Some (SP (Deque Nil (Cons (SP (SP (SP z B0) zs) Nil) xs) q) y)
neject (Deque Nil (Cons (SP (SP (SP z (B1 y)) zs) (Cons r rs)) xs) q) = Some (SP (Deque Nil (Cons (SP (SP (SP z B0) zs) Nil) (Cons (SP r rs) xs)) q) y)
neject (Deque (Cons (SP (B1 z) (B1 y)) Nil) Nil None) = Some (SP (Deque Nil Nil (Some z)) y)
neject (Deque (Cons (SP z (B1 y)) zs) rs q) = Some (SP (Deque Nil (cons13 (SP z B0) zs rs) q) y)

{-
prefix0' ((((B2 x y,z),zs),Nil):xs) q = 
    let Deque a c q' = npush (Node x y) (Deque zs xs q)
    in (cons13 ((B0,z):a) c,q')
prefix0' ((((B2 x y,z),zs),(r:rs)):xs) q = 
    let Deque a c q' = npush (Node x y) (Deque zs ((r,rs):xs) q)
    in (cons13 ((B0,z):a) c, q')

prefix0 ((((B1 x,z),zs),rs):xs) q = 
    let (c,q') = prefix0' xs q
    in ((((B1 x,z),zs),rs):c, q')
prefix0 x y = prefix0' x y

suffix0' ((((z,B2 x y),zs),Nil):xs) q = 
    let Deque a c q' = ninject (Deque zs xs q) (Node x y)
    in (cons13 ((z,B0):a) c,q')
suffix0' ((((z,B2 x y),zs),(r:rs)):xs) q = 
    let Deque a c q' = ninject (Deque zs ((r,rs):xs) q) (Node x y)
    in (cons13 ((z,B0):a) c,q')

suffix0 ((((z,B1 x),zs),rs):xs) q = 
    let (c, q') = suffix0' xs q
    in ((((z,B1 x),zs),rs):c, q')
suffix0 x y = suffix0' x y

prefix2' ((((B0,z),zs),Nil):xs) q = 
    let Some (Node x y,Deque a c q') = npop (Deque zs xs q)
    in (cons13 ((B2 x y,z):a) c, q') 
prefix2' ((((B0,z),zs),(r:rs)):xs) q = 
    let Some (Node x y,Deque a c q') = npop (Deque zs ((r,rs):xs) q)
    in (cons13 ((B2 x y,z):a) c, q')

prefix2 ((((B1 x,z),zs),rs):xs) q = 
    let (c, q') = prefix2' xs q
    in ((((B1 x,z),zs),rs):c, q')
prefix2 x y = prefix2' x y

suffix2' ((((z,B0),zs),Nil):xs) q = 
    let Some (Deque a c q',Node x y) = neject (Deque zs xs q)
    in (cons13 ((z,B2 x y):a) c, q')
suffix2' ((((z,B0),zs),(r:rs)):xs) q = 
    let Some (Deque a c q',Node x y) = neject (Deque zs ((r,rs):xs) q)
    in (cons13 ((z,B2 x y):a) c, q')

suffix2 ((((z,B1 x),zs),rs):xs) q = 
    let (c,q') = suffix2' xs q
    in ((((z,B1 x),zs),rs):c, q')
suffix2 x y = suffix2' x y

fixHelp f (Deque b c d) = 
    let (c',d') = f c d
    in Deque b c' d'

data Size = S0 | S1 | S2 deriving (Show)

prepose' (Deque _ Nil _) = S1
prepose' (Deque _ ((((B0,_),_),_):_) _) = S0
prepose' (Deque _ ((((B2 _ _,_),_),_):_) _) = S2

prepose (Deque p ((((B1 _,_),_),_):xs) q) = prepose' (Deque p xs q)
prepose x = prepose' x

sufpose' (Deque _ Nil _) = S1
sufpose' (Deque _ ((((_,B0),_),_):_) _) = S0
sufpose' (Deque _ ((((_,B2 _ _),_),_):_) _) = S2

sufpose (Deque p ((((_,B1 _),_),_):xs) q) = sufpose' (Deque p xs q)
sufpose x = sufpose' x

push x xs =
    let y = Leaf x
    in case prepose xs of
         S2 -> npush y (fixHelp prefix0 xs)
         _  -> npush y xs

inject xs x =
    let y = Leaf x
    in case sufpose xs of
         S2 -> ninject (fixHelp suffix0 xs) y
         _  -> ninject xs y

pop xs =
    let ans = case prepose xs of
                S0 -> npop (fixHelp prefix2 xs)
                _ -> npop xs
    in case ans of
         None -> None
         Some (Leaf y,ys) -> Some (y,ys)

eject xs =
    let ans = case sufpose xs of
                S0 -> neject (fixHelp suffix2 xs)
                _ -> neject xs
    in case ans of
         None -> None
         Some (ys,Leaf y) -> Some (ys,y)

-----------------------------------

fromList = foldr push empty

---------------------------------

toListTree' (Leaf x) r = x:r
toListTree' (Node x y) r = toListTree' x (toListTree' y r)

toListTree x = toListTree' x Nil

nelist (x,xs) = x:xs

joinUp = concatMap (concatMap nelist . nelist)

toList (Deque x y None) = wrapMap toListTree (x ++ (joinUp y))
toList (Deque x y (Some z)) = wrapMap toListTree (x ++ (joinUp y) ++ [(B0,B1 z)])

wrapMap _ Nil = Nil
wrapMap f ((B0,B0):xs) = wrapMap f xs
wrapMap f ((B0,B1 x):xs) = wrapMap f xs ++ f x
wrapMap f ((B0,B2 x y):xs) = wrapMap f xs ++ f x ++ f y
wrapMap f ((B1 x, y):xs) = f x ++ wrapMap f ((B0,y):xs)
wrapMap f ((B2 x y,z):xs) = f x ++ f y ++ wrapMap f ((B0,z):xs)

nextPre0 Nil = True
nextPre0 ((B0,_):xs) = nextPre2 xs
nextPre0 ((B1 _,_):xs) = nextPre0 xs
nextPre0 _ = False

nextPre2 Nil = True
nextPre2 ((B1 _,_):xs) = nextPre2 xs
nextPre2 ((B2 _ _,_):xs) = nextPre0 xs
nextPre2 _ = False

regularPreAlt (Deque a c _) = 
    let d = a ++ (joinUp c)
    in nextPre0 d || nextPre2 d

nextSuf0 Nil = True
nextSuf0 ((_,B0):xs) = nextSuf2 xs
nextSuf0 ((_,B1 _):xs) = nextSuf0 xs
nextSuf0 _ = False

nextSuf2 Nil = True
nextSuf2 ((_,B1 _):xs) = nextSuf2 xs
nextSuf2 ((_,B2 _ _):xs) = nextSuf0 xs
nextSuf2 _ = False

regularSufAlt (Deque a c _) = 
    let d = a ++ (joinUp c)
    in nextSuf0 d || nextSuf2 d

bottomBias Nil = True
bottomBias [(B2 _ _,B2 _ _)] = True
bottomBias [(B2 _ _,B1 _)] = True
bottomBias [(B1 _,B2 _ _)] = True
bottomBias [(B1 _,B1 _)] = True
bottomBias [_] = False
bottomBias (x:y:ys) = bottomBias (y:ys)

bottomSkip Nil = True
bottomSkip [(B0,B0)] = False
bottomSkip [_] = True
bottomSkip (x:y:ys) = bottomSkip (y:ys)

bottomOK (Deque a c (Some _)) =
    let d = a ++ (joinUp c)
    in bottomSkip d
bottomOK (Deque a c None) = 
    let d = a ++ (joinUp c)
    in bottomBias d

bigEnough (Deque _ _ (Some _)) = True
bigEnough x@(Deque _ _ None) =
    case toList x of
      [x] -> False
      _ -> True

ones (B1 _,B1 _) = True
ones _ = False

top1 (x,xs) =
    do v <- topCheck x
       guard (all ones xs)
       return v

top2 (x,Nil) = top1 x
top2 (x,y:ys) =
    do v <- top1 x
       w <- top2 (y,ys)
       guard (nextTop1 v w)
       return v

top3 x Nil = top2 x
top3 x (y:ys) =
    do v <- top2 x
       w <- top3 y ys
       guard (not (nextTop1 v w))
       return v

topShape Nil = True
topShape (x:xs) = isSome $ top3 x xs

allShape (Deque a b _) =
    all ones a && topShape b

treeDepth (Leaf _) = return 1
treeDepth (Node x y) =
    do i <- treeDepth x
       j <- treeDepth y
       guard (i == j)
       return (i+1)

depthIs i Nil = return i
depthIs i ((B0,B0):xs) = depthIs (i+1) xs
depthIs i ((B0,B1 x):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs (i+1) xs
depthIs i ((B0,B2 x y):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs i ((B0,B1 y):xs)
depthIs i ((B1 x,y):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs i ((B0,y):xs) 
depthIs i ((B2 x y,z):xs) = 
    do j <- treeDepth x
       guard (i == j)
       depthIs i ((B1 y,z):xs)

dequeDepth (Deque a c None) = 
    let d = a ++ (joinUp c)
    in isSome $ depthIs 1 d
dequeDepth (Deque a c (Some q)) = 
    let d = a ++ (joinUp c)
    in isSome $
       do i <- depthIs 1 d
          j <- treeDepth q
          guard (i == j)
          return i

invariants x = allShape x && regularSufAlt x && regularPreAlt x && bottomOK x && bigEnough x && dequeDepth x

{-
unList . fromList = id
toList . fromList = id
-}

-------------------------

unList = unfoldr pop
nuList xs =
    case eject xs of
      None -> Nil
      Some (ys,y) -> (nuList ys)++[y]

popPreserves f x =
    case pop x of
      None -> True
      Some (_,z) -> f z && popPreserves f z

ejectPreserves f x =
    case eject x of
      None -> True
      Some (z,_) -> f z && ejectPreserves f z

pushPreserves 0 _ f _ = True
pushPreserves n x f xs =
    let m = n-1
        ys = push x xs
    in f ys && pushPreserves m x f ys

injectPreserves 0 _ f _ = True
injectPreserves n x f xs =
    let m = n-1
        ys = inject xs x
    in f ys && injectPreserves m x f ys

injectList = foldl' inject empty

test 2 n = and [let v = [1..i] in invariants (fromList v) | i <- [1..n]]
test 4 n = and [let v = [1..i] in popPreserves invariants (fromList v) | i <- [1..n]]
test 6 n = and [let v = [1..i] in invariants (injectList v) | i <- [1..n]]
test 8 n = and [let v = [1..i] in ejectPreserves invariants (fromList v) | i <- [1..n]]
test 10 n = and [let v = [1..i] in popPreserves invariants (injectList v) | i <- [1..n]]
test 12 n = and [let v = [1..i] in ejectPreserves invariants (injectList v) | i <- [1..n]]
test 15 n = and [let v = [1..i] in f (g invariants) (h v) | i <- [1..n], 
                         l <- [[popPreserves, ejectPreserves, pushPreserves (2*i) 42, injectPreserves (2*i) 42]], 
                         f <- l, g <- l,
                         h <- [injectList, fromList]]
test 16 n = and [let v = [1..i] in v == f (g v) | i <- [1..n], f <- [toList, unList, nuList], g <- [fromList, injectList]]
test _ _ = True

tests k n = and [test i n | i <- [1..k]]

-}