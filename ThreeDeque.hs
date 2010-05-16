{-# LANGUAGE GADTs #-}

{- http://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/Notes%20on%20Catenable%20Deques.doc -}

module ThreeDeque where

import Monad
import Maybe
import List

data Buffer a = B0
              | B1 a
              | B2 a a deriving (Show)

data Tree a = Leaf a
            | Node (Tree a) (Tree a) deriving (Show)

type PB a = (Buffer (Tree a),Buffer (Tree a))

-- TODO: non-empty substacks

type NEL a = (a,[a])

data Deque a = Deque [PB a] [NEL (NEL (PB a))] (Maybe (Tree a)) deriving (Show)

data Top = Prefix | Suffix | Both deriving (Show)

topCheck (B1 _, B1 _) = Nothing
topCheck (B0,B1 _) = Just Prefix
topCheck (B2 _ _,B1 _) = Just Prefix
topCheck (B1 _,B0) = Just Suffix
topCheck (B1 _,B2 _ _) = Just Suffix
topCheck _ = Just Both

nextTop1 Prefix Prefix = True
nextTop1 Suffix Suffix = True
nextTop1 _ _ = False

cons13 :: [PB a] -> [NEL (NEL (PB a))] -> [NEL (NEL (PB a))]
cons13 [] [] = []
cons13 [] y = y
cons13 (x:xs) [] = [((x,xs),[])]
cons13 (x:xs) r@(((c,cs),bs):as) = 
    let Just p = topCheck x
        Just q = topCheck c
    in if nextTop1 p q
       then ((x,xs),((c,cs):bs)):as
       else ((x,xs),[]):r

npush x (Deque [] [] Nothing) = Deque [] [] (Just x)
npush x (Deque [] [] (Just y)) = Deque [(B1 x, B1 y)] [] Nothing
npush x (Deque [] ((((B0,B1 z),zs),[]):xs) q) = Deque ((B1 x,B1 z):zs) xs q
npush x (Deque [] ((((B0,B1 z),zs),(y:ys)):xs) q) = Deque ((B1 x,B1 z):zs) ((y,ys):xs) q
npush x (Deque [] ((((B0,z),zs),[]):xs) q) = Deque [] (cons13 ((B1 x,z):zs) xs) q 
npush x (Deque [] [(((B1 y,B0),[]),[])] q) = Deque [(B1 x,B1 y)] [] q 
npush x (Deque [] ((((B1 y,z),zs),[]):xs) q) = Deque [] ((((B2 x y,z),zs),[]):xs) q 
npush x (Deque [] ((((B1 y,z),zs),(r:rs)):xs) q) = Deque [] ((((B2 x y,z),zs),[]):((r,rs):xs)) q
npush x (Deque ((B1 y,z):zs) rs q) = Deque [] (cons13 ((B2 x y,z):zs) rs) q

{-
npush x (Deque [] [] Nothing) = Deque [] [] (Just x)
npush x (Deque [] [] (Just y)) = Deque [(B1 x, B1 y)] [] Nothing
npush x (Deque [] ((((B0,B1 z):zs):ys):xs) q) = Deque ((B1 x,B1 z):zs) (ys:xs) q
npush x (Deque [] ([((B0,z):zs)]:xs) q) = Deque [] (cons13 ((B1 x,z):zs) xs) q
    case topCheck (B0,z) of
      Just Prefix -> Deque ((B1 x,z):zs) (ys:xs) q
      Just Both -> 
          case ys of
            [] ->
                case xs of
                  [] -> Deque [] [[((B1 x,z):zs)]] q
                  (((r:rs):qs):ps) ->
                      case topCheck r of
                        Just Suffix -> Deque [] ((((B1 x,z):zs):((r:rs):qs)):ps) q
                        _ -> Deque [] ([((B1 x,z):zs)]:xs) q
npush x (Deque [] [[[(B1 y,B0)]]] q) = Deque [(B1 x,B1 y)] [] q
npush x (Deque [] ((((B1 y,z):zs):ys):xs) q) = Deque [] ([((B2 x y,z):zs)]:(ys:xs)) q
npush x (Deque ((B1 y,z):zs) [] q) = Deque [] [[((B2 x y,z):zs)]] q
npush x (Deque ((B1 y,z):zs) (((r:rs):qs):ps) q) = 
    case topCheck r of
      Just Prefix -> Deque [] ((((B2 x y,z):zs):((r:rs):qs)):ps) q
      _ -> Deque [] ([(B2 x y,z):zs]:(((r:rs):qs):ps)) q
-}

{-
npop (Deque [] [] [] Nothing) = Nothing
npop (Deque [] [] [] (Just x)) = Just (x,empty)
npop (Deque [] [] ((((B2 x y,z):zs):ys):xs) q) = Just (x,Deque [] (((B1 y,z):zs):ys) xs q)
npop (Deque [] (((B2 x y,z):zs):ys) xs q) = Just (x,Deque ((B1 y,z):zs) ys xs q)
npop (Deque [] [[(B1 x,B2 y z)]] [] q) = Just (x,Deque [(B1 y,B1 z)] [] [] q)
npop (Deque [] (((B1 y,z):zs):ys) xs q) = Just (y,Deque [] [] ((((B0,z):zs):ys):xs) q)
npop (Deque [(B1 y,B1 z)] [] [] Nothing) = Just (y,Deque [] [] [] (Just z))
npop (Deque ((B1 y,z):zs) ys xs q) = Just (y,Deque [] (((B0,z):zs):ys) xs q)
-}

prefix0' (Deque p ((((B2 x y,z),zs),[]):xs) q) = 
    let Deque a c q' = npush (Node x y) (Deque zs xs q)
    in Deque p (cons13 ((B0,z):a) c) q' 
prefix0' (Deque p ((((B2 x y,z),zs),(r:rs)):xs) q) = 
    let Deque a c q' = npush (Node x y) (Deque zs ((r,rs):xs) q)
    in Deque p (cons13 ((B0,z):a) c) q'

prefix0 (Deque p ((((B1 x,z),zs),[]):xs) q) = 
    let Deque a c q' = prefix0' (Deque zs xs q)
    in Deque p (cons13 ((B1 x,z):a) c) q' 
prefix0 (Deque p ((((B1 x,z),zs),(r:rs)):xs) q) = 
    let Deque a c q' = prefix0' (Deque zs ((r,rs):xs) q)
    in Deque p (cons13 ((B1 x,z):a) c) q' 
prefix0 x = prefix0' x

{-
smaller (Deque p (((B1 x,z):zs):(y:ys)) xs q) = 
    let Deque [] b c q' = smaller (Deque [] (y:ys) xs q) -- TODO: this can recurse too far
    in Deque p (((B1 x,z):zs):b) c q'
smaller (Deque p (((B2 x y,z):zs):ys) xs q) = 
    let Deque a b c q' = npush (Node x y) (Deque zs ys xs q)
    in Deque p (((B0,z):a):b) c q'
-}

{-
smaller (Deque p [] ((((B2 x y,z):zs):ys):xs) q) = 
    let Deque a b c q' = npush (Node x y) (Deque zs ys xs q)
    in Deque p [] ((((B0,z):a):b):c) q'
smaller (Deque p [((B1 x,z):zs)] xs q) = 
    let Deque [] [] c q' = smaller (Deque [] [] xs q)
    in Deque p [((B1 x,z):zs)] c q'
smaller (Deque p (((B1 x,z):zs):(y:ys)) xs q) = 
    let Deque [] b c q' = smaller (Deque [] (y:ys) xs q) -- TODO: this can recurse too far
    in Deque p (((B1 x,z):zs):b) c q'
smaller (Deque p (((B2 x y,z):zs):ys) xs q) = 
    let Deque a b c q' = npush (Node x y) (Deque zs ys xs q)
    in Deque p (((B0,z):a):b) c q'

larger (Deque p [] ((((B0,z):zs):ys):xs) q) = 
    let Just (Node x y,Deque a b c q') = npop (Deque zs ys xs q)
    in Deque p [] ((((B2 x y,z):a):b):c) q'
larger (Deque p [((B1 x,z):zs)] xs q) = 
    let Deque [] [] c q' = larger (Deque [] [] xs q)
    in Deque p [((B1 x,z):zs)] c q'
larger (Deque p (((B1 x,z):zs):(y:ys)) xs q) = 
    let Deque [] b c q' = larger (Deque [] (y:ys) xs q)
    in Deque p (((B1 x,z):zs):b) c q'
larger (Deque p (((B0,z):zs):ys) xs q) = 
    let Just (Node x y,Deque a b c q') = npop (Deque zs ys xs q)
    in Deque p (((B2 x y,z):a):b) c q'
-}

data Size = S0 | S1 | S2 deriving (Show)


prepose' (Deque _ [] _) = S1
prepose' (Deque _ ((((B0,_),_),_):_) _) = S0
prepose' (Deque _ ((((B2 _ _,_),_),_):_) _) = S2

prepose (Deque p ((((B1 _,_),_),[]):xs) q) = prepose' (Deque p xs q)
prepose (Deque p ((((B1 _,_),_),(r:rs)):xs) q) = prepose' (Deque p ((r,rs):xs) q)
prepose x = prepose' x
{-
prepose (Deque _ (((B0,_):_):_) _ _) = S0
prepose (Deque _ [((B1 _,_):_)] [] _) = S1
prepose (Deque _ [((B1 _,_):_)] ((((B0,_):zs):ys):xs) _) = S0
prepose (Deque _ [((B1 _,_):_)] ((((B2 _ _,_):zs):ys):xs) _) = S2
prepose (Deque _ (((B1 _,_):_):(((B0,_):_):_)) _ _) = S0
prepose (Deque _ (((B1 _,_):_):(((B2 _ _,_):_):_)) _ _) = S2
prepose (Deque _ (((B2 _ _,_):_):_) _ _) = S2
prepose _ = S1

prepose (Deque _ [] [] _) = S1
prepose (Deque _ [] ((((B0,_):_):_):_) _) = S0
prepose (Deque _ [] ((((B2 _ _,_):_):_):_) _) = S2
prepose (Deque _ (((B0,_):_):_) _ _) = S0
prepose (Deque _ [((B1 _,_):_)] [] _) = S1
prepose (Deque _ [((B1 _,_):_)] ((((B0,_):zs):ys):xs) _) = S0
prepose (Deque _ [((B1 _,_):_)] ((((B2 _ _,_):zs):ys):xs) _) = S2
prepose (Deque _ (((B1 _,_):_):(((B0,_):_):_)) _ _) = S0
prepose (Deque _ (((B1 _,_):_):(((B2 _ _,_):_):_)) _ _) = S2
prepose (Deque _ (((B2 _ _,_):_):_) _ _) = S2
prepose _ = S1
-}

push x xs =
    let y = Leaf x
    in case prepose xs of
         S2 -> npush y (prefix0 xs)
         _  -> npush y xs
{-
pop xs =
    let ans = case prepose xs of
                S0 -> npop (larger xs)
                _ -> npop xs
    in case ans of
         Nothing -> Nothing
         Just (Leaf y,ys) -> Just (y,ys)
-}

empty = Deque [] [] Nothing

-----------------------------------

fromList = foldr push empty

{-
unList = unfoldr pop

popPreserves x =
    case pop x of
      Nothing -> True
      Just (_,z) -> invariants z && popPreserves z
-}


toListTree' (Leaf x) r = x:r
toListTree' (Node x y) r = toListTree' x (toListTree' y r)

toListTree x = toListTree' x []

nelist (x,xs) = x:xs

joinUp = concatMap (concatMap nelist . nelist)

toList (Deque x y Nothing) = wrapMap toListTree (x ++ (joinUp y))
toList (Deque x y (Just z)) = wrapMap toListTree (x ++ (joinUp y) ++ [(B0,B1 z)])

wrapMap _ [] = []
wrapMap f ((B0,B0):xs) = wrapMap f xs
wrapMap f ((B0,B1 x):xs) = wrapMap f xs ++ f x
wrapMap f ((B0,B2 x y):xs) = wrapMap f xs ++ f x ++ f y
wrapMap f ((B1 x, y):xs) = f x ++ wrapMap f ((B0,y):xs)
wrapMap f ((B2 x y,z):xs) = f x ++ f y ++ wrapMap f ((B0,z):xs)

nextPre0 [] = True
nextPre0 ((B0,_):xs) = nextPre2 xs
nextPre0 ((B1 _,_):xs) = nextPre0 xs
nextPre0 _ = False

nextPre2 [] = True
nextPre2 ((B1 _,_):xs) = nextPre2 xs
nextPre2 ((B2 _ _,_):xs) = nextPre0 xs
nextPre2 _ = False

regularPreAlt (Deque a c _) = 
    let d = a ++ (joinUp c)
    in nextPre0 d || nextPre2 d

nextSuf0 [] = True
nextSuf0 ((_,B0):xs) = nextSuf2 xs
nextSuf0 ((_,B1 _):xs) = nextSuf0 xs
nextSuf0 _ = False

nextSuf2 [] = True
nextSuf2 ((_,B1 _):xs) = nextSuf2 xs
nextSuf2 ((_,B2 _ _):xs) = nextSuf0 xs
nextSuf2 _ = False

regularSufAlt (Deque a c _) = 
    let d = a ++ (joinUp c)
    in nextSuf0 d || nextSuf2 d

bottomBias [] = True
bottomBias [(B2 _ _,B1 _)] = True
bottomBias [(B1 _,B2 _ _)] = True
bottomBias [(B1 _,B1 _)] = True
bottomBias [_] = False
bottomBias (x:y:ys) = bottomBias (y:ys)

bottomOK (Deque _ _ (Just _)) = True
bottomOK (Deque a c Nothing) = 
    let d = a ++ (joinUp c)
    in bottomBias d

bigEnough (Deque _ _ (Just _)) = True
bigEnough x@(Deque _ _ Nothing) =
    case toList x of
      [x] -> False
      _ -> True

ones (B1 _,B1 _) = True
ones _ = False

{-
topLeft ((B0,B1 _):xs) = all ones xs
topLeft ((B2 _ _,B1 _):xs) = all ones xs
topLeft _ = False

topRight ((B1 _,B0):xs) = all ones xs
topRight ((B1 _,B2 _ _):xs) = all ones xs
topRight _ = False

topBoth ((B0,B0):xs) = all ones xs
topBoth ((B0,B2 _ _):xs) = all ones xs
topBoth ((B2 _ _,B0):xs) = all ones xs
topBoth ((B2 _ _,B2 _ _):xs) = all ones xs
topBoth _ = False
-}


top1 (x,xs) =
    do v <- topCheck x
       guard (all ones xs)
       return v

top2 (x,[]) = top1 x
top2 (x,y:ys) =
    do v <- top1 x
       w <- top2 (y,ys)
       guard (nextTop1 v w)
       return v

top3 x [] = top2 x
top3 x (y:ys) =
    do v <- top2 x
       w <- top3 y ys
       guard (not (nextTop1 v w))
       return v

topShape [] = True
topShape (x:xs) = isJust $ top3 x xs

allShape (Deque a b _) =
    all ones a && topShape b

treeDepth (Leaf _) = return 1
treeDepth (Node x y) =
    do i <- treeDepth x
       j <- treeDepth y
       guard (i == j)
       return (i+1)

depthIs i [] = return i
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

dequeDepth (Deque a c Nothing) = 
    let d = a ++ (joinUp c)
    in isJust $ depthIs 1 d
dequeDepth (Deque a c (Just q)) = 
    let d = a ++ (joinUp c)
    in isJust $
       do i <- depthIs 1 d
          j <- treeDepth q
          guard (i == j)
          return i

invariants x = allShape x && regularSufAlt x && regularPreAlt x && bottomOK x && bigEnough x && dequeDepth x

{-
unList . fromList = id
toList . fromList = id
-}

