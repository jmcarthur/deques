{-# LANGUAGE GADTs, StandaloneDeriving, RankNTypes #-}

module ThreeDequeGADT where

import Control.Monad
import Data.Maybe

data Both a = Both !a !a deriving (Show)

data MStack a b where
    M0 :: MStack a a
    MS :: !a -> !a -> !(MStack (Both a) b) -> MStack a b

deriving instance Show a => Show (MStack a b)

data Buffer a = B0
              | B1 !a
              | B2 !a !a deriving (Show)

data Stack a b where
    Stack :: !(Buffer a) -> !(Buffer a) -> !(MStack (Both a) b) -> Stack a b

deriving instance Show a => Show (Stack a b)

data Nest f a b where
    Empty :: Nest f a a
    Full :: !(f a b) -> !(Nest f b c) -> Nest f a c

class ChainShow f where
    showOne :: (a -> String) -> f a b -> String
    showMore :: (a -> String) -> f a b -> b -> String

showNest :: ChainShow f => (a -> String) -> Nest f a b -> String
showNest _ Empty = "Empty"
showNest s (Full x xs) = "(Full "++(showOne s x)++" "++(showNest (showMore s x) xs)++")"

instance (Show a, ChainShow f) => Show (Nest f a b) where
    show = showNest show

showBoth f (Both p q) = "(Both "++(f p)++" "++(f q)++")"

showBuffer _ B0 = "B0"
showBuffer f (B1 x) = "(B1 "++(f x)++")"
showBuffer f (B2 x y) = "(B2 "++(f x)++" "++(f y)++")"

instance ChainShow MStack where
    showOne _ M0 = "M0"
    showOne f (MS x y z) = "(MS "++(f x)++" "++(f y)++" "++(showOne (showBoth f) z)++")"
    showMore f M0 = f
    showMore f (MS _ _ x) = showMore (showBoth f) x

instance ChainShow Stack where
    showOne f (Stack x y z) = "(Stack "++(showBuffer f x)++" "++(showBuffer f y)++" "++(showOne (showBoth f) z)++")"
    showMore f (Stack _ _ z) = showMore (showBoth f) z

data SM t = None
          | Some !t deriving (Show)

showSM :: (a -> String) -> SM a -> String
showSM _ None = "None"
showSM f (Some x) = "(Some "++(f x)++")"

data NE f a b where
    NE :: !(f a b) -> !(Nest f b c) -> NE f a c

showNE :: ChainShow f => (a -> String) -> NE f a b -> String
showNE f (NE x y) = "(NE "++(showOne f x)++" "++(showNest (showMore f x) y)++")"

instance (Show a, ChainShow f) => Show (NE f a b) where
    show = showNE show

instance ChainShow f => ChainShow (Nest f) where
    showOne = showNest
    showMore f Empty = f
    showMore f (Full x xs) = showMore (showMore f x) xs

instance ChainShow f => ChainShow (NE f) where
    showOne = showNE
    showMore f (NE x y) = showMore (showMore f x) y

type StackStack = NE Stack

type ThreeStack = Nest StackStack

data Deque a where
    Deque :: !(MStack a b) -> !(ThreeStack b c) -> !(SM c) -> Deque a

showDeque :: (a -> String) -> Deque a -> String
showDeque f (Deque x y z) = 
    let g = showMore f x 
    in "(Deque "++(showOne f x)++" "++(showNest g y)++" "++(showSM (showMore g y) z)++")"

instance Show a => Show (Deque a) where
    show = showDeque show

invariants x = bottomOK x && allShape x && bufsAlternate x

data Size = Small | Medium | Large

bufSize B0 = Small
bufSize B1{} = Medium
bufSize B2{} = Large

sameSize Small Small = True
sameSize Large Large = True
sameSize _ _ = False

nextSize x Medium = x
nextSize _ y = y

bufsAlternate :: Deque a -> Bool
bufsAlternate (Deque _ x _) = bufsAltStart Medium Medium x

bufsAltStart :: Size -> Size -> ThreeStack a b -> Bool
bufsAltStart _ _ Empty = True
bufsAltStart xs ys (Full (NE (Stack x y _) Empty) r) = 
    let xs' = bufSize x
        ys' = bufSize y in
    not (sameSize xs xs')
    &&
    not (sameSize ys ys')
    &&
    bufsAltStart (nextSize xs xs') (nextSize ys ys') r
bufsAltStart xs ys (Full (NE (Stack x y _) (Full z zs)) r) = 
    let xs' = bufSize x
        ys' = bufSize y in
    not (sameSize xs xs')
    &&
    not (sameSize ys ys')
    &&
    bufsAltStart (nextSize xs xs') (nextSize ys ys') (Full (NE z zs) r)

data Top = Prefix | Suffix | Twofix deriving (Show)

topCheck B1{} B1{} = Nothing
topCheck B0{} B1{} = Just Prefix
topCheck B2{} B1{} = Just Prefix
topCheck B1{} B0{} = Just Suffix
topCheck B1{} B2{} = Just Suffix
topCheck _ _ = Just Twofix

nextTop1 Prefix Prefix = True
nextTop1 Suffix Suffix = True
nextTop1 _ _ = False

top1 (Stack x y _) = topCheck x y

top2 :: StackStack a b -> Maybe Top
top2 (NE x Empty) = top1 x
top2 (NE x (Full y ys)) =
    do v <- top1 x
       w <- top2 (NE y ys)
       guard (nextTop1 v w)
       return v

top3 :: StackStack a b -> ThreeStack c d -> Maybe Top
top3 x Empty = top2 x
top3 x (Full y ys) =
    do v <- top2 x
       w <- top3 y ys
       guard (not (nextTop1 v w))
       return v

topShape :: ThreeStack a b -> Bool
topShape Empty = True
topShape (Full x xs) = isJust $ top3 x xs

allShape (Deque a b _) = topShape b

bottomOK :: Deque a -> Bool
bottomOK (Deque _ b (Some _)) = lastPair True bottomSome b
bottomOK (Deque _ b None ) = lastPair True bottomNone b

lastPair :: Bool -> (Size -> Size -> Bool) -> ThreeStack a b -> Bool
lastPair ans cont (Full _ x@(Full _ _)) = lastPair ans cont x
lastPair ans cont Empty = ans
lastPair ans cont (Full (NE _ (Full x xs)) Empty) = lastPair ans cont (Full (NE x xs) Empty)
lastPair ans cont (Full (NE (Stack x y M0) Empty) Empty) = cont (bufSize x) (bufSize y)
lastPair ans cont (Full (NE _ Empty) Empty) = cont Medium Medium

bottomSome Small Small = False
bottomSome _ _ = True

bottomNone Small Small = True
bottomNone Small _ = False
bottomNone _ Small = False
bottomNone _ _ = True

cons13 :: Buffer a -> Buffer a -> MStack (Both a) b -> ThreeStack b c -> ThreeStack a c
cons13 x y xs Empty = Full (NE (Stack x y xs) Empty) Empty
cons13 x y xs t@(Full (NE (Stack p q pq) r) s) =
    let Just i = topCheck x y
        Just j = topCheck p q 
    in if nextTop1 i j
       then Full (NE (Stack x y xs) (Full (Stack p q pq) r)) s
       else Full (NE (Stack x y xs) Empty) t

empty = Deque M0 Empty None

npush :: a -> Deque a -> Deque a
npush x (Deque M0 Empty None) = Deque M0 Empty (Some x) 
npush x (Deque M0 Empty (Some y)) = Deque (MS x y M0) Empty None 
npush x (Deque M0 (Full (NE (Stack B0 (B1 z) zs) Empty) xs) q) = Deque (MS x z zs) xs q 
npush x (Deque M0 (Full (NE (Stack B0 (B1 z) zs) (Full y ys)) xs) q) = Deque (MS x z zs) (Full (NE y ys) xs) q 
npush x (Deque M0 (Full (NE (Stack B0 z zs) Empty) xs) q) = Deque M0 (cons13 (B1 x) z zs xs) q
npush x (Deque M0 (Full (NE (Stack (B1 y) z zs) Empty) xs) q) = Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) xs) q
npush x (Deque M0 (Full (NE (Stack (B1 y) z zs) (Full r rs)) xs) q) = Deque M0 (Full (NE (Stack (B2 x y) z zs) Empty) (Full (NE r rs) xs)) q
npush x (Deque (MS y z zs) rs q) = Deque M0 (cons13 (B2 x y) (B1 z) zs rs) q

ninject :: Deque a -> a -> Deque a
ninject (Deque M0 Empty None) x = Deque M0 Empty (Some x)
ninject (Deque M0 Empty (Some y)) x = Deque (MS y x M0) Empty None
ninject (Deque M0 (Full (NE (Stack (B1 z) B0 zs) Empty) xs) q) x = Deque (MS z x zs) xs q
ninject (Deque M0 (Full (NE (Stack (B1 z) B0 zs) (Full y ys)) xs) q) x = Deque (MS z x zs) (Full (NE y ys) xs) q
ninject (Deque M0 (Full (NE (Stack z B0 zs) Empty) xs) q) x = Deque M0 (cons13 z (B1 x) zs xs) q 
ninject (Deque M0 (Full (NE (Stack z (B1 y) zs) Empty) xs) q) x = Deque M0 (Full (NE (Stack z (B2 y x) zs) Empty) xs) q 
ninject (Deque M0 (Full (NE (Stack z (B1 y) zs) (Full r rs)) xs) q) x = Deque M0 (Full (NE (Stack z (B2 y x) zs) Empty) (Full (NE r rs) xs)) q
ninject (Deque (MS z y zs) rs q) x = Deque M0 (cons13 (B1 z) (B2 y x) zs rs) q

data Back a where
    Back :: !(ThreeStack a b) -> !(SM b) -> Back a

prefix0' :: ThreeStack a b -> SM b -> Back a
prefix0' (Full (NE (Stack (B2 x y) z zs) Empty) xs) q = 
    case npush (Both x y) (Deque zs xs q) of
      Deque a c q' -> Back (cons13 B0 z a c) q'
prefix0' (Full (NE (Stack (B2 x y) z zs) (Full r rs)) xs) q = 
    case npush (Both x y) (Deque zs (Full (NE r rs) xs) q) of
      Deque a c q' -> Back (cons13 B0 z a c) q'

prefix0 :: ThreeStack a b -> SM b -> Back a
prefix0 (Full (NE (Stack (B1 x) z zs) rs) xs) q = 
    case prefix0' xs q of
      Back c q' -> Back (Full (NE (Stack (B1 x) z zs) rs) c) q'
prefix0 x y = prefix0' x y

suffix0' :: ThreeStack a b -> SM b -> Back a
suffix0' (Full (NE (Stack z (B2 x y) zs) Empty) xs) q = 
    case ninject (Deque zs xs q) (Both x y) of
       Deque a c q' -> Back (cons13 z B0 a c) q'
suffix0' (Full (NE (Stack z (B2 x y) zs) (Full r rs)) xs) q = 
    case ninject (Deque zs (Full (NE r rs) xs) q) (Both x y) of
       Deque a c q' -> Back (cons13 z B0 a c) q'

suffix0 :: ThreeStack a b -> SM b -> Back a
suffix0 (Full (NE (Stack z (B1 x) zs) rs) xs) q = 
    case suffix0' xs q of
      Back c q' -> Back (Full (NE (Stack z (B1 x) zs) rs) c) q'
suffix0 x y = suffix0' x y

fixHelp :: (forall a b . ThreeStack a b -> SM b -> Back a) -> Deque t -> Deque t
fixHelp f (Deque b c d) = 
    case f c d of
      Back c' d' -> Deque b c' d'

prepose' :: ThreeStack a b -> Size
prepose' Empty = Medium
prepose' (Full (NE (Stack B0{} _ _) _) _) = Small
prepose' (Full (NE (Stack B2{} _ _) _) _) = Large

prepose (Deque _ (Full (NE (Stack B1{} _ _) _) x) _) = prepose' x
prepose (Deque _ x _) = prepose' x

sufpose' :: ThreeStack a b -> Size
sufpose' Empty = Medium
sufpose' (Full (NE (Stack _ B0{} _) _) _) = Small
sufpose' (Full (NE (Stack _ B2{} _) _) _) = Large

sufpose (Deque _ (Full (NE (Stack _ B1{} _) _) x) _) = sufpose' x
sufpose (Deque _ x _) = sufpose' x

push x xs =
    case prepose xs of
      Large -> npush x (fixHelp prefix0 xs)
      _  -> npush x xs

inject xs x =
    case sufpose xs of
      Large -> ninject (fixHelp suffix0 xs) x
      _  -> ninject xs x

{-
data Buffer a s where
    B0 :: Buffer a S0
    B1 :: !a -> Buffer a S1
    B2 :: !a -> !a -> Buffer a S2


data NEMStack a b where
    M1 :: !a -> !a -> NEMStack a (Both a)
    MS :: !a -> !a -> !(NEMStack (Both a) b) -> NEMStack a b

data MStack a b where
    NEMStack :: !(NEMStack a b) -> MStack a b
    EMStack :: MStack a a

data S0
data S1
data S2


data Medium
data Prefix
data Suffix
data Twofix

data TopType a b c where
    T00 :: TopType S0 S0 Twofix
    T01 :: TopType S0 S1 Prefix
    T02 :: TopType S0 S2 Twofix
    T10 :: TopType S1 S0 Suffix

    T12 :: TopType S1 S2 Suffix
    T20 :: TopType S2 S0 Twofix
    T21 :: TopType S2 S1 Prefix
    T22 :: TopType S2 S2 Twofix


data NextTop a where
    Prefix :: NextTop Prefix 
    Suffix :: NextTop Suffix 

data Opp a b where
    O1 :: Opp S1 S1
    O0 :: Opp S0 S2
    O2 :: Opp S2 S0

data StackStack a b c s t c d e f where
    Lone :: Stack a b c s t c d -> StackStack a b c s t a b d e
    Join :: Stack a b c s t d e -> 
            NextTop c ->
            Opp a f -> Opp b g ->
            StackStack f g c (Both t) u h i j k ->
            StackStack a b c s u h i j k

data Switch a b where
    PreTwo :: Switch Prefix Twofix
    PreSuf :: Switch Prefix Suffix
    TwoAny :: Switch Twofix b
    SufTwo :: Switch Suffix Twofix
    SufPre :: Switch Suffix Prefix
           

data NEThreeStack a b w s t c d e f where
    Single :: StackStack a b w c s t c d e f -> ThreeStack a b w s t c d e f
    More :: StackStack a b w s t c d e f ->
            Switch w v ->
            StackStack t u g h i j
            
-}
{-

Zero
    T0
    OneOne :: TopType One One Medium
     :: TopType 
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

-}