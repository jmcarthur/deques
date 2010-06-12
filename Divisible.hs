module Divisible where

import Deque
import qualified Data.List as L
import Loose 

type Nat = Integer

data Even d s = D0 (d s)
              | D2 s s (d s)

instance (Deque d, Show s) => Show (Even d s) where
    show (D0 x) = "(D0 "++(showDeque x)++")"
    show (D2 x y z) = "(D2 ("++(show x)++") "++(show y)++" "++(showDeque z)++")"

data LSpine d a = LSpine Nat a (d (RSpine d a)) (d (Even d (RSpine d a)))
data RSpine d a = RSpine Nat (d (Even d (LSpine d a))) (d (LSpine d a)) a

instance (Show a, Deque d) => Show (LSpine d a) where
    show (LSpine n x ys zs) = "(LSpine "++(show n)++" "++(show x)++" "++(showDeque ys)++" "++(showDeque zs)++")"

instance (Show a,Deque d) => Show (RSpine d a) where
    show (RSpine n xs ys z) = "(RSpine "++(show n)++" "++(showDeque xs)++" "++(showDeque ys)++" "++(show z)++")"

showDeque xs = show $ dequeToList xs
dequeToList xs = 
    case pop xs of
      Nothing -> []
      Just (y,ys) -> y : (dequeToList ys)

data DD d a = Empty
            | Full (LSpine d a) deriving (Show)

full x =
    case pop x of
      Nothing -> False
      _ -> True

nil x = not (full x)

lrr l@(LSpine n a bs cs) r@(RSpine m ds es f) =
    let nm = n+m
    in case pop ds of
         Nothing -> RSpine nm empty (push l es) f
         Just (D0 d,ds') -> RSpine nm (push (D0 (push l d)) ds') es f
         Just (D2 d1 d2 d,ds') -> RSpine nm (push (D2 d1 d2 (push l d)) ds') es f

lrl l@(LSpine n a bs cs) r@(RSpine m ds es f) =
    let nm = n+m
    in case eject cs of
         Nothing -> LSpine nm a (inject bs r) empty
         Just (cs',D0 c) -> LSpine nm a bs (inject cs' (D0 (inject c r)))
         Just (cs',D2 c1 c2 c) -> LSpine nm a bs (inject cs' (D2 c1 c2 (inject c r)))

rsize (RSpine n _ _ _) = n
lsize (LSpine n _ _ _) = n

ldivlr (LSpine n a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of 
            Nothing -> (Nothing, RSpine 1 empty empty a)
            Just (bs',b) -> (Just (LSpine (n-rsize b) a bs' empty), b)
      Just (cs',D0 c) -> 
          case eject c of
            Nothing -> ldivlr (LSpine n a bs cs')
            Just (c',d) -> (Just (LSpine (n-rsize d) a bs (inject cs' (D0 c'))), d)
      Just (cs',D2 c1 c2 c) -> 
          case eject c of
            Nothing -> 
                case eject cs' of
                  Nothing -> (Just (LSpine (n-rsize c2) a (inject bs c1) empty), c2)
                  Just (ds, D0 d) -> (Just (LSpine (n-rsize c2) a bs (inject ds (D0 (inject d c1)))), c2)
                  Just (ds, D2 d1 d2 d) -> (Just (LSpine (n-rsize c2) a bs (inject ds (D2 d1 d2 (inject d c1)))), c2)
            Just (c',d) -> (Just (LSpine (n-rsize d) a bs (inject cs' (D2 c1 c2 c'))), d)

rdivlr (RSpine n cs bs a) =
    case pop cs of
      Nothing ->
          case pop bs of 
            Nothing -> (LSpine 1 a empty empty, Nothing)
            Just (b,bs') -> (b,Just (RSpine (n-lsize b) empty bs' a))
      Just (D0 c,cs') -> 
          case pop c of
            Nothing -> rdivlr (RSpine n cs' bs a)
            Just (d,c') -> (d, Just (RSpine (n-lsize d) (push (D0 c') cs') bs a))
      Just (D2 c1 c2 c,cs') -> 
          case pop c of
            Nothing -> 
                case pop cs' of
                  Nothing -> (c1, Just (RSpine (n-lsize c1) empty (push c2 bs) a))
                  Just (D0 d, ds) -> (c1, Just (RSpine (n-lsize c1) (push (D0 (push c2 d)) ds) bs a))
                  Just (D2 d1 d2 d, ds) -> (c1, Just (RSpine (n-lsize c1) (push (D2 d1 d2 (push c2 d)) ds) bs a))
            Just (d,c') -> (d, Just (RSpine (n-lsize d) (push (D2 c1 c2 c') cs') bs a))

{-
ldiv (LSpine a bs cs')
            Just (c',d) -> (LSpine a bs (inject cs (D0 c')), d)
-}

{-
BUG 
eject $ push 4 $ push 3 $ push 2 (Empty :: DD TM Int)
-}

ltor' x =
    let (p,q) = ldivlr x 
    in case p of
         Nothing -> q
         Just p' -> lrr p' q

rtol' x =
    let (p,q) = rdivlr x 
    in case q of
         Nothing -> p
         Just q' -> lrl p q'

data Lean l r = Lone r
              | Lentrist l r
              | Rightist l r r

ltop (LSpine n a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of 
            Nothing -> Lone (RSpine 1 empty empty a)
            Just (bs',b) -> Lentrist (LSpine (n-rsize b) a bs' empty) b
      Just (cs',D0 c) -> 
          case eject c of
            Nothing -> ltop (LSpine n a bs cs')
            Just (c',d) -> Lentrist (LSpine (n-rsize d) a bs (inject cs' (D0 c'))) d
      Just (cs',D2 c1 c2 c) -> 
          case eject c of
            Nothing -> Rightist (LSpine (n-rsize c1-rsize c2) a bs cs') c1 c2
            Just (c',d) -> Lentrist (LSpine (n-rsize d) a bs (inject cs' (D2 c1 c2 c'))) d

data Rean l r = Rone l
              | Rentrist l r
              | Leftist l l r

rtop (RSpine n cs bs a) =
    case pop cs of
      Nothing ->
          case pop bs of 
            Nothing -> Rone (LSpine 1 a empty empty)
            Just (b,bs') -> Rentrist b (RSpine (n-lsize b) empty bs' a)
      Just (D0 c,cs') -> 
          case pop c of
            Nothing -> rtop (RSpine n cs' bs a)
            Just (d,c') -> Rentrist d (RSpine (n-lsize d) (push (D0 c') cs') bs a)
      Just (D2 c1 c2 c,cs') -> 
          case pop c of
            Nothing ->  Leftist c1 c2 (RSpine (n-lsize c1-lsize c2) cs' bs a)
            Just (d,c') -> Rentrist d (RSpine (n-lsize d) (push (D2 c1 c2 c') cs') bs a)

-- TODO sizeP invariant

ltor x =
    case ltop x of
      Lone y -> y
      Lentrist y z -> lrr y z
      Rightist p q r -> lrrr p q r

lrrr p q (RSpine n ds es f) =
    case pop ds of
      Just (D2 _ _ _,_) -> RSpine (n+lsize p+rsize q) (push (D0 (push (lrl p q) empty)) ds) es f
      _ -> RSpine (n+lsize p+rsize q) (push (D2 p (rtol' q) empty) ds) es f

rtol x =
    case rtop x of
      Rone y -> y
      Rentrist y z -> lrl y z
      Leftist p q r -> llrr p q r

llrr (LSpine n a bs cs) p q = 
    case eject cs of
      Just (_,D2 _ _ _) -> LSpine (n+lsize p+rsize q) a bs (inject cs (D0 (push (lrr p q) empty)))
      _ -> LSpine (n+lsize p+rsize q) a bs (inject cs (D2 (ltor' p) q empty))

mpush a bs cs = 
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> (push a empty, empty)
            Just (D0 c', cs') -> (push a c', cs')
            _ -> error "mpush D2"
      Just (b,bs') -> (empty, push (D2 a b bs') cs)

prefix0 x@(LSpine n a bs cs) =
    case pop cs of
      Just (D2 c d es,fs) ->
          let cd = lrr (rtol c) d
              (gs,hs) = mpush cd es fs
          in LSpine n a bs (push (D0 gs) hs)
      _ -> x

npush x (LSpine n a bs cs) =
    let (bs',cs') = mpush (RSpine 1 empty empty a) bs cs
    in LSpine (n+1) x bs' cs'

dpush x Empty = Full (LSpine 1 x empty empty)
dpush x (Full xs) = Full $ npush x $ prefix0 xs

minject cs bs a = 
    case eject bs of
      Nothing ->
          case eject cs of
            Nothing -> (empty,inject empty a)
            Just (cs', D0 c) -> (cs',inject c a)
            _ -> error "minject D2"
      Just (bs',b) -> (inject cs (D2 b a bs'),empty)

suffix0 x@(RSpine n cs bs a) =
    case eject cs of
      Just (fs, D2 d c es) ->
          let dc = lrl d (ltor c)
              (hs,gs) = minject fs es dc
          in RSpine n (inject hs (D0 gs)) bs a
      _ -> x

ninject (RSpine n cs bs a) x =
    let (cs',bs') = minject cs bs (LSpine 1 a empty empty)
    in RSpine (n+1) cs' bs' x

dinject' Empty x = RSpine 1 empty empty x
dinject' (Full xs) x = ninject (suffix0 $ ltor xs) x

dinject xs x = Full $ rtol $ dinject' xs x

mpop bs cs = 
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> Nothing
            Just (D2 c1 c2 c', cs') -> Just (c1,push c2 c',cs')
            _ -> error "mpop D0"
      Just (b,bs') -> Just (b,empty, push (D0 bs') cs)

prefix2 x@(LSpine n a bs cs) =
    case pop cs of
      Just (D0 es,fs) ->
          case mpop es fs of
            Nothing -> LSpine n a bs empty
            Just (p,qs,rs) -> 
                let (p1,Just p2) = rdivlr p
                in LSpine n a bs (push (D2 (ltor p1) p2 qs) rs)
      _ -> x


ronly (RSpine 1 _ _ x) = x
ronly _ = error "ronly"

npop (LSpine n a bs cs) =
    case mpop bs cs of
      Nothing -> (a,Empty)
      Just (p,q,r) -> (a,Full (LSpine (n-1) (ronly p) q r))

dpop Empty = Nothing
dpop (Full xs) = Just $ npop $ prefix2 xs

meject cs bs = 
    case eject bs of
      Nothing ->
          case eject cs of
            Nothing -> Nothing
            Just (cs',D2 c1 c2 c') -> Just (cs',inject c' c1,c2)
            _ -> error "meject D0"
      Just (bs',b) -> Just (inject cs (D0 bs'),empty,b)

suffix2 x@(RSpine n cs bs a) =
    case eject cs of
      Just (fs,D0 es) ->
          case meject fs es of
            Nothing -> RSpine n empty bs a
            Just (rs,qs,p) -> 
                let (Just p1,p2) = ldivlr p
                in RSpine n (inject rs (D2 p1 (rtol p2) qs)) bs a
      _ -> x

lonly (LSpine 1 x _ _) = x
lonly _ = error "lonly"

neject (RSpine n cs bs a) =
    case meject cs bs of
      Nothing -> (Empty,a)
      Just (ps,qs,r) -> (Full (rtol (RSpine (n-1) ps qs (lonly r))),a)

deject Empty = Nothing
deject (Full xs) = Just $ neject $ suffix2 $ ltor xs

instance Deque d => Deque (DD d) where
    empty = Empty
    push = dpush
    pop = dpop
    inject = dinject
    eject = deject

instance ({- Loose d, -}Deque d) => Loose (DD d a) where
    proper x = depthP x && alternateP x && perfectP x {- && nestP x -}

{-
nestP Empty = True
nestP (Full l) = nestL l

nestL (LSpine _ x xs) =
    case (pop x, pop xs) of
      (Nothing, Nothing) -> True
      _ -> proper x && proper seach nestR x xs
            
    proper x &&
    case pop xs of
      Nothing -> True
      Just (D0 
-}
-- TODO: replicate
-- TODO: deques that can be joined on left or right
-- TODO: tests
-- TODO: slower split?
-- TODO: proof of divide's evenness
-- TODO: replace (since no split/join
-- TODO: interpolation search? better measure on indexing complexit (fast near ends and middle?)

fromList xs = foldr dpush Empty xs
toList xs = L.unfoldr dpop xs

divide Empty = (Empty,Empty)
divide (Full x) =
    let (p,q) = ldivlr x 
        q' = Full $ rtol q
        p' = case p of
               Nothing -> Empty
               Just v -> Full v
    in (p',q')

size Empty = 0
size (Full x) = lsize x

data DBG = Leaf Bool String
         | Branch Bool String DBG DBG deriving (Show)

dval (Leaf x _) = x
dval (Branch x _ _ _) = x

band v p q = p && q --Branch (dval p && dval q) v p q
leaf x y = x -- Leaf x y

--ldepth :: Deque d => Nat -> Maybe Nat -> d (RSpine d a) -> d (Even d (RSpine d a)) -> Bool
ldepth n m bs cs =
    case pop bs of
      Nothing ->
          case pop cs of
            Nothing -> 
                case m of
                  Nothing -> leaf True (show n) 
                  Just m' -> leaf (n==m') (show (n,m'))
            Just (D0 c',ds) 
              -> ldepth (n+1) m c' ds
            Just (D2 (RSpine _ p1 p2 _ ) q r,ss) 
              -> band "L2" 
                 (rdepth (Just (n-0)) 1 p1 p2)
                 (ldepth n m (push q r) ss)
      Just (RSpine _ b1 b2 _,bs') 
          -> band "Lall"
             (rdepth (Just (n-0)) 1 b1 b2)
             (ldepth (n+1) m bs' cs)

--rdepth :: Deque d => Maybe Nat -> Nat -> d (Even d (LSpine d a)) -> d (LSpine d a) -> Bool
rdepth m n cs bs = 
    case eject bs of
      Nothing ->
          case eject cs of
            Nothing -> 
                case m of
                  Nothing -> leaf True (show n)
                  Just m' -> leaf (n == m') (show (n,m'))
            Just (ds,D0 c') 
              -> rdepth m (n+1) ds c'
            Just (ss,D2 (LSpine _ _ p1 p2) q r) 
              -> band "R2"
                 (ldepth 1 (Just (n-0)) p1 p2)
                 (rdepth m n ss (inject r q))
      Just (bs',LSpine _ _ b1 b2) 
          -> band "Rall"
             (ldepth 1 (Just (n-0)) b1 b2)
             (rdepth m (n+1) cs bs')

depthP Empty = True
depthP (Full (LSpine _ _ x y)) = ldepth 1 Nothing x y

data Force = Big | Small | Any

{-
biggest _ 1 = 1
biggest Nothing n = maximum
-}

topalt Any x = 
    case pop x of
      Nothing -> True
      Just (D0 _,xs) -> topalt Big xs
      Just (D2 _ _ _,xs) -> topalt Small xs
topalt Big x = 
    case pop x of
      Nothing -> True
      Just (D0 _,xs) -> False
      Just (D2 _ _ _,xs) -> topalt Small xs
topalt Small x = 
    case pop x of
      Nothing -> True
      Just (D0 _,xs) -> topalt Big xs
      Just (D2 _ _ _,xs) -> False

dlast xs =
    case eject xs of
      Nothing -> Nothing
      Just (_,ans) -> Just ans

lastRight xs ys =
    case eject ys of
      Nothing -> dlast xs
      Just (zs,D0 z) -> 
          case dlast z of
            Nothing -> lastRight xs zs
            x -> x
      Just (_,D2 _ z' z) -> 
          case dlast z of
            Nothing -> Just z'
            x -> x

alternateP Empty = True
alternateP (Full (LSpine _ _ xs ys)) = 
    topalt Any ys &&
    case lastRight xs ys of
      Nothing -> True
      Just (RSpine _ zs _ _) -> topalt Any zs

deach f xs =
    case pop xs of
      Nothing -> True
      Just (y,ys) -> f y && deach f ys

leven (LSpine _ _ xs ys) =
    case pop ys of
      Nothing -> deach reven xs
      Just _ -> False
reven (RSpine _ ys xs _) =
    case pop ys of
      Nothing -> deach leven xs
      Just _ -> False

seject xs ys =
    case eject ys of
      Nothing -> 
          case eject xs of
            Nothing -> Nothing
            Just (zs,z) -> Just (zs,empty,z)
      Just (zs,D0 z) -> 
          case eject z of
            Nothing -> seject xs zs
            Just (ps,p) -> Just (xs,inject zs (D0 ps),p)
      Just (zs,D2 z1 z2 z) -> 
          case eject z of
            Nothing -> 
                case eject zs of
                  Nothing -> Just (inject xs z1,empty,z2)
                  Just (ps, D0 p) -> Just (xs, inject ps (D0 (inject p z1)), z2)
                  Just (ps, D2 p1 p2 p) -> Just (xs, inject ps (D2 p1 p1 (inject p z1)), z2)
            Just (ps,p) -> Just (xs,inject zs (D2 z1 z2 ps),p)


seach f xs ys =
    deach f xs &&
    case pop ys of
      Nothing -> True
      Just (D0 z,zs) -> seach f z zs
      Just (D2 z1 z2 z,zs) -> f z1 && f z2 && seach f z zs

perfectP Empty = True
perfectP (Full (LSpine a b xs ys)) =
    case seject xs ys of
      Nothing -> True
      Just (ps,qs,RSpine _ ss rs _) -> 
          seach reven ps qs &&
          seach leven rs ss

-- middle trees perfect

{-
and [let x = (fromList [0..i] :: DD [] Int) in depthP x && alternateP x && perfectP x | i <- [1..1000]]
-}

{-
npush x Empty = Single x 
npush x (Single y) = More (LSpine x empty empty) Empty (RSpine empty empty y) 
npush x (More (LSpine a bs cs) cn rs) =
    case pop bs of
      Just (b',bs') -> More (LSpine x empty (push (L2 (Single a) b' bs') cs)) cn rs 
      Nothing ->
          case pop cs of
            Just (L0 cs1,cs2) -> More (LSpine x (push (RSpine empty empty a) cs1) cs2) cn rs
            Just (L2 _ _ _,_) -> error "npush 2-exposed"
            Nothing -> 
                case cn of
                  Empty -> More (LSpine x empty empty) (Single a) rs -}{-
                  Some cn' ->
                        let cx = get1c cn'
                            rx = get1r rs
                        in More (LSpine x (push (RSpine empty empty a) empty) empty) None (RSpine empty (inject empty (LSpine cx empty empty)) rx)

-}

{-
mpush xy bs cs cn rs =
    case pop bs of
      Just (b',bs') -> (empty,push (L2 (Gop xy) b' bs') cs,cn,rs)
      Nothing ->
          case pop cs of
            Just (L0 cs1,cs2) -> (push xy cs1, cs2, cn, rs)
            Just (L2 _ _ _,_) -> error "npush 2-exposed"
            Nothing -> 
                case cn of
                  None -> (empty,empty,Some (Gop xy),rs) -} {-
                  Some cn' ->
                        let cx = get1c cn'
                            rx = get1r rs
                        in More (LSpine x (push xy empty) empty) None (RSpine empty (inject empty (LSpine cx empty empty)) rx) -}
    

{-
  
-}    

{-
divide Empty = (Empty,Empty)
divide (Single x) = (Single x,Empty)
divide (More l Empty r) = (ltoc l, rtoc r)
divide (More l (Single c) r) =
    let l' = get1l l
    in (More l Empty (RSpine empty empty c), rtoc r)
-}
{-
divide (More l (More a b c) r) =
    let abc = ctor a b c
    in (More l Empty abc,r)
-}
{-
ctor (More a b (RSpine cs ds e)) =
    case pop cs of
      Just (R2 _ _ _,_) ->
          let bigl = 
              let LSpine p qs rs = a
              in case eject rs of
                   Nothing -> LSpine p (inject qs b) rs
                   Just (rs',L0 r) -> LSpine p qs (inject rs' (L0 (inject r b)))
                   Just (rs',L2 x y r) -> LSpine p qs (inject rs' (L2 x y (inject r b)))
          in RSpine (push (L0 bigl
      _ -> RSpine (push (R2 a b empty) cs) ds e



ltoc (LSpine a bs cs) =
    case eject cs of
      Nothing ->
          case eject bs of
            Nothing -> Single a
            Just (bs',b) -> More (LSpine a bs' empty) Empty b
      Just (cs',L0 c) ->
          case eject c of
            Nothing -> ltoc (LSpine a bs cs')
            Just (ds,d) -> More (LSpine a bs (inject cs' (L0 ds))) Empty d
      Just (cs',L2 c1 c2 c) ->
          case eject c of
            Nothing -> More (LSpine a bs cs') c1 c2
            Just (ds,d) -> More (LSpine a bs (inject cs' (L2 c1 c2 ds))) Empty d

rtoc (RSpine as bs c) =      
    case pop as of
      Nothing ->
          case pop bs of
            Nothing -> Single c
            Just (b,bs') -> More b Empty (RSpine empty bs' c)
      Just (R0 a,as') ->
          case pop a of
            Nothing -> rtoc (RSpine as' bs c)
            Just (z,zs) -> More z Empty (RSpine (push (R0 zs) as') bs c)
      Just (R2 a a1 a2,as') ->
          case pop a of
            Nothing -> More a1 a2 (RSpine as' bs c)
            Just (z,zs) -> More z Empty (RSpine (push (R2 zs a1 a2) as') bs c)
-}

data Opt a = None
           | Some a deriving (Show)


{-
divide (More (LSpine a bs cs) ds (RSpine es fs g)) =
    case 
-}
{-
data Div d a = Spine (Spine d a)
             | Single a deriving (Show)
-}

-- TODO: Maybe bit at end?
{-
get1l (LSpine p q r) = 
    case (pop q, pop r) of
      (Nothing,Nothing) -> p
      _ -> error "LSpine too big"
get1r (RSpine p q r) = 
    case (pop p, pop q) of
      (Nothing,Nothing) -> r
      _ -> error "RSpine too big"
-}
{-
get1c (Dem p) = get1l p
get1c (Gop p) = get1r p
-}                            

{-
--lrlcomb :: LSpine d a -> RSpine d a -> LSpine d a
lrlcomb (LSpine x y z) r = 
    case eject z of
      Nothing -> LSpine x (inject y r) empty
      Just (zs,L0 w) -> LSpine x y (zs `inject` (L0 (w `inject` r)))
      Just (zs,L2 p q w) -> LSpine x y (zs `inject` (L2 p q (w `inject` r)))

lrrcomb l (RSpine z y x) = 
    case pop z of
      Nothing -> RSpine empty (push l y) x
      Just (R0 w,zs) -> RSpine (push (R0 (push l w)) zs) y x
      Just (R2 w p q,zs) -> RSpine (push (R2 (push l w) p q) zs) y x
          
ltor (LSpine x y z) =
    case eject z of
      Nothing ->
          case eject y of
            Nothing -> RSpine empty empty x
            Just (rs,r) -> lrrcomb (LSpine x rs empty) r
      Just (rs,L0 r) -> 
          case eject r of
            Nothing -> ltor (LSpine x y rs) --error "ends in 0 error 1"
            Just (ss,s) -> 
                case pop ss of
                  Nothing -> lrrcomb (LSpine x y rs) s 
                  _ -> lrrcomb (LSpine x y (rs `inject` (L0 ss))) s
      Just (rs,L2 p q r) -> 
          case eject r of
            Nothing -> 
                larrcomb (LSpine x y rs
                let RSpine qc qb qa = q
                in case pop qc of
                     


ltor (LSpine x y rs)
            Just (ss,s) -> 
                case pop ss of
                  Nothing -> lrrcomb (LSpine x y rs) s
                  _ -> lrrcomb (LSpine x y (rs `inject` (L0 ss))) s
-}