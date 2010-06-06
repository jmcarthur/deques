{-# LANGUAGE StandaloneDeriving #-}

module Divisible where

import Deque

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
            | Full (LSpine d a)

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

ltor x =
    let (p,q) = ldivlr x 
    in case p of
         Nothing -> q
         Just p' -> lrr p' q

rtol x =
    let (p,q) = rdivlr x 
    in case q of
         Nothing -> p
         Just q' -> lrl p q'
{-
prefix0 x@(LSpine n a bs cs) =
    case pop cs of
      Just (L2 c d es,fs) ->
      _ -> x
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