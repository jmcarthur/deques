{-# LANGUAGE NamedFieldPuns #-}

module LazyRealTimeDeque where

{- This is a model of the real-time deques (that is, O(1) worst-case performance)
   invented by Okasaki
-}

import Data.List
import Deque
import Loose

type Nat = Integer

data LRT a = LRT  {front :: [a], 
                   sizef :: Nat,
                   rear :: [a], 
                   sizer :: Nat,
                   pendingf :: [a], 
                   pendingr :: [a]} deriving (Show)

{-

    (* INVARIANTS                                               *)
    (*  1. sizef = length front /\ sizer = length rear          *)
    (*  2. sizer <= c * sizef + 1 /\ sizef <= c * sizer + 1     *)
    (*  3. pendingf <= max (2j+2-k,0) /\                        *)
    (*     pendingr <= max (2j+2-k,0)                           *)
    (*       where j = min (length front,length rear)           *)
    (*             k = max (length front,length rear)           *)
    (*                                                          *)
    (*  Invariant 3 guarantees that both pending lists are      *)
    (*  completed by the time of the next rotation.             *)

    (* In general, c must be greater than or equal to 2, but for *)
    (* this implementation we assume c = 2 or 3.  The only place *)
    (* this makes a difference is in the function rotate2.       *)
-}

ratio :: Nat
ratio = 3


unfailtail [] = []
unfailtail (_:xs) = xs

tail2 xs = unfailtail (unfailtail xs)
{-
stake 0 xs = []
stake (n,xs) = lcons (head xs,fn () => take (n-1,tail xs))

    fun drop (0,xs) = xs
      | drop (n,xs) = drop (n-1,tail xs)
-}

rotate1 n xs ys =
   if n >= ratio 
   then (head xs):(rotate1 (n-ratio) (tail xs) (genericDrop ratio ys))
   else rotate2 xs (genericDrop n ys) []

{- if c > 3, slightly more complicated code is required here -}
rotate2 [] ys rys = revonto ys rys
rotate2 (z:zs) ys rys =
    z:(let (ys',rys') = partialrev ratio ys rys
       in rotate2 zs ys' rys')

revonto [] rys = rys
revonto (z:zs) rys = revonto zs (z:rys)

partialrev 0 ys rys = (ys,rys)
partialrev n ys rys = partialrev (n-1) (tail ys) ((head ys):rys)

{- Psuedo-constructor that enforces invariant -}

deque (q @ LRT {front,sizef,pendingf,rear,sizer,pendingr}) = 
    if sizef > ratio * sizer + 1 
    then let size = sizef + sizer
             half = size `div` 2
             front' = genericTake half front
             rear'  = rotate1 half rear front
     in LRT {front = front', 
             sizef = half,
             rear  = rear',  
             sizer = size - half,
             pendingf = front', 
             pendingr = rear'}
    else if sizer > ratio * sizef + 1 
         then let size = sizef + sizer
                  half = size `div` 2
                  front' = rotate1 half front rear
                  rear'  = genericTake half rear
              in LRT {front = front', 
                      sizef = size - half,
                      rear  = rear',  
                      sizer = half,
                      pendingf = front', 
                      pendingr = rear'}
         else q

lempty = LRT {front = [], 
              sizef = 0, 
              rear  = [], 
              sizer = 0,
              pendingf = [],  
              pendingr = []}

isempty x = sizef x+sizer x == 0

lsize x = sizef x+sizer x

insertl x (LRT {front,sizef,rear,sizer,pendingf,pendingr}) = 
    deque (LRT {front = (x:front), 
                sizef = sizef + 1,
                rear  = rear,           
                sizer = sizer,
                pendingf = unfailtail pendingf, 
                pendingr = unfailtail pendingr})

insertr (LRT {front,sizef,rear,sizer,pendingf,pendingr}) x = 
   deque (LRT {front = front,
               sizef = sizef,
               rear  = (x:rear), 
               sizer = sizer + 1,
               pendingf = unfailtail pendingf, 
               pendingr = unfailtail pendingr})

removel (LRT {front,sizef,rear,sizer,pendingf,pendingr}) =
  if null front 
  then if null rear 
       then Nothing
       else Just (head rear,lempty) 
  else Just (head front,
             deque (LRT {front = tail front, 
                         sizef = sizef - 1,
                         rear  = rear,       
                         sizer = sizer,
                         pendingf = tail2 pendingf, 
                         pendingr = tail2 pendingr}))

remover (LRT {front,sizef,rear,sizer,pendingf,pendingr}) =
  if null rear 
  then if null front 
       then Nothing
       else Just (lempty,head front) 
  else Just (deque (LRT {front = front,
                         sizef = sizef,
                         rear  = tail rear, 
                         sizer = sizer - 1,
                         pendingf = tail2 pendingf, 
                         pendingr = tail2 pendingr}),
             head rear)

instance Empty LRT where
    empty = lempty

instance Deque LRT where
    push = insertl
    pop = removel
    inject = insertr
    eject = remover

instance Loose (LRT a) where
    proper x = sizef x <= ratio * sizer x + 1 && 
               sizer x <= ratio * sizef x + 1 &&
               sizef x == genericLength (front x) &&
               sizer x == genericLength (rear x) &&
               genericLength (pendingf x) <= max (2*j+2-k) 0 &&
               genericLength (pendingr x) <= max (2*j+2-k) 0
        where j = min (genericLength (front x)) (genericLength (rear x))
              k = max (genericLength (front x)) (genericLength (rear x))

instance Eq a => Eq (LRT a) where
    xs == ys =
        case (pop xs,pop ys) of
          (Nothing,Nothing) -> True
          (Just (a,as), Just (b,bs)) -> a == b && as == bs
          _ -> False