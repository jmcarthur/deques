Set Implicit Arguments.
(*Set Contextual Implicit.*)
(*Unset Strict Implicit.*)

Inductive Both t := Two : t -> t -> Both t.

Inductive MStack a : Type -> Type :=
  M0 : MStack a a
| MS : forall b, a -> a -> MStack (Both a) b -> MStack a b.

Inductive Buffer a := 
  B0
| B1: a -> Buffer a
| B2: a -> a -> Buffer a.

Inductive Stuck a b :=
  Stack :  Buffer a -> Buffer a -> MStack (Both a) b -> Stuck a b.

Inductive Nest f a : Type -> Type :=
  Empty : Nest f a a
| Full : forall b c, f a b -> Nest f b c -> Nest f a c.

Inductive SE f a c :=
  NE : forall b, f a b -> Nest f b c -> SE f a c.

Definition StackStack := SE Stuck.

Definition ThreeStack := Nest StackStack.

Inductive SM a :=
  None
| Some : a -> SM a.

Inductive Deq a :=
 Deque : forall b c, MStack a b -> ThreeStack b c -> SM c -> Deq a.

Inductive Size := Small | Medium | Large.

Definition bufSize t (x:Buffer t) :=
  match x with
    | B0 => Small
    | B1 _ => Medium
    | B2 _ _ => Large
  end.

Definition sameSize x y :=
  match x,y with
    | Small,Small => true
    | Large,Large => true
    | _,_ => false
  end.

Definition nextSize x y :=
  match y with
    | Medium => x
    | _ => y
  end.

Definition SameSize x y :=
  match x,y with
    | Small,Small => True
    | Large,Large => True
    | _,_ => False
  end.

Inductive BufsAltStart (xs ys:Size) 
  : forall a b, ThreeStack a b -> Prop :=
    Stop : forall a, BufsAltStart xs ys (Empty _ a)
  | Bit : forall t (x y:Buffer t) s u (r:ThreeStack s u) z, 
    ~(SameSize xs (bufSize x)) ->
    ~(SameSize ys (bufSize y)) ->
    BufsAltStart (nextSize xs (bufSize x))
                 (nextSize ys (bufSize y))
                 r ->
    BufsAltStart xs ys (Full _ (NE _ (Stack x y z) (Empty _ _)) r)
  | Go : forall t (x y:Buffer t) za (q:MStack (Both t) za) zb (z:Stuck za zb) zc (zs:Nest Stuck zb zc) zd (r:ThreeStack zc zd), 
    ~(SameSize xs (bufSize x)) ->
    ~(SameSize ys (bufSize y)) ->
    BufsAltStart (nextSize xs (bufSize x))
                 (nextSize ys (bufSize y))
                 (Full _ (@NE Stuck za zc zb z zs) r) ->
    BufsAltStart xs ys (Full _ (NE _ (Stack x y q) (Full za z zs)) r).

Fixpoint bufsAltStart2 (f:Size -> Size -> Prop) a b (m:Stuck a b) c (n:Nest Stuck b c) d e (r:ThreeStack d e) (xs ys:Size) :=
  match m with
    | Stack x y _ =>
      let xs' := bufSize x in
        let ys' := bufSize y in
          (~ (SameSize xs xs')
           /\
           ~ (SameSize ys ys')
           /\
           (match n with
              | Empty => f 
              | Full _ _ z zs => bufsAltStart2 f z zs r
            end) (nextSize xs xs') (nextSize ys ys')
           )
  end.

Fixpoint bufsAltStart a b (r:ThreeStack a b) (xs ys:Size) :=
  match r with
    | Empty => True
    | Full _ _ (NE _ p ps) qs => bufsAltStart2 (bufsAltStart qs) p ps qs xs ys
  end.

Definition BufsAlternate t (x:Deq t) :=
  match x with
    | Deque _ _ _ y _ => bufsAltStart y Medium Medium
  end.

Inductive Top := Prefix | Suffix | Twofix.

Definition topCheck t (x y:Buffer t) :=
  match x,y with
    | B1 _, B1 _ => None _
    | B0, B1 _ => Some Prefix
    | B2 _ _, B1 _ => Some Prefix
    | B1 _, B0 => Some Suffix
    | B1 _, B2 _ _ => Some Suffix
    | _,_ => Some Twofix
  end.

Definition NextTop1 x y :=
  match x,y with
    | Prefix,Prefix => True
    | Suffix,Suffix => True
    | _,_ => False
  end.

Definition nextTop1 x y :=
  match x,y with
    | Prefix,Prefix => true
    | Suffix,Suffix => true
    | _,_ => false
  end.

Definition top1 a b (z:Stuck a b) :=
  match z with
    | Stack x y _ => topCheck x y
  end.

Fixpoint top2' a b (x:Stuck a b) c (yys:Nest Stuck b c) {struct yys} :=
  match yys with
    | Empty => top1 x
    | (Full _ _ y ys) => 
      match top1 x, top2' y ys with
        | Some v, Some w =>
          if nextTop1 v w
            then Some v
            else None _
        | _,_ => None _
      end
  end.

Definition top2 a b (x:StackStack a b) :=
  match x with
    | NE _ p q => top2' p q
  end.

Fixpoint top3 a b (x:StackStack a b) d e (yys:ThreeStack d e) {struct yys} :=
  match yys with
    | Empty => top2 x
    | Full _ _ y ys => 
      match top2 x, top3 y ys with
        | Some v, Some w =>
          if nextTop1 v w
            then None _
            else Some v
        | _,_ => None _
      end
  end.

Definition topShape a b (x:ThreeStack a b) :=
  match x with
    | Empty => True
    | Full _ _ y ys => 
      match top3 y ys with
        | None => False
        | _ => True
      end
  end.

Definition allShape a (x:Deq a) :=
  match x with
    | Deque _ _ _ b _ => topShape b
  end.

Fixpoint lastPair2 (ans:Prop) (cont:Size->Size->Prop) a b (x:Stuck a b) c d (xs:Nest Stuck c d) :=
  match xs with
    | Empty => 
      match x with
        | Stack p q rs =>
          match rs with
            | M0 => cont (bufSize p) (bufSize q)
            | _ => cont Medium Medium
          end
      end
    | Full _ _ y ys => lastPair2 ans cont y ys
  end.

Fixpoint LastPair (ans:Prop) (cont:Size->Size->Prop) a b (x:ThreeStack a b)  :=
  match x with
    | Empty => ans
    | Full _ _ y ys =>
      match ys with
        | Empty =>
          match y with
            | NE _ z zs => lastPair2 ans cont z zs
          end
        | _ => LastPair ans cont ys
      end
  end.

Definition BottomSome x y :=
  match x,y with
    | Small,Small => False
    | _,_ => True
  end.

Definition BottomNone x y :=
  match x,y with
    | Small,Small => True
    | Small,_ => False
    | _,Small => False
    | _,_ => True
  end.

Definition BottomOK a (x:Deq a) :=
  match x with
    | Deque _ _ _ b (Some _) => LastPair True BottomSome b
    | Deque _ _ _ b None => LastPair True BottomNone b
  end.

Definition invariants a (x:Deq a) := BottomOK x /\ allShape x /\ BufsAlternate x.

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

npop :: Deque a -> Maybe (a,Deque a)
npop (Deque M0 Empty None) = Nothing
npop (Deque M0 Empty (Some y)) =  Just (y,empty)
npop (Deque M0 (Full (NE (Stack (B2 y x) (B1 z) zs) Empty) xs) q) = Just (y,Deque (MS x z zs) xs q)
npop (Deque M0 (Full (NE (Stack (B2 y x) (B1 z) zs) (Full r rs)) xs) q) = Just (y,Deque (MS x z zs) (Full (NE r rs) xs) q)
npop (Deque M0 (Full (NE (Stack (B2 y x) z zs) Empty) xs) q) = Just (y,Deque M0 (cons13 (B1 x) z zs xs) q)
npop (Deque M0 (Full (NE (Stack (B1 y) (B2 x z) M0) Empty) Empty) None) = Just (y,Deque (MS x z M0) Empty None)
npop (Deque M0 (Full (NE (Stack (B1 y) B0 M0) Empty) Empty) (Some (Both x z))) = Just (y,Deque (MS x z M0) Empty None)
npop (Deque M0 (Full (NE (Stack (B1 y) z zs) Empty) xs) q) = Just (y,Deque M0 (Full (NE (Stack B0 z zs) Empty) xs) q)
npop (Deque M0 (Full (NE (Stack (B1 y) z zs) (Full r rs)) xs) q) = Just (y,Deque M0 (Full (NE (Stack B0 z zs) Empty) (Full (NE r rs) xs)) q)
npop (Deque (MS y z M0) Empty None) = Just (y,Deque M0 Empty (Some z))
npop (Deque (MS y z zs) rs q) = Just (y,Deque M0 (cons13 B0 (B1 z) zs rs) q)

neject :: Deque a -> Maybe (Deque a,a)
neject (Deque M0 Empty None) = Nothing
neject (Deque M0 Empty (Some y)) = Just (empty,y)
neject (Deque M0 (Full (NE (Stack (B1 x) (B2 z y) zs) Empty) xs) q) = Just (Deque (MS x z zs) xs q,y)
neject (Deque M0 (Full (NE (Stack (B1 x) (B2 z y) zs) (Full r rs)) xs) q) = Just (Deque (MS x z zs) (Full (NE r rs) xs) q, y)
neject (Deque M0 (Full (NE (Stack z (B2 x y) zs) Empty) xs) q) = Just (Deque M0 (cons13 z (B1 x) zs xs) q, y)
neject (Deque M0 (Full (NE (Stack (B2 x z) (B1 y) M0) Empty) Empty) None) = Just (Deque (MS x z M0) Empty None, y)
neject (Deque M0 (Full (NE (Stack B0 (B1 y) M0) Empty) Empty) (Some (Both x z))) = Just (Deque (MS x z M0) Empty None, y)
neject (Deque M0 (Full (NE (Stack z (B1 y) zs) Empty) xs) q) = Just (Deque M0 (Full (NE (Stack z B0 zs) Empty) xs) q, y)
neject (Deque M0 (Full (NE (Stack z (B1 y) zs) (Full r rs)) xs) q) = Just (Deque M0 (Full (NE (Stack z B0 zs) Empty) (Full (NE r rs) xs)) q, y)
neject (Deque (MS z y M0) Empty None) = Just (Deque M0 Empty (Some z), y)
neject (Deque (MS z y zs) rs q) = Just (Deque M0 (cons13 (B1 z) B0 zs rs) q, y)

Inductive Back a where
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

prefix2' :: ThreeStack a b -> SM b -> Back a
prefix2' (Full (NE (Stack B0 z zs) Empty) xs) q = 
    case npop (Deque zs xs q) of
      Just (Both x y,Deque a c q') ->
          Back (cons13 (B2 x y) z a c) q' 
prefix2' (Full (NE (Stack B0 z zs) (Full r rs)) xs) q = 
    case npop (Deque zs (Full (NE r rs) xs) q) of
      Just (Both x y,Deque a c q') ->
          Back (cons13 (B2 x y) z a c) q' 

prefix2 (Full (NE (Stack (B1 x) z zs) rs) xs) q = 
    case prefix2' xs q of
      Back c q' -> 
          Back (Full (NE (Stack (B1 x) z zs) rs) c) q'
prefix2 x y = prefix2' x y

suffix2' :: ThreeStack a b -> SM b -> Back a
suffix2' (Full (NE (Stack z B0 zs) Empty) xs) q = 
    case neject (Deque zs xs q) of
      Just (Deque a c q',Both x y) ->
          Back (cons13 z (B2 x y) a c) q' 
suffix2' (Full (NE (Stack z B0 zs) (Full r rs)) xs) q = 
    case neject (Deque zs (Full (NE r rs) xs) q) of
      Just (Deque a c q',Both x y) ->
          Back (cons13 z (B2 x y) a c) q' 

suffix2 (Full (NE (Stack z (B1 x) zs) rs) xs) q = 
    case suffix2' xs q of
      Back c q' ->
          Back (Full (NE (Stack z (B1 x) zs) rs) c) q'
suffix2 x y = suffix2' x y

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

pop xs =
    case prepose xs of
      Small -> npop (fixHelp prefix2 xs)
      _ -> npop xs

eject xs =
    case sufpose xs of
      Small -> neject (fixHelp suffix2 xs)
      _ -> neject xs

*)