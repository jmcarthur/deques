(* Chris Okasaki
   School of Computer Science
   Carnegie Mellon University
   Pittsburgh, PA 15213
   cokasaki@cs.cmu.edu *)

functor Deque (structure Stream : STREAM) : DEQUE =
    (* Implementation of deques with O(1) worst-case performance. *)
struct

    open Stream

    datatype 'a Deque =	Deque of {front  : 'a Stream, sizef  : int,
				  rear   : 'a Stream, sizer  : int,
				  pendingf : 'a Stream, pendingr : 'a Stream}

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
    val c = 3

    fun tail2 xs = tail (tail xs)

    fun take (0,xs) = Stream.empty
      | take (n,xs) = lcons (head xs,fn () => take (n-1,tail xs))

    fun drop (0,xs) = xs
      | drop (n,xs) = drop (n-1,tail xs)

    fun rotate1 (n,xs,ys) =
	  if n >= c then lcons (head xs,
				fn () => rotate1 (n-c,tail xs,drop (c,ys)))
	  else rotate2 (xs,drop (n,ys),Stream.empty)

    and rotate2 (xs,ys,rys) =
	  (* if c > 3, slightly more complicated code is required here *)
	  if Stream.isempty xs then revonto (ys,rys)
	  else lcons (head xs,
		      fn () => 
		        let val (ys,rys) = partialrev (c,ys,rys)
		        in rotate2 (tail xs,ys,rys) end)

    and revonto (ys,rys) =
	  if Stream.isempty ys then rys
	  else revonto (tail ys,cons (head ys,rys))

    and partialrev (0,ys,rys) = (ys,rys)
      | partialrev (n,ys,rys) = partialrev (n-1,tail ys,cons (head ys,rys))

    (* Psuedo-constructor that enforces invariant *)
    fun deque (q as {front,sizef,pendingf,rear,sizer,pendingr}) =
          if sizef > c * sizer + 1 then
	    let val size = sizef + sizer
		val half = size div 2
		val front' = take (half,front)
		val rear'  = rotate1 (half,rear,front)
	    in
		Deque {front = front', sizef = half,
		       rear  = rear',  sizer = size - half,
		       pendingf = front', pendingr = rear'}
	    end
	  else if sizer > c * sizef + 1 then
	    let val size = sizef + sizer
		val half = size div 2
		val front' = rotate1 (half,front,rear)
		val rear'  = take (half,rear)
	    in
		Deque {front = front', sizef = size - half,
		       rear  = rear',  sizer = half,
		       pendingf = front', pendingr = rear'}
	    end
	  else
	    Deque q


    exception Empty

    val empty = Deque {front = Stream.empty, sizef = 0, 
		       rear  = Stream.empty, sizer = 0,
		       pendingf = Stream.empty,  pendingr = Stream.empty}

    fun isempty (Deque {sizef,sizer,...}) = sizef+sizer = 0

    fun size (Deque {sizef,sizer,...}) = sizef+sizer

    fun insertl (x, Deque {front,sizef,rear,sizer,pendingf,pendingr}) = 
	  deque {front = cons (x,front), sizef = sizef + 1,
		 rear  = rear,           sizer = sizer,
		 pendingf = tail pendingf, pendingr = tail pendingr}

    fun insertr (x, Deque {front,sizef,rear,sizer,pendingf,pendingr}) = 
	  deque {front = front,         sizef = sizef,
		 rear  = cons (x,rear), sizer = sizer + 1,
		 pendingf = tail pendingf, pendingr = tail pendingr}

    fun removel (Deque {front,sizef,rear,sizer,pendingf,pendingr}) =
	 if Stream.isempty front then
	   if Stream.isempty rear then raise Empty
	   else (head rear,empty) 
         else
	   (head front,
	    deque {front = tail front, sizef = sizef - 1,
		   rear  = rear,       sizer = sizer,
		   pendingf = tail2 pendingf, pendingr = tail2 pendingr})

    fun remover (Deque {front,sizef,rear,sizer,pendingf,pendingr}) =
	 if Stream.isempty rear then
	   if Stream.isempty front then raise Empty
	   else (head front,empty) 
         else
	   (head rear,
	    deque {front = front,     sizef = sizef,
		   rear  = tail rear, sizer = sizer - 1,
		   pendingf = tail2 pendingf, pendingr = tail2 pendingr})

end
