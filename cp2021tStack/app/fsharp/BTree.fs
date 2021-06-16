
// (c) MP-I (1998/9-2006/7) and CP (2005/6-2016/7)

module BTree

open Cp

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x

let outBTree x =
    match x with
    | Empty -> i1 ()
    | Node (a,(l,r)) -> i2 (a,(l,r))

// (2) Ana + cata + hylo -------------------------------------------------------

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree g = baseBTree id g

let rec cataBTree g x = (g << (recBTree (cataBTree g)) << outBTree) x 

let rec anaBTree g x = (inBTree << (recBTree (anaBTree g)) << g) x

let hyloBTree c a x = ((cataBTree c) << (anaBTree a)) x

// (3) Map ---------------------------------------------------------------------

let fmap f t = cataBTree (inBTree << baseBTree f id) t

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree t = cataBTree (inBTree << (id -|- (id >< swap))) t

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------
let singl x = [x]

let inord t =
    let join(x,(l,r)) = l @ (singl x) @ r
    in (either nil join) t

let inordt t = cataBTree inord t

let preord t =
    let f(x,(l,r)) = x :: l @ r
    in (either nil f) t

let preordt t = cataBTree preord t

let postord t =
    let f(x,(l,r)) = l @ r @ (singl x)
    in (either nil f) t

let postordt t = cataBTree postord t

// (4.4) Quicksort -------------------------------------------------------------

let app a l = a :: l

let rec part h t = //pivot / list
    match t with
    | [] -> ([],[])
    | x::xs -> if x < h then ((app x) >< id) (part h xs)
                        else (id >< (app x)) (part h xs)

let qsep list =
    match list with
    | [] -> i1 ()
    | h::t -> let (s,l) = part h t
              in i2 (h,(s,l))

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------

let rec union l1 l2 = 
    match l2 with
    | [] -> l1
    | h::t -> if List.exists (fun e -> e = h) l1 then union l1 t else union (l1 @ [h]) t

let tunion (a,(l,r)) = union (List.map (app a) l) (List.map (app a) r)

let traces x = (cataBTree (either (konst [[]]) tunion)) x

// (4.6) Towers of Hanoi -------------------------------------------------------

let strategy l =
    match l with
    | (d,0) -> i1 ()
    | (d,n) -> i2 ((n-1,d),((not d,n-1),(not d, n-1)))

let hanoi x = hyloBTree inord strategy x

// (5) Depth and balancing (using mutual recursion) --------------------------

let baldepth x = 
    let h (a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1, 1 + (max d1 d2))
    let f ((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))
    let g g1 = either (konst (true, 1)) (h << (id >< f)) g1
    in (cataBTree g) x

let balBTree x = (p1 << baldepth) x

let depthBTree x = (p2 << baldepth) x

// (6) Going polytipic -------------------------------------------------------

let tnat f x =
    let theta (a,b) = a @ b
    in  (either (konst []) (theta << (f >< theta))) x

let monBTree f a = cataBTree (tnat f) a

// alternative to (4.3) serialization ----------------------------------------

let preordt' t = monBTree singl t

// (7) Zipper ----------------------------------------------------------------

type Deriv<'a> = 
    | Dr of bool * ('a  * BTree<'a>)

type Zipper<'a> = List<Deriv<'a>>

let rec plug l t =
    match l with
    | [] -> t
    | (Dr (false,(a,l))::z)  -> Node (a,(plug z t,l))
    | (Dr (true,(a, r))::z)  -> Node (a,(r,plug z t)) 