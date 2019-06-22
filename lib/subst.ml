open Core
open Ebso
open Stackarg

type vvar = constarg [@@deriving show { with_path = false }, sexp, compare, equal]
type vval = Stackarg.t [@@deriving show { with_path = false }, sexp, compare, equal]

type ventr = (vvar * vval) [@@deriving show { with_path = false }, sexp, compare, equal]
type t = ventr list [@@deriving show { with_path = false }, sexp, compare]

let equal s1 s2 = List.equal [%eq: ventr]
    (List.sort ~compare:[%compare: ventr] s1)
    (List.sort ~compare:[%compare: ventr] s2)

let is_mapped x s = List.Assoc.mem s x ~equal:[%eq: vvar]

let map_exn x s = List.Assoc.find_exn s x ~equal:[%eq: vvar]

(* only extend if is_mapped x s is false *)
let map_extend x v s = List.Assoc.add s x v ~equal:[%eq: vvar]

let update_subst x v s =
  if not (is_mapped x s)
  then Some (map_extend x v s)
  else if (map_exn x s) = v then (Some s) else None

let compute_subst p1 p2 =
  let rec compute_subst' p1 p2 s = match p1, p2 with
    | [], [] -> Some s
    | Instruction.PUSH (Const a1) :: t1, Instruction.PUSH v :: t2 ->
      Option.(update_subst a1 v s >>= compute_subst' t1 t2)
    | i1 :: t1, i2 :: t2 when i1 = i2 -> compute_subst' t1 t2 s
    | _ -> None
  in compute_subst' p1 p2 []

let map_to_val v s =
  List.fold s ~init:[] ~f:(fun xs (x,v') -> if v = v' then x :: xs else xs )
