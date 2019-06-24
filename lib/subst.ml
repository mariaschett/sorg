open Core
open Ebso
open Instruction
open Stackarg

type vvar = constarg [@@deriving show { with_path = false }, sexp, compare, equal]
type vval = Stackarg.t [@@deriving show { with_path = false }, sexp, compare, equal]

type ventr = (vvar * vval) [@@deriving show { with_path = false }, sexp, compare, equal]
type t = ventr list [@@deriving show { with_path = false }, sexp, compare]

let equal s1 s2 = List.equal [%eq: ventr]
    (List.sort ~compare:[%compare: ventr] s1)
    (List.sort ~compare:[%compare: ventr] s2)

let dom s = List.map s ~f:Tuple.T2.get1

let in_dom x s = List.Assoc.mem s x ~equal:[%eq: vvar]

let map_exn x s = List.Assoc.find_exn s x ~equal:[%eq: vvar]

(* only extend if is_mapped x s is false *)
let map_extend x v s = List.Assoc.add s x v ~equal:[%eq: vvar]

let update_subst x v s =
  if not (in_dom x s)
  then Some (map_extend x v s)
  else if (map_exn x s) = v then (Some s) else None

let match_opt p1 p2 =
  let rec match_opt' p1 p2 s = match p1, p2 with
    | [], [] -> Some s
    | PUSH (Const a1) :: t1, PUSH v :: t2 ->
      Option.(update_subst a1 v s >>= match_opt' t1 t2)
    | i1 :: t1, i2 :: t2 when i1 = i2 -> match_opt' t1 t2 s
    | _ -> None
  in match_opt' p1 p2 []

let map_to_val v s =
  List.fold s ~init:[] ~f:(fun xs (x,v') -> if v = v' then x :: xs else xs)

let apply p s =
  let apply_instruction = function
    | PUSH (Const x) when in_dom x s -> PUSH (map_exn x s)
    | i -> i
  in
  List.map p ~f:(apply_instruction)
