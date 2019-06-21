open Core
open Ebso
open Stackarg

type vvar = Stackarg.t [@@deriving show { with_path = false }, sexp, compare, equal]
type vval = Stackarg.t [@@deriving show { with_path = false }, sexp, compare, equal]

type ventr = (vvar * vval) [@@deriving show { with_path = false }, sexp, compare, equal]
type t = ventr list [@@deriving show { with_path = false }, sexp, compare, equal]

let equal_var_subst s1 s2 = List.equal [%eq: ventr]
    (List.sort ~compare:[%compare: ventr] s1)
    (List.sort ~compare:[%compare: ventr] s2)

let is_mapped a s = List.Assoc.mem s a ~equal:[%eq: vvar]

let map_exn a s = List.Assoc.find_exn s a ~equal:[%eq: vval]

(* only extend if is_mapped a1 s is false *)
let map_extend a1 a2 s = List.Assoc.add s a1 a2 ~equal:[%eq: vval]

let update_var_subst x v s =
  if not (is_mapped x s)
  then Some (map_extend x v s)
  else if (map_exn x s) = v then (Some s) else None

let compute_var_subst p1 p2 =
  let rec compute_subst' p1 p2 s = match p1, p2 with
    | [], [] -> Some s
    | Instruction.PUSH (Const a1) :: t1, Instruction.PUSH (Const a2) :: t2 ->
      Option.(update_var_subst (Const a1) (Const a2) s >>= compute_subst' t1 t2)
    | i1 :: t1, i2 :: t2 when i1 = i2 -> compute_subst' t1 t2 s
    | _ -> None
  in compute_subst' p1 p2 []
