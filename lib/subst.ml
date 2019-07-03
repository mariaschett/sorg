open Core
open Ebso
open Instruction
open Stackarg

type vvar = constarg [@@deriving show { with_path = false }, sexp, compare, equal]
type vval = Stackarg.t [@@deriving show { with_path = false }, sexp, compare, equal]

let show_vval = function
  | Val n -> n
  | Const y -> y
  | Tmpl -> failwith "No Template variables allowed"

type ventr = (vvar * vval) [@@deriving show { with_path = false }, sexp, compare, equal]
type t = ventr list [@@deriving show { with_path = false }, sexp, compare]

let equal s1 s2 = List.equal [%eq: ventr]
    (List.sort ~compare:[%compare: ventr] s1)
    (List.sort ~compare:[%compare: ventr] s2)

let dom s = List.map s ~f:Tuple.T2.get1

let in_dom x s = List.Assoc.mem s x ~equal:[%eq: vvar]

let maps_to_exn x s = List.Assoc.find_exn s x ~equal:[%eq: vvar]

let maps_to_val x v s = if in_dom x s then v = maps_to_exn x s else false

let preimages_of_val v s = List.filter (dom s) ~f:(fun x -> maps_to_val x v s)

(* only extend if in_dom x s is false *)
let extend_maps_to x v s = List.Assoc.add s x v ~equal:[%eq: vvar]

let match_instruction s p1 p2 = match s, p1, p2 with
  | Some s', PUSH (Const x), PUSH w when not (in_dom x s') -> Some (extend_maps_to x w s')
  | Some s', PUSH (Const x), PUSH w -> if (maps_to_exn x s') = w then s else None
  | Some _, i1, i2 when i1 = i2 -> s
  | _ -> None

let match_opt p1 p2 =
  let match_prefix = List.fold2 p1 p2 ~init:(Some []) ~f:match_instruction in
  match match_prefix with
  | Ok s -> s
  | Unequal_lengths -> None

let apply p s =
  let apply_instruction = function
    | PUSH (Const x) when in_dom x s -> PUSH (maps_to_exn x s)
    | i -> i
  in
  List.map p ~f:(apply_instruction)

let is_instance s t = Option.is_some (match_opt t s)

let same_image_larger x s =
  let v = maps_to_exn x s in
  List.filter (preimages_of_val v s) ~f:(fun y -> x < y)

let binding_alts x s =
  [(x, Const x); (x, maps_to_exn x s)] @
  List.map (same_image_larger x s) ~f:(fun y -> (x, Const y))

let all_binding_alts s = List.map (dom s) ~f:(fun x -> binding_alts x s)

let rec n_cartesian_product = function
| [] -> [[]]
| xs :: yys ->
    List.concat
      (List.map xs ~f:(fun x -> List.map (n_cartesian_product yys) ~f:(fun ys -> x :: ys)))

let all_subst_alts s = n_cartesian_product (all_binding_alts s)

(* providing program t which contains dom (s1 \cup dom s2) is
   simplification to use existing functionality *)
let more_general_subst t s1 s2 = is_instance (apply t s2) (apply t s1)

let less_general_subst t s1 s2 = [%eq: t] s1 s2 || more_general_subst t s2 s1

let rm_less_general t s = List.fold ~init:[]
    ~f:(fun ss s' -> if less_general_subst t s' s then ss else s' :: ss)

let rm_more_general t s = List.fold ~init:[]
    ~f:(fun ss s' -> if more_general_subst t s' s then ss else s' :: ss)
