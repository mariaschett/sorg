open Core
open Ebso
open Evmenc
open Z3util
open Stackarg
open Rule
open Subst

(* to construct the constraints for a variable *)
type enc_var = {
  x : vvar;
  v : vval;
  forall : vval;
  eqv : vval list; (* contains only smaller variables *)
}

let mk_enc_var x s =
  let v = maps_to_exn x s in
  { x = x;
    v = v;
    forall = Const (x ^ "'");
    eqv = List.filter_map (preimages_to_val v s)
        ~f:(fun y -> if x < y then Some (Const (y ^ "'")) else None);
  }

let mk_enc_vars s = List.map (dom s) ~f:(fun x -> mk_enc_var x s)

let proxy_name x y =  "b_" ^ x ^ "_" ^ [%show: vval] y

let proxy_assigns evs =
  let assign_proxy m ev =
    List.fold ev.eqv ~init:m
      ~f:(fun m y -> Map.add_exn m ~key:(proxy_name ev.x y) ~data:(ev.x, y))
    |> Map.add_exn ~key:(proxy_name ev.x ev.v) ~data:(ev.x, ev.v)
    |> Map.add_exn ~key:(proxy_name ev.x ev.forall) ~data:(ev.x, ev.forall)
  in
  List.fold evs ~init:String.Map.empty ~f:assign_proxy

let enc_literals_atleastone evs =
  let enc_literal_atleastone ev =
    [ boolconst @@ proxy_name ev.x ev.v
    ; boolconst @@ proxy_name ev.x ev.forall
    ] @ List.map ev.eqv ~f:(fun y -> boolconst @@ proxy_name ev.x y)
  in
  conj @@ List.map evs ~f:(fun ev -> disj @@ enc_literal_atleastone ev)

let z3_const = function
  | Val n -> senum_string n
  | Const y -> seconst y
  | Tmpl -> failwith "No Template variables allowed"

let enc_literals_def evs =
  let mk_def l x v =
    let open Z3Ops in
    boolconst l ==> (seconst x == z3_const v)
  in
  Map.fold (proxy_assigns evs)
    ~init:top ~f:(fun ~key:l ~data:(x, v) c -> c <&> mk_def l x v)

let enc_rule_valid r =
  let open Z3Ops in
  let ea = mk_enc_consts r.lhs (`User []) in
  let sts = mk_state ea "_lhs" in
  let stt = mk_state ea "_rhs" in
  let kt = num (List.length r.rhs) and ks = num (List.length ea.p) in
  ((List.foldi r.rhs ~init:(enc_program ea sts)
      ~f:(fun j enc oc -> enc <&> enc_instruction ea stt (num j) oc)) &&
   (enc_equivalence_at ea sts stt (num 0) (num 0)) &&
   sts.used_gas @@ (forall_vars ea @ [num 0]) ==
                   stt.used_gas @@ (forall_vars ea @ [num 0]) &&
   (enc_equivalence_at ea sts stt ks kt))

let enc_generalize r evs =
  foralls (List.map evs ~f:(fun ev -> z3_const ev.forall)) (
    existss (List.map evs ~f:(fun ev -> seconst @@ ev.x)) (
      enc_literals_atleastone evs <&> enc_rule_valid r
      <&> enc_literals_def evs
    )
  )

let dec_generalize m ls =
  Map.fold ls ~init:[] ~f:(fun ~key:l ~data:xv s ->
      if Z3.Boolean.is_true (eval_const m (boolconst l)) then xv :: s else s)

let forbid_subst s =
  ~! (conj (List.map s ~f:(fun (x, v) -> boolconst @@ proxy_name x v)))

let find_different_subst ls c =
  match solve_model [c] with
  | None -> None
  | Some m ->
    let s = dec_generalize m ls in
    Some (s, c <&> forbid_subst s)

let generalize r =
  let r_0 = maximal_rule_schema r in
  let s_0 = Option.value_exn (Subst.match_opt (r_0.lhs @ r_0.rhs) (r.lhs @ r.rhs)) in
  let evs = mk_enc_vars s_0 in
  let ps = proxy_assigns evs in
  let c = enc_generalize r_0 evs in
  let rec substs ss c = match find_different_subst ps c with
    | None -> ss
    | Some (s, c) -> substs (s :: ss) c
  in
  List.map (substs [] c) ~f:(Rule.apply r_0)
