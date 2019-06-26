open Core
open Ebso
open Evmenc
open Z3util
open Stackarg
open Rule
open Subst

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

let proxy_name x y =  "p_" ^ x ^ "_" ^ [%show: vval] y
let enc_proxy x v = boolconst @@ proxy_name x v

let self_name x = x ^ "'"
let self_vval x = Const (self_name x)

let same_image_larger x s =
  let v = maps_to_exn x s in
  List.filter_map (preimages_of_val v s)
        ~f:(fun y -> if x < y then Some (self_vval y) else None)

let proxy_assigns s =
  let add_assign x v m = Map.add_exn m ~key:(proxy_name x v) ~data:(x, v) in
  let assign_proxy m x =
    let v = maps_to_exn x s in
    List.fold (same_image_larger x s) ~init:m ~f:(fun m y -> add_assign x y m)
    |> add_assign x v
    |> add_assign x (self_vval x)
  in
  List.fold (dom s) ~init:String.Map.empty ~f:assign_proxy

let enc_at_least_one s x =
  disj @@
  [ enc_proxy x (maps_to_exn x s)
  ; enc_proxy x (self_vval x)
  ] @ List.map (same_image_larger x s) ~f:(enc_proxy x)

let enc_at_least_one_per_proxy s =
  conj @@ List.map (dom s) ~f:(enc_at_least_one s)

let enc_vval = function
  | Val n -> senum_string n
  | Const y -> seconst y
  | Tmpl -> failwith "No Template variables allowed"

let enc_proxy_assigns evs =
  let mk_def l x v =
    let open Z3Ops in
    boolconst l ==> (seconst x == enc_vval v)
  in
  Map.fold (proxy_assigns evs)
    ~init:top ~f:(fun ~key:l ~data:(x, v) c -> c <&> mk_def l x v)

let enc_generalize r s =
  foralls (List.map (dom s) ~f:(fun x -> enc_vval (self_vval x))) (
    existss (List.map (dom s) ~f:(fun x -> seconst @@ x)) (
      enc_at_least_one_per_proxy s <&> enc_rule_valid r
      <&> enc_proxy_assigns s
    )
  )

let dec_generalize m ls =
  Map.fold ls ~init:[] ~f:(fun ~key:l ~data:xv s ->
      if Z3.Boolean.is_true (eval_const m (boolconst l)) then xv :: s else s)

let enc_exclude_subst s =
  ~! (conj (List.map s ~f:(fun (x, v) -> enc_proxy x v)))

let find_different_subst ls c =
  match solve_model [c] with
  | None -> None
  | Some m ->
    let s = dec_generalize m ls in
    Some (s, c <&> enc_exclude_subst s)

let generalize r =
  let r_0 = maximal_rule_schema r in
  let s_0 = Option.value_exn (Subst.match_opt (r_0.lhs @ r_0.rhs) (r.lhs @ r.rhs)) in
  let ps = proxy_assigns s_0 in
  let c = enc_generalize r_0 s_0 in
  let rec substs ss c = match find_different_subst ps c with
    | None -> ss
    | Some (s, c) -> substs (s :: ss) c
  in
  List.map (substs [] c) ~f:(Rule.apply r_0)
