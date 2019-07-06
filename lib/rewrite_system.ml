open Core
open Rule

type t = Rule.t list

let equal rs1 rs2 =
  let module RS = Set.Make_plain(Rule) in
  Set.equal (RS.of_list rs1) (RS.of_list rs2)

let pp fmt rs =
  Format.fprintf fmt "@[<v>";
  List.iter rs ~f:(Format.fprintf fmt "%a@," Rule.pp);
  Format.fprintf fmt "@]"

let show rs = pp Format.str_formatter rs |> Format.flush_str_formatter

(* identifies alpha equvivalent rules *)
let contains_rule rs r = List.mem rs r ~equal:[%eq: Rule.t]

let size = List.length

let vars rs = List.stable_dedup @@ List.concat_map rs ~f:Rule.vars

let rec insert_max_general r rs =
  let is_instance_rule r r' =
    Subst.is_instance (r.lhs @ r.rhs) (r'.lhs @ r'.rhs)
  in
  match rs with
  | [] -> [r]
  | r' :: rs' ->
    if is_instance_rule r' r then insert_max_general r rs'
    else if is_instance_rule r r' then rs
    else r' :: insert_max_general r rs'

let insert_non_dup_rules rs' rs =
  let insert (rs, dups) r =
    if contains_rule rs r then (rs, r :: dups) else (r :: rs, dups)
  in
  List.fold rs' ~init:(rs, []) ~f:insert

(* print in tpdb format *)

let pp_tpdb fmt ?(var="P") rs =
  Format.fprintf fmt "@[<v>(VAR@[<hov>@ %s" var;
  List.iter (vars rs) ~f:(fun v -> Format.fprintf fmt "@ %s" v);
  Format.fprintf fmt "@])@,(RULES@,@[<v>";
  List.iter rs ~f:(Format.fprintf fmt "  %a@," (Rule.pp_tpdb ~var:var));
  Format.fprintf fmt "@])@]"

let show_tpdb ?(var="P") rs =
  pp_tpdb Format.str_formatter ~var:var rs |> Format.flush_str_formatter
