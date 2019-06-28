open Core

type t = Rule.t list

let equal rs1 rs2 =
  let module RS = Set.Make_plain(Rule) in
  Set.equal (RS.of_list rs1) (RS.of_list rs2)

let pp fmt rs =
  Format.fprintf fmt "@[<v>";
  List.iter rs ~f:(Format.fprintf fmt "%a@," Rule.pp);
  Format.fprintf fmt "@]"

let show rs = pp Format.str_formatter rs |> Format.flush_str_formatter

let consts rs = List.stable_dedup @@ List.concat_map rs ~f:Rule.consts

let pp_tpdb fmt ?(var="P") rs =
  Format.fprintf fmt "@[<v>(VAR@[<hov>";
  List.iter (consts rs) ~f:(fun v -> Format.fprintf fmt "@ %s" v);
  Format.fprintf fmt "@])@,(RULES@,@[<v>";
  List.iter rs ~f:(fun r -> Format.fprintf fmt "  %a@," (Rule.pp_tpdb ~var:var) r);
  Format.fprintf fmt "@])@]"

let show_tpdb ?(var="P") rs =
  pp_tpdb Format.str_formatter ~var:var rs |> Format.flush_str_formatter
