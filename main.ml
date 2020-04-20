open Core
open Ebso
open Sorg

let outcsv_header =
  [ "rule lhs"
  ; "rule rhs"
  ; "gas saved"
  ; "optimization source"
  ; "optimization target"
  ; "tpdb"
  ]

let process_optimization s t =
    try
      Some (Generate.generate_rules s t)
    with Z3util.Z3_Timeout _ ->
      None

let result_to_csv rs s t =
  let output = [outcsv_header] in
  match rs with
  | None ->
    output @ [[""; ""; ""; Program.show_h s ; Program.show_h t; ""]]
  | Some rules ->
    let rule_to_row r =
      let open Rule in
      let module GC = Gas_cost in
      let g = GC.to_int (Program.total_gas_cost r.lhs) - GC.to_int (Program.total_gas_cost r.rhs) in
      [ Program.show_h r.lhs
      ; Program.show_h r.rhs
      ; [%show: int] g
      ; Program.show_h s
      ; Program.show_h t
      ; Rule.show_tpdb r
      ]
    in
    output @ List.map rules ~f:rule_to_row

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"sorg: A SuperOptimization based Rule Generator"
    [%map_open
      let lhs = anon ("LHS" %: string)
      and rhs = anon ("RHS" %: string)
      and timeout = flag "timeout" (optional int)
          ~doc:"TO passes timeout TO in seconds to each call to Z3; if one call \
                times out then sorg gives up for that optimization."
      and tpdb = flag "tpdb" no_arg ~doc:"print output in tpdb format"
      and out_csv = flag "outcsv" (optional string)
          ~doc:"csv write output to csv"
      in
      fun () ->
        Program_schema.timeout := (Option.value ~default:0 timeout) * 1000;
        let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
        let (lhs, rhs) =  (parse lhs, parse rhs) in
        Word.set_wsz 256;
        let rules = process_optimization lhs rhs in
        if tpdb then
          Out_channel.printf "%s" (Rewrite_system.show_tpdb (Option.value ~default:[] rules))
        else
          let msg =
            if Option.is_some rules
            then Rewrite_system.show (Option.value_exn rules)
            else "TIME-OUT\n" in
          Out_channel.printf "%s" msg;
          Option.iter out_csv ~f:(fun out -> Csv.save out (result_to_csv rules lhs rhs))
    ]
  |> Command.run ~version:"1.0"
