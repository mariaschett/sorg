open Core
open Ebso

type result =
  { rules : Rule.t list
  ; duplicates : Rule.t list
  ; multiples : ((Program.t * Program.t) * Rule.t list) list
  ; origins : (Rule.t * (Program.t * Program.t)) list
  }

let incsv_header =
  [ "source bytecode"
  ; "target bytecode"
  ; "target opcode"
  ; "target instruction count"
  ; "source gas"
  ; "target gas"
  ; "gas saved"
  ; "known optimal"
  ; "translation validation"
  ]

let show_optimization (s, t) =
  Printf.sprintf "%s >= %s" (Program.show_h s) (Program.show_h t)

let row_to_optimization r =
  let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
  let sbc = Csv.Row.find r "source bytecode"
  and tbc = Csv.Row.find r "target bytecode"
  and tv = Csv.Row.find r "translation validation"
  and gs = Csv.Row.find r "gas saved" in
  if String.equal gs "0" || String.equal tv "false" then None
  else Some (parse sbc, parse tbc)

let process_optimization result (s, t) =
  let rs = Generate.generate_rules s t in
  let muls' = if Rewrite_system.size rs > 1 then [((s, t), rs)] else [] in
  let (rs', dups') = Rewrite_system.insert_non_dup_rules rs result.rules in
  { rules = rs'
  ; duplicates = dups' @ result.duplicates
  ; multiples = muls' @ result.multiples
  ; origins = result.origins @ List.map rs ~f:(fun r -> (r, (s, t)))
  }

let process_optimizations opts =
  let process_opt_with_timeout (result, timeouts) opt =
    try
      Out_channel.fprintf stderr "[%s] Generating rules for %s\n"
        ([%show: Time.t] (Time.now ())) (show_optimization opt);
      Out_channel.flush stderr;
      (process_optimization result opt, timeouts)
    with Z3util.Z3_Timeout ->
      Out_channel.fprintf stderr "[%s] timed out.\n" ([%show: Time.t] (Time.now ()));
      Out_channel.flush stderr;
      (result, opt :: timeouts)
  in
  let result = {rules = []; duplicates = []; multiples = []; origins = []} in
  List.fold opts ~init:(result, []) ~f:process_opt_with_timeout

let print_dups dups =
  Format.printf "\nThe following rules were generated more than once:\n";
  Format.printf "%s" (Rewrite_system.show dups)

let print_muls muls =
  let print_mul (opt, rs) =
    Format.printf "@[<v 2>%s@," (show_optimization opt);
    List.iter rs ~f:(fun r -> Format.printf "%s@," (Rule.show r));
    Format.printf "@]"
  in
  Format.printf "\nThe following optimizations generated multiple rules:";
  List.iter muls ~f:print_mul

let print_timeouts timeouts =
  let print_opt opt =
    Format.printf "%s@," (show_optimization opt)
  in
  Format.printf "\nThe following optimizations timed out:";
  Format.printf "@[<v>";
  List.iter timeouts ~f:print_opt;
  Format.printf "@]"

let get_opts in_csv opt =
  match in_csv with
  | Some file ->
    let csv = Csv.Rows.load ~has_header:true ~header:incsv_header file in
    List.filter_map csv ~f:row_to_optimization
  | None ->
    match opt with
    | Some (lhs, rhs) ->
      let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
      [(parse lhs, parse rhs)]
    | None -> []

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"sorg: A SuperOptimization based Rule Generator"
    [%map_open
      let in_csv = flag "incsv" (optional string)
          ~doc:"csv read optimizations from csv"
      and timeout = flag "timeout" (optional int)
          ~doc:"TO passes timeout TO in seconds to each call to Z3; if one call \
                times out then sorg gives up for that optimization."
      and tpdb = flag "tpdb" no_arg ~doc:"print output in tpdb format"
      and pmuls = flag "print-multiples" no_arg
          ~doc:"report which optimizations gave rise to multiple rules"
      and pdups = flag "print-duplicates" no_arg
          ~doc:"report which rules were generated more than once"
      and ptos = flag "print-timeouts" no_arg
          ~doc:"report which optimizations timed out"
      and  _ = flag "outcsv" (optional string)
          ~doc:"csv write output to csv"
      and opt = anon (maybe (t2 ("LHS" %: string) ("RHS" %: string)))
      in
      fun () ->
        Generate.timeout := (Option.value ~default:0 timeout) * 1000;
        let opts = get_opts in_csv opt in
        Evmenc.set_wsz 256;
        let (result, timeouts) = process_optimizations opts in
        if tpdb then
          Out_channel.printf "%s" (Rewrite_system.show_tpdb result.rules)
        else
          Out_channel.printf "%s" (Rewrite_system.show result.rules);
        if pdups then print_dups result.duplicates else ();
        if pmuls then print_muls result.multiples else ();
        if ptos then print_timeouts timeouts else ()
    ]
  |> Command.run ~version:"1.0"
