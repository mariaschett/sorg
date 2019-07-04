open Core
open Ebso

let header =
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

let row_to_optimization r =
  let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
  let sbc = Csv.Row.find r "source bytecode"
  and tbc = Csv.Row.find r "target bytecode"
  and tv = Csv.Row.find r "translation validation"
  and gs = Csv.Row.find r "gas saved" in
  if String.equal gs "0" || String.equal tv "false" then None
  else Some (parse sbc, parse tbc)

let process_optimization (rs, dups, muls) (s, t) =
  let rs' = Generate.generate_rules s t in
  let muls' =
    if Rewrite_system.size rs' > 1 then ((s, t), rs') :: muls else muls
  in
  let (rs'', dups') = Rewrite_system.insert_non_dup_rules rs' rs in
  (rs'', dups' @ dups, muls')

let process_optimizations opts =
  let process_opt_with_timeout (rs, tos) (s,t) =
    try
      Out_channel.fprintf stderr "[%s] Generating rules for %s >= %s\n"
        ([%show: Time.t] (Time.now ())) (Program.show_h s) (Program.show_h t);
      Out_channel.flush stderr;
      (process_optimization rs (s,t), tos)
    with Z3util.Z3_Timeout ->
      Out_channel.fprintf stderr "[%s] timed out.\n" ([%show: Time.t] (Time.now ()));
      Out_channel.flush stderr;
      (rs, (s, t) :: tos)
  in
  List.fold opts ~init:(([], [], []), []) ~f:process_opt_with_timeout

let print_dups dups =
  Format.printf "\nThe following rules were generated more than once:\n";
  Format.printf "%s" (Rewrite_system.show dups)

let print_muls muls =
  let print_mul ((s, t), rs) =
    Format.printf "@[<v 2>%s >= %s@," (Program.show_h s) (Program.show_h t);
    List.iter rs ~f:(fun r -> Format.printf "%s@," (Rule.show r));
    Format.printf "@]"
  in
  Format.printf "\nThe following optimizations generated multiple rules:";
  List.iter muls ~f:print_mul

let print_timeouts timeouts =
  let print_opt (s, t) =
    Format.printf "%s >= %s@," (Program.show_h s) (Program.show_h t)
  in
  Format.printf "\nThe following optimizations timed out:";
  Format.printf "@[<v>";
  List.iter timeouts ~f:print_opt;
  Format.printf "@]"

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
        let opts =
          match in_csv with
          | Some file ->
            let csv = Csv.Rows.load ~has_header:true ~header:header file in
            List.filter_map csv ~f:row_to_optimization
          | None ->
            match opt with
            | Some (lhs, rhs) ->
              let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
              [(parse lhs, parse rhs)]
            | None -> []
        in
        Evmenc.set_wsz 256;
        let ((rs, dups, muls), timeouts) = process_optimizations opts in
        if tpdb then
          Out_channel.printf "%s" (Rewrite_system.show_tpdb rs)
        else
          Out_channel.printf "%s" (Rewrite_system.show rs);
        if pdups then print_dups dups else ();
        if pmuls then print_muls muls else ();
        if ptos then print_timeouts timeouts else ()
    ]
  |> Command.run ~version:"1.0"
