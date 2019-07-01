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

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"sorg: A SuperOptimization based Rule Generator"
    [%map_open
      let in_csv = flag "incsv" (optional string)
          ~doc:"csv read optimizations from csv"
      and timeout = flag "timeout" (optional int)
          ~doc:"TO passes timeout TO in seconds to each call to Z3; if one call \
                times out then sorg gives up for that optimization."
      and  _ = flag "out" (optional string)
          ~doc:"filename write output to csv file"
      and opt = anon (maybe (t2 ("LHS" %: string) ("RHS" %: string)))
      in
      fun () ->
        Generate.timeout := (Option.value ~default:0 timeout) * 1000;
        let rs =
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
        let ((rs, dups, muls), timeouts) =
          List.fold rs ~init:(([], [], []), []) ~f:(fun (rs, tos) (s,t) ->
              try
                Out_channel.fprintf stderr "%s"
                  ("[" ^ [%show: Time.t] (Time.now ()) ^ "]" ^
                   " Generating rules for " ^ Program.show_h s ^ " >= " ^ Program.show_h t ^ "\n");
                Out_channel.flush stderr;
                (process_optimization rs (s,t), tos)
              with Z3util.Z3_Timeout ->
                Out_channel.fprintf stderr "%s"
                  ("[" ^ [%show: Time.t] (Time.now ()) ^ "]" ^ " timed out.\n");
                Out_channel.flush stderr;
                (rs, (s, t) :: tos))
        in
        Out_channel.printf "%s" (Rewrite_system.show rs);
        Out_channel.printf "\nDups\n%s" (Rewrite_system.show (List.sort ~compare:Rule.compare dups));
        Out_channel.printf "\nMuls\n%s\n" ([%show: ((Program.t * Program.t) * Rule.t list) list] muls);
        Out_channel.printf "\nTimeouts\n%s\n" ([%show: (Program.t * Program.t) list] timeouts)
    ]
  |> Command.run ~version:"1.0"
