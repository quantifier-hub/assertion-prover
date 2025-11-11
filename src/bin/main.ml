(* *********************************************************************

    The file main.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)

open Lib
open Preprocess
open Search
open Parser

let query x = comp proof_search preprocess x;;



let rec process x = match x with [] -> ()
                               | (s, f) :: xs ->
                                 (let (psg, fsg, vs) = formula_sigs [] [] [] f in
                                  let fsg_msg = (match fsg with [] -> ""
                                                              | _ -> "\n>>> the function signature:\n" ^ pp_sig fsg) in
                                  let psg_msg = (match psg with [] -> ""
                                                              | _ -> "\n>>> the predicate signature:\n" ^ pp_sig psg) in
                                  let vs_msg = (match vs with [] -> ""
                                                            | [v] -> "\n>>> free variable: " ^ quote(char3_to_string_var v) ^ "\n"
                                                            | _ -> "\n>>> free variables: " ^ pp_vars vs ^ "\n") in
                                  let qs = dquote s in
                                  let ppf = ppFormula f ^ "\n" in
                                  let parsed_msg = "\n>>> the assertion " ^ qs ^ " :\n\n" in
                                  let _ = Printf.printf "%s%s%s%s%s\n%!" parsed_msg ppf psg_msg fsg_msg vs_msg in
                                  let _ = Printf.printf ">>> processing %s ... \n%!" qs in
                                  let lt = Sys.time () in
                                  let _ = (if query f then Printf.printf ">>> the assertion %s confirmed in %f sec.\n\n%!" qs  (Sys.time () -. lt)
                                           else Printf.printf ">>> the assertion %s rejected in %f sec.\n\n%!" qs (Sys.time () -. lt)) in
                                  process xs);;

                                  

let () = (match parseFile(Sys.argv.(1)) with Failed msg ->  failwith ("Syntax error(s): " ^ msg)
                                           | Parsed(x, _) -> process x);;


