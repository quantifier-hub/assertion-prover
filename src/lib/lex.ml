(* *********************************************************************

    The file lex.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)



open Lib


let test (a : string) i = 
    try
        Some a.[i]
    with _ -> None;;

                  
let rec mem_chr c (x : char list) =
    match x with
        [] -> false
      | y::ys -> (if Char.equal c y then true else mem_chr c ys);;

let rec mem_string c (x : string list) =
  match x with
    [] -> false
  | y::ys -> (if String.equal c y then true else mem_string c ys);;

                                   
type 'a llist = LNil
              | LCons of ('a * (unit -> 'a llist))

let force f = f();;

let rec toList ll =
    match ll with LNil -> []
                | LCons(x, f) -> x::toList(f());;
                      

let rec lmap m ll =
    match ll with LNil -> LNil
                | LCons(x, f) -> LCons(m x, fun () -> lmap m (f ()));;
                                   





type token = { content : string; line : int; row : int }
let mk_token c l r = { content = c; line = l; row = r };;
let token2string (t : token) = " token '"^t.content^"' at line "^ (string_of_int t.line) ^ " row "^(string_of_int t.row);;



let skips = [ ' '; '\t' ];;
let delims = [ '('; ')'; '~'; '.'; ','; ';'; ':'; '['; ']'];;
let esc = '"';;


let buf = ref [];;                              

let rec split_file em (t : string) i l r (f : in_channel) =
  let lt = String.length t in
  let lb = size_list (!buf) in
  if lb <= i then
    try
      let c = input_char f in
      let _ = (buf := c::!buf) in
      if em then
        (if Char.equal c esc then (if String.equal t "" then LCons(mk_token (Char.escaped c) l r, 
                                                                 fun () -> split_file false "" (i+1) l (r+1) f) 
                                            else LCons (mk_token t l r,
                                                        fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                        fun () -> split_file false "" (i+1) l (r + lt + 1) f)))
         else (if Char.equal c '\n' then failwith ("illegal new line at " ^ (string_of_int l))
              else split_file true (t ^ (Char.escaped c)) (i+1) l r f))
      else (if Char.equal c esc then (if String.equal t "" then LCons(mk_token (Char.escaped c) l r, 
                                                                 fun () -> split_file true "" (i+1) l (r+1) f) 
                                            else LCons (mk_token t l r,
                                                        fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                        fun () -> split_file true "" (i+1) l (r + lt + 1) f)))
              
      else (if Char.equal c '\n' then (if String.equal t "" then split_file false t (i+1) (l+1) 1 f 
                        else LCons (mk_token t l r, fun () -> split_file false "" (i+1) (l+1) 1 f))
      else (if mem_chr c skips then (if String.equal t "" then split_file false t (i+1) l (r+1) f 
                                     else LCons (mk_token t l r, fun () -> split_file false "" (i+1) l (r + lt + 1) f))
            else (if mem_chr c delims then (if String.equal t "" then LCons(mk_token (Char.escaped c) l r, 
                                                                 fun () -> split_file false "" (i+1) l (r+1) f) 
                                            else LCons (mk_token t l r,
                                                        fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                        fun () -> split_file false "" (i+1) l (r + lt + 1) f)))
                  else split_file false (t ^ (Char.escaped c)) (i+1) l r f))))
    with
      End_of_file -> if String.equal t "" then LNil else LCons (mk_token t l r, fun () -> LNil)
    | e ->  close_in_noerr f;           (* emergency closing *)
            raise e                                                 
  else
    let c = List.nth (!buf) (lb - 1 - i) in
    if Char.equal c '\n' then (if String.equal t "" then split_file false t (i+1) (l+1) 1 f 
                      else LCons (mk_token t l r, fun () -> split_file false "" (i+1) (l+1) 1 f))
    else (if mem_chr c skips then (if String.equal t "" then split_file false t (i+1) l (r+1) f 
                                   else LCons (mk_token t l r, fun () -> split_file false "" (i+1) l (r + lt + 1) f))
          else (if mem_chr c delims then (if String.equal t "" then LCons(mk_token (Char.escaped c) l r, 
                                                               fun () -> split_file false "" (i+1) l (r+1) f) 
                                          else LCons (mk_token t l r, 
                                                      fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                      fun () -> split_file false "" (i+1) l (r + lt + 1) f)))
                else split_file false (t ^ (Char.escaped c)) (i+1) l r f))

           
let tokenize_file x =
  let _ = (buf := []) in
  split_file false "" 0 1 1 x


