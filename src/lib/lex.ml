(* *********************************************************************

    The file lex.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)



                  
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


let rec split_file buf em (t : string) i l r (f : in_channel) =
  let lt = String.length t in
  if Dynarray.length buf <= i then
    try
      let c = input_char f in
      Dynarray.add_last buf c;
      if em then
        (if c = esc then (if t = "" then LCons(mk_token (Char.escaped c) l r, 
                                                                 fun () -> split_file buf false "" (i+1) l (r+1) f) 
                                            else LCons (mk_token t l r,
                                                        fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                        fun () -> split_file buf false "" (i+1) l (r + lt + 1) f)))
         else (if c = '\n' then failwith ("illegal new line at " ^ (string_of_int l))
              else split_file buf true (t ^ (Char.escaped c)) (i+1) l r f))
      else (if c = esc then (if t = "" then LCons(mk_token (Char.escaped c) l r, 
                                                                 fun () -> split_file buf true "" (i+1) l (r+1) f) 
                             else LCons (mk_token t l r,
                                         fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                         fun () -> split_file buf true "" (i+1) l (r + lt + 1) f)))
                            
            else (if c = '\n' then (if t = "" then split_file buf false t (i+1) (l+1) 1 f 
                                    else LCons (mk_token t l r, fun () -> split_file buf false "" (i+1) (l+1) 1 f))
                  else (if mem_chr c skips then (if t = "" then split_file buf false t (i+1) l (r+1) f 
                                                 else LCons (mk_token t l r, fun () -> split_file buf false "" (i+1) l (r + lt + 1) f))
                        else (if mem_chr c delims then (if t = "" then LCons(mk_token (Char.escaped c) l r, 
                                                                             fun () -> split_file buf false "" (i+1) l (r+1) f) 
                                                        else LCons (mk_token t l r,
                                                                    fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                                    fun () -> split_file buf false "" (i+1) l (r + lt + 1) f)))
                              else split_file buf false (t ^ (Char.escaped c)) (i+1) l r f))))
    with
      End_of_file -> if t = "" then LNil else LCons (mk_token t l r, fun () -> LNil)
    | e ->  close_in_noerr f;           (* emergency closing *)
            raise e                                                 
  else
    let c = Dynarray.get buf i in
    if c = '\n' then (if t = "" then split_file buf false t (i+1) (l+1) 1 f 
                      else LCons (mk_token t l r, fun () -> split_file buf false "" (i+1) (l+1) 1 f))
    else (if mem_chr c skips then (if t = "" then split_file buf false t (i+1) l (r+1) f 
                                   else LCons (mk_token t l r, fun () -> split_file buf false "" (i+1) l (r + lt + 1) f))
          else (if mem_chr c delims then (if t = "" then LCons(mk_token (Char.escaped c) l r, 
                                                               fun () -> split_file buf false "" (i+1) l (r+1) f) 
                                          else LCons (mk_token t l r, 
                                                      fun () -> LCons(mk_token (Char.escaped c) l (r + lt),
                                                                      fun () -> split_file buf false "" (i+1) l (r + lt + 1) f)))
                else split_file buf false (t ^ (Char.escaped c)) (i+1) l r f));;


           
let tokenize_file x = split_file (Dynarray.create ()) false "" 0 1 1 x;;


