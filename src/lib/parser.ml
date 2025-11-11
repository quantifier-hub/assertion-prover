(* *********************************************************************

    The file parser.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)

open Lib
open Lex

type 'a parseResult = Parsed of ('a * token llist)
                    | Failed of string

type 'a parser = token llist -> 'a parseResult

let succeed (x : 'a) (_ : unit) : 'a parser = (fun ll -> Parsed(x, ll));; 

let failed msg (_ : unit) : 'a parser = (fun _ -> Failed msg);;

let (>>=) (p : unit -> 'a parser) (f : 'a -> unit -> 'b parser) =
   (fun () -> (fun ll -> match p () ll with Failed msg -> Failed msg
                                          | Parsed(x, rm) -> f x () rm));;

let (|||) (p : unit -> 'a parser) (q : unit -> 'a parser) =
  (fun () -> (fun ll -> match p () ll with
               Failed _ -> q () ll 
              | x -> x));;


let (--) (p : unit -> 'a parser) (q : unit -> 'b parser) = p >>= (fun u -> (q >>= (fun v -> succeed(u, v))));;

let (|--) (p : unit -> 'a parser) (q : unit -> 'b parser) = p >>= (fun _ -> (q >>= (fun v -> succeed v)));;

let (--|) (p : unit -> 'a parser) (q : unit -> 'b parser) = p >>= (fun u -> (q >>= (fun _ -> succeed u)));;


let match_eq (x : string) (_ : unit) : string parser =
  (fun ll -> match ll with
               LNil -> Failed(x ^ " expected but nothing found.\n")
             | LCons(t, f) -> if String.equal (t.content) x then Parsed(x, f()) 
                              else Failed("'"^x^"' at line " ^ (string_of_int t.line) ^
                                            " row " ^ (string_of_int t.row) ^ " expected, but '" ^
                                          t.content ^ "' found.\n"));;

let is_alphaC c = let i = Char.code c in i >= 65 && i <= 90;;

let is_alpha c = let i = Char.code c in i >= 97 && i <= 122;;

let is_num c = let i = Char.code c in i >= 48 && i <= 57;;

let ix1 = ["="; "<"; ">"];;
let ix2 = ["<="; "=>"; "<<"; ">>"; "=="; ">="; "<>"];;
let ix3 = ["/"; "%"; "@"; "+"; "*"; "-"; "!"];;
let ix4 = ["++"; "--"; "**"; "->"];;
let accents = ['#'; '*'; '^'];;


let consume_str (_ : unit) : string parser =
  (fun ll -> match ll with
       LNil -> Failed("a string expected but nothing found.")
     | LCons(t, f) -> Parsed(t.content, f()));;
  

let consume_id b (_ : unit) : (char * (char * char)) parser =
  (fun ll -> match ll with
       LNil -> Failed("an identifier expected but nothing found.")
     | LCons(t, f) -> (if String.length(t.content) = 1
                       then (let c0 = t.content.[0] in
                             if (b && is_alphaC c0) || (not b && (is_alpha c0 || is_num c0))
                             then Parsed(('\000', ('\000', c0)), f())
                             else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                         " row " ^ (string_of_int t.row) ^ " is an illegal identifier.\n"))
                       else if String.length(t.content) = 2
                                 then (let c0 = t.content.[0] in
                                       let c1 = t.content.[1] in
                                       if (b && is_alphaC c0 && (is_alphaC c1 || is_alpha c1 || is_num c1 || mem_chr c1 accents)) ||
                                          (not b && (is_alpha c0 || is_num c0) && (is_alpha c1 || is_num c1 || mem_chr c1 accents))
                                       then Parsed(('\000', (c0, c1)), f())
                                       else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                                   " row " ^ (string_of_int t.row) ^ " is an illegal identifier.\n"))
                                 else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                             " row " ^ (string_of_int t.row) ^ " is too long for an identifier.\n")));;




 let consume_infix_id b (_ : unit) : (char * (char * char)) parser =
  (fun ll -> match ll with
       LNil -> Failed("an identifier expected but nothing found.")
     | LCons(t, f) -> (if String.length(t.content) = 1
                       then (let c0 = t.content.[0] in
                             if (b && mem_string t.content ix1) || (not b && mem_string t.content ix3)
                             then Parsed(('\000', ('\001', c0)), f())
                             else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                         " row " ^ (string_of_int t.row) ^ " is an illegal infix identifier.\n"))
                       else if String.length(t.content) = 2
                                 then (let c0 = t.content.[0] in
                                       let c1 = t.content.[1] in
                                       if (b && mem_string t.content ix2) || (not b && mem_string t.content ix4)
                                       then Parsed(('\001', (c0, c1)), f())
                                       else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                                   " row " ^ (string_of_int t.row) ^ " is an illegal infix identifier.\n"))
                                 else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                             " row " ^ (string_of_int t.row) ^ " is too long for an identifier.\n")));;
                                      


 let consume_var_id (_ : unit) : (char * (char * char)) parser =
  (fun ll -> match ll with
       LNil -> Failed("an identifier expected but nothing found.")
     | LCons(t, f) -> (if String.length(t.content) = 1
                       then (let c0 = t.content.[0] in
                             if is_alpha c0
                             then Parsed(('\000', ('\000', c0)), f())
                             else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                         " row " ^ (string_of_int t.row) ^ " is an illegal variable identifier.\n"))
                       else if String.length(t.content) = 2
                                 then (let c0 = t.content.[0] in
                                       let c1 = t.content.[1] in
                                       if is_alpha c0 && (is_alpha c1 || is_num c1)
                                       then Parsed(('\000', (c0, c1)), f())
                                       else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                                   " row " ^ (string_of_int t.row) ^ " is an illegal variable identifier.\n"))
                                 else Failed("'"^t.content^"' at line " ^ (string_of_int t.line) ^
                                             " row " ^ (string_of_int t.row) ^ " is too long for an identifier.\n")));;
                                     


let rec many1 (p : unit -> 'a parser) : unit -> 'a list parser =
    p >>= (fun u -> ((many1 p >>= (fun ls -> succeed(u::ls))) ||| succeed [u]));;

let rec list1 (sep : string) (p : unit -> 'a parser) : unit -> 'a list parser =
    p >>= (fun u -> ((match_eq sep |-- list1 sep p) >>= (fun ls -> succeed(u::ls))) 
                  ||| succeed [u]);;

let list (sep : string) (p : unit -> 'a parser) : unit -> 'a list parser = (list1 sep p ||| succeed []);;


let optional (p : unit -> 'a parser) : unit -> 'a option parser = 
 (p >>= (fun a -> succeed (Some a)))
     ||| succeed None;;



(* *************************** *)
(* *** a formula parser    *** *)
(* *************************** *)


let rec termP'(u) : ((char * (char * char)) aTerm) parser =
  ((termP >>= (fun tL -> (consume_infix_id false >>= (fun s -> (termP >>= (fun tR -> succeed(TApp(s, [tL;tR]))))))))
   ||| 
   (consume_id false >>= (fun f -> ((match_eq "(" |-- list "," termP') --| match_eq ")") >>= (fun ts -> succeed(TApp(f, ts)))
                                                                                      ||| succeed(Var f)))) u
and termP(u) : ((char * (char * char)) aTerm) parser =
 (((match_eq "(" |-- termP) >>= (fun tL -> (consume_infix_id false >>= (fun s -> ((termP --| match_eq ")") >>=
                                                                      (fun tR -> succeed(TApp(s, [tL;tR]))))))))
   ||| 
   (consume_id false >>= (fun f -> ((match_eq "(" |-- list "," termP') --| match_eq ")") >>= (fun ts -> succeed(TApp(f, ts)))
                          ||| succeed(Var f)))) u           


let rec f0(u) : ((char * (char * char)) aFormula) parser =
   ((match_eq "ALL" |-- many1 consume_var_id --| match_eq ".") >>= (fun vs -> f0 >>= (fun f -> succeed(AQs(vs, f)))) 
    ||| 
    ((match_eq "EX" |--  many1 consume_var_id --| match_eq ".") >>= (fun vs -> f0 >>= (fun f -> succeed(EQs(vs, f)))) 
     |||
      f1)) u

and f1(u) : ((char * (char * char)) aFormula) parser =
    (f2 >>= (fun l -> ((match_eq "-->" |-- f1) >>= (fun r -> succeed(Imp(l, r))))
                       |||
                       ((match_eq "<->" |-- f1) >>= (fun r -> succeed(Iff(l, r)))
                        ||| succeed l))) u

      
and f2(u) : ((char * (char * char)) aFormula) parser = (f3 >>= f2') u
and f2'(f) : unit -> ((char * (char * char)) aFormula) parser =
  (((match_eq "&" |-- f3) >>= (fun g -> f2'(Conj(f, g))))
   |||
     ((match_eq "|" |-- f3) >>= (fun g -> f2'(Disj(f, g))))) 
  |||
    succeed f
    
            
and f3(u) : ((char * (char * char)) aFormula) parser =
   ((match_eq "~" |-- f4) >>= (fun f -> succeed(Negation f))
    |||
     f4) u

and f4(u) : ((char * (char * char)) aFormula) parser =
   (match_eq "True" >>= (fun _ -> succeed TRUE) 
    |||
    (match_eq "False" >>= (fun _ -> succeed FALSE) 
    |||
      ((termP' >>= (fun tL -> (consume_infix_id true >>= (fun s -> (termP' >>= (fun tR -> succeed(Pred(s, [tL; tR])))))))) 
    |||
       ((consume_id true >>= (fun p -> ((match_eq "(" |-- list1 "," termP') --| match_eq ")") >>= (fun ts -> succeed(Pred(p, ts))) 
                             ||| 
                                succeed(Pred(p, [])))) 
    ||| 
        ((match_eq "(" |-- f0) --| match_eq ")"))))) u


(* *** *)
(* a query parser *)
(* *** *)

let commentP(u) : string parser = (match_eq "[" |-- (match_eq "\"" |-- (consume_str --| (match_eq "\"" |-- match_eq "]")))) u;;
  

let queryP(u) : (string * ((char * (char * char)) aFormula)) parser =
  (match_eq "assertion" |-- (match_eq "\"" |-- (consume_str -- (match_eq "\"" |-- (optional(commentP) |-- (match_eq ":" |-- f0)))))) u;;



let parse_from_channel (ch : In_channel.t) =  
  let ll = tokenize_file ch in
  let p = list1 ";" queryP () ll in
  match p with
    Failed msg -> let _ = print_string ("Syntax error:\n" ^ msg) ; flush_all() in
                   Failed msg                   
  | Parsed(x, rm) -> match rm with
                       LNil -> Parsed(x, LNil)
                     | _ -> let _ = print_string("Syntax error(s): \n" ^ (print_list " " (toList(lmap (fun t -> t.content) rm)))); flush_all() in
                            Failed ""




let parseFile (s : string)  =
  let ch = open_in s in
  let x = parse_from_channel ch in
  let _ = close_in ch in
  x;;
