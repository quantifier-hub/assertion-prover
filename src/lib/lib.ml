(* *********************************************************************

    The file lib.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)



type order = Less | Equal | Greater;;
type 'a tree = Tip | Node of 'a tree * Z.t * 'a * 'a tree;;
type 'a aTerm = Var of 'a | TApp of 'a * 'a aTerm list;;

type res_CORE = Nothing | Empty |
  Res of ((Z.t * Z.t aTerm list) list * (Z.t * Z.t aTerm list) list);;

type fol = App of Z.t * Z.t aTerm list | Neg of fol | Or of fol * fol |
  And of fol * fol | AQ of fol | EQ of fol;;

type balance = Eq | LeftLess | RightLess;;


type 'a aFormula = Pred of 'a * 'a aTerm list | Negation of 'a aFormula |
  Disj of 'a aFormula * 'a aFormula | Conj of 'a aFormula * 'a aFormula |
  Imp of 'a aFormula * 'a aFormula | Iff of 'a aFormula * 'a aFormula |
  AQs of 'a list * 'a aFormula | EQs of 'a list * 'a aFormula | TRUE | FALSE;;


type cKind = Positive | Negative | Mixed;;


type eCls =
  { clause : ((Z.t * Z.t aTerm list) list * (Z.t * Z.t aTerm list) list);
    factorsa : ((Z.t * Z.t aTerm list) * ((Z.t * Z.t aTerm list) list * (Z.t * Z.t aTerm list) list)) list;
    kind : cKind
  }


let isPos ecls = (match ecls.kind with Positive -> true
                                     | Negative -> false
                                     | Mixed -> false);;
let isNeg ecls = (match ecls.kind with Positive -> false
                                     | Negative -> true
                                     | Mixed -> false);;
                    
  

let (===) a b = Z.equal a b 
let less_nat a b = Z.lt a b 
let less_eq_nat a b = Z.leq a b
                                                        
let zero_nat = Z.zero;; 
let one_nat = Z.one;; 
let two_nat = Z.of_int(2);;            
let suc(x) = Z.succ(x);; 
let pred(x) = Z.pred(x);; 
let plus_nat a b = Z.add a b;;
let minus_nat a b = Z.sub a b;;                          
let times_nat a b = Z.mul a b;;

let ord_nat n m = (if less_nat m n then Less else (if n === m then Equal else Greater));;
let ord_int n m = (if m < n then Less else (if n = m then Equal else Greater));;

 
let rec length_tr d xs = match xs with [] -> d
                                     | _ :: xs1 -> length_tr (d+1) xs1;;
let size_list (xs : 'a list) = length_tr 0 xs;;

let length_Cls x = (fun (n, p) -> (length_tr 0 n) + (length_tr 0 p)) x;;

let all_POS x = (fun (n, _) -> (length_tr 0 n = 0)) x;;
let all_NEG x = (fun (_, p) -> (length_tr 0 p = 0)) x;;

 
let hd x = match x with [] -> failwith "unexpected hd of Nil"
                      | (x21 :: _) -> x21;;
let tl = function [] -> []
                | _ :: x22 -> x22;;
                               
let is_empty = function [] -> true
                      | _ -> false;;
                                   
let fst (x1, _) = x1;;
let snd (_, x2) = x2;;
 
let is_none = function Some _ -> false
                     | None -> true;;
let is_some = function None -> false
                     | Some _ -> true;;

let the x = match x with None -> failwith "unexpected the of None"
                       | (Some x2) -> x2;;

let rec foldl f a x2 = match x2 with [] -> a
                                   | x :: xs -> foldl f (f a x) xs;;

let rec filter p x1 = match x1 with [] -> []                                          
                                  | x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec map f x1 = match x1 with [] -> []
                               | x21 :: x22 -> f x21 :: map f x22;;
  
let rec map_foldl f g e x3 = match x3 with [] -> e
                                         | x :: xs -> map_foldl f g (f e (g x)) xs;;
  
let map_option f x1 = match x1 with None -> None
                                  | Some x2 -> Some (f x2);;

let rec map_opt f x1 st = match x1 with [] -> st
                                      | x :: xs -> (match f x with None -> map_opt f xs st
                                                                 | Some y -> map_opt f xs (y :: st));;

let rec app x0 ys = match x0 with [] -> ys
                                | x :: xs -> app xs (x :: ys);;
 
let rec map_tr f x1 ys = match x1 with [] -> app ys []
                                     | x :: xs -> map_tr f xs (f x :: ys);;

let rec map_tra f x1 ys = match x1 with [] -> ys
                                      | x :: xs -> map_tra f xs (f x :: ys);;

let rec map_filtera f p x2 st = match x2 with [] -> st
                                            | x :: xs -> (if p x then map_filtera f p xs (f x :: st)
                                                          else map_filtera f p xs st);;
let map_filter f p xs = map_filtera f p xs [];;

let rec map_app_tr f x1 rs = match x1 with [] -> rs
                                         | x :: xs -> map_app_tr f xs (app (f x) rs);;

let rec map_app_tra f x1 st = match x1 with [] -> Some st
                                          | x :: xs -> (match f x with None -> None
                                                                     | Some y -> map_app_tra f xs (app y st));;
let map_app f xs = map_app_tra f xs [];;

  
let rec nmin_nmaxa mn mx x2 = match x2 with [] -> (mn, mx)
                                          | x :: xs ->
                                               (if less_nat x mn then nmin_nmaxa x mx xs
                                                else (if less_nat mx x then nmin_nmaxa mn x xs
                                                      else nmin_nmaxa mn mx xs));;
let nmin_nmax = function [] -> (zero_nat, zero_nat)
                       | u :: xs -> nmin_nmaxa u u xs;;
  
let fun_upd f a b = (fun x -> (if x === a then b else f x));;
let comp f g = (fun x -> f (g x));;
  
let rec zip_tr st x1 ys = match x1, ys with [], _ -> st
                                          | _ :: _, [] -> st
                                          | a :: xs, b :: ys -> zip_tr ((a, b) :: st) xs ys;;  

let rec forall p x1 = match x1 with x :: xs -> (if p x then forall p xs else false)
                                  | [] -> true;;
let rec exists p x1 = match x1 with x :: xs -> (if p x then true else exists p xs)
                                  | [] -> false;;


let rec ord_term_tr (x1 : (Z.t aTerm * Z.t aTerm) list) =
  match x1 with
    [] -> Equal
  | (Var i, Var j)::st ->
    (match Z.compare i j with
     | -1 -> Less
     | 1 -> Greater
     | _ -> ord_term_tr st)
  | (Var _, _)::_ -> Less
  | (_, Var _)::_ -> Greater
  | (TApp(f, tsa), TApp(g, ts))::st ->
    (match Z.compare f g with
     | -1 -> Less  
     | 1 -> Greater 
     | _ -> ord_term_tr (zip_tr st tsa ts));;


let ord_term x0 x1 = ord_term_tr [(x0, x1)];;


let ord_atom (p, tsa) (q, ts) =
  match Z.compare p q with
  | -1 -> Less
  | 1 -> Greater
  | _ -> ord_term_tr (zip_tr [] tsa ts);;



let eq_atoms a b = (match ord_atom a b with Less -> false
                                          | Equal -> true
                                          | Greater -> false);;

let taut_check x = (fun (n, p) -> exists (fun a -> exists (eq_atoms a) p) n) x;;



let rec insa cmp rs x2 a = match x2 with [] -> app rs [a]
                                       | x :: xs -> (match cmp a x with Less -> app rs (a :: x :: xs)
                                                                      | Equal -> app rs (x :: xs)
                                                                      | Greater -> insa cmp (x :: rs) xs a);;
let ins cmp = insa cmp [];;

let ins_except cmp v xs a = (match cmp v a with Less -> insa cmp [] xs a
                                              | Equal -> xs
                                              | Greater -> insa cmp [] xs a);;

  
let rec unionSa cmp st xs x3 = match xs, x3 with xs, [] -> app st xs
                                               | [], v :: va -> app st (v :: va)
                                               | a :: xs, b :: ys -> (match cmp a b with Less -> unionSa cmp (a :: st) xs (b :: ys)
                                                                                       | Equal -> unionSa cmp (a :: st) xs ys
                                                                                       | Greater -> unionSa cmp (b :: st) (a :: xs) ys);;
let unionS cmp = unionSa cmp [];;


let rec remS cmp st xa2 x = match xa2 with [] -> app st []
                                         | a :: xs -> (match cmp a x with Less -> remS cmp (a :: st) xs x
                                                                        | Equal -> app st xs
                                                                        | Greater -> app st (a :: xs));;


let rec occursVarT v x1 = match x1 with TApp (_, ts) -> exists (occursVarT v) ts
                                      | Var i -> i === v;;


let rec occursVar v x1 = match x1 with App (_, ts) -> exists (occursVarT v) ts
                                     | Neg f -> occursVar v f
                                     | Or (f, g) -> occursVar v f || occursVar v g
                                     | And (f, g) -> occursVar v f || occursVar v g
                                     | AQ f -> occursVar (suc v) f
                                     | EQ f -> occursVar (suc v) f;;


let rec freevarsT d x1 = match x1 with TApp (_, ts) -> map_foldl (unionS ord_nat) (freevarsT d) [] ts
                                     | Var i -> (if less_eq_nat d i then [minus_nat i d] else []);;


let rec freevars k x1 = match x1 with EQ f -> freevars (suc k) f
                                    | AQ f -> freevars (suc k) f
                                    | And (f, g) -> unionS ord_nat (freevars k f) (freevars k g)
                                    | Or (f, g) -> unionS ord_nat (freevars k f) (freevars k g)
                                    | Neg f -> freevars k f
                                    | App (_, ts) -> map_foldl (unionS ord_nat) (freevarsT k) [] ts;;

let vars_of_atom x = (fun (_, a) -> map_foldl (unionS ord_nat) (freevarsT zero_nat) [] a) x;;

let vars_OF x = (fun (n, a) -> map_foldl (unionS ord_nat) vars_of_atom
                    (map_foldl (unionS ord_nat) vars_of_atom [] n) a) x;;


let rec funsymsT = function TApp (f, ts) -> ins ord_nat (map_foldl (unionS ord_nat) funsymsT [] ts) f
                          | Var _ -> [];;

let rec funsyms = function EQ f -> funsyms f
                         | AQ f -> funsyms f
                         | And (f, g) -> unionS ord_nat (funsyms f) (funsyms g)
                         | Or (f, g) -> unionS ord_nat (funsyms f) (funsyms g)
                         | Neg f -> funsyms f
                         | App (_, ts) -> map_foldl (unionS ord_nat) funsymsT [] ts;;


let ord_list_max = function [] -> zero_nat
                          | x :: _ -> x;;

let newFun f = suc(ord_list_max (funsyms f));;


let rec liftT = function (k, TApp (f, ts)) -> TApp (f, map (fun x -> liftT (k, x)) ts)
                       | (k, Var i) -> (if less_nat i k then Var i else Var (suc i));;



let lambda sigma i =
    (if less_nat zero_nat i then liftT (zero_nat, sigma (pred i))
     else Var i);;

let rec endo_ext sigma x1 = match x1 with TApp (f, ts) -> TApp (f, map_tr (endo_ext sigma) ts [])            
                                        | Var i -> sigma i;;


let rec endo_extF x0 sigma = match x0 with App (p, ts) -> App (p, map_tr (endo_ext sigma) ts [])
                                         | Neg f -> Neg (endo_extF f sigma)
                                         | Or (f, g) -> Or (endo_extF f sigma, endo_extF g sigma)
                                         | And (f, g) -> And (endo_extF f sigma, endo_extF g sigma)
                                         | AQ f -> AQ (endo_extF f (lambda sigma))
                                         | EQ f -> EQ (endo_extF f (lambda sigma));;


let shift k d i = (if less_nat i k then Var i else Var (plus_nat i d));;

let lift k f = endo_extF f (shift k one_nat);;

let dsubst f v t = endo_extF f (fun j -> (if less_nat j v then Var j
                                          else (if j === v then t else Var (pred j))));;

let subst f v t = endo_extF f (fun_upd (fun a -> Var a) v t);;

let rec substT = function (TApp (f, ts), (k, t)) -> TApp (f, map_tr (fun x -> substT (x, (k, t))) ts [])
                        | (Var i, (k, t)) -> (if i === k then t else Var i);;

let lift_Cls f = (fun (n, p) -> (map_tr (fun x -> (fst x, map_tr f (snd x) [])) n [],
                                 map_tr (fun x -> (fst x, map_tr f (snd x) [])) p []));;

let shiftCls d = lift_Cls (endo_ext (shift zero_nat d));;


(* trees *)
let max a b = (if a <= b then b else a);;

let rec tree_depth = function Tip -> 0
                            | Node (l, _, _, r) -> (max (tree_depth l) (tree_depth r))  + 1;;

let rec mapVal f x1 = match x1 with Tip -> Tip
                                  | Node (l, k, v, r) -> Node (mapVal f l, k, f v, mapVal f r);;
  
let balance = function Tip -> Eq
                     | Node (l, _, _, r) ->
                              (let dl = tree_depth l in
                               let dr = tree_depth r in
                               (if dl = dr then Eq
                                else (if dl < dr then LeftLess else RightLess)));;
  
let rotateRL x = match x with (l, (t, (c, Node (Node (rll, s, b, rlr), k, a, rr)))) -> Node (Node (l, t, c, rll), s, b, Node (rlr, k, a, rr))
                            | _ -> failwith "unexpected match in rotateRL";;

let rotateR x = match x with (l, (s, (a, Node (rl, k, b, rr)))) -> Node (Node (l, s, a, rl), k, b, rr)
                           | _ -> failwith "unexpected match in rotateR";;

let rotateRight l key x r = (match balance r with Eq -> rotateR (l, (key, (x, r)))
                                                | LeftLess -> rotateR (l, (key, (x, r)))
                                                | RightLess -> rotateRL (l, (key, (x, r))));;


let rotateLR x = match x with (Node (ll, k, a, Node (lrl, s, b, lrr)), (t, (c, r))) -> Node (Node (ll, k, a, lrl), s, b, Node (lrr, t, c, r))
                            | _ -> failwith "unexpected match in rotateLR";;

let rotateL x = match x with (Node (ll, s, b, lr), (k, (a, r))) -> Node (ll, s, b, Node (lr, k, a, r))
                           | _ -> failwith "unexpected match in rotateL";;

let rotateLeft l key x r = (match balance l with Eq -> rotateL (l, (key, (x, r)))
                                               | LeftLess -> rotateLR (l, (key, (x, r)))
                                               | RightLess -> rotateL (l, (key, (x, r))));;


(* updates *)
let rec updateBTT x0 key v = match x0 with Node (l, keya, va, r) ->
  (if key === keya then (match ord_term v va with Less -> None
                                                | Equal -> Some (Node (l, key, v, r))
                                                | Greater -> None)
   else (if less_nat key keya then (match updateBTT l key v with None -> None
                                                               | Some la ->          
                                                                 (if (tree_depth r) + 2 = (tree_depth la)
                                                                  then Some (rotateLeft la keya va r)
                                                                  else Some (Node (la, keya, va, r))))
      else (match updateBTT r key v with None -> None
                                       | Some ra ->
                                         (if (tree_depth l) + 2 = (tree_depth ra)
                                          then Some (rotateRight l keya va ra)
                                          else Some (Node (l, keya, va, ra))))))
                                         | Tip -> Some (Node (Tip, key, v, Tip));;
  

let rec updateBT x0 key v = match x0 with Node (l, keya, va, r) ->
  (if key === keya then Node (l, key, v, r)
   else (if less_nat key keya
         then (let la = updateBT l key v in
               (if (tree_depth r) + 2 = (tree_depth la)
                then rotateLeft la keya va r
                else Node (la, keya, va, r)))
         else (let ra = updateBT r key v in
               (if (tree_depth l) + 2 = (tree_depth ra)
                then rotateRight l keya va ra
                else Node (l, keya, va, ra)))))
                                        | Tip -> Node (Tip, key, v, Tip);;


let rec lookupTerm x0 i = match x0 with Tip -> Var i
                                      | Node (l, k, v, r) -> (if i === k then v
                                                              else (if less_nat i k then lookupTerm l i else lookupTerm r i));;



let rec weighted_ins f x1 a w = match x1 with [] -> [a]
                                            | x :: xs -> (if w <= (f x) then a :: x :: xs
                                                          else x :: weighted_ins f xs a w);;

let weighted_insSort f = foldl (fun zs z -> weighted_ins f zs z (f z)) [];;



(* *** a pretty-printer for terms and formulas *** *)


let quote s = "'" ^ s ^ "'"
let dquote s = "\"" ^ s ^ "\""
let prnth s = "(" ^ s ^ ")"

let rec print_list sep xs =
        match xs with
         [] -> ""
       | [x] -> x
       | y :: ys -> y ^ sep ^ print_list sep ys;;  

  
let str_of_char = Char.escaped 
let char3_eq a b = (let (a1, (a2, a3)) = a in
                    let (b1, (b2, b3)) = b in
                    Char.equal a1 b1 && Char.equal a2 b2 && Char.equal a3 b3);;
let fun_upd_c3 f a b = (fun x -> (if char3_eq x a then b else f x));;

let rec mem_char3 c x =
  match x with
    [] -> false
  | y::ys -> (if char3_eq c y then true else mem_char3 c ys);;


type iden_kinds = Reg of string | Infix of string;;
let char3_to_string (c0, (c1, c2)) =
  if Char.equal c0 '\000' then
    if Char.equal c1 '\000' then Reg (Char.escaped c2)
    else (if Char.equal c1 '\001' then Infix (Char.escaped c2)
          else Reg ((Char.escaped c1)^(Char.escaped c2)))
  else Infix ((Char.escaped c1)^(Char.escaped c2))

let char3_to_string_var (_, (c1, c2)) =
  if Char.equal c1 '\000' then (Char.escaped c2)
  else ((Char.escaped c1)^(Char.escaped c2))
    

let rec ppTerm b t =
  match t with Var x -> (match char3_to_string x with Reg s -> s
                                                    | _ -> failwith ": unexpected variable identifier")
             | TApp(f, ts) -> (match char3_to_string f with Reg s -> s ^ prnth(print_list ", " (map (ppTerm true) ts))
                                                          | Infix s -> (match ts with [l; r] ->
                                                              (if b then (ppTerm false l)^" "^s^" "^(ppTerm false r)
                                                               else prnth((ppTerm b l)^" "^s^" "^(ppTerm b r)))
                                                                                    | _ -> failwith ": unexpected rank for an infix function"));;



let ppD pp x = 
  match x with
    Negation _ -> pp x
  | Pred(_, _) -> pp x
  | Disj(_, _) -> pp x
  | TRUE -> "True"
  | FALSE -> "False"
  | _ -> prnth(pp x)

let ppC pp x = 
  match x with
    Negation _ -> pp x
  | Pred(_, _) -> pp x
  | Conj(_, _) -> pp x
  | TRUE -> "True"
  | FALSE -> "False"
  | _ -> prnth(pp x)

let ppI pp b x = 
    match x with
     Negation _ -> pp x
   | Pred(_, _) -> pp x
   | Conj(_, _) -> pp x
   | Disj(_, _) -> pp x
   | TRUE -> "True"
   | FALSE -> "False"
   | Imp(_, _) -> (if b then prnth(pp x) else pp x) 
   | Iff(_, _) -> (if b then prnth(pp x) else pp x) 
   | _ -> prnth(pp x)




let rec ppFormula f = match f with Pred(p, ts) ->
  (match char3_to_string p with Reg s -> (match ts with [] -> s
                                                      | _ -> s ^ prnth(print_list ", " (map (ppTerm true) ts)))
                              | Infix s -> (match ts with [a; b] -> (ppTerm true a)^" "^s^" "^(ppTerm true b)            
                                                        | _ -> failwith ": unexpected rank for an infix predicate"))
  
                                  | Negation g -> (match g with Pred(_, _) -> "~ "^ ppFormula g
                                                              | _ -> "~"^ prnth(ppFormula g))
                                  | Disj(g, h) -> ppD ppFormula g ^ " | " ^ ppD ppFormula h
                                  | Conj(g, h) -> ppC ppFormula g ^ " & " ^ ppC ppFormula h
                                  | Imp(g, h) -> ppI ppFormula true g ^ " --> " ^ ppI ppFormula false h
                                  | Iff(g, h) -> ppI ppFormula true g ^ " <-> " ^ ppI ppFormula false h
                                  | AQs(vs, g) -> "ALL "^print_list " " (map char3_to_string_var vs)^". " ^ ppFormula g
                                  | EQs(vs, g) -> "EX "^print_list " " (map char3_to_string_var vs)^". " ^ ppFormula g                  
                                  | TRUE -> "True"
                                  | FALSE -> "False"
                                    



(* *** signatures *** *)

let rec ins_var xs x = match xs with [] -> [x]
                                   | v::vs -> (if char3_eq x v then xs else v::ins_var vs x);;

let rec rem_vars xs vs = match xs with [] -> []
                                     | x::xsa -> (if mem_char3 x vs then rem_vars xsa vs else x::rem_vars xsa vs);;


let rec insert2 xs (s, a) = (match xs with [] -> [(s, a)]
                                         | (t,r)::ys -> (if char3_eq s t then (if a = r then (t,r)::ys
                                                                               else (match char3_to_string s with Reg s -> failwith (": ambiguous rank for the symbol " ^ quote s)
                                                                                                                | Infix s -> failwith (": ambiguous rank for the symbol " ^ quote s)))
                                                         else (t, r)::(insert2 ys (s, a))));;
                                                           


let rec term_sig sg vs t = match t with Var v -> (sg, ins_var vs v)
                                      | TApp(f, ts) -> (let sg1 = insert2 sg (f, length_tr 0 ts) in
                                                     terms_sig sg1 vs ts)
and terms_sig sg vs ts = match ts with [] -> (sg, vs)
                                     | t::xs -> (let (sga, vsa) = term_sig sg vs t in
                                                 terms_sig sga vsa xs)
                                                   
    
let rec formula_sigs psg fsg vs f = match f with Pred(p, ts) -> (let (fsg1, vs1) = terms_sig fsg vs ts in
                                                                 let psg1 = insert2 psg (p, length_tr 0 ts) in
                                                                 (psg1, fsg1, vs1))
                                            | Negation g -> formula_sigs psg fsg vs g
                                            | Disj(g,h) -> (let (psg1, fsg1, vs1) = formula_sigs psg fsg vs g in
                                                            formula_sigs psg1 fsg1 vs1 h)
                                            | Conj(g,h) -> (let (psg1, fsg1, vs1) = formula_sigs psg fsg vs g in
                                                            formula_sigs psg1 fsg1 vs1 h)               
                                            | Imp(g,h) -> (let (psg1, fsg1, vs1) = formula_sigs psg fsg vs g in
                                                            formula_sigs psg1 fsg1 vs1 h)
                                            | Iff(g,h) -> (let (psg1, fsg1, vs1) = formula_sigs psg fsg vs g in
                                                           formula_sigs psg1 fsg1 vs1 h)
                                            | AQs(xs, g) -> (let (psg1, fsg1, vs1) = formula_sigs psg fsg vs g in
                                                             (psg1, fsg1, rem_vars vs1 xs))
                                            | EQs(xs, g) -> (let (psg1, fsg1, vs1) = formula_sigs psg fsg vs g in
                                                             (psg1, fsg1, rem_vars vs1 xs))
                                            | TRUE -> (psg,fsg,vs)
                                            | FALSE -> (psg,fsg,vs);;




let rec pp_sig sg = match sg with [] -> ""
                                | (s, a)::xs -> (match char3_to_string s with Reg t -> (("> the symbol " ^ quote t ^ " of rank " ^ (string_of_int a) ^ "\n")^(pp_sig xs))          
                                                                            | Infix t -> (("> the infix symbol " ^ quote t ^ "\n")^(pp_sig xs)));;
                               

let rec pp_vars vs = match vs with [] -> ""
                                 | [x] -> quote(char3_to_string_var x)
                                 | x::xs -> (quote(char3_to_string_var x) ^ ", " ^ pp_vars xs);;
