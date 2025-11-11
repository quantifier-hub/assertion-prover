(* *********************************************************************

    The file preprocess.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)

open Lib


let rec nnf = function App (p, ts) -> App (p, ts)
                     | Neg f -> (match f with App (_, _) -> Neg f
                                            | Neg a -> nnf a
                                            | Or (fa, g) -> And (nnf (Neg fa), nnf (Neg g))
                                            | And (fa, g) -> Or (nnf (Neg fa), nnf (Neg g))
                                            | AQ fa ->
                                              (let fb = nnf (Neg fa) in
                                               (if occursVar zero_nat fb then EQ fb
                                                else dsubst fb zero_nat (TApp (one_nat, []))))
                                            | EQ fa ->
                                              (let fb = nnf (Neg fa) in
                                               (if occursVar zero_nat fb then AQ fb
                                                else dsubst fb zero_nat (TApp (one_nat, [])))))
                     | Or (f, g) -> Or (nnf f, nnf g)
                     | And (f, g) -> And (nnf f, nnf g)
                     | AQ f -> (let fa = nnf f in
                                (if occursVar zero_nat fa then AQ fa
                                 else dsubst fa zero_nat (TApp (one_nat, []))))
                     | EQ f -> (let fa = nnf f in
                                (if occursVar zero_nat fa then EQ fa
                                 else dsubst fa zero_nat (TApp (one_nat, []))));;



let rec replace_fvs x0 ub f = match x0 with [] -> f
                                          | v :: vs -> replace_fvs vs (suc ub) (subst f v (TApp (ub, [])));;

let sentence f = replace_fvs (freevars zero_nat f) (newFun f) f;;



let rec eq_elimF x0 b = match x0 with AQ f -> (let (fa, a) = eq_elimF f b in (AQ fa, a))
                                    | EQ f ->
                                      (let fvs = freevars one_nat f in 
                                       eq_elimF (dsubst f zero_nat (TApp (b, map_tra (fun a -> Var a) fvs []))) (suc b))
                                    | Or (f, g) -> (let (fa, ba) = eq_elimF f b in
                                                    let (ga, a) = eq_elimF g ba in
                                                       (Or (fa, ga), a))
                                    | And (f, g) -> (let (fa, ba) = eq_elimF f b in
                                                     let (ga, a) = eq_elimF g ba in                                     
                                                       (And (fa, ga), a))
                                    | App (v, va) -> (App (v, va), b)      
                                    | Neg v -> (Neg v, b);;

let eq_elim f = fst (eq_elimF f (newFun f));;




let rec prenex_d x0 g = match x0, g with AQ f, g -> AQ (prenex_d f (lift zero_nat g))
                                       | App (v, va), AQ g -> AQ (prenex_d (lift zero_nat (App (v, va))) g)
                                       | Neg v, AQ g -> AQ (prenex_d (lift zero_nat (Neg v)) g)
                                       | Or (v, va), AQ g -> AQ (prenex_d (lift zero_nat (Or (v, va))) g)
                                       | And (v, va), AQ g -> AQ (prenex_d (lift zero_nat (And (v, va))) g)
                                       | EQ v, AQ g -> AQ (prenex_d (lift zero_nat (EQ v)) g)
                                       | App (v, va), App (vb, vc) -> Or (App (v, va), App (vb, vc))
                                       | App (v, va), Neg vb -> Or (App (v, va), Neg vb)
                                       | App (v, va), Or (vb, vc) -> Or (App (v, va), Or (vb, vc))
                                       | App (v, va), And (vb, vc) -> Or (App (v, va), And (vb, vc))
                                       | App (v, va), EQ vb -> Or (App (v, va), EQ vb)
                                       | Neg v, App (va, vb) -> Or (Neg v, App (va, vb))
                                       | Neg v, Neg va -> Or (Neg v, Neg va)
                                       | Neg v, Or (va, vb) -> Or (Neg v, Or (va, vb))
                                       | Neg v, And (va, vb) -> Or (Neg v, And (va, vb))
                                       | Neg v, EQ va -> Or (Neg v, EQ va)
                                       | Or (v, va), App (vb, vc) -> Or (Or (v, va), App (vb, vc))
                                       | Or (v, va), Neg vb -> Or (Or (v, va), Neg vb)
                                       | Or (v, va), Or (vb, vc) -> Or (Or (v, va), Or (vb, vc))
                                       | Or (v, va), And (vb, vc) -> Or (Or (v, va), And (vb, vc))
                                       | Or (v, va), EQ vb -> Or (Or (v, va), EQ vb)
                                       | And (v, va), App (vb, vc) -> Or (And (v, va), App (vb, vc))
                                       | And (v, va), Neg vb -> Or (And (v, va), Neg vb)
                                       | And (v, va), Or (vb, vc) -> Or (And (v, va), Or (vb, vc))
                                       | And (v, va), And (vb, vc) -> Or (And (v, va), And (vb, vc))
                                       | And (v, va), EQ vb -> Or (And (v, va), EQ vb)
                                       | EQ v, App (va, vb) -> Or (EQ v, App (va, vb))
                                       | EQ v, Neg va -> Or (EQ v, Neg va)
                                       | EQ v, Or (va, vb) -> Or (EQ v, Or (va, vb))
                                       | EQ v, And (va, vb) -> Or (EQ v, And (va, vb))
                                       | EQ v, EQ va -> Or (EQ v, EQ va);;

let rec prenex_c x0 x1 = match x0, x1 with AQ f, AQ g -> AQ (prenex_c f g)
                                         | AQ f, App (v, va) -> AQ (prenex_c f (lift zero_nat (App (v, va))))
                                         | AQ f, Neg v -> AQ (prenex_c f (lift zero_nat (Neg v)))
                                         | AQ f, Or (v, va) -> AQ (prenex_c f (lift zero_nat (Or (v, va))))
                                         | AQ f, And (v, va) -> AQ (prenex_c f (lift zero_nat (And (v, va))))
                                         | AQ f, EQ v -> AQ (prenex_c f (lift zero_nat (EQ v)))
                                         | App (v, va), AQ g -> AQ (prenex_c (lift zero_nat (App (v, va))) g)
                                         | Neg v, AQ g -> AQ (prenex_c (lift zero_nat (Neg v)) g)
                                         | Or (v, va), AQ g -> AQ (prenex_c (lift zero_nat (Or (v, va))) g)
                                         | And (v, va), AQ g -> AQ (prenex_c (lift zero_nat (And (v, va))) g)
                                         | EQ v, AQ g -> AQ (prenex_c (lift zero_nat (EQ v)) g)
                                         | App (v, va), App (vb, vc) -> And (App (v, va), App (vb, vc))
                                         | App (v, va), Neg vb -> And (App (v, va), Neg vb)
                                         | App (v, va), Or (vb, vc) -> And (App (v, va), Or (vb, vc))
                                         | App (v, va), And (vb, vc) -> And (App (v, va), And (vb, vc))
                                         | App (v, va), EQ vb -> And (App (v, va), EQ vb)
                                         | Neg v, App (va, vb) -> And (Neg v, App (va, vb))
                                         | Neg v, Neg va -> And (Neg v, Neg va)
                                         | Neg v, Or (va, vb) -> And (Neg v, Or (va, vb))
                                         | Neg v, And (va, vb) -> And (Neg v, And (va, vb))
                                         | Neg v, EQ va -> And (Neg v, EQ va)
                                         | Or (v, va), App (vb, vc) -> And (Or (v, va), App (vb, vc))
                                         | Or (v, va), Neg vb -> And (Or (v, va), Neg vb)
                                         | Or (v, va), Or (vb, vc) -> And (Or (v, va), Or (vb, vc))
                                         | Or (v, va), And (vb, vc) -> And (Or (v, va), And (vb, vc))
                                         | Or (v, va), EQ vb -> And (Or (v, va), EQ vb)
                                         | And (v, va), App (vb, vc) -> And (And (v, va), App (vb, vc))
                                         | And (v, va), Neg vb -> And (And (v, va), Neg vb)
                                         | And (v, va), Or (vb, vc) -> And (And (v, va), Or (vb, vc))
                                         | And (v, va), And (vb, vc) -> And (And (v, va), And (vb, vc))
                                         | And (v, va), EQ vb -> And (And (v, va), EQ vb)
                                         | EQ v, App (va, vb) -> And (EQ v, App (va, vb))
                                         | EQ v, Neg va -> And (EQ v, Neg va)
                                         | EQ v, Or (va, vb) -> And (EQ v, Or (va, vb))
                                         | EQ v, And (va, vb) -> And (EQ v, And (va, vb))
                                         | EQ v, EQ va -> And (EQ v, EQ va);;


let rec prenex = function App (p, ts) -> App (p, ts)
                        | Neg f -> Neg f
                        | Or (f, g) -> prenex_d (prenex f) (prenex g)
                        | And (f, g) -> prenex_c (prenex f) (prenex g)
                        | AQ f -> AQ (prenex f)
                        | EQ f -> EQ f;;






let rec cnf_disj x0 h = match x0, h with And (f, g), h -> And (cnf_disj f h, cnf_disj g h)
                                       | App (v, va), And (g, h) -> And (cnf_disj (App (v, va)) g, cnf_disj (App (v, va)) h)
                                       | Neg v, And (g, h) -> And (cnf_disj (Neg v) g, cnf_disj (Neg v) h)
                                       | Or (v, va), And (g, h) -> And (cnf_disj (Or (v, va)) g, cnf_disj (Or (v, va)) h)
                                       | AQ v, And (g, h) -> And (cnf_disj (AQ v) g, cnf_disj (AQ v) h)
                                       | EQ v, And (g, h) -> And (cnf_disj (EQ v) g, cnf_disj (EQ v) h)
                                       | App (v, va), App (vb, vc) -> Or (App (v, va), App (vb, vc))
                                       | App (v, va), Neg vb -> Or (App (v, va), Neg vb)
                                       | App (v, va), Or (vb, vc) -> Or (App (v, va), Or (vb, vc))
                                       | App (v, va), AQ vb -> Or (App (v, va), AQ vb)
                                       | App (v, va), EQ vb -> Or (App (v, va), EQ vb)
                                       | Neg v, App (va, vb) -> Or (Neg v, App (va, vb))
                                       | Neg v, Neg va -> Or (Neg v, Neg va)
                                       | Neg v, Or (va, vb) -> Or (Neg v, Or (va, vb))
                                       | Neg v, AQ va -> Or (Neg v, AQ va)
                                       | Neg v, EQ va -> Or (Neg v, EQ va)
                                       | Or (v, va), App (vb, vc) -> Or (Or (v, va), App (vb, vc))
                                       | Or (v, va), Neg vb -> Or (Or (v, va), Neg vb)
                                       | Or (v, va), Or (vb, vc) -> Or (Or (v, va), Or (vb, vc))
                                       | Or (v, va), AQ vb -> Or (Or (v, va), AQ vb)
                                       | Or (v, va), EQ vb -> Or (Or (v, va), EQ vb)
                                       | AQ v, App (va, vb) -> Or (AQ v, App (va, vb))
                                       | AQ v, Neg va -> Or (AQ v, Neg va)
                                       | AQ v, Or (va, vb) -> Or (AQ v, Or (va, vb))
                                       | AQ v, AQ va -> Or (AQ v, AQ va)
                                       | AQ v, EQ va -> Or (AQ v, EQ va)
                                       | EQ v, App (va, vb) -> Or (EQ v, App (va, vb))
                                       | EQ v, Neg va -> Or (EQ v, Neg va)
                                       | EQ v, Or (va, vb) -> Or (EQ v, Or (va, vb))
                                       | EQ v, AQ va -> Or (EQ v, AQ va)
                                       | EQ v, EQ va -> Or (EQ v, EQ va);;


let rec cnf = function Or (f, g) -> cnf_disj (cnf f) (cnf g)
                     | And (f, g) -> And (cnf f, cnf g)
                     | AQ f -> AQ (cnf f)
                     | App (v, va) -> App (v, va)
                     | Neg v -> Neg v
                     | EQ v -> EQ v;;



let toCNFa b f = (let f2 = nnf f in
                  let (f3, ba) = eq_elimF f2 b in
                  let f4 = prenex f3 in
                       (ba, cnf f4));;

let toCNF f = (let f1 = sentence f in
               let a = toCNFa (newFun f1) f1 in
                    snd a);;




let rec scheme = function AQ f -> scheme f
                        | App (v, va) -> App (v, va)
                        | Neg v -> Neg v
                        | Or (v, va) -> Or (v, va)
                        | And (v, va) -> And (v, va)
                        | EQ v -> EQ v;;

let rec clausala x0 x1 = match x0, x1 with App (pa, ts), (n, p) -> (n, insa ord_atom [] p (pa, ts))
                                         | Neg (App (pa, ts)), (n, p) -> (insa ord_atom [] n (pa, ts), p)
                                         | Or (f, g), (n, p) -> clausala g (clausala f (n, p))
                                         | _, _ -> failwith "unexpected match in clausala";;


let rec clausal = function App (p, ts) -> [([], [(p, ts)])]
                         | Neg (App (p, ts)) -> [([(p, ts)], [])]
                         | Or (f, g) ->
                            (let cls = clausala (Or (f, g)) ([], []) in
                             (if taut_check cls then [] else [cls]))
                         | And (f, g) -> app (clausal f) (clausal g)
                         | _ -> failwith "unexpected match in clausal";;


let fol_transform x = comp (comp clausal scheme) toCNF x;;



let rec avl_match tr x1 = match x1 with [] -> Some tr
                                      | (Var i, t) :: ts ->
                                         (match updateBTT tr i t with None -> None
                                                                    | Some tra -> avl_match tra ts)
                                      | (TApp (_, _), Var _) :: _ -> None                                 
                                      | (TApp (f, xs), TApp (g, ys)) :: ts ->
                                         (if f === g then avl_match tr (zip_tr ts xs ys) else None);;


let match_atoms tr (pa, tsa) (p, ts) =
    (if pa === p then avl_match tr (zip_tr [] tsa ts) else None);;


let rec all_matches1 tr a x2 rs = match x2 with [] -> rs
                                              | x :: ls -> (match match_atoms tr a x with None -> all_matches1 tr a ls rs
                                                                                        | Some tra -> all_matches1 tr a ls (tra :: rs));;


let rec all_matchesa tr xs x2 = match x2 with [] -> [tr]
                                            | a :: ys -> (let m = all_matches1 tr a xs [] in
                                                           map_app_tr (fun x -> all_matchesa x xs ys) m []);;


let all_matches x = (fun (n, p) -> (let m = all_matchesa Tip n n in
                                    map_app_tr (fun xa -> all_matchesa xa p p) m [])) x;;




let subsumes_approx x = (fun (n1, p1) (n2, p2) ->
    forall (fun a -> exists (fun aa -> (is_some (match_atoms Tip a aa))) n2) n1 &&
      forall (fun a -> exists (fun aa -> (is_some (match_atoms Tip a aa))) p2) p1) x;;


let rec fixed_atom l x1 tr = match x1 with [] -> None
                                         | la :: ls -> (match match_atoms tr l la with None -> fixed_atom l ls tr
                                                                                     | Some tra -> Some (tra, ls));;

let rec subsumesa x0 x1 tr x3 = match x0, x1, x3 with ([], []), (_, _), (_, _) -> Some tr
                                                    | ([], l :: ys), (rsL, rsR), (lsL, lsR) ->
                                                           (match fixed_atom l rsR tr with None -> None
                                                                                         | Some (tra, rs) ->
                                                                                            (match subsumesa ([], ys) (rsL, lsR) tra (lsL, lsR)
                                                                                             with None -> subsumesa ([], l :: ys) (rsL, rs) tr (lsL, lsR)
                                                                                                | Some a -> Some a))
                                                    | (l :: xs, ys), (rsL, rsR), (lsL, lsR) ->
                                                           (match fixed_atom l rsL tr with None -> None
                                                                                         | Some (tra, rs) ->
                                                                                            (match subsumesa (xs, ys) (lsL, rsR) tra (lsL, lsR)
                                                                                             with None -> subsumesa (l :: xs, ys) (rs, rsR) tr (lsL, lsR)
                                                                                                | Some a -> Some a));;

let subsumes x = (fun (n1, p1) (n2, p2) -> subsumesa (n1, p1) (n2, p2) Tip (n2, p2)) x;;


let subsumes_check lsa ls =
    (if subsumes_approx lsa ls then is_some (subsumes lsa ls) else false);;

let rec find_min mcls b x2 = match x2 with [] -> mcls
                                         | ls :: lsL ->
                                            (let ba = length_Cls ls in
                                             (if ba < b then find_min ls ba lsL else find_min mcls b lsL));;


let min_cls ls = (match all_matches ls with [_] -> ls
                                          | trs ->
                                            (let a = map_tra (fun t ->
                                                 (let (n, p) = ls in
                                                  (map_foldl (insa ord_atom [])
                                                     (fun x -> (fst x, map_tr (endo_ext (lookupTerm t)) (snd x) [])) [] n,
                                                   map_foldl (insa ord_atom [])
                                                     (fun x -> (fst x, map_tr (endo_ext (lookupTerm t)) (snd x) [])) [] p)))
                                                 trs []
                                             in
                                             find_min ls (length_Cls ls) a));;






let rec preproca x0 rs = match x0, rs with [], rs -> rs
                                         | ls :: cs, rs ->
                                            (if exists (fun lsa -> subsumes_check lsa ls) cs then preproca cs rs
                                             else (if exists (fun lsa -> subsumes_check lsa ls) rs
                                                   then preproca cs rs
                                                   else (let lsa = min_cls ls in preproca cs (lsa :: rs))));;


let preproc cs = preproca cs [];;




let rec simplify
  = function Pred (p, ts) -> Pred (p, ts)
    | Negation f ->
        (match simplify f with Pred (a, lista) -> Negation (Pred (a, lista))
          | Negation aFormula -> Negation (Negation aFormula)
          | Disj (aFormula1, aFormula2) ->
            Negation (Disj (aFormula1, aFormula2))
          | Conj (aFormula1, aFormula2) ->
            Negation (Conj (aFormula1, aFormula2))
          | Imp (aFormula1, aFormula2) -> Negation (Imp (aFormula1, aFormula2))
          | Iff (aFormula1, aFormula2) -> Negation (Iff (aFormula1, aFormula2))
          | AQs (lista, aFormula) -> Negation (AQs (lista, aFormula))
          | EQs (lista, aFormula) -> Negation (EQs (lista, aFormula))
          | TRUE -> FALSE | FALSE -> TRUE)
    | Disj (f, g) ->
        (match simplify f
          with Pred (a, lista) ->
            (match simplify g
              with Pred (aa, listaa) ->
                Disj (Pred (a, lista), Pred (aa, listaa))
              | Negation aFormula -> Disj (Pred (a, lista), Negation aFormula)
              | Disj (aFormula1, aFormula2) ->
                Disj (Pred (a, lista), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Disj (Pred (a, lista), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Disj (Pred (a, lista), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Disj (Pred (a, lista), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormula) ->
                Disj (Pred (a, lista), AQs (listaa, aFormula))
              | EQs (listaa, aFormula) ->
                Disj (Pred (a, lista), EQs (listaa, aFormula))
              | TRUE -> TRUE | FALSE -> Pred (a, lista))
          | Negation aFormula ->
            (match simplify g
              with Pred (a, lista) -> Disj (Negation aFormula, Pred (a, lista))
              | Negation aFormulaa ->
                Disj (Negation aFormula, Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Disj (Negation aFormula, Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Disj (Negation aFormula, Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Disj (Negation aFormula, Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Disj (Negation aFormula, Iff (aFormula1, aFormula2))
              | AQs (lista, aFormulaa) ->
                Disj (Negation aFormula, AQs (lista, aFormulaa))
              | EQs (lista, aFormulaa) ->
                Disj (Negation aFormula, EQs (lista, aFormulaa))
              | TRUE -> TRUE | FALSE -> Negation aFormula)
          | Disj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Disj (Disj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Disj (Disj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Disj (Disj (aFormula1, aFormula2),
                       Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Disj (Disj (aFormula1, aFormula2),
                       Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Disj (Disj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Disj (Disj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Disj (Disj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Disj (Disj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Disj (aFormula1, aFormula2))
          | Conj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Disj (Conj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Disj (Conj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Disj (Conj (aFormula1, aFormula2),
                       Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Disj (Conj (aFormula1, aFormula2),
                       Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Disj (Conj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Disj (Conj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Disj (Conj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Disj (Conj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Conj (aFormula1, aFormula2))
          | Imp (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Disj (Imp (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Disj (Imp (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Disj (Imp (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Disj (Imp (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Disj (Imp (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Disj (Imp (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Disj (Imp (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Disj (Imp (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Imp (aFormula1, aFormula2))
          | Iff (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Disj (Iff (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Disj (Iff (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Disj (Iff (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Disj (Iff (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Disj (Iff (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Disj (Iff (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Disj (Iff (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Disj (Iff (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Iff (aFormula1, aFormula2))
          | AQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Disj (AQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Disj (AQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Disj (AQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Disj (AQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Disj (AQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Disj (AQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Disj (AQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Disj (AQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> TRUE | FALSE -> AQs (lista, aFormula))
          | EQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Disj (EQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Disj (EQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Disj (EQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Disj (EQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Disj (EQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Disj (EQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Disj (EQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Disj (EQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> TRUE | FALSE -> EQs (lista, aFormula))
          | TRUE -> TRUE | FALSE -> simplify g)
    | Conj (f, g) ->
        (match simplify f
          with Pred (a, lista) ->
            (match simplify g
              with Pred (aa, listaa) ->
                Conj (Pred (a, lista), Pred (aa, listaa))
              | Negation aFormula -> Conj (Pred (a, lista), Negation aFormula)
              | Disj (aFormula1, aFormula2) ->
                Conj (Pred (a, lista), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Conj (Pred (a, lista), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Conj (Pred (a, lista), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Conj (Pred (a, lista), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormula) ->
                Conj (Pred (a, lista), AQs (listaa, aFormula))
              | EQs (listaa, aFormula) ->
                Conj (Pred (a, lista), EQs (listaa, aFormula))
              | TRUE -> Pred (a, lista) | FALSE -> FALSE)
          | Negation aFormula ->
            (match simplify g
              with Pred (a, lista) -> Conj (Negation aFormula, Pred (a, lista))
              | Negation aFormulaa ->
                Conj (Negation aFormula, Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Conj (Negation aFormula, Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Conj (Negation aFormula, Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Conj (Negation aFormula, Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Conj (Negation aFormula, Iff (aFormula1, aFormula2))
              | AQs (lista, aFormulaa) ->
                Conj (Negation aFormula, AQs (lista, aFormulaa))
              | EQs (lista, aFormulaa) ->
                Conj (Negation aFormula, EQs (lista, aFormulaa))
              | TRUE -> Negation aFormula | FALSE -> FALSE)
          | Disj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Conj (Disj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Conj (Disj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Conj (Disj (aFormula1, aFormula2),
                       Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Conj (Disj (aFormula1, aFormula2),
                       Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Conj (Disj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Conj (Disj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Conj (Disj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Conj (Disj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Disj (aFormula1, aFormula2) | FALSE -> FALSE)
          | Conj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Conj (Conj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Conj (Conj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Conj (Conj (aFormula1, aFormula2),
                       Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Conj (Conj (aFormula1, aFormula2),
                       Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Conj (Conj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Conj (Conj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Conj (Conj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Conj (Conj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Conj (aFormula1, aFormula2) | FALSE -> FALSE)
          | Imp (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Conj (Imp (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Conj (Imp (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Conj (Imp (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Conj (Imp (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Conj (Imp (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Conj (Imp (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Conj (Imp (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Conj (Imp (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Imp (aFormula1, aFormula2) | FALSE -> FALSE)
          | Iff (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Conj (Iff (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Conj (Iff (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Conj (Iff (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Conj (Iff (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Conj (Iff (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Conj (Iff (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Conj (Iff (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Conj (Iff (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Iff (aFormula1, aFormula2) | FALSE -> FALSE)
          | AQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Conj (AQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Conj (AQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Conj (AQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Conj (AQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Conj (AQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Conj (AQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Conj (AQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Conj (AQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> AQs (lista, aFormula) | FALSE -> FALSE)
          | EQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Conj (EQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Conj (EQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Conj (EQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Conj (EQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Conj (EQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Conj (EQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Conj (EQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Conj (EQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> EQs (lista, aFormula) | FALSE -> FALSE)
          | TRUE -> simplify g | FALSE -> FALSE)
    | Imp (f, g) ->
        (match simplify f
          with Pred (a, lista) ->
            (match simplify g
              with Pred (aa, listaa) -> Imp (Pred (a, lista), Pred (aa, listaa))
              | Negation aFormula -> Imp (Pred (a, lista), Negation aFormula)
              | Disj (aFormula1, aFormula2) ->
                Imp (Pred (a, lista), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Imp (Pred (a, lista), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Imp (Pred (a, lista), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Imp (Pred (a, lista), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormula) ->
                Imp (Pred (a, lista), AQs (listaa, aFormula))
              | EQs (listaa, aFormula) ->
                Imp (Pred (a, lista), EQs (listaa, aFormula))
              | TRUE -> TRUE | FALSE -> Negation (Pred (a, lista)))
          | Negation aFormula ->
            (match simplify g
              with Pred (a, lista) -> Imp (Negation aFormula, Pred (a, lista))
              | Negation aFormulaa ->
                Imp (Negation aFormula, Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Imp (Negation aFormula, Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Imp (Negation aFormula, Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Imp (Negation aFormula, Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Imp (Negation aFormula, Iff (aFormula1, aFormula2))
              | AQs (lista, aFormulaa) ->
                Imp (Negation aFormula, AQs (lista, aFormulaa))
              | EQs (lista, aFormulaa) ->
                Imp (Negation aFormula, EQs (lista, aFormulaa))
              | TRUE -> TRUE | FALSE -> Negation (Negation aFormula))
          | Disj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Imp (Disj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Imp (Disj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Imp (Disj (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Imp (Disj (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Imp (Disj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Imp (Disj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Imp (Disj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Imp (Disj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Negation (Disj (aFormula1, aFormula2)))
          | Conj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Imp (Conj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Imp (Conj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Imp (Conj (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Imp (Conj (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Imp (Conj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Imp (Conj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Imp (Conj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Imp (Conj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Negation (Conj (aFormula1, aFormula2)))
          | Imp (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Imp (Imp (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Imp (Imp (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Imp (Imp (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Imp (Imp (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Imp (Imp (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Imp (Imp (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Imp (Imp (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Imp (Imp (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Negation (Imp (aFormula1, aFormula2)))
          | Iff (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Imp (Iff (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Imp (Iff (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Imp (Iff (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Imp (Iff (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Imp (Iff (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Imp (Iff (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Imp (Iff (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Imp (Iff (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> TRUE | FALSE -> Negation (Iff (aFormula1, aFormula2)))
          | AQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Imp (AQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Imp (AQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Imp (AQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Imp (AQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Imp (AQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Imp (AQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Imp (AQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Imp (AQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> TRUE | FALSE -> Negation (AQs (lista, aFormula)))
          | EQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Imp (EQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Imp (EQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Imp (EQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Imp (EQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Imp (EQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Imp (EQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Imp (EQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Imp (EQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> TRUE | FALSE -> Negation (EQs (lista, aFormula)))
          | TRUE -> simplify g | FALSE -> TRUE)
    | Iff (f, g) ->
        (match simplify f
          with Pred (a, lista) ->
            (match simplify g
              with Pred (aa, listaa) -> Iff (Pred (a, lista), Pred (aa, listaa))
              | Negation aFormula -> Iff (Pred (a, lista), Negation aFormula)
              | Disj (aFormula1, aFormula2) ->
                Iff (Pred (a, lista), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Iff (Pred (a, lista), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Iff (Pred (a, lista), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Iff (Pred (a, lista), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormula) ->
                Iff (Pred (a, lista), AQs (listaa, aFormula))
              | EQs (listaa, aFormula) ->
                Iff (Pred (a, lista), EQs (listaa, aFormula))
              | TRUE -> Pred (a, lista) | FALSE -> Negation (Pred (a, lista)))
          | Negation aFormula ->
            (match simplify g
              with Pred (a, lista) -> Iff (Negation aFormula, Pred (a, lista))
              | Negation aFormulaa ->
                Iff (Negation aFormula, Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Iff (Negation aFormula, Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Iff (Negation aFormula, Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Iff (Negation aFormula, Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Iff (Negation aFormula, Iff (aFormula1, aFormula2))
              | AQs (lista, aFormulaa) ->
                Iff (Negation aFormula, AQs (lista, aFormulaa))
              | EQs (lista, aFormulaa) ->
                Iff (Negation aFormula, EQs (lista, aFormulaa))
              | TRUE -> Negation aFormula
              | FALSE -> Negation (Negation aFormula))
          | Disj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Iff (Disj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Iff (Disj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Iff (Disj (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Iff (Disj (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Iff (Disj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Iff (Disj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Iff (Disj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Iff (Disj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Disj (aFormula1, aFormula2)
              | FALSE -> Negation (Disj (aFormula1, aFormula2)))
          | Conj (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Iff (Conj (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Iff (Conj (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Iff (Conj (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Iff (Conj (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Iff (Conj (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Iff (Conj (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Iff (Conj (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Iff (Conj (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Conj (aFormula1, aFormula2)
              | FALSE -> Negation (Conj (aFormula1, aFormula2)))
          | Imp (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Iff (Imp (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Iff (Imp (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Iff (Imp (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Iff (Imp (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Iff (Imp (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Iff (Imp (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Iff (Imp (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Iff (Imp (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Imp (aFormula1, aFormula2)
              | FALSE -> Negation (Imp (aFormula1, aFormula2)))
          | Iff (aFormula1, aFormula2) ->
            (match simplify g
              with Pred (a, lista) ->
                Iff (Iff (aFormula1, aFormula2), Pred (a, lista))
              | Negation aFormula ->
                Iff (Iff (aFormula1, aFormula2), Negation aFormula)
              | Disj (aFormula1a, aFormula2a) ->
                Iff (Iff (aFormula1, aFormula2), Disj (aFormula1a, aFormula2a))
              | Conj (aFormula1a, aFormula2a) ->
                Iff (Iff (aFormula1, aFormula2), Conj (aFormula1a, aFormula2a))
              | Imp (aFormula1a, aFormula2a) ->
                Iff (Iff (aFormula1, aFormula2), Imp (aFormula1a, aFormula2a))
              | Iff (aFormula1a, aFormula2a) ->
                Iff (Iff (aFormula1, aFormula2), Iff (aFormula1a, aFormula2a))
              | AQs (lista, aFormula) ->
                Iff (Iff (aFormula1, aFormula2), AQs (lista, aFormula))
              | EQs (lista, aFormula) ->
                Iff (Iff (aFormula1, aFormula2), EQs (lista, aFormula))
              | TRUE -> Iff (aFormula1, aFormula2)
              | FALSE -> Negation (Iff (aFormula1, aFormula2)))
          | AQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Iff (AQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Iff (AQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Iff (AQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Iff (AQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Iff (AQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Iff (AQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Iff (AQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Iff (AQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> AQs (lista, aFormula)
              | FALSE -> Negation (AQs (lista, aFormula)))
          | EQs (lista, aFormula) ->
            (match simplify g
              with Pred (a, listaa) ->
                Iff (EQs (lista, aFormula), Pred (a, listaa))
              | Negation aFormulaa ->
                Iff (EQs (lista, aFormula), Negation aFormulaa)
              | Disj (aFormula1, aFormula2) ->
                Iff (EQs (lista, aFormula), Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Iff (EQs (lista, aFormula), Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Iff (EQs (lista, aFormula), Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Iff (EQs (lista, aFormula), Iff (aFormula1, aFormula2))
              | AQs (listaa, aFormulaa) ->
                Iff (EQs (lista, aFormula), AQs (listaa, aFormulaa))
              | EQs (listaa, aFormulaa) ->
                Iff (EQs (lista, aFormula), EQs (listaa, aFormulaa))
              | TRUE -> EQs (lista, aFormula)
              | FALSE -> Negation (EQs (lista, aFormula)))
          | TRUE -> simplify g
          | FALSE ->
            (match simplify g with Pred (a, lista) -> Negation (Pred (a, lista))
              | Negation aFormula -> Negation (Negation aFormula)
              | Disj (aFormula1, aFormula2) ->
                Negation (Disj (aFormula1, aFormula2))
              | Conj (aFormula1, aFormula2) ->
                Negation (Conj (aFormula1, aFormula2))
              | Imp (aFormula1, aFormula2) ->
                Negation (Imp (aFormula1, aFormula2))
              | Iff (aFormula1, aFormula2) ->
                Negation (Iff (aFormula1, aFormula2))
              | AQs (lista, aFormula) -> Negation (AQs (lista, aFormula))
              | EQs (lista, aFormula) -> Negation (EQs (lista, aFormula))
              | TRUE -> FALSE | FALSE -> TRUE))
    | AQs (vs, f) ->
        (match simplify f with Pred (a, lista) -> AQs (vs, Pred (a, lista))
          | Negation aFormula -> AQs (vs, Negation aFormula)
          | Disj (aFormula1, aFormula2) -> AQs (vs, Disj (aFormula1, aFormula2))
          | Conj (aFormula1, aFormula2) -> AQs (vs, Conj (aFormula1, aFormula2))
          | Imp (aFormula1, aFormula2) -> AQs (vs, Imp (aFormula1, aFormula2))
          | Iff (aFormula1, aFormula2) -> AQs (vs, Iff (aFormula1, aFormula2))
          | AQs (lista, aFormula) -> AQs (vs, AQs (lista, aFormula))
          | EQs (lista, aFormula) -> AQs (vs, EQs (lista, aFormula))
          | TRUE -> TRUE | FALSE -> FALSE)
    | EQs (vs, f) ->
        (match simplify f with Pred (a, lista) -> EQs (vs, Pred (a, lista))
          | Negation aFormula -> EQs (vs, Negation aFormula)
          | Disj (aFormula1, aFormula2) -> EQs (vs, Disj (aFormula1, aFormula2))
          | Conj (aFormula1, aFormula2) -> EQs (vs, Conj (aFormula1, aFormula2))
          | Imp (aFormula1, aFormula2) -> EQs (vs, Imp (aFormula1, aFormula2))
          | Iff (aFormula1, aFormula2) -> EQs (vs, Iff (aFormula1, aFormula2))
          | AQs (lista, aFormula) -> EQs (vs, AQs (lista, aFormula))
          | EQs (lista, aFormula) -> EQs (vs, EQs (lista, aFormula))
          | TRUE -> TRUE | FALSE -> FALSE)
    | TRUE -> TRUE
    | FALSE -> FALSE;;


let rec toTerm tau vMap x2 = match x2 with TApp (f, ts) -> TApp (tau f, map_tr (toTerm tau vMap) ts [])
                                         | Var x -> Var (vMap x);;


let rec toFOL tau vMap x2 = match x2 with Pred(p, ts) -> App (tau p, map_tr (toTerm tau vMap) ts [])
                                        | Negation f -> Neg (toFOL tau vMap f)
                                        | Disj(f, g) -> Or (toFOL tau vMap f, toFOL tau vMap g)
                                        | Conj(f, g) -> And (toFOL tau vMap f, toFOL tau vMap g)
                                        | Imp (f, g) -> Or (Neg (toFOL tau vMap f), toFOL tau vMap g)
                                        | Iff (f, g) -> And (Or (Neg (toFOL tau vMap f), toFOL tau vMap g),
                                                             Or (Neg (toFOL tau vMap g), toFOL tau vMap f))
                                        | AQs ([], f) -> toFOL tau vMap f
                                        | AQs (x :: xs, f) -> AQ (toFOL tau (fun_upd_c3 (fun n -> suc (vMap n)) x zero_nat) (AQs (xs, f)))
                                        | EQs ([], f) -> toFOL tau vMap f
                                        | EQs (x :: xs, f) -> EQ (toFOL tau (fun_upd_c3 (fun n -> suc (vMap n)) x zero_nat) (EQs (xs, f)))
                                        | TRUE -> Or (App (zero_nat, []), Neg (App (zero_nat, [])))
                                        | FALSE -> And (App (zero_nat, []), Neg (App (zero_nat, [])));;


let clausal_transforma tau = comp (comp fol_transform (toFOL tau tau)) simplify;;

let clausal_transform tau = comp (clausal_transforma tau) (fun a -> Negation a);;


let nat_of_char c = Z.of_int (Char.code c);;

let char3_nat x = (fun (a, (b, c)) ->
        plus_nat
          (times_nat (Z.of_int 256)
            (plus_nat
              (times_nat (Z.of_int 256) (nat_of_char a))
              (nat_of_char b)))
          (nat_of_char c))
        x;;

let clausal_transform3 x = clausal_transform char3_nat x;;

let preprocess x = comp preproc clausal_transform3 x;;



