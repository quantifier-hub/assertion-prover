(* *********************************************************************

    The file search.ml is part of the 'assertion' prover package.
    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************* *)


open Lib
open Preprocess
    

let subfactor x = (fun (l, cl) (la, cla) -> (match match_atoms Tip l la with None -> false
                                                                           | Some tr -> is_some (subsumesa cl cla tr cla))) x;;

let rec trim_factorsa x0 rs = match x0 with [] -> rs
                                          | x :: fs ->
                                              (if exists (fun xa -> subfactor xa x) fs then trim_factorsa fs rs
                                               else (if exists (fun xa -> subfactor xa x) rs then trim_factorsa fs rs
                                                     else trim_factorsa fs (x :: rs)));;

let trim_factors fs = trim_factorsa fs [];;
  


let rec unifya = function ([], tr) -> Some tr
                        | ((Var i, Var j) :: ts, tr) ->
        (if i === j then unifya (ts, tr)
         else unifya (map_tra (fun (l, r) -> (substT (l, (i, Var j)), substT (r, (i, Var j)))) ts [],
                      updateBT (mapVal (fun x -> substT (x, (i, Var j))) tr) i (Var j)))
                        | ((Var i, TApp (v, va)) :: ts, tr) ->
        (if occursVarT i (TApp (v, va)) then None
         else unifya (map_tra (fun (l, r) -> (substT (l, (i, TApp (v, va))), substT (r, (i, TApp (v, va))))) ts [],
                      updateBT (mapVal (fun x -> substT (x, (i, TApp (v, va)))) tr) i (TApp (v, va))))
                        | ((TApp (v, va), Var i) :: ts, tr) ->
        (if occursVarT i (TApp (v, va)) then None
         else unifya (map_tra (fun (l, r) -> (substT (l, (i, TApp (v, va))), substT (r, (i, TApp (v, va))))) ts [],
                      updateBT (mapVal (fun x -> substT (x, (i, TApp (v, va)))) tr) i (TApp (v, va))))
                        | ((TApp (f, xs), TApp (g, ys)) :: ts, tr) ->
        (if f === g then unifya (zip_tr ts xs ys, tr) else None);;

let avl_unify ts = map_option lookupTerm (unifya (ts, Tip));;
  
let rec zipT_tr st x1 = match x1 with [] -> st
                                    | [_] -> st
                                    | xs :: ys :: ts -> zipT_tr (zip_tr st xs ys) (ys :: ts);;

let unify ts = avl_unify (zipT_tr [] ts);;

let rec trl x0 rs = match x0 with [] -> Some rs
                                | [(_, ts)] -> Some (ts :: rs)
                                | (p, tsa) :: (q, ts) :: xs ->
                                    (if p === q then trl ((q, ts) :: xs) (tsa :: rs) else None);;


let unifyb ls = (match trl ls [] with None -> None
                                    | Some a -> unify a);;
 

let rec factors_tr x0 st = match x0 with [] -> st
                                       | x :: xs ->
                                           factors_tr xs (map_opt (fun a -> (match a with ([], _) -> Some ([x], None)
                                                                                        | (aa :: lista, _) ->
                                                                                          (let ls = x :: aa :: lista in
                                                                                           (match unifyb ls with None -> None
                                                                                                               | Some u -> Some (ls, Some u))))) st st);;


let factorsN x = (fun (n, p) ->
        (let a = factors_tr n [([], None)] in
          map_filter (fun (xs, u) -> (match xs with [] -> (let s = endo_ext (the u) in
                                                           let (pa, ts) = hd xs in                                                           
                                                           let tsa = map_tr s ts [] in
                                                           let aa = (pa, tsa) in
                                                           (aa, (map_foldl (ins_except ord_atom aa) (fun (pb, tsb) -> (pb, map_tr s tsb [])) [] n,
                                                                 map_foldl (insa ord_atom []) (fun (pb, tsb) -> (pb, map_tr s tsb [])) [] p)))
                                                  | [l] -> (l, (remS ord_atom [] n l, p))                            
                                                  | _ :: _ :: _ -> (let s = endo_ext (the u) in
                                                                    let (pa, ts) = hd xs in
                                                                    let tsa = map_tr s ts [] in
                                                                    let aa = (pa, tsa) in
                                                                    (aa, (map_foldl (ins_except ord_atom aa) (fun (pb, tsb) -> (pb, map_tr s tsb [])) [] n,
                                                                          map_foldl (insa ord_atom []) (fun (pb, tsb) -> (pb, map_tr s tsb [])) [] p)))))
            (fun aa -> (match aa with ([], _) -> false | (_ :: _, _) -> true)) a)) x;;

let factors x = (fun (n, p) ->
    (let a = factors_tr p [([], None)] in
     map_filter (fun (xs, u) -> (match xs with [] -> (let s = endo_ext (the u) in
                                                      let (pa, ts) = hd xs in
                                                      let tsa = map_tr s ts [] in
                                                      let aa = (pa, tsa) in
                                                      (aa, (n, map_foldl (ins_except ord_atom aa) (fun (pb, tsb) -> (pb, map_tr s tsb [])) [] p)))
                                             | [l] -> (l, (n, remS ord_atom [] p l))
                                             | _ :: _ :: _ -> (let s = endo_ext (the u) in
                                                               let (pa, ts) = hd xs in
                                                               let tsa = map_tr s ts [] in
                                                               let aa = (pa, tsa) in
                                                               (aa, (n, map_foldl (ins_except ord_atom aa) (fun (pb, tsb) -> (pb, map_tr s tsb [])) [] p)))))
       (fun aa -> (match aa with ([], _) -> false | (_ :: _, _) -> true)) a)) x;;


let resolution_core l r =
  (if (fst (fst l)) === (fst (fst r)) 
   then (match avl_unify (zip_tr [] (snd (fst r)) (snd (fst l))) with None -> Nothing
                                                                    | Some u ->
                                                                      (let ua = endo_ext u in
                                                                       let n = map_foldl (insa ord_atom []) (fun (p, ts) -> (p, map_tr ua ts [])) [] (fst (snd l)) in
                                                                       let na = map_foldl (insa ord_atom []) (fun (p, ts) -> (p, map_tr ua ts [])) n (fst (snd r)) in
                                                                       let p = map_foldl (insa ord_atom []) (fun (p, ts) -> (p, map_tr ua ts [])) [] (snd (snd l)) in                                                   
                                                                       let pa = map_foldl (insa ord_atom []) (fun (pa, ts) -> (pa, map_tr ua ts [])) p (snd (snd r)) in
                                                                       (match (na, pa) with ([], []) -> Empty
                                                                                          | ([], a :: lista) ->
                                                                                            (if taut_check ([], a :: lista) then Nothing
                                                                                             else Res (min_cls ([], a :: lista)))
                                                                                          | (aa :: lista, b) ->
                                                                                            (if taut_check (aa :: lista, b) then Nothing
                                                                                             else Res (min_cls (aa :: lista, b))))))
   else Nothing);;



let rec factors_resolvents1 pf x1 st = match x1 with [] -> Some st
                                                   | f :: fs ->
                                                     (match resolution_core pf f with Nothing -> factors_resolvents1 pf fs st
                                                                                    | Empty -> None
                                                                                    | Res r -> factors_resolvents1 pf fs (r :: st));;


let rec factors_resolvents x0 mfs st = match x0 with [] -> Some st
                                                   | pf :: fs ->
                                                     (match factors_resolvents1 pf mfs st with None -> None
                                                                                             | Some a -> factors_resolvents fs mfs a);;


let resolve_pos ecls = map_app (fun eclsa -> (if isPos eclsa then Some []
                                              else factors_resolvents ecls.factorsa eclsa.factorsa []));;

let resolve_mx ecls = map_app (fun eclsa -> (if not (isPos eclsa) then Some []
                                             else factors_resolvents eclsa.factorsa ecls.factorsa []));;





let rec repl_pos lsa x1 rs = match x1 with [] -> app rs [lsa]
                                         | ls :: cs ->
                                           (if all_NEG ls then repl_pos lsa cs (ls :: rs)
                                            else (if subsumes_check lsa ls then
                                                          (let csa = filter (fun lsb -> all_NEG lsb || not (subsumes_check lsa lsb)) cs
                                                           in
                                                           app rs (lsa :: csa))
                                                        else repl_pos lsa cs (ls :: rs)));;


let rec repl_neg lsa x1 rs = match x1 with [] -> app rs [lsa]
                                         | ls :: cs ->
                                           (if all_POS ls then repl_neg lsa cs (ls :: rs)
                                            else (if subsumes_check lsa ls then
                                                          (let csa = filter (fun lsb -> all_POS lsb || not (subsumes_check lsa lsb)) cs
                                                           in
                                                           app rs (lsa :: csa))
                                                        else repl_neg lsa cs (ls :: rs)));;

let rec repl_mx lsa x1 rs = match x1 with [] -> app rs [lsa]
                                        | ls :: cs ->
                                          (if all_POS ls || all_NEG ls then repl_mx lsa cs (ls :: rs)
                                                 else (if subsumes_check lsa ls
                                                       then app rs (lsa :: filter(fun lsb -> all_POS lsb || (all_NEG lsb || not(subsumes_check lsa lsb))) cs)
                                                       else repl_mx lsa cs (ls :: rs)));;


let rec incorp gcl x1 cs = match x1 with [] -> cs
                                       | ls :: rs ->
                                         (if all_POS ls
                                          then (if subsumes_check gcl ls || exists (fun lsa -> all_POS lsa && subsumes_check lsa ls) cs
                                                then incorp gcl rs cs else incorp gcl rs (repl_pos ls cs []))
                                          else (if all_NEG ls
                                                then (if subsumes_check gcl ls || exists (fun lsa -> all_NEG lsa && subsumes_check lsa ls) cs
                                                      then incorp gcl rs cs
                                                      else incorp gcl rs (repl_neg ls cs []))
                                                else (if subsumes_check gcl ls || exists (fun lsa -> subsumes_check lsa ls) cs
                                                      then incorp gcl rs cs
                                                      else incorp gcl rs (repl_mx ls cs []))));;


let rec gc (vbound, (used, unused)) =
    (match unused with [] -> false
                     | ls :: unuseda ->
                       (let (lsa, vbounda) =
                          (match vars_OF ls with [] -> (ls, vbound)
                                               | a :: lista ->
                                  (let (nmn, nmx) = nmin_nmax (a :: lista) in
                                   (if less_eq_nat vbound nmn then (ls, suc nmx)
                                    else (let diff = minus_nat vbound nmn in
                                          (shiftCls diff ls, suc (plus_nat nmx diff))))))
                        in
                        (if all_POS lsa then
                           (let useda = filter (fun ecls -> isNeg ecls || not (subsumes_check lsa ecls.clause)) used in
                            let ecls = {clause = lsa; factorsa = trim_factors (factors lsa); kind = Positive} in
                            let usedaa = ecls :: useda in
                            (match resolve_pos ecls useda with None -> true
                                                             | Some rs -> gc (vbounda, (usedaa, incorp lsa rs unuseda))))
                         else (let useda = filter (fun ecls -> isPos ecls || not (subsumes_check lsa ecls.clause)) used in
                               let ecls = {clause = lsa; factorsa = trim_factors (factorsN lsa); kind = (if all_NEG lsa then Negative else Mixed)} in
                               let usedaa = ecls :: useda in
                               (match resolve_mx ecls useda with None -> true           
                                                               | Some rs -> gc (vbounda, (usedaa, incorp lsa rs unuseda)))))));;




let proof_search cs = (match filter (fun a -> (match a with ([], []) -> true
                                                          | ([], _ :: _) -> false
                                                          | (_ :: _, _) -> false)) cs
   with [] -> gc (zero_nat, ([], weighted_insSort (fun (n, p) -> (size_list n) + (size_list p)) cs))
      | _ :: _ -> true);;


 
  

