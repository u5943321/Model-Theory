open HolKernel Parse boolLib bossLib;
open nlistTheory listTheory;
open pred_setTheory;

val _ = new_theory "chap1";

(*    
Definition FV2C_def:
  FV2C x c (V n) = if n = x then (Fn c []) else (V n) /\
  FV2C x c (Fn n l) = Fn n (MAP (\t. FV2C x c t) l)
End
*)

Definition wit_prop_def:
  wit_prop L TH (:α) <=> !ϕ x. L_form L ϕ /\ FV ϕ = {x} ==>
                             ?c. L.Fun_sym c 0 /\
                                 !M:α model v.
                                     struc L M /\ valuation M v /\
                                     (!ψ. ψ IN TH ==> satis M v ψ) /\
                                     satis M v (Exists x ϕ) ==>
                                       satis M (\x. M.Fun c []) ϕ
End

        
Definition maxi_def:
  maxi L TH <=> L_theory L TH /\
                (!ϕ. L_form L ϕ /\ sen ϕ ==> (ϕ IN TH \/ (Not ϕ) IN TH) /\
                                             ¬(ϕ IN TH /\ (Not ϕ) IN TH))
End                      
                                            
Theorem lemma_2_1_6:
  maxi L TH /\ fin_satisfiable L TH (:α) ==>
  !Δ ψ. Δ ⊆ TH /\ FINITE Δ /\ cons L Δ ψ (:α) /\ sen ψ ==> ψ IN TH
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘(Not ψ) IN TH’
  by
   (fs[maxi_def] >>
    ‘L_form L ψ ∧ sen ψ /\ ψ NOTIN TH’ suffices_by metis_tac[] >>
    rw[] >> metis_tac[cons_def]) >>
fs[fin_satisfiable_def] >>
‘(Δ ∪ {Not ψ}) ⊆ TH ∧ FINITE (Δ ∪ {Not ψ}) /\ ¬satisfiable L (Δ ∪ {Not ψ}) (:α)’
  suffices_by metis_tac[] >>
strip_tac (* 2 *)
>- fs[SUBSET_DEF] >>
strip_tac (* 2 *)
>- fs[] >>
SPOSE_NOT_THEN ASSUME_TAC >> fs[cons_def,satisfiable_def] >>
‘M.Dom <> {}’ by fs[struc_def] >>
fs[GSYM MEMBER_NOT_EMPTY] >>
‘valuation M (\a:num.x)’ by rw[valuation_def] >>
‘satis M (λa. x) (Not ψ)’
  by metis_tac[] >>
‘satis M (λa. x) ψ’
  by metis_tac[] >>
fs[satis_def,holds_def,Not_def]
QED

Definition L_with_eq_def:
  L_with_eq L (:α) <=> L.Pred_sym 0 2 /\
                       (!M:α model. struc L M ==> !a b. M.Pred 0 [a;b] <=>
                                          (a IN M.Dom /\ b IN M.Dom /\ a = b))
End                                    

Definition sim_const_def:
  sim_const L TH (:α) c d <=> L_with_eq L (:α) /\
                         L.Fun_sym c 0 /\ L.Fun_sym d 0 /\ L_theory L TH /\
                         (Pred 0 [Fn c [];Fn d []]) IN TH
End
(*
Theorem sim_const_IN_TH:
  L_with_eq L (:α) /\ sim_const L TH (:α) c d /\ maxi L TH /\ fin_satisfiable L TH (:α) ==>
  Pred 0 [Fn c []; Fn d []] ∈ TH
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘(Not (Pred 0 [Fn c []; Fn d []])) IN TH’
  by
   (fs[maxi_def] >>
   ‘L_form L (Pred 0 [Fn c []; Fn d []]) ∧ sen (Pred 0 [Fn c []; Fn d []])’
     by
      (fs[L_form_def,form_predicates,form_functions_def,sen_def,
          FV_def,sim_const_def,L_with_eq_def] >> metis_tac[]) >>
   metis_tac[]) >>
‘’
irule lemma_2_1_6 >> rw[sen_def,form_predicates] >>
map_every qexists_tac [‘L’,‘’]
*)                                                     

Theorem lemma_2_1_7_claim_1:
  L_with_eq L (:α) /\ L_theory L TH /\
  maxi L TH /\ fin_satisfiable L TH (:α) ==>
  (sim_const L TH (:α)) equiv_on {c | L.Fun_sym c 0}
Proof     
rw[equiv_on_def] (* 3 *)
>- (rw[sim_const_def] >> irule lemma_2_1_6 >> rw[sen_def,form_predicates] >>
   map_every qexists_tac [‘L’,‘{}’] >> rw[cons_def,satis_def,holds_def] (* 2 *)
   >- fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
   fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
   fs[struc_def])
>- (rw[sim_const_def,EQ_IMP_THM] (* 2 *)
   >- (irule lemma_2_1_6 >> rw[sen_def,form_predicates] >>
       map_every qexists_tac [‘L’,‘{Pred 0 [Fn x []; Fn y []]}’] >>
       rw[cons_def,satis_def,holds_def] (* 3 *)
       >- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
          metis_tac[])
       >- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
          metis_tac[]) >>
       fs[L_with_eq_def] >> metis_tac[]) >>
   irule lemma_2_1_6 >> rw[sen_def,form_predicates] >>
   map_every qexists_tac [‘L’,‘{Pred 0 [Fn y []; Fn x []]}’] >>
   rw[cons_def,satis_def,holds_def] (* 3 *)
   >- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
       metis_tac[])
   >- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
       metis_tac[]) >>
   fs[L_with_eq_def] >> metis_tac[]) >>
rw[sim_const_def] >> irule lemma_2_1_6 >> rw[sen_def,form_predicates] >>
map_every qexists_tac
[‘L’,‘{Pred 0 [Fn x []; Fn y []]; Pred 0 [Fn y []; Fn z []]}’] >>
rw[cons_def,satis_def,holds_def] (* 6 *)
>- fs[sim_const_def] 
>- fs[sim_const_def]
>- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
    metis_tac[])
>- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
    metis_tac[])
>- (fs[L_form_def,form_predicates,form_functions_def,L_with_eq_def] >>
    metis_tac[]) >>
‘holds M v (Pred 0 [Fn x []; Fn y []]) /\ holds M v (Pred 0 [Fn y []; Fn z []])’  by metis_tac[] >>
fs[holds_def,L_with_eq_def] >> metis_tac[]     
QED

Theorem lemma_2_1_7_claim_2:
  L_with_eq L (:α) /\ L.Pred_sym r nr /\ LENGTH cs = nr /\ LENGTH ds = nr /\
  L_theory L TH /\ maxi L TH /\ fin_satisfiable L TH (:α) /\
  (!n. n < nr ==> sim_const L TH (:α) (EL n cs) (EL n ds)) ==>
  ((Pred r (MAP (\a. Fn a []) cs)) IN TH <=>    
   (Pred r (MAP (\a. Fn a []) ds)) IN TH)
Proof
rw[EQ_IMP_THM] (* 2 *)
>- (irule lemma_2_1_6 >>
   rw[sen_def,form_predicates,FVT_def,LIST_UNION_def,MAP_MAP_o] (* 2 *)
   >- (SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY,MEM_MAP] >> 
       metis_tac[MEMBER_NOT_EMPTY]) >>
   qexists_tac ‘L’ >>
   qexists_tac ‘((Pred r (MAP (λa. Fn a []) cs)) INSERT 
                  {Pred 0 [Fn (EL n cs) [] ; Fn (EL n ds) []] | n | n < LENGTH ds})’ >>
   rw[cons_def,satis_def,holds_def] (* 6 *)
   >- (qabbrev_tac
        ‘eqs = {Pred 0 [Fn (EL n cs) []; Fn (EL n ds) []] |n| n < LENGTH ds}’ >>
      ‘?f s0:num -> bool. FINITE s0 /\ eqs = IMAGE f s0’
         suffices_by metis_tac[IMAGE_FINITE]>>
      map_every qexists_tac
        [‘\n. (Pred 0 [Fn (EL n cs) []; Fn (EL n ds) []])’,
         ‘{n | n < LENGTH ds}’] >>
      rw[] (* 2 *)
      >- (‘FINITE (count (LENGTH ds))’ by metis_tac[FINITE_COUNT] >>
         ‘(count (LENGTH ds)) = {n | n < LENGTH ds}’ by rw[count_def] >>
         metis_tac[]) >>
      rw[Abbr‘eqs’,EXTENSION,IMAGE_DEF])
   >- (fs[sim_const_def] >> rw[SUBSET_DEF] >> metis_tac[])
   >- (rw[L_form_def,form_predicates,form_functions_def] >>
      fs[MEM_MAP] >> rw[] >> fs[term_functions_def] >> rw[] >>
      fs[L_theory_def,L_form_def] >> first_x_assum drule >> rw[] >>
      first_x_assum irule >> qexists_tac ‘{(a,0)}’ >> rw[MAP_MAP_o,MEM_MAP] >>
      rw[PULL_EXISTS])
   >- (rw[L_form_def,form_predicates,form_functions_def] >>
      fs[MEM_MAP] >> rw[] >> fs[term_functions_def] >> rw[] (* 3 *) >>
      fs[sim_const_def,L_with_eq_def])
   >- (rw[L_form_def,form_predicates,form_functions_def] >>
      fs[MEM_MAP,MAP_MAP_o] >> rw[] >> fs[sim_const_def] >> rw[] >>
      fs[MEM_EL]) >>
   ‘M.Pred r (MAP (termval M v) (MAP (λa. Fn a []) cs)) /\
   (MAP (termval M v) (MAP (λa. Fn a []) cs) =
    MAP (termval M v) (MAP (λa. Fn a []) ds))’
      suffices_by metis_tac[] >>
   strip_tac (* 2 *)
   >- (‘holds M v (Pred r (MAP (λa. Fn a []) cs))’ by metis_tac[] >>
      fs[holds_def]) >>
   rw[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP] >>
   ‘holds M v (Pred 0 [Fn (EL x cs) []; Fn (EL x ds) []])’
     by metis_tac[] >>
   fs[holds_def,L_with_eq_def] >> metis_tac[]) >>
irule lemma_2_1_6 >>
rw[sen_def,form_predicates,FVT_def,LIST_UNION_def,MAP_MAP_o] (* 2 *)
>- (SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY,MEM_MAP] >> 
    metis_tac[MEMBER_NOT_EMPTY]) >>
qexists_tac ‘L’ >>
qexists_tac
  ‘((Pred r (MAP (λa. Fn a []) ds)) INSERT 
    {Pred 0 [Fn (EL n cs) [] ; Fn (EL n ds) []] | n | n < LENGTH ds})’ >>
rw[cons_def,satis_def,holds_def] (* 6 *)
>- (qabbrev_tac
      ‘eqs = {Pred 0 [Fn (EL n cs) []; Fn (EL n ds) []] |n| n < LENGTH ds}’ >>
    ‘?f s0:num -> bool. FINITE s0 /\ eqs = IMAGE f s0’
      suffices_by metis_tac[IMAGE_FINITE]>>
    map_every qexists_tac
      [‘\n. (Pred 0 [Fn (EL n cs) []; Fn (EL n ds) []])’,
       ‘{n | n < LENGTH ds}’] >>
    rw[] (* 2 *)
   >- (‘FINITE (count (LENGTH ds))’ by metis_tac[FINITE_COUNT] >>
       ‘(count (LENGTH ds)) = {n | n < LENGTH ds}’ by rw[count_def] >>
         metis_tac[]) >>
   rw[Abbr‘eqs’,EXTENSION,IMAGE_DEF])
>- (fs[sim_const_def] >> rw[SUBSET_DEF] >> metis_tac[])
>- (rw[L_form_def,form_predicates,form_functions_def] >>
    fs[MEM_MAP] >> rw[] >> fs[term_functions_def] >> rw[] >>
    fs[L_theory_def,L_form_def] >> first_x_assum drule >> rw[] >>
    first_x_assum irule >> qexists_tac ‘{(a,0)}’ >> rw[MAP_MAP_o,MEM_MAP] >>
    rw[PULL_EXISTS])
>- (rw[L_form_def,form_predicates,form_functions_def] >>
    fs[MEM_MAP] >> rw[] >> fs[term_functions_def] >> rw[] (* 3 *) >>
    fs[sim_const_def,L_with_eq_def])
>- (rw[L_form_def,form_predicates,form_functions_def] >>
    fs[MEM_MAP,MAP_MAP_o] >> rw[] >> fs[sim_const_def] >> rw[] >>
    fs[MEM_EL]) >>
‘M.Pred r (MAP (termval M v) (MAP (λa. Fn a []) ds)) /\
 (MAP (termval M v) (MAP (λa. Fn a []) ds) =
  MAP (termval M v) (MAP (λa. Fn a []) cs))’
  suffices_by metis_tac[] >>
strip_tac (* 2 *)
>- (‘holds M v (Pred r (MAP (λa. Fn a []) ds))’ by metis_tac[] >>
    fs[holds_def]) >>
rw[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP] >>
‘holds M v (Pred 0 [Fn (EL x cs) []; Fn (EL x ds) []])’
  by metis_tac[] >>
fs[holds_def,L_with_eq_def] >> metis_tac[]
QED
          
Theorem lemma_2_1_7:
  maxi L TH /\ fin_satisfiable L TH (:α) /\ wit_prop L TH (:α) ==>
  ?M:(num -> bool) model f. struc L M /\ SURJ f {c | L.Fun_sym c 0} M.Dom
Proof        
 
        
  

val _ = export_theory();
