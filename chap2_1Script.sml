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
                (!ϕ. L_form L ϕ /\ sen ϕ ==> (ϕ IN TH \/ (Not ϕ) IN TH))
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

           

        
  

val _ = export_theory();
