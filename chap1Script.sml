open HolKernel Parse boolLib bossLib;
open nlistTheory listTheory;
open pred_setTheory;
open folLangTheory;
     

val _ = new_theory "chap1";
(*
val _ = Hol_datatype`
  lang = <| func_sym: 'a -> num -> bool;
             rel_sym: 'a -> num -> bool;
             const_sym: 'a -> bool|>`;
             
val _ = Hol_datatype`
  model = <| dom: 'b -> bool;
             func: 'a -> num -> 'b list -> 'b;
             rel: 'a -> num -> 'b list-> bool;
             const: 'a -> 'b|>`;
             

Definition struc:
  struc L (M :(α, β) model) <=> (M.dom <> {}) /\
  (!f nf. L.func_sym f nf ==> !as. (M.func f nf as) IN M.dom) /\
  (!r nr. L.rel_sym r nr ==>
          !as:'b list. (M.rel r nr as /\ LENGTH as = nr) ==>
               (!a. MEM a as ==> a IN M.dom)) /\
  (!c. L.const_sym c ==> (M.const c) IN M.dom)
End

Definition embed:
  embed L eta M N <=>
  (!f nf. L.func_sym f nf ==>
          !as. (LENGTH as = nf /\ 
               (!a. MEM a as ==> a IN M.dom)) ==>
               M.func f nf as = N.func f nf (MAP eta as)) /\
  (!r nr. L.rel_sym r nr ==>
          !as. (LENGTH as = nr /\
               (!a. MEM a as ==> a IN M.dom)) ==>
               M.rel r nr as = N.rel r nr (MAP eta as)) /\
  (!c. L.const_sym c ==> M.const c = N.const (eta c))
End

Definition substruc:
  substruc L M N <=> struc L M /\ struc L N /\  M.dom ⊆ N.dom /\
                     embed L (\a. a) M N
End
*)

Datatype:
  lang = <| Fun_sym: num -> num -> bool;
            Pred_sym: num -> num -> bool;
            |>
End            
 
val _ = Datatype‘
  model = <| Dom : α set ;
             Fun : num -> α list -> α ;
             Pred : num -> α list -> bool |>
’;       

Definition struc_def:
  struc L (M :α model) <=> (M.Dom <> {}) /\
  (!f nf. L.Fun_sym f nf ==>
          !as. LENGTH as = nf ==> (M.Fun f as) IN M.Dom) /\
  (!r nr. L.Pred_sym r nr ==>
          !as. (LENGTH as = nr /\ M.Pred r as) ==>
               !a. MEM a as ==> a IN M.Dom)
End      

Definition embed_def:
  embed L eta M N <=>
  (!f nf. L.Fun_sym f nf ==>
          !as. (LENGTH as = nf /\ 
               (!a. MEM a as ==> a IN M.Dom)) ==>
               M.Fun f as = N.Fun f (MAP eta as)) /\
  (!r nr. L.Pred_sym r nr ==>
          !as. (LENGTH as = nr /\
               (!a. MEM a as ==> a IN M.Dom)) ==>
               M.Pred r as = N.Pred r (MAP eta as))
End

Definition substruc_def:
  substruc L M N <=> struc L M /\ struc L N /\ M.Dom ⊆ N.Dom /\
                     embed L (\a. a) M N
End        
                        
Definition qfree_def:
  (qfree False ⇔ T) ∧
  (qfree (Pred _ _) ⇔ T) ∧
  (qfree (IMP f1 f2) ⇔ qfree f1 ∧ qfree f2) ∧
  (qfree (FALL _ _) ⇔ F)
End

Definition satis_def:
  satis M v ϕ <=> valuation M v /\ holds M v ϕ
End

Definition L_term_def:
  L_term L t <=> (!f nf. (f, nf) IN (term_functions t) ==> L.Fun_sym f nf)
End        

Definition L_form_def:
  L_form L ϕ <=> (!f nf. (f, nf) IN (form_functions ϕ) ==> L.Fun_sym f nf) /\                    (!r nr. (r, nr) IN (form_predicates ϕ) ==> L.Pred_sym r nr)
End

Theorem L_term_MEM:
  L_term L (Fn n l) /\ MEM x l ==> L_term L x
Proof
  rw[L_term_def] >> first_x_assum irule >>
  ‘∃s. MEM s (MAP (λa. term_functions a) l) ∧ (f,nf') ∈ s’
    suffices_by metis_tac[] >>
  qexists_tac ‘term_functions x’ >> rw[MEM_MAP] >>
  qexists_tac ‘x’ >> rw[]
QED

Theorem L_term_termval_in_Dom:
  !t. L_term L t /\ struc L M /\ valuation M v ==> (termval M v t) IN M.Dom
Proof
completeInduct_on ‘term_size t’ >> Cases_on ‘t’ >> rw[termval_def] (* 2 *)
>- fs[valuation_def] >>
fs[struc_def] >> last_x_assum irule >> fs[L_term_def]
QED       
                  
Theorem prop_1_1_8_i:
  !t. substruc L M N /\ L_term L t /\ valuation M v ==>
  termval M v t = termval N v t
Proof
completeInduct_on ‘term_size t’ >> rw[] >> Cases_on ‘t’ >> rw[termval_def] >>
fs[substruc_def,embed_def] >>
‘(MAP (λa. termval M v a) l) = (MAP (λa. termval N v a) l)’
  by
   (irule MAP_CONG >> rw[] >> first_x_assum irule >> rw[] (* 2 *)
    >- (drule term_size_lemma >> strip_tac >>
    ‘term_size x < 1 + (n + term1_size l)’ by metis_tac[] >>
    fs[]) >>
    metis_tac[L_term_MEM]) >>
rw[] >> first_x_assum irule >> rw[] (* 2 *)
>- (fs[MEM_MAP] >> fs[MAP_EQ_f] >> first_x_assum drule >> rw[] >>
   ‘termval M v a' ∈ M.Dom’ suffices_by metis_tac[] >>
   irule L_term_termval_in_Dom >> rw[] >>
   qexists_tac ‘L’ >> rw[] >>
   metis_tac[L_term_MEM]) >>
fs[L_term_def,term_functions_def]
QED

Theorem substruc_valuation:
  substruc L M N /\ valuation M v ==> valuation N v
Proof
rw[substruc_def,valuation_def,SUBSET_DEF]
QED    

Theorem L_term_Pred_MEM:
  L_form L (Pred n l) /\ MEM x l ==> L_term L x
Proof
  rw[L_term_def,L_form_def,PULL_EXISTS] >> first_x_assum irule >>
  qexists_tac ‘term_functions x’ >> rw[MEM_MAP] >>
  qexists_tac ‘x’ >> rw[]
QED

Theorem L_form_IMP:
  L_form L (IMP ϕ1 ϕ2) ==> L_form L ϕ1 /\ L_form L ϕ2
Proof
rw[L_form_def]
QED
       
Theorem prop_1_1_8_ii:
  !ϕ v. substruc L M N /\ L_form L ϕ /\ qfree ϕ /\ valuation M v ==>
        satis M v ϕ = satis N v ϕ
Proof
Induct_on ‘ϕ’ >> rw[satis_def,qfree_def,holds_def] (* 2 *)
>- (‘valuation N v’ by metis_tac[substruc_valuation] >> rw[] >>
   fs[substruc_def,embed_def] >>
   ‘MAP (termval M v) l = MAP (termval N v) l’
     by
      (irule MAP_CONG >> rw[] >>
      ‘L_term L x’ by metis_tac[L_term_Pred_MEM] >> irule prop_1_1_8_i >>
      rw[substruc_def,embed_def] >> qexists_tac ‘L’ >> rw[]) >>
   rw[] >> first_x_assum irule >> rw[] (* 2 *)
   >- (fs[MEM_MAP,MAP_EQ_f] >>
      ‘termval M v y ∈ M.Dom’ suffices_by metis_tac[] >>
      irule L_term_termval_in_Dom >> rw[] >> qexists_tac ‘L’ >> rw[] >>
      metis_tac[L_term_Pred_MEM]) >>
   fs[L_form_def]) >>
‘valuation N v’ by metis_tac[substruc_valuation] >> rw[] >>
drule L_form_IMP >> strip_tac >> metis_tac[satis_def]
QED

Definition sen_def:
  sen ϕ <=> FV ϕ = {}
End          

Definition elem_equiv_def:
elem_equiv L M N <=> struc L M /\ struc L N /\
                     (!ϕ v. L_form L ϕ /\ sen ϕ /\ valuation M v ==>
                            satis M v ϕ = satis N v ϕ)       
End  
           

val _ = export_theory();
