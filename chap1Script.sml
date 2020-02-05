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

Definition struc:
  struc L (M :α model) <=> (M.Dom <> {}) /\
  (!f nf. L.Fun_sym f nf ==>
          !as. LENGTH as = nf ==> (M.Fun f as) IN M.Dom) /\
  (!r nr. L.Pred_sym r nr ==>
          !as. (LENGTH as = nr /\ M.Pred r as) ==>
               !a. MEM a as ==> a IN M.Dom)
End      

Definition embed:
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

Definition substruc:
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

Definition L_form_def:
  L_form L ϕ <=> (!f nf. (f, nf) IN (form_functions ϕ) ==> L.Fun_sym f nf) /\                    (!r nr. (r, nr) IN (form_predicates ϕ) ==> L.Pred_sym r nr)
End
                  
Theorem prop_1_1_8_i:
  substruc L M N /\ qfree ϕ /\  ==>
  
  
           

val _ = export_theory();
