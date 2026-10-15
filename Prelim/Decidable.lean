
import Mathlib.Tactic

/-!
Some extra decidable instances not available elsewhere
-/

set_option linter.style.longLine.maxLineLength 150

assert_not_exists complete SimpleGraph

variable {T : Type} {ε γ : T → Prop} {φ ψ τ : Prop}

section Cexists_Decidable

inductive Cexists_Decidable (φ : T → Prop) where
  | CE_isFalse (h : ∀x : T,¬(φ x))
  | CE_isTrue (x : T) (h : φ x)


def CED_to_Decidable : Cexists_Decidable ε→Decidable (∃x : T,ε x)
  | .CE_isFalse h => isFalse (by simp_all only [exists_false, not_false_eq_true])
  | .CE_isTrue x h => isTrue ⟨x,h⟩

end Cexists_Decidable
section Decidable_Reductions
section Basic

def Dnot :  Decidable φ → Decidable ¬φ
  | isFalse h => isTrue h
  | isTrue _ => isFalse (by simp_all only [not_true_eq_false, not_false_eq_true])

def decidable_and : Decidable φ→Decidable ψ→Decidable (φ∧ψ)
  | isFalse _, _ => isFalse (by simp_all only [false_and, not_false_eq_true])
  | isTrue _, isFalse _ => isFalse (by simp_all only [and_false, not_false_eq_true])
  | isTrue _, isTrue _ => isTrue (by simp_all only [and_self])

def decidable_or : (Decidable φ)→(Decidable ψ)→(Decidable (φ∨ψ))
  | isFalse _,isFalse _ => isFalse (by simp_all only [or_self, not_false_eq_true])
  | isFalse _,isTrue _ => isTrue (by simp_all only [or_true])
  | isTrue _, _ => isTrue (by simp_all only [true_or])

def decidable_not : Decidable ¬φ→Decidable φ
  | isFalse _ => isTrue (by simp_all only [not_not])
  | isTrue _ => isFalse (by simp_all only [not_false_eq_true])

def decidable_imp : (Decidable φ)→(Decidable ψ)→(Decidable (φ→ψ)) := by intro _ _;exact instDecidableForall

def decidable_iff : (Decidable φ)→(Decidable ψ)→(Decidable (φ↔ψ)) := by intro _ _;infer_instance

def decidable_ite : (δ : Decidable φ)→(Decidable ψ)→(Decidable τ)→(Decidable (if φ then ψ else τ))
  | isTrue _,isTrue _,_ => isTrue (by simp_all only [ite_true])
  | isTrue _,isFalse _,_ => isFalse (by simp_all only [ite_true, not_false_eq_true])
  | isFalse _,_,isTrue _ => isTrue (by simp_all only [ite_false])
  | isFalse _,_,isFalse _ => isFalse (by simp_all only [ite_false, not_false_eq_true])

def decidable_dite : (δ : Decidable φ)→(Decidable ψ)→(Decidable τ)→(Decidable (if φ then φ → ψ else ¬φ → τ))
  | isTrue _,isTrue _,_ => isTrue (by simp_all only [imp_self, not_false_eq_true, IsEmpty.forall_iff, ite_true])
  | isTrue _,isFalse _,_ => isFalse (by simp_all only [imp_false, not_true_eq_false, not_false_eq_true, IsEmpty.forall_iff, ite_self])
  | isFalse _,_,isTrue _ => isTrue (by simp_all only [forall_const, not_false_eq_true, ite_false])
  | isFalse _,_,isFalse _ => isFalse (by simp_all only [forall_const, not_false_eq_true, ite_false])

end Basic
section List

def Cexists_Decidable_list : (l : List T)→((x : T)→Decidable (ε x))→Cexists_Decidable (fun x => x∈l ∧ (ε x))
  | [] => fun _ => .CE_isFalse (by simp_all only [List.not_mem_nil, false_and, not_false_eq_true, implies_true])
  | (head :: tail) => by intro p;cases (Cexists_Decidable_list tail p) with
    | CE_isFalse h => cases p head with
      | isFalse nh => exact .CE_isFalse (by simp_all only [not_and, List.mem_cons, forall_eq_or_imp, not_false_eq_true, implies_true, and_self])
      | isTrue h => exact .CE_isTrue head (by simp_all only [not_and, List.mem_cons, true_or, and_self])
    | CE_isTrue x h => exact .CE_isTrue x ⟨(by simp_all only [List.mem_cons, or_true]),h.right⟩

def decidable_list_exist : (l : List T)→((x : T)→Decidable (ε x))→Decidable (∃x∈l,ε x) := fun l p => (CED_to_Decidable (Cexists_Decidable_list l p))

def decidable_list_forall : (l : List T)→((x : T)→Decidable (ε x))→Decidable (∀x∈l,ε x)
  | [] => fun _ => isTrue (fun x h => by exfalso;exact (List.mem_nil_iff x).mp h)
  | (head :: tail) => fun p => by cases (decidable_list_forall tail p) with
    | isFalse _ => exact isFalse (by simp_all only [not_forall, List.mem_cons, forall_eq_or_imp, not_and, implies_true])
    | isTrue _ => cases p head with
      | isFalse _ => exact isFalse (by simp_all only [List.mem_cons, forall_eq_or_imp, implies_true, and_true, not_false_eq_true])
      | isTrue _ => exact isTrue (by simp_all only [List.mem_cons, forall_eq_or_imp, implies_true, and_self])

end List
section Fintype

lemma univ_carries_forall [l : Fintype T] : (∀x : T,ε x) ↔ (∀x ∈ Finset.univ,ε x) := ⟨fun h x _ ↦ h x,fun h x ↦ h x (Finset.mem_univ x)⟩

def decidable_multiset_forall : (l : Multiset T)→((x : T)→Decidable (ε x))→Decidable (∀x∈l,ε x) := by {
  intro l dec;
  refine Quotient.recOn l ?_ ?_
  {
    clear l;intro l
    unfold Membership.mem Multiset.instMembership Multiset.Mem;simp_all only [Multiset.quot_mk_to_coe, Multiset.lift_coe]
    refine decidable_list_forall ?_ dec
  }
  clear l;intro l k lik;simp_all only [Multiset.quot_mk_to_coe, id_eq];subsingleton
}

def decidable_finset_forall : (l : Finset T)→((x : T)→Decidable (ε x))→Decidable (∀x∈l,ε x) := by
  intro ⟨l,nd⟩ dec;simp_all only [Finset.mem_mk];infer_instance

def forallFintype_dec [F : Fintype T] : ((x : T)→Decidable (ε x))→Decidable (∀x : T,ε x) := by exact
  fun a ↦ Fintype.decidableForallFintype

end Fintype
section Set

instance decidableEq_FD_set (S₁ S₂ : Set T) [D₁ : DecidablePred S₁] [D₂ : DecidablePred S₂] [F : Fintype T] : Decidable (S₁ = S₂) := by {
  have t : Decidable (∀ (x : T), x ∈ S₁ ↔ x ∈ S₂) := forallFintype_dec (fun x ↦ decidable_iff (by revert x;exact D₁) (by revert x; exact D₂))
  exact decidable_of_decidable_of_iff Set.ext_iff.symm
}

end Set
end Decidable_Reductions
section DecidableRel

def decidableEq_from_DecidableRel {r : Setoid T} (decSet : DecidableRel r) : DecidableEq (Quotient r) := by
  intro x y;refine Quotient.recOnSubsingleton₂ x y ?_;intro a b;cases (decSet a b) with
  | isTrue eq => exact isTrue (Quotient.sound eq)
  | isFalse neq => exact isFalse (by contrapose neq;exact Quotient.eq''.mp neq)

end DecidableRel
section decidable_eq

instance subtype_DecidableEq (ε : T → Prop) [d : DecidableEq T] : DecidableEq {x : T // ε x} := by {
  intro ⟨x,xh⟩ ⟨y,yh⟩;rw [← Subtype.val_inj];specialize d x y;simp_all only;exact d
}

end decidable_eq
section constructive_or

universe α β

inductive cor (T1 : Sort α) (T2 : Sort β) where
  | left (a : T1)
  | right (a : T2)

infixl:25 " ∨c " => cor

end constructive_or
section constructive_cases

syntax "const_cases" term : tactic

def listExists_constructible {l : List T} (h : ∃ x ∈ l, ε x) [DecidablePred ε] : {x : T // x∈l ∧ ε x} := by {
  induction l with
  | nil => simp_all only [List.not_mem_nil, false_and, exists_false]
  | cons head tail ih => {
    simp_all only [List.mem_cons, exists_eq_or_imp]
    by_cases εh : ε head
    · use head;simp_all only [true_or, and_self]
    simp_all only [false_or];have ⟨x,ih⟩ := ih h;use x;simp_all only [or_true, and_self]
  }
}

macro_rules
  | `(tactic|const_cases $t) =>
    `(tactic|have _ := listExists_constructible $t)

def listExists_constructible' {l : List T} (h : ∃ x ∈ l, ε x) [d : DecidablePred (fun (x : {x : T // x∈l}) ↦ ε x.val)] : {x : T // x∈l ∧ ε x} := by {
  revert d
  induction l with
  | nil => simp_all only [List.not_mem_nil, false_and, exists_false]
  | cons head tail ih => {
    intro d
    simp_all only [List.mem_cons, exists_eq_or_imp]
    have t : DecidablePred fun (x : {x // x∈tail}) ↦ ε ↑x := by {
      intro ⟨x,xh⟩;have t : x ∈ head :: tail := by simp_all only [List.mem_cons, or_true]
      specialize d ⟨x,t⟩
      cases d with
      | isFalse h => refine isFalse ?_;simp_all only [not_false_eq_true]
      | isTrue h => refine isTrue ?_;simp_all only
    }
    specialize d ⟨head,by simp_all only [List.mem_cons, true_or]⟩
    by_cases εh : ε head
    · use head;simp_all only [true_or, and_self]
    simp_all only [false_or];have ⟨x,ih⟩ := ih h;use x;simp_all only [or_true, and_self]
  }
}

macro_rules
  | `(tactic|const_cases $t) =>
    `(tactic|have _ := listExists_constructible' $t)

universe α

def cases_or_constructible1 {T : Sort α} (p : φ → T) (s : ψ → T) [Decidable φ] : (φ ∨ ψ)→T := by {
  intro x;by_cases h : φ
  · exact p h
  simp_all only [false_or];exact s x
}

macro_rules
  | `(tactic|const_cases $t) =>
    `(tactic|revert $t;refine cases_or_constructible1 ?_ ?_;all_goals intro _)

def cases_or_constructible2 {T : Sort α} (p : φ → T) (s : ψ → T) [Decidable ψ] : (φ ∨ ψ)→T := by {
  intro x;by_cases h : ψ
  · exact s h
  simp_all only [or_false];exact p x
}

macro_rules
  | `(tactic|const_cases $t) =>
    `(tactic|revert $t;refine cases_or_constructible2 ?_ ?_;all_goals intro _)

end constructive_cases
section decidable_set

instance mem_dec (S : Set T) [d : DecidablePred S] (x : T) : Decidable (x∈S)  := by {
  specialize d x;cases d with
  | isFalse d => exact isFalse d
  | isTrue d => exact isTrue d
}

end decidable_set
