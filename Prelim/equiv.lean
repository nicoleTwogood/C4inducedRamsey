
import Test.List

import Mathlib.Tactic

assert_not_exists complete SimpleGraph

variable {D C : Type} (x : D) (f : D ≃ C)

section equiv_examples

def id_equiv  : D ≃ D := by refine ⟨?_,?_,?_,?_⟩;(all_goals intro x);(any_goals exact x);all_goals simp_all only

@[simp]lemma id_equiv_apply : id_equiv x = x := by unfold id_equiv;simp_all only [Equiv.coe_fn_mk]

end equiv_examples
section lemmas

lemma equivIsBijective : Function.Bijective f := by
  constructor;all_goals intro x
  intro _ _;have _ : f.symm (f x) = x := by simp_all only [EmbeddingLike.apply_eq_iff_eq, Equiv.symm_apply_apply];;simp_all only [Equiv.symm_apply_apply]
  use f.symm x;simp_all only [Equiv.apply_symm_apply]

end lemmas


@[simp]lemma mem_listFun_equiv (x : C) (l : List D) : x∈(f.toFun.lf l)↔(f.symm x)∈l := by
    have nonempty : Nonempty D := Nonempty.intro (f.symm x)
    have stupid : Function.invFun f.toFun x = f.symm x := by
      apply (equivIsBijective f).injective;simp_all only [Equiv.apply_symm_apply]
      change (f.toFun (Function.invFun (f.toFun) x))=x;exact Function.invFun_eq ⟨(f.symm x),by simp_all only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]⟩
    rw [← stupid];exact mem_listFun_biject f l x (equivIsBijective f)

section finEquivs

def Equiv.toNatEquiv {n : ℕ} (f : (Fin n)≃(Fin n)) : ℕ≃ℕ where
  toFun (x : ℕ) := if h : x<n then (f ⟨x,h⟩) else x
  invFun (x : ℕ) := if h : x<n then (f.symm ⟨x,h⟩) else x
  left_inv := by {
    intro x;simp_all only;by_cases x<n
    simp_all only [dite_true, Fin.is_lt, Fin.eta, symm_apply_apply, dite_false, dite_eq_ite, ite_self]
    simp_all only [dite_false]
  }
  right_inv := by {
    intro x;simp_all only;by_cases x<n
    simp_all only [dite_true, Fin.is_lt, Fin.eta, apply_symm_apply, dite_false, dite_eq_ite, ite_self]
    simp_all only [dite_false]
  }

end finEquivs
