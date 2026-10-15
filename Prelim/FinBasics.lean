
import Mathlib.Tactic


/-!
Some basic extra lemmas about Fin n
-/

assert_not_exists SimpleGraph complete
set_option linter.style.longLine.maxLineLength 150

variable {n m : ℕ} {T : Type} (x y head : Fin n) (x1 y1 head1 : Fin (n + 1)) (j k l tail : List (Fin n)) (j1 k1 l1 tail1 : List (Fin (n + 1)))


section finCases


lemma finNotMaxImpln (h : ¬x1=(Fin.last n)) : x1.val<n := by contrapose h;simp_all only [not_lt];exact Fin.last_le_iff.mp h


universe α
variable {φ : Sort α}

def finCases_lemma (lt : {y : Fin n // y.castSucc=x1} → φ) (il : x1 = Fin.last n → φ) : φ := by
  by_cases h : x1.val<n;· exact lt (by use ⟨x1.val,h⟩;simp_all only [Fin.castSucc_mk, Fin.eta]);;exact il (Fin.eq_last_of_not_lt h)

@[simp] lemma finCases_lemma_last (lt : {y : Fin n // y.castSucc=Fin.last n} → φ) (il : Fin.last n = Fin.last n → φ)
  : (finCases_lemma (Fin.last n) lt il)=(il (by rfl)) := by{
  unfold finCases_lemma;simp only [Fin.val_last, lt_self_iff_false, dite_false]
}

@[simp] lemma finCases_lemma_cs (lt : {y : Fin n // y.castSucc=x.castSucc} → φ) (il : x.castSucc = Fin.last n → φ)
  : (finCases_lemma x.castSucc lt il) = (lt ⟨x,by rfl⟩) := by
  unfold finCases_lemma;simp_all only [Fin.val_castSucc, Fin.is_lt, Fin.eta, dite_true]

syntax "finCases" term : tactic
macro_rules
  | `(tactic|finCases $t) =>
    `(tactic|refine (finCases_lemma $t ?_ ?_);intro ⟨$t,s⟩;subst s;(any_goals intro h;subst h))

lemma succNotZero : ¬ x.succ = 0 := by {
  exact Fin.succ_ne_zero x
}

def finCasez_lemma (lt : {y : Fin n // y.succ=x1} → φ) (iz : x1 = 0 → φ) : φ
  := if h : x1=0 then iz h else lt ⟨x1.pred h,by symm;rw [← Fin.pred_eq_iff_eq_succ]⟩

@[simp] lemma finCasez_lemma_zero (lt : {y : Fin n // y.succ=0} → φ) (iz : 0 = 0 → φ) : finCasez_lemma 0 lt iz = (iz (by rfl)) := by
  unfold finCasez_lemma;simp_all only [dite_true]

@[simp] lemma finCasez_lemma_succ (lt : {y : Fin n // y.succ=x.succ} → φ) (iz : x.succ = 0 → φ) : finCasez_lemma x.succ lt iz = lt ⟨x,by rfl⟩ := by
  unfold finCasez_lemma;simp_all only [Fin.pred_succ];have _ := Fin.succ_ne_zero x;simp_all only [dite_false]

syntax "finCasez" term : tactic
macro_rules
  | `(tactic|finCasez $t) =>
    `(tactic|refine (finCasez_lemma $t ?_ ?_);intro ⟨$t,s⟩;subst s;(any_goals intro h;subst h))

section finCases_useful_lemmas

lemma succ_not_last : ¬x.castSucc=Fin.last n := by
  obtain ⟨x,h⟩ := x;rw [← Fin.val_inj];simp_all only [Fin.castSucc_mk, Fin.val_last];contrapose h;simp_all only [lt_self_iff_false, not_false_eq_true]

lemma succ_not_last' : ¬Fin.last n=x.castSucc := by
  obtain ⟨x,h⟩ := x;rw [← Fin.val_inj];simp_all only [Fin.castSucc_mk, Fin.val_last];contrapose h;simp_all only [lt_self_iff_false, not_false_eq_true]

end finCases_useful_lemmas
end finCases
section castToType

instance : Coe ℕ Type := ⟨fun n ↦ Fin n⟩

end castToType
