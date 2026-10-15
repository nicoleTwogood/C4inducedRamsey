
import Mathlib.Tactic

/-everything in here should not be used permanently. This file should not be imported under any conditions other than testing, since all of this is nonprovable, often because it's false.-/


/--This function uses sorry. temp_canonical removes the quotient by grabbing the representative the code is using. i.e., since the quotient is the quotient of something it grabs that something that lean is using internally.

You could easily prove false with this. This is only for testing where a quotient is inconvenient.-/
def temp_canonical {T : Type} {s : Setoid T} (q : Quotient s) : T := by {
  revert q;apply Quotient.rec
  sorry/-this is in almost every case, blatantly false.-/
  intro t;exact t
}

/--Importing this file gives contradiction, never use this in a final project-/
theorem contradiction : False := by  {
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  apply h;clear h
  have ⟨s,sh⟩ : {s : Setoid (Fin 2) // ∀x y,s x y} := ⟨⟨?_,?_⟩,?_⟩
  case refine_1 => intro _ _;exact True
  case refine_2 => refine ⟨?_,?_,?_⟩;intro _;trivial;intro _ _ _;trivial;intro _ _ _ _ _;trivial
  case refine_3 => simp_all only [implies_true]
  have e : (⟦0⟧ : Quotient s)=⟦1⟧ := by simp_all only [Quotient.eq];
  have e₀ (x : Fin 2): (temp_canonical (⟦x⟧ : Quotient s))=x := by unfold temp_canonical;simp_all only [Quotient.eq];rfl
  have eq : temp_canonical (⟦0⟧ : Quotient s) = temp_canonical (⟦1⟧ : Quotient s) := congrArg temp_canonical e
  simp_all only [Quotient.eq, zero_ne_one]
}
