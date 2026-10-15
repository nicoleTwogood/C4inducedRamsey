

import Test.equiv

assert_not_exists complete SimpleGraph

section Invertable/-working on this little improvement-/

variable {D C : Type} (f : D → C)

/--f.Invertable can be thought of as saying "f has a two-sided inverse", constructively. f.Inverse is the inverse function. -/
class Function.Invertable where
  inverse : C → D
  leftInv : f.LeftInverse inverse
  rightInv : f.RightInverse inverse

def Function.Inverse [i : f.Invertable] : C → D := i.inverse

lemma Function.Inverse_LeftInverse [i : f.Invertable] : f.LeftInverse f.Inverse := i.leftInv
lemma Function.Inverse_RightInverse [i : f.Invertable] : f.RightInverse f.Inverse := i.rightInv
instance Function.Inverse_Invertable {f : D → C} [i : f.Invertable] : Invertable f.Inverse where
  inverse := f
  leftInv := f.Inverse_RightInverse
  rightInv := f.Inverse_LeftInverse
lemma Function.Invertable_hasLeftInverse [i : f.Invertable] : f.HasLeftInverse := by use f.Inverse;exact f.Inverse_RightInverse
lemma Function.Invertable_hasRightInverse [i : f.Invertable] : f.HasRightInverse := by use f.Inverse;exact f.Inverse_LeftInverse

instance Invertable_givesBijective [i : f.Invertable] : f.Bijective := by {
  refine ⟨?_,?_⟩
  apply Function.HasLeftInverse.injective;exact f.Invertable_hasLeftInverse
  apply Function.HasRightInverse.surjective;exact f.Invertable_hasRightInverse
}

section Function.Inverse_unique

lemma leftInv_impEq_inverse {g : C → D} (inv : f.LeftInverse g) [i : f.Invertable] : g = f.Inverse := by
  ext x;have t := Function.HasLeftInverse.injective f.Invertable_hasLeftInverse;apply t;rw [inv];rw [f.Inverse_LeftInverse]
lemma rightInv_impEq_inverse {g : C → D} (inv : f.RightInverse g) [i : f.Invertable] : g = f.Inverse := by
  ext x;have t := Function.HasRightInverse.surjective f.Invertable_hasRightInverse;specialize t x;obtain ⟨y,yₕ⟩ := t;rw [← yₕ];rw [inv];rw [f.Inverse_RightInverse]

instance Function.Invertable_Subsingleton : Subsingleton f.Invertable := by {
  refine ⟨?_⟩;intro ⟨g,gₗ,gᵣ⟩ ⟨h,hₗ,hᵣ⟩
  have e : g = h := by ext x;have t : f.HasLeftInverse := by use g;exact gᵣ;;replace t : f.Injective := t.injective;apply t;rw [gₗ,hₗ]
  subst e;simp_all only
}

end Function.Inverse_unique

end Invertable
section Inverse

def Inverse {domain codomain : Type} (f : domain→codomain) (g : codomain → domain) : Prop := Function.LeftInverse f g ∧ Function.RightInverse f g

@[symm]lemma Inverse_symm {domain codomain : Type} (f : domain→codomain) (g : codomain → domain) : Inverse f g ↔ Inverse g f := by
  constructor;all_goals intro h;exact ⟨h.right,h.left⟩
@[symm]lemma Inverse_symm' {domain codomain : Type} (f : domain→codomain) (g : codomain → domain) (h : Inverse f g) : Inverse g f := by rw [Inverse_symm];exact h


def Inverse_givesBijective {domain codomain : Type} {f : domain→codomain} {g : codomain → domain} (inv : Inverse f g) : Function.Bijective f := by {
  refine Function.bijective_iff_has_inverse.mpr ?_
  use g
  constructor
  exact inv.right
  exact inv.left
}
def Inverse_givesBijective' {domain codomain : Type} {f : domain→codomain} {g : codomain → domain} (inv : Inverse f g) : Function.Bijective g := by {
  symm at inv
  exact Inverse_givesBijective inv
}

lemma Inverse_unique {domain codomain : Type} (f : domain→codomain) (g g' : codomain → domain) (inv : Inverse f g) : Inverse f g' ↔ g=g' := by {
  constructor
  {
    intro inv'
    ext x
    have bij := Inverse_givesBijective inv
    apply bij.injective
    rw [inv.left,inv'.left]
  }
  {
    intro h
    subst h
    exact inv
  }
}

lemma Inverse_circ {type1 type2 type3: Type} {f : type1→type2} {g : type2→type3} {fi : type2→type1} {gi : type3→type2} (fih : Inverse f fi) (gih : Inverse g gi)
  : Inverse (g∘f) (fi ∘ gi) := by {
    constructor
    {
      intro x
      simp_all only [Function.comp_apply]
      rw [fih.left (gi x),gih.left x]
    }
    {
      intro x
      simp_all only [Function.comp_apply]
      rw [gih.right (f x),fih.right x]
    }
  }

lemma Inverse_id {D : Type} : Inverse (id (α := D) ) id := by constructor;all_goals intro x;simp_all only [id_eq]

end Inverse
section Equiv


lemma equiv_symm_inverse {d c : Type} (e : d ≃ c) : Inverse e e.symm := by refine ⟨?_,?_⟩;repeat intro x;simp_all only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]


lemma equiv_bijective {d c : Type} (e : d ≃ c) : Function.Bijective e :=  Inverse_givesBijective (equiv_symm_inverse e)


end Equiv
section other_lemmas

lemma inputEq {D C : Type} {f : D→C} {x y : D} (eq : x=y) : f x = f y := by rw [eq]

lemma specializeFunEq {D C : Type} {f g : D→C} (h : f=g) (x : D) : f x = g x := by subst h;rfl



end other_lemmas

section general_use_functions

def transposition {D : Type} (x y : D) [DecidableEq D] : D → D := (λ d ↦ if d=x then y else (if d=y then x else d))

@[simp]lemma transposition_apply_1 {D : Type} (x y : D) [DecidableEq D] : transposition x y x = y := by simp_all only [transposition, ite_true]
@[simp]lemma transposition_apply_2 {D : Type} (x y : D) [DecidableEq D] : transposition x y y = x := by simp_all only [transposition, ite_true, ite_self]
@[simp]lemma transposition_apply_o {D : Type} {x y o : D} [DecidableEq D] (o_is_other : ¬o = x) (o_is_other' : ¬o = y) : transposition x y o = o := by
  simp_all only [transposition, ite_false]
@[simp]lemma transposition_apply_o' {D : Type} {x y o : D} [DecidableEq D] (o_is_other : ¬x = o) (o_is_other' : ¬o = y) : transposition x y o = o := by
  have t : ¬o = x := by {contrapose o_is_other;simp_all only [not_not]};exact transposition_apply_o t o_is_other'
@[simp]lemma transposition_apply_o'' {D : Type} {x y o : D} [DecidableEq D] (o_is_other : ¬o = x) (o_is_other' : ¬y = o) : transposition x y o = o := by
  have t : ¬o = y := by {contrapose o_is_other';simp_all only [not_not]};exact transposition_apply_o o_is_other t
@[simp]lemma transposition_apply_o''' {D : Type} {x y o : D} [DecidableEq D] (o_is_other : ¬x = o) (o_is_other' : ¬y = o) : transposition x y o = o := by
  have t : ¬o = y := by {contrapose o_is_other';simp_all only [not_not]};exact transposition_apply_o' o_is_other t

@[simp]lemma transposition_id {D : Type} (x : D) [DecidableEq D] : (transposition x x) = id := by {
  ext y;by_cases x=y
  simp_all only [transposition_apply_1, id_eq]
  simp_all only [not_false_eq_true, transposition_apply_o''', id_eq]
}
lemma transposition_comm {D : Type} (x y : D) [DecidableEq D] : (transposition x y) = (transposition y x) := by {
  ext z;by_cases z=x;simp_all only [transposition_apply_1, transposition_apply_2]
  by_cases z=y;simp_all only [transposition_apply_2, transposition_apply_1]
  simp_all only [not_false_eq_true, and_self, transposition_apply_o]
}
lemma transposition_inverse {D : Type} (x y : D) [DecidableEq D] : Inverse (transposition x y) (transposition x y) := by {
  refine ⟨?_,?_⟩;all_goals {
    intro a
    by_cases xia : x=a;subst xia;simp_all only [transposition_apply_1, transposition_apply_2]
    by_cases yia : y=a;subst yia;simp_all only [transposition_apply_2, transposition_apply_1]
    simp_all only [not_false_eq_true, transposition_apply_o''']
  }
}
lemma transposition_inverse' {D : Type} (x y : D) [DecidableEq D] : Inverse (transposition x y) (transposition y x) := by
  rw [transposition_comm];apply transposition_inverse
@[simp]lemma transposition_selfInverse_a {n : ℕ} (x y k : Fin n) :  (transposition x y) ((transposition x y) k)=k := by apply (transposition_inverse x y).left
@[simp]lemma transposition_selfInverse_a' {n : ℕ} (x y k : Fin n) :  (transposition x y) ((transposition x y) k)=k := by rw [transposition_comm];apply transposition_selfInverse_a
@[simp]lemma transposition_selfInverse {n : ℕ} (x y : Fin n) : (transposition x y) ∘ (transposition x y) = id := by
  ext x;simp_all only [Function.comp_apply, transposition_selfInverse_a, id_eq]
@[simp]lemma transposition_selfInverse' {n : ℕ} (x y : Fin n) : (transposition x y) ∘ (transposition y x) = id := by rw [transposition_comm];apply transposition_selfInverse

instance transposition_bijective {D : Type} (x y : D) [DecidableEq D] : (transposition x y).Bijective := by
  apply Inverse_givesBijective;exact transposition_inverse x y

@[simp]lemma transposition_castSucc {n : ℕ} (x y z: Fin n) : (transposition x.castSucc y.castSucc z.castSucc)=(transposition x y z).castSucc := by {
  by_cases h : z=x ∨ z=y
  cases h with
  | inl h => simp_all only [transposition_apply_1]
  | inr h => simp_all only [transposition_apply_2]
  simp_all only [not_or, Fin.castSucc_inj, not_false_eq_true, transposition_apply_o]
}

end general_use_functions
section embeddings





def composeEmbed {D C B : Type} (gₑ : C ↪ B) (fₑ : D ↪ C)  : D ↪ B :=  by {
  refine ⟨gₑ ∘ fₑ,?_⟩
  intro x y h;apply fₑ.injective;apply gₑ.injective;exact h
}

infixl:25 " ∘e " => composeEmbed

end embeddings
