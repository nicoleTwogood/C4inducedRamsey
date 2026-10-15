import Test.ramsey
import Test.graph6
import Test.temp


abbrev C₄ := (SimpleGraph.cycleGraph 4)

section using_the_conditions

lemma C₄_min_degree : C₄.minDegree=2 := by rfl
instance : Supersingleton ↑C₄.edgeSet := by {
  have ⟨⟨edge1,edge2⟩,h⟩ : {e : (C₄.edgeSet × C₄.edgeSet) // e.1 ≠ e.2} := by {
    refine ⟨⟨⟨s(0,1),by decide⟩,⟨s(1,2),by decide⟩⟩,?_⟩
    simp_all only [ne_eq, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, zero_ne_one, false_and, Prod.swap_prod_mk, and_true, false_or]
    decide
    }
  refine ⟨?_,?_⟩
  exact ⟨edge1⟩
  intro x;by_cases h : x=edge1
  subst h;use edge2
  use edge1
}
instance : Supersingleton (Fin 2) := by {
  refine ⟨?_,?_⟩
  exact ⟨0⟩
  intro x;finCases x
  use Fin.last 1;decide +revert
  use 0;decide
}

def ramsey_conditions_C₄ {n : ℕ} (h : n>0 := by decide): DecidablePred fun (H : (Quotient (DGraph.hasIso (V:=Fin n)))) ↦ ¬DGraph_isoClass_minimal_ramsey_conditions H C₄ := by {
  intro H
  refine @instDecidableNot _ ?_
  revert H;apply Quotient.rec
  intro _ _ _;subsingleton
  intro G
  unfold DGraph_isoClass_minimal_ramsey_conditions
  simp_all only [gt_iff_lt, Quotient.lift_mk]
  exact if mdlt2 : G.minDegree≤2
    then isTrue (by {
      apply SimpleGraph.lowMinDegree_imp_minimal_ramsey_conditions
      rw [C₄_min_degree]
      rw [C₄_min_degree];exact mdlt2
    })
    else if isolated : (∃ v : (Fin n),∀copy : C₄ ↪g G,v ∉ (Set.range copy))
    then isTrue (Or.inl isolated)
    else if semirelevantEdge : (∃e : G.edgeSet,Subsingleton {copy : C₄ ↪g G // e.val ∈ copy.toFun})
    then isTrue (Or.inr (Or.inl semirelevantEdge))
    else if connectedEdges : (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : C₄ ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun)))
    then isTrue (Or.inr (Or.inr (Or.inl connectedEdges)))
    else isFalse (by {
      unfold minimal_ramsey_conditions
      simp_all only [not_le, Set.mem_range, not_exists, not_forall, Decidable.not_not,
        Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Subtype.exists, exists_prop,
        not_and, SuperSingleton_iff_notsubsingleton, ne_eq, exists_and_right, Subtype.mk.injEq,
        Classical.not_imp, and_imp, not_or, implies_true, not_false_eq_true, not_nonempty_iff,
        not_isEmpty_of_nonempty, imp_false, not_isEmpty_iff, true_and]
      match n with
      | 0 => contrapose h;simp_all only [SimpleGraph.minDegree_of_isEmpty, not_lt_zero']
      | n + 1 => exact ⟨0⟩
    })
}

instance completeBipartiteGraph_dec (V U : Type) : DecidableRel (completeBipartiteGraph V U).Adj := fun v u ↦ match v,u with
  | .inl v, .inl u =>
    isFalse (by simp_all only [completeBipartiteGraph_adj, Sum.isLeft_inl, Sum.isRight_inl, Bool.false_eq_true, and_false, and_true, or_self, not_false_eq_true])
  | .inl v, .inr u =>
    isTrue (by simp_all only [completeBipartiteGraph_adj, Sum.isLeft_inl, Sum.isRight_inr, and_self, Sum.isRight_inl, Bool.false_eq_true, Sum.isLeft_inr, or_false])
  | .inr v, .inl u =>
    isTrue (by simp_all only [completeBipartiteGraph_adj, Sum.isLeft_inr, Bool.false_eq_true, Sum.isRight_inl, and_self, Sum.isRight_inr, Sum.isLeft_inl, or_true])
  | .inr v, .inr u =>
    isFalse (by simp_all only [completeBipartiteGraph_adj, Sum.isLeft_inr, Bool.false_eq_true, Sum.isRight_inr, and_true, and_false, or_self, not_false_eq_true])




lemma size6filter : (@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 6))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ)
  = ⟨⟦[
    ⟦("EFz_" : SimpleGraph (Fin 6))⟧
    ]⟧,by simp_all⟩ := by sorry
lemma size7filter : (@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 7))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ)
  = ⟨⟦[
    ⟦("F?~v_" : SimpleGraph (Fin 7))⟧
    ]⟧,by simp_all⟩ := by sorry/-decide +native-/
lemma size8filter : (@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 8))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ)
  = ⟨⟦[
    ⟦("G?B~vo" : SimpleGraph (Fin 8))⟧,
    ⟦("G?zTb_" : SimpleGraph (Fin 8))⟧,
    ⟦("G?zTf_" : SimpleGraph (Fin 8))⟧,
    ⟦("G?zVf_" : SimpleGraph (Fin 8))⟧,
    ⟦("G?zvf_" : SimpleGraph (Fin 8))⟧,
    ⟦("G?~vf_" : SimpleGraph (Fin 8))⟧,
    ]⟧,by sorry⟩ := by sorry/-decide +native-/


/-
#eval! temp_canonical ((@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 2))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ).val.map (temp_canonical))
#eval! temp_canonical ((@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 6))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ).val.map (temp_canonical))
#eval! temp_canonical ((@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 7))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ).val.map (temp_canonical))
#eval! temp_canonical ((@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 8))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ).val.map (temp_canonical))
#eval! temp_canonical ((@Finset.filter (Quotient (DGraph.hasIso (V:=Fin 9))) (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)) ramsey_conditions_C₄ Finset.univ).val.map (temp_canonical))
-/


lemma Ri_C₄_n0_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 0)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n1_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 1)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n2_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 2)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n3_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 3)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n4_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 4)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n5_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 5)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n6_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 6)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n7_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 7)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/
lemma Ri_C₄_n8_Diso_conditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 8)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by sorry/-decide +native-/

lemma Ri_C₄_n9_Diso_byConditions : ∀G : Quotient (DGraph.hasIso (V:=Fin 9)),¬(DGraph_quot_minimal_ramsey (Fin 2) G C₄) := by {

  intro G
  have t : (G ∈ ((Finset.univ : Finset (Quotient (DGraph.hasIso (V:=Fin 9)))).filter (fun H ↦ DGraph_isoClass_minimal_ramsey_conditions H C₄)))
    ∨ (G ∈ ((Finset.univ : Finset (Quotient (DGraph.hasIso (V:=Fin 9)))).filter (fun H ↦ ¬(DGraph_isoClass_minimal_ramsey_conditions H C₄)))) := by {
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and];exact Decidable.em (DGraph_isoClass_minimal_ramsey_conditions G C₄)
    }
  sorry;try/-remove to do computation-/
  cases t with
  | inl h => {
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]
    induction G using Quotient.ind;rename_i G;rw [← DGraph_isoClass.minimal_ramsey_conditions_iff] at h;apply minimal_ramsey_conditions_imp_notMinRamsey (Fin 2) at h
    rw [← DGraph_quot_minimal_ramsey_iff_minimal_ramsey];exact h
  }
  | inr h => {
    induction G using Quotient.ind;rename_i G;rw [← DGraph_quot_minimal_ramsey_iff_minimal_ramsey]
    have conc : ¬ (SimpleGraph.ramsey (Fin 2) G.toSimpleGraph C₄) := by {
      rw [DGraph_isoClass.ramsey_iff_ramsey];revert G
      have conc : ∀(G : Quotient (DGraph.hasIso (V:=Fin 9))), ∀(h : G ∈ Finset.filter (fun H ↦ ¬DGraph_isoClass_minimal_ramsey_conditions H C₄) Finset.univ), ¬DGraph_isoClass.ramsey (Fin 2) G C₄ := by {
        decide +native
      }
      intro G;specialize conc ⟦G⟧;exact conc
    }
    unfold SimpleGraph.minimal_ramsey;simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, RelHom.coe_fn_toFun, false_and, not_false_eq_true]
  }
}


lemma Ri_C₄_g8_Diso_conditions : ∀n : Fin 9,∀G : Quotient (DGraph.hasIso (V:=Fin n.val)),(DGraph_isoClass_minimal_ramsey_conditions G C₄) := by {
  intro n;repeat finCases n;;apply finZeroElim n
  exact Ri_C₄_n0_Diso_conditions
  exact Ri_C₄_n1_Diso_conditions
  exact Ri_C₄_n2_Diso_conditions
  exact Ri_C₄_n3_Diso_conditions
  exact Ri_C₄_n4_Diso_conditions
  exact Ri_C₄_n5_Diso_conditions
  exact Ri_C₄_n6_Diso_conditions
  exact Ri_C₄_n7_Diso_conditions
  exact Ri_C₄_n8_Diso_conditions
}

lemma Ri_C₄_g9_Diso_byConditions : ∀n : Fin 10, ∀G : Quotient (DGraph.hasIso (V:=Fin n.val)),¬(DGraph_quot_minimal_ramsey (Fin 2) G C₄) := by {
  intro n G;finCases n
  have t := Ri_C₄_g8_Diso_conditions n G
  induction G using Quotient.ind;rename_i G
  apply minimal_ramsey_conditions_imp_notMinRamsey;rw [DGraph_isoClass.minimal_ramsey_conditions_iff]
  exact t
  revert G;exact Ri_C₄_n9_Diso_byConditions
}

theorem Ri_C₄_g9 (n : Fin 10) : ∀ G : SimpleGraph (Fin n.val),¬(G.ramsey (Fin 2) C₄) := by {
  revert n;rw [← minimal_ramsey_sufficient]
  intro n G;have Gd : DecidableRel G.Adj := Classical.decRel G.Adj
  exact Ri_C₄_g9_Diso_byConditions n ⟦G⟧
}

end using_the_conditions

lemma Ri_C₄_n0 : ∀G : Graph (Fin 0),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 0
lemma Ri_C₄_n1 : ∀G : Graph (Fin 1),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 1
lemma Ri_C₄_n2 : ∀G : Graph (Fin 2),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 2
lemma Ri_C₄_n3 : ∀G : Graph (Fin 3),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 3
lemma Ri_C₄_n4 : ∀G : Graph (Fin 4),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 4
lemma Ri_C₄_n5 : ∀G : Graph (Fin 5),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 5
lemma Ri_C₄_n6 : ∀G : Graph (Fin 6),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 6
lemma Ri_C₄_n7 : ∀G : Graph (Fin 7),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 7
lemma Ri_C₄_n8 : ∀G : Graph (Fin 8),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 8
lemma Ri_C₄_n9 : ∀G : Graph (Fin 9),¬(G.ramsey (Fin 2) C₄) := Ri_C₄_g9 9


section conclusion

/-This is proven by some other people.-/
theorem Ri_C₄_le10 : (completeBipartiteGraph (Fin 5) (Fin 5)).ramsey (Fin 2) C₄ := by sorry/-decide +native-/

end conclusion
