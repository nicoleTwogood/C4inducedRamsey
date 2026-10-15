
import Test.Decidable_Graph

import Mathlib/-specify files-/

section fintype_proofs

theorem enumerative_proof {T : Type} [F : Fintype T] {φ : T → Prop} (h : ∀t ∈ (Finset.univ : Finset T),φ t): ∀t : T, φ t := by {
  intro t;specialize h t;apply h;exact Finset.mem_univ t
}

end fintype_proofs
section colorings

def SimpleGraph.coloring {V : Type} (G : SimpleGraph V) (C : Type) : Type := G.edgeSet → C

def SimpleGraph.coloring.mapAlongIso {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U} {C : Type} (coloring : G.coloring C) (iso : G ≃g H) : H.coloring C := by {
  unfold SimpleGraph.coloring;intro ⟨x,xi⟩;revert x;

  intro e eiH
  have t : (e.map iso.symm) ∈ G.edgeSet := (Iso.map_mem_edgeSet_iff iso.symm).mpr eiH
  exact coloring ⟨(e.map iso.symm),t⟩
}

@[simp]lemma sym2.map_repeat {D C B : Type} (g : C → B) (f : D → C) (e : Sym2 D) : (e.map f).map g = e.map (g ∘ f) := by {
  induction e with
  | h x y => simp_all only [Sym2.map_pair_eq, Function.comp_apply]
}

@[simp]lemma SimpleGraph.coloring.mapAlongIso_id {V : Type} {G : SimpleGraph V} {C : Type} (coloring : G.coloring C) : (coloring.mapAlongIso (id_iso G)) = coloring := by {
  unfold SimpleGraph.coloring.mapAlongIso;simp_all only [id_eq];unfold SimpleGraph.coloring;unfold SimpleGraph.coloring at coloring
  ext h;apply congrArg;obtain ⟨e,ei⟩ := h
  induction e with
  | h x y => simp_all only [id_iso_symm, id_iso_apply, Sym2.map_id', id_eq]
}

@[simp]lemma SimpleGraph.coloring.mapAlongIso_repeat {V U T : Type} {G : SimpleGraph V} {H : SimpleGraph U} {I : SimpleGraph T} {C : Type} (coloring : G.coloring C) (iGH : G ≃g H) (iHI : H ≃g I) : (coloring.mapAlongIso iGH).mapAlongIso iHI = coloring.mapAlongIso (iHI ∘gi iGH) := by {
  unfold SimpleGraph.coloring.mapAlongIso;simp_all only [id_eq, composeIsos_symm, composeIsos_apply]
  unfold SimpleGraph.coloring;ext h
  apply congrArg;simp_all only [Subtype.mk.injEq]
  simp_all only [sym2.map_repeat, Function.comp_apply]
}

@[simp]lemma SimpleGraph.coloring.mapAlongIso_isoSymm {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U} {C : Type} (coloring : G.coloring C) (iso : G ≃g H) : (coloring.mapAlongIso iso).mapAlongIso iso.symm = coloring := by {
  simp_all only [mapAlongIso_repeat,compoesIsos_symm_iso,mapAlongIso_id]
}

instance SimpleGraph.coloring.fintype {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] [DecidableEq V] (C : Type) [Fintype C]
  : Fintype (G.coloring C) := Pi.instFintype

instance SimpleGraph.Embedding_equiv_subtype' {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  : {x : U ↪ V // ∀ {v u : U}, G.Adj (x v) (x u) ↔ S.Adj v u} ≃ (S ↪g G) where
  toFun (x : {x : U ↪ V // ∀ {v u : U}, G.Adj (x v) (x u) ↔ S.Adj v u}) := by show S.Adj ↪r G.Adj;refine ⟨x.val,x.property⟩
  invFun (x : S ↪g G) := ⟨x.1,x.2⟩
  left_inv := by intro x;simp_all only [id_eq, Subtype.coe_eta]
  right_inv := by intro x;simp_all only [id_eq]

instance embeddings.fintype' (D C : Type) [Fintype D] [Fintype C] [DecidableEq D] [DecidableEq C] : Fintype (D ↪ C) := by {
  exact Fintype.ofEquiv { f : D → C // Function.Injective f } (Equiv.subtypeInjectiveEquivEmbedding D C)
}

instance SimpleGraph.Embedding.fintype' {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Fintype (S ↪g G) := by {
    refine Fintype.ofEquiv {x : U ↪ V // ∀ {v u : U}, G.Adj (x v) (x u) ↔ S.Adj v u} (SimpleGraph.Embedding_equiv_subtype' G S)
  }

def SimpleGraph.coloring.monochromatic {V U : Type} {G : SimpleGraph V} {S : SimpleGraph U} (IC : S ↪g G)
  {C : Type} (f : G.coloring C) : Prop
  := ∃color : C,∀e : Sym2 U, (h : (e.map IC.toFun) ∈ G.edgeSet) → f ⟨(e.map IC.toFun),h⟩=color

instance SimpleGraph.coloring.monochromatic.decidable {V U : Type} {G : SimpleGraph V} {S : SimpleGraph U} (IC : S ↪g G)
  {C : Type} (f : G.coloring C) [DecidableRel G.Adj] [Fintype C] [Fintype U] [DecidableEq C]
  : Decidable (f.monochromatic IC) := by unfold SimpleGraph.coloring.monochromatic;infer_instance

@[simp]lemma SimpleGraph.coloring.mapAlongIso_preservesMonochromaticity {V U W : Type} {G : SimpleGraph V} {H : SimpleGraph U} {C : Type} (coloring : G.coloring C) (iso : G ≃g H) (S : SimpleGraph W) (IC : S ↪g G)
  : (coloring.mapAlongIso iso).monochromatic ((iso) ∘ge IC) ↔ coloring.monochromatic IC := by {
    unfold SimpleGraph.coloring.monochromatic;simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
    /-t₁ proof easily simplified by proving compositional applying-/
    have t₁ : (fun x ↦ ( (iso : G ↪g H) ∘ge IC) x) = (iso) ∘ (IC) := by {
      ext x;simp_all only [Function.comp_apply];unfold graph_composeEmbed Equiv.toEmbedding RelEmbedding.toEmbedding composeEmbed
      simp_all only [RelIso.coe_fn_toEquiv, Function.Embedding.coeFn_mk, RelEmbedding.coe_toEmbedding, RelEmbedding.coe_mk, Function.comp_apply]
    }
    /-this should be a general simp lemma, but isn't-/
    have t₂ : ⇑(iso) = iso := by rfl
    constructor;all_goals intro ⟨color,h⟩;use color;intro e eMap
    {
      specialize h e ?_
      induction e with
      | h v u => clear t₁ t₂;simp_all only [Sym2.map_pair_eq, mem_edgeSet,
        Embedding.map_adj_iff]
      conv at h => lhs;rhs;lhs;rw [t₁]
      conv at h => lhs;rhs;lhs;rw [← sym2.map_repeat]
      conv at h => lhs;rhs;lhs;rw [t₂]
      unfold SimpleGraph.coloring.mapAlongIso at h;simp_all only [Function.comp_apply,
        sym2.map_repeat, id_eq, RelIso.symm_apply_apply]
    }
    {
      specialize h e ?_
      {
        induction e with
        | h v u => clear t₁ t₂;simp_all only [Sym2.map_pair_eq, mem_edgeSet,
          Embedding.map_adj_iff]
      }
      conv => lhs;rhs;lhs;rw [t₁]
      conv => lhs;rhs;lhs;rw [← sym2.map_repeat]
      conv => lhs;rhs;lhs;rw [t₂]
      unfold SimpleGraph.coloring.mapAlongIso;simp_all only [sym2.map_repeat, Function.comp_apply,
        id_eq, RelIso.symm_apply_apply]

    }
  }

def SimpleGraph.coloring.bad {V U C : Type} {G : SimpleGraph V} (f : G.coloring C) (S : SimpleGraph U) : Prop
  := ∃copy : S ↪g G, f.monochromatic copy

/-Fintype.decidableExistsFintype-/
instance SimpleGraph.coloring.bad.decidable {V U C : Type} {G : SimpleGraph V} (f : G.coloring C) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [Fintype C] [DecidableEq C] [DecidableEq V] [DecidableEq U]
  : Decidable (f.bad S) := by unfold SimpleGraph.coloring.bad;infer_instance

@[simp]lemma SimpleGraph.coloring.mapAlongIso_preservesBadness {V U W : Type} {G : SimpleGraph V} {H : SimpleGraph U} {C : Type} (coloring : G.coloring C) (iso : G ≃g H) (S : SimpleGraph W)
  : (coloring.mapAlongIso iso).bad S ↔ coloring.bad S := by {
    unfold SimpleGraph.coloring.bad;constructor;all_goals intro ⟨copy,mono⟩
    use (iso.symm) ∘ge copy;
    have t := SimpleGraph.coloring.mapAlongIso_isoSymm coloring iso;rw [← t]
    rw [SimpleGraph.coloring.mapAlongIso_preservesMonochromaticity];exact mono
    use iso ∘ge copy;simp_all only [mapAlongIso_preservesMonochromaticity]
  }

def SimpleGraph.ramsey {V U : Type} (colors : Type) (G : SimpleGraph V) (S : SimpleGraph U) : Prop := ∀ f : G.coloring colors,f.bad S

instance SimpleGraph.ramsey.decidable {V U : Type} (C : Type) (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [Fintype C] [DecidableEq V] [DecidableEq C] [DecidableEq U]
  : Decidable (G.ramsey C S) := by unfold SimpleGraph.ramsey;infer_instance


lemma SimpleGraph.ramsey_iso {V U T : Type} (colors : Type) {G : SimpleGraph V} {H : SimpleGraph T} (S : SimpleGraph U) (i : G ≃g H) : G.ramsey colors S ↔ H.ramsey colors S := by {
  unfold SimpleGraph.ramsey
  constructor;rename SimpleGraph V => H;rename SimpleGraph T => G;replace i := i.symm
  all_goals {
    intro h coloring
    specialize h (SimpleGraph.coloring.mapAlongIso coloring i)
    simp_all only [SimpleGraph.coloring.mapAlongIso_preservesBadness]
  }
}

def DGraph_isoClass.ramsey {V U : Type} (colors : Type) (G : Quotient (DGraph.hasIso (V:=V))) (S : SimpleGraph U) : Prop := by {
  apply Quotient.lift (s:=DGraph.hasIso (V:=V)) (fun G : DGraph V ↦ SimpleGraph.ramsey colors G.toSimpleGraph S) ?_ G
  intro G H iso
  unfold HasEquiv.Equiv instHasEquivOfSetoid at iso;simp only at iso
  unfold DGraph.hasIso at iso;simp_all only [eq_iff_iff];obtain ⟨iso⟩ := iso
  unfold SimpleGraph.ramsey
  constructor;rename DGraph V => G;rename_i H;have iso := iso.symm
  all_goals {
    intro h coloring
    specialize h (SimpleGraph.coloring.mapAlongIso coloring iso)
    simp_all only [SimpleGraph.coloring.mapAlongIso_preservesBadness]
  }
}

lemma DGraph_isoClass.ramsey_iff_ramsey {V U : Type} (colors : Type) (G : DGraph V) (S : SimpleGraph U) : G.toSimpleGraph.ramsey colors S ↔ DGraph_isoClass.ramsey colors ⟦G⟧ S
  := by unfold DGraph_isoClass.ramsey;simp_all only [Quotient.lift_mk]


instance DGraph_isoClass.ramsey.decidable {V U : Type} (C : Type) (G : Quotient (DGraph.hasIso (V:=V))) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel S.Adj] [Fintype C] [DecidableEq V] [DecidableEq C] [DecidableEq U]
  : Decidable (DGraph_isoClass.ramsey C G S) := by {
    revert G;apply Quotient.rec;subsingleton
    intro G
    exact decidable_of_decidable_of_iff (DGraph_isoClass.ramsey_iff_ramsey C G S)
  }

end colorings
section minimal_ramsey

def SimpleGraph.minimal_ramsey {V U : Type} (colors : Type) (G : SimpleGraph V) (S : SimpleGraph U) : Prop
  := (G.ramsey colors S) ∧ (∀T : Type,∀H : SimpleGraph T,∀e : H →g G,e.toFun.Injective → (H.ramsey colors S) → (∃eᵢ : G →g H,e.toFun.LeftInverse eᵢ))

lemma SimpleGraph.generic_cases {n : ℕ} (G : SimpleGraph (Fin n))
  {V : Type} {H : SimpleGraph V} {e : H →g G} (inj : (⇑e).Injective)
  : (∃k : ℕ,k<n ∧ ∃I : SimpleGraph (Fin k),Nonempty (H ≃g I)) ∨ (∃I : SimpleGraph (Fin n),Nonempty (H ≃g I) ∧ I<G) ∨ (∃eᵣ : G →g H, e.toFun.LeftInverse eᵣ)
  := by {
    by_cases surj : (⇑e).Surjective
    {
      right;
      have HGequiv : V ≃ Fin n := Equiv.ofBijective (⇑e) ⟨inj,surj⟩
      have ⟨HiI,HiItf⟩ : {ee : H ≃g (H.map ⟨⇑e,inj⟩) // ⇑ee = ⇑e} := by {
          refine ⟨⟨?_,?_⟩,?_⟩
          have bij : (⇑e).Bijective := ⟨inj,surj⟩
          exact Equiv.ofBijective (⇑e) bij
          intro v u;simp_all only [Equiv.ofBijective_apply, map_adj, Function.Embedding.coeFn_mk]
          constructor
          {
            intro ⟨a,b,adj,amv,bmy⟩
            replace amv := inj amv;replace bmy := inj bmy;subst amv;subst bmy
            exact adj
          }
          {
            intro adj;use v;use u
          }
          simp_all only [RelIso.coe_fn_mk];rfl
      }
      have t : (H.map ⟨⇑e,inj⟩)≤G := by {
        intro v u adj;simp_all only [map_adj, Function.Embedding.coeFn_mk]
        obtain ⟨a,b,adj,amv,bmu⟩ := adj;subst amv;subst bmu
        exact Hom.map_adj e adj
      }
      have t : (H.map ⟨⇑e,inj⟩)<G ∨ G=(H.map ⟨⇑e,inj⟩) := by {
        by_cases h : G≤(H.map ⟨⇑e,inj⟩)
        right;{
          unfold LE.le instLE IsSubgraph at t;unfold LE.le instLE IsSubgraph at h;simp_all only;refine adj_inj.mp ?_
          ext v u;constructor;all_goals intro a
          exact h a;exact t a
        }
        left;exact lt_of_le_not_le t h
      }
      cases t with
      | inl t => exact Or.inl ⟨(H.map ⟨⇑e,inj⟩),⟨⟨HiI⟩,t⟩⟩
      | inr t => {
        right
        have ⟨HiG,HiGtf⟩ : {ee : H ≃g G // ⇑ee = ⇑e} := by {
          refine ⟨⟨HiI,?_⟩,?_⟩
          {
            intro v u
            conv =>
              lhs
              congr
              · rw [t]
            exact HiI.map_rel_iff'
          }
          {
            simp_all only [le_refl, RelIso.coe_fn_mk, EquivLike.coe_coe]
          }
        }
        use HiG.symm;simp_all only [le_refl, RelHom.coe_fn_toFun, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]
        rw [← HiGtf];clear HiGtf;
        refine Function.leftInverse_of_surjective_of_rightInverse (RelIso.surjective HiG) HiG.left_inv'
      }
    }
    {
      left
      have ⟨k,lt,⟨iso⟩⟩ := inj_implies_fin inj surj
      use k;use lt;use H.map iso;refine ⟨?_⟩
      exact Iso.map iso H
    }
  }


lemma emptyVertices_imp_notRamsey {V U : Type} (C : Type) (G : SimpleGraph V) (S : SimpleGraph U)
  : ((IsEmpty V) ∧ (Nonempty U)) → ¬(G.ramsey C S) := by {
    intro ⟨Ve,Une⟩
    unfold SimpleGraph.ramsey;simp_all only [not_forall]
    use ?_;case w => unfold SimpleGraph.coloring;{
      have c : IsEmpty ↑G.edgeSet := by infer_instance
      intro x;exfalso;simp_all only [Set.isEmpty_coe_sort];
      rw [← Set.subset_empty_iff] at c;specialize c x.property;exact c
    }
    simp_all only [id_eq];unfold SimpleGraph.coloring.bad;simp_all only [not_exists]
    intro Sᵢ;exfalso
    have ⟨x⟩ := Classical.inhabited_of_nonempty Une
    have y := Sᵢ x
    exact IsEmpty.false y
  }

lemma no_color_implies_not_ramsey {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U) (C : Type) [empt : IsEmpty C] [ne : Nonempty (↑G.edgeSet)] : (G.ramsey C S) := by {
  unfold SimpleGraph.ramsey;intro f;
  have ⟨e⟩ := Classical.inhabited_of_nonempty ne
  exfalso;unfold SimpleGraph.coloring at f;specialize f e;exact IsEmpty.false f
}

/-set_option linter.unusedTactic false
lemma minimal_ramsey_exists {U : Type} {n : ℕ} (S : SimpleGraph U) (C : Type) (G : SimpleGraph (Fin n)) (h : G.ramsey C S)
  : ∃k : ℕ, ∃H : SimpleGraph (Fin k), ∃e : H →g G, e.toFun.Injective ∧ H.minimal_ramsey C S := by {
    revert h
    have ind := SimpleGraph.generic_induction' G
      (λ {V : Type} (I : SimpleGraph V) ↦  (I.ramsey C S) → ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (e : H →g I), (Function.Injective e.toFun ∧ SimpleGraph.minimal_ramsey C H S))
    apply ind;constructor
    {
      clear ind;intro ih Gram
      by_cases Gmin : G.minimal_ramsey C S
      {
        use n;use G
        use ?_;case w => use id;simp_all only [RelHom.coe_fn_toFun, exists_and_right, id_eq, implies_true]
        simp_all only [RelHom.coe_fn_toFun, exists_and_right, and_true];exact fun ⦃a₁ a₂⦄ a ↦ a
      }
      {
        unfold SimpleGraph.minimal_ramsey at Gmin
        simp_all only [RelHom.coe_fn_toFun, exists_and_right, true_and, not_forall, Classical.not_imp, not_exists]
        obtain ⟨V,H,e,inj,Hram,HlG⟩ := Gmin
        specialize ih inj Hram;obtain ⟨k,I,⟨e₀,e₀ₕ⟩,Imin⟩ := ih
        use k;use I;simp_all only [and_true]
        use e ∘g e₀;
        have t : ⇑(e ∘g e₀) = ⇑e ∘ ⇑e₀ := by rfl
        rw [t];exact Function.Injective.comp inj e₀ₕ
      }

    }
    {
      clear ind;intro ramsey
      by_cases Ue : IsEmpty U
      {
        use 0;use (⊥ : SimpleGraph (Fin 0));
        use ?_;case w => use (by intro x;apply finZeroElim x);{

          intro x;apply finZeroElim x
        }
        simp_all only;constructor
        {
          intro x;apply finZeroElim x
        }
        {
          unfold SimpleGraph.minimal_ramsey;constructor
          {
            have eq : (⊥ : SimpleGraph Empty) ≃g (⊥ : SimpleGraph (Fin 0)) := by {
              use ?_;use ?_
              intro x;apply finZeroElim x
              intro x;exfalso;exact Aesop.BuiltinRules.empty_false x
              intro x;apply finZeroElim x
              intro x;exfalso;exact Aesop.BuiltinRules.empty_false x
            }
            exact (SimpleGraph.ramsey_iso C S eq).mp ramsey
          }
          {
            intro V H e inj Hramsey;simp_all only [RelHom.coe_fn_toFun]
            use ?_;case w => skip;{
              refine ⟨?_,?_⟩
              intro x;apply finZeroElim x
              intro x;apply finZeroElim x
            }
            intro x;apply finZeroElim x
          }
        }
      }
      {
        contrapose ramsey;clear ramsey;apply emptyVertices_imp_notRamsey
        simp_all only [not_isEmpty_iff, and_true];exact Empty.instIsEmpty
      }

    }
  }-/


lemma subgraph_gives_edgeSizele {k n : ℕ} {I : SimpleGraph (Fin k)} {G : SimpleGraph (Fin n)} {ItG : I →g G} (inj : (⇑ItG).Injective)
  : I.edgeSet.ncard ≤ G.edgeSet.ncard := by {
    have h : (I.map ⟨⇑ItG,inj⟩) ≤ G := by {
      intro v u adj;simp_all only [SimpleGraph.map_adj, Function.Embedding.coeFn_mk]
      obtain ⟨a,b,adj,amv,bmu⟩ := adj;subst amv;subst bmu
      exact SimpleGraph.Hom.map_adj ItG adj
    }
    have e : I.edgeSet.ncard = (I.map ⟨⇑ItG,inj⟩).edgeSet.ncard := by {
      have e : (SimpleGraph.map { toFun := ⇑ItG, inj' := inj } I).edgeSet= ((Sym2.map ItG) '' I.edgeSet) := by {
        ext x;induction x with
        | h x y => {
        simp_all only [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj, Function.Embedding.coeFn_mk, Set.mem_image]
        constructor
        {
          simp_all only [forall_exists_index, and_imp]
          intro v u adj vmx umy;subst vmx;subst umy
          use s(v,u);simp_all only [SimpleGraph.mem_edgeSet, Sym2.map_pair_eq, and_self]
        }
        {
          intro ⟨e,⟨eie,maph⟩⟩;induction e with
          | h a b =>
          simp_all only [SimpleGraph.mem_edgeSet, Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
          cases maph with
          | inl h => obtain ⟨h₁,h₂⟩ := h;subst h₁;subst h₂;use a;use b
          | inr h => obtain ⟨h₁,h₂⟩ := h;subst h₁;subst h₂;use b;use a;simp_all only [and_self, and_true];exact SimpleGraph.adj_symm I eie
        }
        }
      }
      rw [e];exact Eq.symm (Set.ncard_image_of_injective I.edgeSet (Sym2.map.injective inj))
    }
    rw [e]
    refine Set.ncard_le_ncard ?_
    simp_all only [SimpleGraph.edgeSet_subset_edgeSet]
  }

lemma minimal_ramsey_exists {U : Type} {n : ℕ} (S : SimpleGraph U) (C : Type) (G : SimpleGraph (Fin n)) (h : G.ramsey C S)
  : ∃k : ℕ, ∃H : SimpleGraph (Fin k), ∃e : H →g G, e.toFun.Injective ∧ H.minimal_ramsey C S := by {


    by_cases minimal : G.minimal_ramsey C S
    {
      use n;use G;use ⟨id,?_⟩;simp_all only [and_true];exact fun ⦃a₁ a₂⦄ a ↦ a;exact fun {a b} a ↦ a
    }
    unfold SimpleGraph.minimal_ramsey at minimal;
    simp only [RelHom.coe_fn_toFun, not_and, not_forall, Classical.not_imp, not_not, exists_and_right] at minimal
    specialize minimal h;obtain ⟨V,H,e,i,s,r⟩ := minimal

    have test := SimpleGraph.generic_cases G i
    cases test with
    | inl t => {
      obtain ⟨k,kln,⟨I,⟨i⟩⟩⟩ := t

      simp only [not_exists] at r;

      have test := minimal_ramsey_exists S C I ((SimpleGraph.ramsey_iso C S i).mp s)


      obtain ⟨m,A,e₂,⟨inj,min⟩⟩ := test
      use m;use A;use e ∘g (i.symm ∘g e₂);
      simp_all only [RelHom.coe_fn_toFun, and_true]
      have t : ⇑(e ∘g (i.symm ∘g e₂)) = (e ∘ (i.symm ∘ e₂)) := by rfl
      rw [t];simp_all only [Function.Injective.of_comp_iff, EmbeddingLike.comp_injective]
    }
    | inr test => cases test with
    | inl h => {
      obtain ⟨I,⟨⟨Iiso⟩,h⟩⟩ := h
      have test := minimal_ramsey_exists S C I ((SimpleGraph.ramsey_iso C S Iiso).mp s)
      obtain ⟨m,A,e₂,⟨inj,min⟩⟩ := test

      use m;use A;use e ∘g Iiso.symm ∘g e₂;
      simp_all only [not_exists, RelHom.coe_fn_toFun, and_true]
      have t : ⇑(e ∘g Iiso.symm ∘g e₂) = (e ∘ (Iiso.symm ∘ e₂)) := by rfl
      rw [t];simp_all only [Function.Injective.of_comp_iff, EmbeddingLike.comp_injective]
    }
    | inr h => {
      obtain ⟨eᵣ,eᵣh⟩ := h
      use n;use G;use (e ∘g eᵣ);constructor
      {
        have eq : (e ∘g eᵣ).toFun = e ∘ eᵣ := by unfold composeHomos;simp_all only [not_exists, RelHom.coe_fn_toFun]
        rw [eq];refine Function.Injective.comp i (Function.LeftInverse.injective eᵣh)
      }
      {
        unfold SimpleGraph.minimal_ramsey;simp_all only [not_exists, RelHom.coe_fn_toFun]
      }
    }

  }
termination_by n + (G.edgeSet.ncard)
decreasing_by
  · {
  refine Nat.add_lt_add_of_lt_of_le kln (subgraph_gives_edgeSizele (ItG := (e ∘g i.symm)) ?_)
  rename_i _ _ _ _ _ _ _ _ _ _ _ einj _ _ _ _ _ _;obtain ⟨einj,_⟩ := einj
  exact (EquivLike.injective_comp i.symm ⇑e).mpr einj
}
  · {
  refine Nat.add_lt_add_of_le_of_lt (Nat.le_refl n) ?_
  refine Set.ncard_lt_ncard ?_
  exact SimpleGraph.edgeSet_ssubset_edgeSet.mpr h
}


#print axioms minimal_ramsey_exists

set_option linter.unusedTactic false
lemma minimal_ramsey_sufficient {U : Type} (n : ℕ) (S : SimpleGraph U) (C : Type)
  : (∀k : Fin n, ∀ G : SimpleGraph (Fin k.val), ¬(G.minimal_ramsey C S))
  ↔ (∀k : Fin n, ∀ G : SimpleGraph (Fin k.val), ¬(G.ramsey C S))
  := by {
    constructor
    case mpr => intro h k G;specialize h k G;contrapose h;simp_all only [not_not];exact h.left
    intro h k G
    contrapose h;simp_all only [not_not, not_forall]
    obtain ⟨j,H,e,i,h⟩ := minimal_ramsey_exists (n:=k.val) S C G h
    use ⟨j,?_⟩;case w => skip;{
      calc
        _ ≤ k.val := by {
      have t : Fin j ↪ (Fin k.val) := ⟨e.toFun,i⟩
      exact embedding_lt t
    }
        _ < _ := k.isLt
    }
    use H
  }


def DGraph_quot_minimal_ramsey {V U : Type} (colors : Type) (G : Quotient (DGraph.hasIso (V:=V))) (S : SimpleGraph U) : Prop
  := by {
    revert G;apply Quotient.lift (λ G : DGraph V ↦ G.minimal_ramsey colors S)
    intro G H i;simp_all only [eq_iff_iff];unfold HasEquiv.Equiv instHasEquivOfSetoid DGraph.hasIso at i;obtain ⟨i⟩ := i
    suffices conc {V U : Type} (colors : Type) (S : SimpleGraph U) (H G : DGraph V) (i : G.toSimpleGraph ≃g H.toSimpleGraph)
      : SimpleGraph.minimal_ramsey colors H.toSimpleGraph S → SimpleGraph.minimal_ramsey colors G.toSimpleGraph S
    constructor;exact conc colors S G H i.symm;exact conc colors S H G i
    unfold SimpleGraph.minimal_ramsey;intro h;constructor
    rw [DGraph_isoClass.ramsey_iff_ramsey];rw [DGraph_isoClass.ramsey_iff_ramsey] at h
    have e : (⟦G⟧ : Quotient (DGraph.hasIso (V:=V)))= ⟦H⟧ := by apply Quotient.sound;unfold HasEquiv.Equiv instHasEquivOfSetoid DGraph.hasIso;simp_all only;exact ⟨i⟩
    rw [e];exact h.left
    intro U I e inj;replace h := h.right U I ?_
    case conc.right.refine_1 => use (i.toFun ∘ e.toFun);{
      intro v u Ia;simp_all only [RelHom.coe_fn_toFun, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Function.comp_apply]
      have Ga : G.Adj (e v) (e u);exact SimpleGraph.Hom.map_adj e Ia
      exact (SimpleGraph.Iso.map_adj_iff i).mpr Ga
    }

    intro r;
    specialize h ?_ r
    simp_all only [RelHom.coe_fn_toFun, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, EmbeddingLike.comp_injective, forall_const]
    obtain ⟨eᵢ,h⟩ := h;

    simp_all only

    use eᵢ ∘g i;simp_all only [RelHom.coe_fn_toFun, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv]
    have eq : ⇑(eᵢ ∘g (i :  G.toSimpleGraph →g H.toSimpleGraph)) = eᵢ ∘ i := by rfl
    rw [eq];intro x;have h₀ := h (i x);simp_all only [Function.comp_apply]
    have t :  i.symm (i (e (eᵢ (i x)))) = i.symm (i x) := congrArg (⇑i.symm) (h (i x))
    simp only [RelIso.symm_apply_apply] at t
    exact t
  }

lemma DGraph_quot_minimal_ramsey_iff_minimal_ramsey {V U : Type} (colors : Type) (G : DGraph V) (S : SimpleGraph U)
  : G.toSimpleGraph.minimal_ramsey colors S ↔ DGraph_quot_minimal_ramsey colors ⟦G⟧ S := by {
    unfold DGraph_quot_minimal_ramsey;simp_all only [Quotient.lift_mk]
  }


section tempSupersingleton
class Superinhabited (T : Type) where
  default : T
  other : T → T
  otherDif : ∀x : T,x≠other x

instance Superinhabited.Inhabited {T : Type} [si : Superinhabited T] : Inhabited T := ⟨si.default⟩

def other {T : Type} (x : T) [si : Superinhabited T] : T := si.other x

lemma other_dif {T : Type} (x : T) [si : Superinhabited T] : x ≠ other x := by unfold other;exact si.otherDif x

lemma other_dif' {T : Type} (x : T) [si : Superinhabited T] : ¬x = other x := other_dif x

lemma other_dif'' {T : Type} (x : T) [si : Superinhabited T] : other x ≠ x := by unfold other;have t := si.otherDif x;contrapose t;simp_all only [ne_eq, not_not, not_true_eq_false, not_false_eq_true]

lemma other_dif''' {T : Type} (x : T) [si : Superinhabited T] : ¬other x = x := other_dif'' x

class Supersingleton (T : Type) where
  nonempty : Nonempty T
  apply : ∀x : T,∃y : T,x≠y

instance Nonempty_of_supersingleton {T : Type} [ss : Supersingleton T] : Nonempty T := ss.nonempty

noncomputable def Classical.superinhabited_of_supersingelton (T : Type) [ss : Supersingleton T] : Superinhabited T := by {
  have inh : Inhabited T := Classical.inhabited_of_nonempty Nonempty_of_supersingleton
  refine ⟨default,?_,?_⟩
  intro t;exact Classical.choose (ss.apply t);intro t;exact Classical.choose_spec (ss.apply t)
}

@[simp]lemma SuperSingleton_iff_notsubsingleton {T : Type} : ¬(Subsingleton T) ↔ (Supersingleton T) := by {
  symm
  constructor
  {
    intro super;have si := Classical.superinhabited_of_supersingelton T
    by_contra sub
    have c : (default : T) = other default := by subsingleton
    exact other_dif (default : T) c
  }
  {
    intro nsub
    refine { nonempty := ?_, apply := ?_ }
    contrapose nsub;simp_all only [not_nonempty_iff, not_not];exact IsEmpty.instSubsingleton
    intro x;contrapose nsub;simp_all only [ne_eq, not_exists, not_not]
    refine { allEq := ?_ };intro a b
    trans x
    specialize nsub a;symm;exact nsub
    specialize nsub b;exact nsub
  }
}


@[simp]lemma subsingleton_iff_notSuperSingleton {T : Type} : ¬(Supersingleton T) ↔ (Subsingleton T) := by
  rw [← SuperSingleton_iff_notsubsingleton];simp only [not_not]


instance SubsingletonDecidable {T : Type} [F : Fintype T] : Decidable (Subsingleton T) := by {
  obtain ⟨⟨l,nd⟩,c⟩ := F
  simp_all only [Finset.mem_mk]
  revert l;apply Multiset.rec
  case mk.mk.C_0 => intro nd c;refine isTrue ?_;simp_all only [Multiset.not_mem_zero];refine ⟨?_⟩;intro x;exfalso;apply c;exact x
  case mk.mk.C_cons => intro head tail ih c;{
    clear ih;revert tail;apply Multiset.rec
    case C_0 => intro nd c;refine isTrue ?_;simp_all only [Multiset.cons_zero, Multiset.mem_singleton];refine ⟨?_⟩;{
      intro x y;trans head
      exact c x
      symm;exact c y
    }
    case C_cons => intro head₂ tail ih nd c;clear ih;refine isFalse ?_;{
      by_contra s;have headEq := Subsingleton.elim head head₂
      simp_all only [Multiset.nodup_cons, Multiset.mem_cons, true_or, not_true_eq_false, false_and]
    }
    case C_cons_heq => intro a b c d;{
      refine Function.hfunext ?_ ?_
      simp_all only [Multiset.nodup_cons, Multiset.mem_cons, not_or, eq_iff_iff]
      {
        apply Iff.intro
        · intro a_1
          simp_all only [not_false_eq_true, and_self, and_true, true_and]
          obtain ⟨left, right⟩ := a_1
          obtain ⟨left, right_1⟩ := left
          obtain ⟨left_1, right⟩ := right
          obtain ⟨left_2, right_1⟩ := right_1
          obtain ⟨left_1, right_2⟩ := left_1
          obtain ⟨left_3, right⟩ := right
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_false_eq_true, not_true_eq_false]
        · intro a_1
          simp_all only [not_false_eq_true, and_self, and_true, true_and]
          obtain ⟨left, right⟩ := a_1
          obtain ⟨left, right_1⟩ := left
          obtain ⟨left_1, right⟩ := right
          obtain ⟨left_2, right_1⟩ := right_1
          obtain ⟨left_1, right_2⟩ := left_1
          obtain ⟨left_3, right⟩ := right
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_false_eq_true, not_true_eq_false]
      }
      intro h₁ h₂ h₃
      refine Function.hfunext ?_ ?_
      simp_all only [heq_eq_eq, Multiset.mem_cons, eq_iff_iff]
      {
        simp_all only [Multiset.nodup_cons, Multiset.mem_cons, not_or, or_self, not_false_eq_true, or_false, and_self,
          and_true, true_and]
        obtain ⟨left, right⟩ := h₁
        obtain ⟨left, right_1⟩ := left
        obtain ⟨left_1, right⟩ := right
        obtain ⟨left_2, right_1⟩ := right_1
        obtain ⟨left_1, right_2⟩ := left_1
        obtain ⟨left_3, right⟩ := right
        apply Iff.intro
        · intro a_1 x
          specialize a_1 x
          cases a_1 with
          | inl h =>
            subst h
            simp_all only [or_self, or_false]
          | inr h_1 =>
            cases h_1 with
            | inl h =>
              subst h
              simp_all only [or_false, or_true]
            | inr h_2 =>
              cases h_2 with
              | inl h =>
                subst h
                simp_all only [or_self, or_false, or_true]
              | inr h_1 => simp_all only [or_true]
        · intro a_1 x
          specialize a_1 x
          cases a_1 with
          | inl h =>
            subst h
            simp_all only [or_self, or_false]
          | inr h_1 =>
            cases h_1 with
            | inl h =>
              subst h
              simp_all only [or_false, or_true]
            | inr h_2 =>
              cases h_2 with
              | inl h =>
                subst h
                simp_all only [or_self, or_false, or_true]
              | inr h_1 => simp_all only [or_true]
      }
      intro i₁ i₂ i₃
      simp_all only [heq_eq_eq, implies_true]
    }
  }
  case mk.mk.C_cons_heq => intro a b c d;{
    refine Function.hfunext ?_ ?_
    simp_all only [Multiset.nodup_cons, Multiset.mem_cons, not_or, eq_iff_iff]
    apply Iff.intro
    · intro a_1
      simp_all only [not_false_eq_true, and_true, and_self]
      obtain ⟨left, right⟩ := a_1
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right⟩ := right
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [not_false_eq_true, not_true_eq_false]
    · intro a_1
      simp_all only [not_false_eq_true, and_true, and_self]
      obtain ⟨left, right⟩ := a_1
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right⟩ := right
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [not_false_eq_true, not_true_eq_false]
    intro n₁ n₂ n₃
    refine Function.hfunext ?_ ?_
    simp_all only [heq_eq_eq, Multiset.mem_cons, eq_iff_iff]
    simp_all only [Multiset.nodup_cons, Multiset.mem_cons, not_or, or_false, not_false_eq_true, and_self, and_true]
    obtain ⟨left, right⟩ := n₁
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    apply Iff.intro
    · intro a_1 x
      specialize a_1 x;cases a_1 with
      | inl h =>
        subst h
        simp_all only [or_false, or_true]
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          simp_all only [or_self, or_false]
        | inr h_2 => simp_all only [or_true]
    · intro a_1 x
      specialize a_1 x;cases a_1 with
      | inl h =>
        subst h
        simp_all only [or_false, or_true]
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          simp_all only [or_self, or_false]
        | inr h_2 => simp_all only [or_true]
    intro h₁ h₂ h₃
    simp_all only [heq_eq_eq, implies_true, Multiset.cons_zero, eq_mp_eq_cast]
    subsingleton
  }
}

instance Supersingleton_decidable (T : Type) [Fintype T] : Decidable (Supersingleton T) := by {
  rw [← SuperSingleton_iff_notsubsingleton];infer_instance
}

end tempSupersingleton
section copyMembership

instance FunMem {D C : Type} : Membership C (D → C) := ⟨
  fun f x ↦ ∃y : D,f y = x
⟩

instance FunMem_Decidable {D C : Type} [Fintype D] [DecidableEq C] (x : C) (f : D → C) : Decidable (x ∈ f) := by {
  unfold Membership.mem FunMem;simp_all only;infer_instance
}

instance Sym2Mem {M S : Type} [Membership M S] : Membership (Sym2 M) S := ⟨fun s ↦ by {
    apply Sym2.rec;case f => intro ⟨x,y⟩;exact x ∈ s ∧ y ∈ s;;aesop
  }⟩

instance {D C : Type} : Membership (Sym2 C) (D → C) := Sym2Mem

lemma Sym2Mem_isInRange {D C : Type} (e : Sym2 C) (f : D → C) : e ∈ f ↔ ∃e₀ : Sym2 D,e₀.map f = e := by {
  unfold Membership.mem instMembershipSym2Forall_test Sym2Mem Membership.mem FunMem
  simp_all only

  induction e with
  | h x y => {
    trans (fun h ↦ (∃ y, f y = h.1) ∧ ∃ y, f y = h.2) (⟨x,y⟩ : C × C);rfl
    simp_all only;constructor
    intro ⟨⟨a,ah⟩,⟨b,bh⟩⟩;subst ah bh;use s(a,b);simp_all only [Sym2.map_pair_eq]
    intro ⟨e₀,h⟩;induction e₀ with
    | h a b => simp_all only [Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk];aesop
  }
}

instance Sym2_funMem {D C : Type} [Fintype D] [DecidableEq C] (x : Sym2 C) (f : D → C) : Decidable (x ∈ f) := by {
  rw [Sym2Mem_isInRange];infer_instance
}

end copyMembership

/-discussed in notes as P₁-//-needs to have the written proof redone.-/
lemma irrelevantVertex_imp_notMinRamsey {V U : Type} (C : Type) [ne : Nonempty C] (G : SimpleGraph V) (S : SimpleGraph U)
  : (∃ v : V,∀copy : S ↪g G,v ∉ (Set.range copy)) → ¬(G.minimal_ramsey C S) := by {
    /-Since we assumed that our type of colors is nonempty, we may use a default color.-/
    have inh : Inhabited C := Classical.inhabited_of_nonempty ne

    /-PB-/

    /-As per our assumption we introduce a vertex v, which is not present in any copies of S.-/
    intro ⟨v,h⟩

    /-We wish to show G is not minimal ramsey, equivalently, we will assume G is ramsey, and show that there exists a ramsey subgraph.-/
    unfold SimpleGraph.minimal_ramsey
    simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Set.mem_range,
      not_exists, RelHom.coe_fn_toFun, not_and, not_forall, Classical.not_imp, not_not, exists_and_right]
    intro ramsey

    /-Use the graph G.induce {u | u≠v}, which denotes the graph G restricted by removing the vertex v. -/
    use {u : V // u≠v}
    use G.induce {u : V | u≠v};use G.induce_subgraph {u : V | u≠v}
    use by {
      simp_all only [ne_eq,SimpleGraph.induce_subgraph_funCoe];exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
    }
    simp_all only [ne_eq, not_nonempty_iff, exists_prop];constructor
    case h.right => skip;{
      intro eᵢ;
      have nsurj : ¬(⇑(SimpleGraph.induce_subgraph {u | u ≠ v} G)).Surjective := by {
        unfold DFunLike.coe RelHom.instFunLike;simp_all only;rw [SimpleGraph.induce_subgraph_toFun]
        simp_all only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq];unfold Function.Surjective;
        simp_all only [Subtype.exists, exists_prop, exists_eq_right, forall_eq, not_false_eq_true]
      }
      contrapose nsurj;simp_all only [ne_eq, not_not, Set.coe_setOf, RelHom.coe_fn_toFun];exact Function.RightInverse.surjective nsurj
    }

    {
      /-In order to show G.induce {u | u≠v} is ramsey, we need to show that all colorings γ of G.induce {u | u≠v} have a monochromatic copy of S.-/
      unfold SimpleGraph.ramsey SimpleGraph.coloring.bad;intro γ

      /-PB-/

      /-We may extend γ to a full coloring of G by assigning the default value to all edges neighboring v. Since G is ramsey, there exists a copy Sᵢ of S in G that is monochromatic under the extension of γ.-/
      unfold SimpleGraph.ramsey at ramsey;specialize ramsey (by {
        unfold SimpleGraph.coloring;intro ⟨e,ei⟩
        have _ : Decidable (∃ e₀ : Sym2 {u // u ≠ v}, Sym2.map Subtype.val e₀ = e) := by apply Classical.propDecidable
        refine if isVal : ∃e₀ : Sym2 {u // u ≠ v},(e₀.map Subtype.val) = e then (γ ⟨Classical.choose isVal,?_⟩) else default

        rw [← Classical.choose_spec isVal,← SimpleGraph.induce_edgeInc] at ei;exact ei
      });obtain ⟨Sᵢ,mono⟩ := ramsey

      /-By our assumption, all copies of S do not contain v, thus Sᵢ may be considered as a copy of S within G.induce {u | u≠v}.-/
      specialize h Sᵢ;use by {
        refine ⟨⟨λ x ↦ ⟨Sᵢ x,h x⟩,?_⟩,?_⟩
        intro _ _ _;simp_all only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
        simp_all only [ne_eq, id_eq, Function.Embedding.coeFn_mk, SimpleGraph.comap_adj,
          Set.mem_setOf_eq, Function.Embedding.coe_subtype, SimpleGraph.Embedding.map_adj_iff,
          implies_true]
      };simp_all only [ne_eq, id_eq]

      /-Since Sᵢ is monochromatic under the extension of γ and does not include v, Sᵢ is monochromatic under γ itself.-/
      unfold SimpleGraph.coloring.monochromatic at mono;unfold SimpleGraph.coloring.monochromatic;
      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
      obtain ⟨c,mono⟩ := mono;use c;intro e ei;specialize mono e (by {

        rw [SimpleGraph.induce_edgeInc] at ei;simp_all only [sym2.map_repeat, Function.comp_apply]
      })
      induction e with
      | h x y => {
        simp_all only [Sym2.map_pair_eq]
        split at mono;all_goals rename_i isVal
        {
          rw [← mono];clear mono;apply congrArg
          rw [← Subtype.val_inj];simp_all only
          have  h := Classical.choose_spec isVal
          have inj : (fun e : Sym2 { u // ¬u = v } ↦ Sym2.map Subtype.val e).Injective := by {
            intro x y meq;induction x with
            | h xₗ xᵣ => induction y with
            | h yₗ yᵣ => {
              simp_all only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj,
                Set.mem_setOf_eq, Function.Embedding.coe_subtype, SimpleGraph.Embedding.map_adj_iff,
                Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
              aesop
            }
          }
          apply inj;simp_all only [Sym2.map_pair_eq]
        }
        {
          contrapose isVal;simp_all only [not_exists, not_forall, not_not];use s(⟨Sᵢ x,h x⟩,⟨Sᵢ y,h y⟩)
          simp_all only [Sym2.map_pair_eq]
        }
      }
    }
  }

instance irrelevantVertex_decidable {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Decidable (∃ v : V,∀copy : S ↪g G,v ∉ (Set.range copy)) := by infer_instance

lemma SimpleGraph.Hom.map_edge' {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U} (f : G →g H) {e : Sym2 V} : e ∈ G.edgeSet → (e.map f) ∈ H.edgeSet := by {
  induction e with
  | h x y => simp_all only [mem_edgeSet, Sym2.map_pair_eq];exact f.map_rel'
}


lemma SimpleGraph.Embedding.map_edge_iff {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U} (f : G ↪g H) {e : Sym2 V} : e ∈ G.edgeSet ↔ (e.map f) ∈ H.edgeSet := by {
  induction e with
  | h x y => simp_all only [mem_edgeSet, Sym2.map_pair_eq];exact Iff.symm (map_adj_iff f)
}

lemma SimpleGraph.Embedding.map_edge_iff' {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U} (f : G ↪g H) {e : Sym2 V} : e ∈ G.edgeSet ↔ (e.map f.toFun) ∈ H.edgeSet := by {
  induction e with
  | h x y => simp_all only [mem_edgeSet, Sym2.map_pair_eq];exact Iff.symm (map_adj_iff f)
}

@[simp]lemma SimpleGraph.edgeSet_of_deleteEdges {V : Type} (G : SimpleGraph V) (edges : Set (Sym2 V)) : (G.deleteEdges edges).edgeSet = G.edgeSet \ edges := by {
  ext e;induction e with
  | h x y => simp_all only [mem_edgeSet, deleteEdges_adj, Set.mem_diff]
}

def SimpleGraph.deleteEdges_hom {V : Type} (G : SimpleGraph V) (S : Set (Sym2 V)) : G.deleteEdges S →g G := by {
  refine ⟨id,?_⟩;simp_all only [deleteEdges_adj, id_eq, implies_true]
}
@[simp]lemma SimpleGraph.deleteEdges_hom_id {V : Type} (G : SimpleGraph V) (S : Set (Sym2 V)) : (⇑(G.deleteEdges_hom S))=id := by {
  unfold SimpleGraph.deleteEdges_hom DFunLike.coe RelHom.instFunLike;simp_all only
}
lemma SimpleGraph.deleteEdges_hom_inj {V : Type} (G : SimpleGraph V) (S : Set (Sym2 V)) : (⇑(G.deleteEdges_hom S)).Injective := by {
  simp_all only [deleteEdges_hom_id];exact fun ⦃a₁ a₂⦄ a ↦ a
}
lemma Set_disjoint_mem {T : Type} {A B : Set T} : Disjoint A B ↔ ∀x : T,x ∈ A → x ∉ B := by {
  unfold Disjoint;simp_all only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
  constructor
  {
    intro h x xiA;by_contra xiB
    have xiA' : {x} ⊆ A := by simp_all only [subset_refl, Set.singleton_subset_iff]
    have xiB' : {x} ⊆ B := by simp_all only [subset_refl, Set.singleton_subset_iff]
    specialize h xiA' xiB';simp_all only [Set.empty_subset, Set.singleton_ne_empty]
  }
  {
    intro h S SsA SsB;ext x;simp_all only [Set.mem_empty_iff_false, iff_false];by_contra xiS
    specialize SsA xiS;specialize SsB xiS;exact h x SsA SsB
  }
}
lemma SimpleGraph.deleteEdges_hom_invertible {V : Type} (G : SimpleGraph V) (S : Set (Sym2 V)) :
  (∃(x : G →g G.deleteEdges S), Function.LeftInverse ⇑(G.deleteEdges_hom S) ⇑x) ↔ Disjoint S G.edgeSet := by {
  constructor
  {
    intro ⟨f,fh⟩;simp_all only [deleteEdges_hom_id]
    rw [Set_disjoint_mem];intro x xiS xiE
    have fid : ⇑f = id := by ext x;specialize fh x;simp_all only [id_eq]
    have t := f.map_edge' xiE
    simp_all only [edgeSet_of_deleteEdges, id_eq, Sym2.map_id', Set.mem_diff, not_true_eq_false, and_false]
  }
  {
    intro disj;simp_all only [deleteEdges_hom_id]
    use ⟨id,?_⟩
    exact Function.Involutive.leftInverse (congrFun rfl)
    intro v u adj;simp_all only [id_eq, deleteEdges_adj, true_and]
    have t : s(v,u)∈G.edgeSet := adj
    replace disj := disj.symm;rw [Set_disjoint_mem] at disj
    exact disj s(v,u) t
  }
}
lemma SimpleGraph.deleteEdges_hom_invertible' {V : Type} (G : SimpleGraph V) (S : Set (Sym2 V)) :
  (∀(x : G →g G.deleteEdges S), ¬Function.LeftInverse ⇑(G.deleteEdges_hom S) ⇑x) ↔ ¬Disjoint S G.edgeSet:= by {
  have t := not_congr (deleteEdges_hom_invertible G S)
  simp_all only [not_exists]
}

lemma irrelevantEdge_imp_notMinRamsey {V U : Type} (C : Type) [ne : Nonempty C] (G : SimpleGraph V) (S : SimpleGraph U)
  : (∃ e : G.edgeSet,∀copy : S ↪g G,e.val ∉ copy.toFun) → ¬(G.minimal_ramsey C S) := by {
    /-Since we assumed that our type of colors is nonempty, we may use a default color.-/
    have inh : Inhabited C := Classical.inhabited_of_nonempty ne

    /-PB-/

    /-As per our assumption we introduce a vertex v, which is not present in any copies of S-/
    intro ⟨⟨e,ei⟩,h⟩

    /-We wish to show G is not minimal ramsey, equivalently, we will assume G is ramsey, and show that there exists a ramsey subgraph.-/
    unfold SimpleGraph.minimal_ramsey
    simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Set.mem_range,
      not_exists, RelHom.coe_fn_toFun, not_and, not_forall, Classical.not_imp, not_not, exists_and_right]
    intro ramsey

    /-Use the graph G.deleteEdges {e}, which denotes the graph G restricted by removing the edge e. -/
    use V
    use G.deleteEdges {e};use G.deleteEdges_hom {e}
    use G.deleteEdges_hom_inj {e}
    simp_all only [ne_eq, not_nonempty_iff, exists_prop];constructor
    case h.right => rw [SimpleGraph.deleteEdges_hom_invertible'];simp_all only [Set.disjoint_singleton_left, not_true_eq_false, not_false_eq_true]

    {
      /-In order to show G.deleteEdges {e} is ramsey, we need to show that all colorings γ of G.deleteEdges {e} have a monochromatic copy of S.-/
      unfold SimpleGraph.ramsey SimpleGraph.coloring.bad;intro γ

      /-PB-/

      /-We may extend γ to a full coloring of G by assigning the default value to e. Since G is ramsey, there exists a copy Sᵢ of S in G that is monochromatic under the extension of γ.-/
      unfold SimpleGraph.ramsey at ramsey;specialize ramsey (by {
      unfold SimpleGraph.coloring;intro ⟨e₀,e₀i⟩
      have _ : Decidable (e₀=e) := by apply Classical.propDecidable
      refine if isVal : e₀=e then default else γ ⟨e₀,?_⟩
      simp_all only [SimpleGraph.edgeSet_of_deleteEdges, Set.mem_diff, Set.mem_singleton_iff, not_false_eq_true, and_self]
      });obtain ⟨Sᵢ,mono⟩ := ramsey

      /-By our assumption, all copies of S do not contain e, thus Sᵢ may be considered as a copy of S within G.deleteEdges {e}.-/
      specialize h Sᵢ;use by {
        refine ⟨⟨λ x ↦ Sᵢ x,?_⟩,?_⟩
        intro _ _ _;simp_all only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
        simp_all only [id_eq, Function.Embedding.coeFn_mk, SimpleGraph.deleteEdges_adj,
          SimpleGraph.Embedding.map_adj_iff, Set.mem_singleton_iff, and_iff_left_iff_imp];rw [Sym2Mem_isInRange] at h;simp_all only [not_exists]
        intro a b aba;specialize h s(a,b);simp_all only [Sym2.map_pair_eq, not_false_eq_true]
      };simp_all only [ne_eq, id_eq]

      /-Since Sᵢ is monochromatic under the extension of γ and does not include v, Sᵢ is monochromatic under γ itself.-/
      unfold SimpleGraph.coloring.monochromatic at mono;unfold SimpleGraph.coloring.monochromatic;
      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
      obtain ⟨c,mono⟩ := mono;use c;intro e₀ e₀i;specialize mono e₀ (by {
        simp_all only [SimpleGraph.edgeSet_of_deleteEdges, Set.mem_diff, Set.mem_singleton_iff, Function.const_apply]
      })
      have hyp : ¬ Sym2.map (⇑Sᵢ) e₀ = e := by {
        rw [Sym2Mem_isInRange] at h;simp_all only [not_exists, dite_false, not_false_eq_true]
      }
      simp_all only [dite_false]
    }
  }




instance semirelevantEdge_decidable {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Decidable (∃v u : V, (G.Adj v u) ∧ (Subsingleton {copy : S ↪g G // v ∉ (Set.range copy) ∨ u ∉ (Set.range copy)})) := by infer_instance



/-discussed in notes as P₄-/
lemma connectedEdges_imp_notMinRamsey {V U : Type} (C : Type) [Supersingleton C] (G : SimpleGraph V) (S : SimpleGraph U)
  : (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : S ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun)))
  → ¬(G.minimal_ramsey C S) := by {
    have _ : Superinhabited C := Classical.superinhabited_of_supersingelton C

    intro ⟨e₁,e₂,ydif,h⟩

    unfold SimpleGraph.minimal_ramsey
    simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Set.mem_range,
      not_exists, RelHom.coe_fn_toFun, not_and, not_forall, Classical.not_imp, not_not, exists_and_right]
    intro ramsey

    use V;use G.deleteEdges {e₁.val};use ⟨id,(by {
      simp_all only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, not_or, not_and, id_eq, implies_true]
    })⟩;use (by {exact fun ⦃a₁ a₂⦄ a ↦ a})
    simp_all only [exists_prop];constructor
    case h.right => skip;{
      simp_all only [ne_eq, and_imp, forall_exists_index];intro f li
      have fid : ⇑f = id := by {
        ext x;specialize li x;simp_all only [id_eq];unfold DFunLike.coe RelHom.instFunLike at li;unfold DFunLike.coe RelHom.instFunLike;simp_all only
        exact li
      }
      have t := f.map_edge' e₁.property;simp_all only [SimpleGraph.edgeSet_of_deleteEdges, id_eq, Sym2.map_id', Set.mem_diff, Subtype.coe_prop, Set.mem_singleton_iff, not_true_eq_false, and_false]
    }

    unfold SimpleGraph.ramsey SimpleGraph.coloring.bad;intro γ




    unfold SimpleGraph.ramsey at ramsey;specialize ramsey (by {
      unfold SimpleGraph.coloring;intro ⟨e,ei⟩
      have _ : Decidable (e=e₁) := by apply Classical.propDecidable
      refine if isVal : e=e₁ then other (γ ⟨e₂,?_⟩) else γ ⟨e,?_⟩
      simp_all only [ne_eq, Subtype.coe_prop, SimpleGraph.edgeSet_of_deleteEdges, Set.mem_diff,
        Set.mem_singleton_iff, true_and];exact Subtype.coe_ne_coe.mpr fun a ↦ ydif (id (Eq.symm a))
      induction e with
      | h x y => simp_all only [ne_eq, SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet_of_deleteEdges, Set.mem_diff, Set.mem_singleton_iff, not_false_eq_true, and_self]

    });obtain ⟨Sᵢ,mono⟩ := ramsey;simp_all only [and_imp, forall_exists_index, id_eq]

    specialize h Sᵢ
    have Sᵢdcvu : (e₁.val ∉ Sᵢ.toFun) := by {
      by_contra ec;simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, forall_const]
      unfold SimpleGraph.coloring.monochromatic at mono
      obtain ⟨c,mono⟩ := mono
      rw [Sym2Mem_isInRange] at h;obtain ⟨e₂₀,e20h⟩ := h;have e20h' := e20h;unfold DFunLike.coe RelEmbedding.instFunLike at e20h
      rw [Sym2Mem_isInRange] at ec;obtain ⟨e₁₀,e10h⟩ := ec;have e10h' := e10h;unfold DFunLike.coe RelEmbedding.instFunLike at e10h
      have mono₁ := mono e₁₀ (by {rw [e10h];exact e₁.property});
      have mono₂ := mono e₂₀ (by {rw [e20h];exact e₂.property});

      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, dite_true, id_eq, eq_mpr_eq_cast, dite_eq_left_iff]
      contrapose mono₁;specialize mono₂ ?_;contrapose ydif;simp_all only [Function.Embedding.toFun_eq_coe,
        RelEmbedding.coe_toEmbedding, IsEmpty.forall_iff, not_false_eq_true, not_not, ne_eq];symm;rw [← Subtype.val_inj];exact ydif
      rw [mono₂];exact other_dif'' c

    }

    use by {
      refine ⟨Sᵢ.toEmbedding,?_⟩
      obtain ⟨e₁,e₁h⟩ := e₁;induction e₁ with
      | h x y =>
      intro a b;simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        SimpleGraph.deleteEdges_adj, SimpleGraph.Embedding.map_adj_iff, Set.mem_singleton_iff,
        Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, not_or, not_and,
        and_iff_left_iff_imp, IsEmpty.forall_iff]
      intro abe;contrapose Sᵢdcvu;simp_all only [not_and, Classical.not_imp, not_not];rw [Sym2Mem_isInRange]
      use s(a,b);simp_all only [Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      by_cases c : Sᵢ a = x ∧ Sᵢ b = y
      left;exact c
      right;apply Sᵢdcvu;simp_all only [not_and, not_false_eq_true, implies_true, forall_const, not_true_eq_false, imp_false]
    }

    unfold SimpleGraph.coloring.monochromatic at mono;unfold SimpleGraph.coloring.monochromatic;
    simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
    obtain ⟨c,mono⟩ := mono;use c;intro e ei;specialize mono e (by {
      simp_all only [Set.mem_range, not_exists, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
      induction e with
      | h x y => {
        simp_all only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet, SimpleGraph.deleteEdges_adj,
          SimpleGraph.Embedding.map_adj_iff, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff',
          Prod.mk.injEq, Prod.swap_prod_mk, not_or, not_and]
      }
    })
    have monoh : ¬ (e.map Sᵢ) = e₁ := by {
      by_contra c;induction e with
      | h x y => obtain ⟨e₁,e₁h⟩ := e₁;induction e₁ with
      | h v u =>
      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, dite_true,
        Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
        IsEmpty.forall_iff, dite_eq_left_iff]
      aesop
    }
    simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, dite_false]
  }

lemma lowMinDegree_imp_connectedEdges  {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [DecidableRel G.Adj] [Fintype U] [DecidableRel S.Adj] (isSs : ∀v : V,Supersingleton (G.neighborFinset v))
  : (∃v : V,∀u : U,(G.degree v) ≤ (S.degree u))
  → (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : S ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun))) := by {
    intro ⟨v,h⟩
    specialize isSs v
    have isSi := Classical.superinhabited_of_supersingelton (G.neighborFinset v);clear isSs
    use ⟨s(v,(default : (G.neighborFinset v)).val),?_⟩
    case w => skip;{
      have t : (default : (G.neighborFinset v)).val ∈ (G.neighborSet v) := Set.mem_toFinset.mp (default : (G.neighborFinset v)).property
      simp_all only [SimpleGraph.mem_neighborSet, SimpleGraph.mem_edgeSet]
    }
    use ⟨s(v,(other default : (G.neighborFinset v)).val),?_⟩
    case w => skip;{
      have t : (other default : (G.neighborFinset v)).val ∈ (G.neighborSet v) := Set.mem_toFinset.mp (other default : (G.neighborFinset v)).property
      simp_all only [SimpleGraph.mem_neighborSet, SimpleGraph.mem_edgeSet]
    }
    constructor
    {
      by_contra c;rw [← Subtype.val_inj] at c;simp_all only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk]
      cases c with
      | inl c => rw [Subtype.val_inj] at c;apply other_dif default at c;exact c
      | inr c => {
        replace c : (other default : (G.neighborFinset v)).val = (default : (G.neighborFinset v)).val  := by rw [← c.left,c.right]
        rw [Subtype.val_inj] at c;apply other_dif'' default at c;exact c
      }
    }
    {
      intro Sᵢ defInSᵢ
      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
      have vad : G.Adj v (default : (G.neighborFinset v)).val := by {
        have t := (default : (G.neighborFinset v)).property
        unfold SimpleGraph.neighborFinset SimpleGraph.neighborSet at t;simp_all only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
      }
      have vao : G.Adj v (other default : (G.neighborFinset v)).val := by {
        have t := (other default : (G.neighborFinset v)).property
        unfold SimpleGraph.neighborFinset SimpleGraph.neighborSet at t;simp_all only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
      }

      unfold Membership.mem instMembershipSym2Forall_test Sym2Mem Sym2.rec Quot.rec
      unfold Membership.mem instMembershipSym2Forall_test Sym2Mem Sym2.rec Quot.rec at defInSᵢ
      simp_all only [eq_rec_constant, true_and]
      unfold Membership.mem FunMem
      simp_all only

      obtain ⟨u,us⟩ : {u : U // Sᵢ u = v} := by {
        unfold Membership.mem FunMem at defInSᵢ
        simp_all only
        obtain ⟨uh,t⟩ := defInSᵢ
        use Classical.choose uh
        exact Classical.choose_spec uh
      }
      subst us

      have _ : DecidableEq V := Classical.typeDecidableEq V

      have t : ((S.neighborFinset u).image Sᵢ) ⊆ (G.neighborFinset (Sᵢ u)) := by {
        intro x xi
        simp_all only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        obtain ⟨xᵢ,xᵢa,xᵢm⟩ := xi;subst xᵢm
        exact (SimpleGraph.Embedding.map_adj_iff Sᵢ).mpr xᵢa
      }

      /-Finset.eq_iff_card_le_of_subset-/

      replace t : ((S.neighborFinset u).image Sᵢ) = (G.neighborFinset (Sᵢ u)) := by {
        specialize h u
        rw [← Finset.eq_iff_card_le_of_subset]
        {
          have s : (Finset.image (⇑Sᵢ) (S.neighborFinset u)).card = (S.neighborFinset u).card := by {
            rw [Finset.card_image_iff]
            intro x xh y yh ih;apply (RelEmbedding.injective Sᵢ);exact ih
          }
          rw [s]
          simp_all only [SimpleGraph.card_neighborFinset_eq_degree]
        }
        {
          exact t
        }
      }

      have odns : (other default : (G.neighborFinset (Sᵢ u))).val ∈ (G.neighborSet (Sᵢ u)) := vao
      replace odns : (other default : (G.neighborFinset (Sᵢ u))).val ∈ (G.neighborFinset (Sᵢ u)) :=
        (SimpleGraph.mem_neighborFinset G (Sᵢ u) (other default : (G.neighborFinset (Sᵢ u))).val).mpr vao

      conv at odns => lhs;rw [← t]
      clear t;simp_all only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
      obtain ⟨y,ya,yh⟩ := odns
      use y
    }
  }

lemma lowMinDegree_imp_connectedEdges'  {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Nonempty V] [DecidableRel G.Adj] [Fintype U] [DecidableRel S.Adj] (isSs : 2≤G.minDegree)
  : (G.minDegree ≤ S.minDegree)
  → (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : S ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun))) := by {
    intro md;apply lowMinDegree_imp_connectedEdges

    replace isSs : ∀v : V,2≤G.degree v := by
      intro v;trans G.minDegree;exact isSs;exact G.minDegree_le_degree v
    intro v;specialize isSs v
    unfold SimpleGraph.degree at isSs

    contrapose isSs
    simp_all only [SimpleGraph.mem_neighborFinset, not_nonempty_iff, not_le]
    apply Nat.lt_add_one_of_le
    rw [Finset.card_le_one]
    simp_all only [subsingleton_iff_notSuperSingleton, SimpleGraph.mem_neighborFinset]
    intro x vax y vay
    have t : (⟨x,vax⟩ : {x // G.Adj v x}) = ⟨y,vay⟩ := by subsingleton
    simp_all only [Subtype.mk.injEq]

    have ⟨v,vh⟩ := G.exists_minimal_degree_vertex
    use v;intro u;rw [← vh];clear vh
    trans S.minDegree;exact md
    exact S.minDegree_le_degree u
  }

lemma SimpleGraph.embedding_degreeLE {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U) (Sᵢ : S ↪g G)
  [Fintype V] [Nonempty V] [DecidableRel G.Adj] [Fintype U] [DecidableRel S.Adj]
  (u : U)
  : (S.degree u) ≤ (G.degree (Sᵢ u)) := by {
    unfold SimpleGraph.degree
    have r : (S.neighborFinset u).card=(Finset.map (Sᵢ : U ↪ V) (S.neighborFinset u)).card :=
      Eq.symm (Finset.card_map { toFun := ⇑Sᵢ, inj' := instCoeDepEmbeddingEmbedding_test.proof_1 Sᵢ })
    rw [r];apply Finset.card_le_card
    simp_all only [card_neighborFinset_eq_degree, Finset.card_map]
    intro x
    simp_all only [Finset.mem_map, mem_neighborFinset, Function.Embedding.coeFn_mk, forall_exists_index, and_imp]
    intro y uay yix;subst yix
    exact (Embedding.map_adj_iff Sᵢ).mpr uay
  }

lemma strictLowMinDegree_imp_isolatedVertex  {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V]  [DecidableRel G.Adj] [Fintype U] [DecidableRel S.Adj] [Nonempty V]
  : (G.minDegree < S.minDegree)
  → (∃ v : V,∀copy : S ↪g G,v ∉ (Set.range copy)) := by {
    intro lt

    have ⟨v,vh⟩ := G.exists_minimal_degree_vertex
    use v;intro Sᵢ;simp_all only [Set.mem_range, not_exists];intro u
    have ud := S.minDegree_le_degree u
    replace lt : G.degree v < S.degree u := by calc
        _ < S.minDegree := lt
        _ ≤ _ := ud
    contrapose lt;simp_all only [ne_eq, not_not, not_lt];rw [← lt];clear lt
    exact SimpleGraph.embedding_degreeLE G S Sᵢ u
  }

/-discussed in notes as P₃-/
lemma singularEdge_imp_notMinRamsey {V U : Type} (C : Type) [Supersingleton C] (G : SimpleGraph V) (S : SimpleGraph U) [Supersingleton S.edgeSet]
  : (∃e : G.edgeSet, (∃! copy : S ↪g G,e.val ∈ copy.toFun)) → ¬(G.minimal_ramsey C S) := by {
    have _ := Classical.superinhabited_of_supersingelton S.edgeSet

    /-As per our assumption, we introduce an edge e and a unique copy of S, Sᵢ which contains e-/
    intro ⟨⟨e,ei⟩,Sᵢ,h,unique⟩;apply connectedEdges_imp_notMinRamsey C G S
    simp_all only;rw [Sym2Mem_isInRange] at h;obtain ⟨e,s2m⟩ := h;subst s2m
    use ⟨e.map Sᵢ,ei⟩
    have ei' := ei;rw [← Sᵢ.map_edge_iff'] at ei';use ⟨(other (⟨e,ei'⟩ : S.edgeSet)).val.map Sᵢ,?_⟩
    case w => rw [← Sᵢ.map_edge_iff];exact (other (⟨e,ei'⟩ : S.edgeSet)).property
    constructor
    {
      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, ne_eq, Subtype.mk.injEq]
      have t : e ≠ (other (⟨e,ei'⟩ : S.edgeSet)).val := by {
        by_contra c;
        have ee : e=(⟨e,ei'⟩ : S.edgeSet).val := by rfl
        conv at c => lhs;rw [ee];;rw [Subtype.val_inj] at c;contrapose c;exact other_dif (⟨e,ei'⟩ : S.edgeSet)
      }
      contrapose t;simp_all only [not_not]
      have inj : (Sym2.map ⇑Sᵢ).Injective := by apply Sym2.map.injective;exact RelEmbedding.injective Sᵢ
      apply inj;exact t
    }
    {
      intro copy2 h;specialize unique copy2 ?_;simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
      subst unique;rw [Sym2Mem_isInRange];use (other (⟨e, ei'⟩ : S.edgeSet)).val;simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
    }
  }

lemma semirelevantEdge_imp_notMinRamsey {V U : Type} (C : Type) [Supersingleton C] (G : SimpleGraph V) (S : SimpleGraph U) [Supersingleton S.edgeSet]
  : (∃e : G.edgeSet,Subsingleton {copy : S ↪g G // e.val ∈ copy.toFun}) → ¬(G.minimal_ramsey C S) := by {
    intro ⟨e,h⟩
    by_cases ne : Nonempty {copy : S ↪g G // ↑e ∈ copy.toFun }
    {
      have copy := (Classical.inhabited_of_nonempty ne).1
      apply singularEdge_imp_notMinRamsey;use e;use copy;
      constructor
      {
        simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, nonempty_subtype]
        exact copy.property
      }
      {
        intro y yh
        have ys : y = (⟨y,yh⟩ : {copy : S ↪g G // ↑e ∈ copy.toFun }).val :=
          by simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, nonempty_subtype]
        rw [ys];rw [Subtype.val_inj];subsingleton
      }

    }
    {
      apply irrelevantEdge_imp_notMinRamsey;use e;intro copy
      simp_all only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, nonempty_subtype, not_exists, not_false_eq_true]
    }
  }

instance connectedEdges_decidable {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Decidable (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : S ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun))) := by infer_instance


/-should be talked about as P₅-/
lemma emptyVertices_imp_notMinRamsey {V U : Type} (C : Type) (G : SimpleGraph V) (S : SimpleGraph U)
  : ((IsEmpty V) ∧ (Nonempty U)) → ¬(G.minimal_ramsey C S) := by {
    unfold SimpleGraph.minimal_ramsey;simp_all only [RelHom.coe_fn_toFun, not_and, not_forall, Classical.not_imp, not_exists]
    intro ⟨Ve,Une⟩;intro ramsey;exfalso;exact emptyVertices_imp_notRamsey C G S ⟨Ve,Une⟩ ramsey
  }

instance nonempty_decidable {T : Type} [F : Fintype T] : Decidable (Nonempty T) := by {
  obtain ⟨⟨l,nd⟩,c⟩ := F
  revert l;apply Multiset.rec
  case mk.mk.C_0 => intro nd c;refine isFalse ?_;simp_all only [Finset.mk_zero, Finset.not_mem_empty, not_nonempty_iff];refine ⟨?_⟩;exact c
  case mk.mk.C_cons => intro head tail ih nd c;refine isTrue ?_;use head
  case mk.mk.C_cons_heq => intro head₁ head₂ tail ih;{
    simp_all only [Finset.mk_cons]
    refine Function.hfunext ?_ ?_
    aesop
    intro n₁ n₂ n₃
    refine Function.hfunext ?_ ?_
    simp_all only [heq_eq_eq, Finset.mem_cons, Finset.mem_mk, eq_iff_iff]
    simp_all only [Multiset.nodup_cons, Multiset.mem_cons, not_or, or_false, not_false_eq_true, and_self, and_true]
    obtain ⟨left, right⟩ := n₁
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    apply Iff.intro
    · intro a x
      specialize a x;cases a with
      | inl h =>
        subst h
        simp_all only [or_false, or_true]
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          simp_all only [or_self, or_false]
        | inr h_2 => simp_all only [or_true]
    · intro a x
      specialize a x;cases a with
      | inl h =>
        subst h
        simp_all only [or_false, or_true]
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          simp_all only [or_self, or_false]
        | inr h_2 => simp_all only [or_true]
    intro h₁ h₂ h₃;simp_all only [heq_eq_eq, implies_true]
  }
}

instance emptyVertices_decidable {V U : Type}
  [Fintype V] [Fintype U]
  : Decidable ((IsEmpty V) ∧ (Nonempty U)) := by {
    refine @instDecidableAnd ?_ ?_ ?_ ?_
    apply decidable_not;simp_all only [not_isEmpty_iff]
    infer_instance;infer_instance
  }

def minimal_ramsey_conditions {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U) : Prop
  := (∃ v : V,∀copy : S ↪g G,v ∉ (Set.range copy))
  ∨ (∃e : G.edgeSet,Subsingleton {copy : S ↪g G // e.val ∈ copy.toFun})
  ∨ (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : S ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun)))
  ∨ ((IsEmpty V) ∧ (Nonempty U))

lemma minimal_ramsey_conditions_imp_notMinRamsey {V U : Type} (C : Type) (G : SimpleGraph V) (S : SimpleGraph U)
  [Supersingleton C] [Supersingleton S.edgeSet]
  : (minimal_ramsey_conditions G S) → ¬(G.minimal_ramsey C S) := by {
    unfold minimal_ramsey_conditions
    intro h;cases h with
    | inl h => apply irrelevantVertex_imp_notMinRamsey;exact h
    | inr h => cases h with
    | inl h => apply semirelevantEdge_imp_notMinRamsey;exact h
    | inr h => cases h with
    | inl h => apply connectedEdges_imp_notMinRamsey;exact h
    | inr h => apply emptyVertices_imp_notMinRamsey;exact h
  }



instance minimal_ramsey_conditions_decidable {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Decidable (minimal_ramsey_conditions G S) := if h₁ : (∃v : V,∀u : U,(G.degree v) ≤ (S.degree u)) ∧ ∀ (v : V), Supersingleton ↑(G.neighborFinset v)
    then isTrue (Or.inr (Or.inr (Or.inl (lowMinDegree_imp_connectedEdges G S h₁.right h₁.left))))
    else if h₂ : (∃ v : V,∀copy : S ↪g G,v ∉ (Set.range copy))
    then isTrue (Or.inl h₂)
    else if h₃ : (∃e : G.edgeSet,Subsingleton {copy : S ↪g G // e.val ∈ copy.toFun})
    then isTrue (Or.inr (Or.inl h₃))
    else if h₄ : (∃e₁ e₂ : G.edgeSet, (e₁ ≠ e₂) ∧ (∀copy : S ↪g G, (e₁.val ∈ copy.toFun) → (e₂.val ∈ copy.toFun)))
    then isTrue (Or.inr (Or.inr (Or.inl h₄)))
    else if h₅ : IsEmpty V ∧ Nonempty U
    then isTrue (Or.inr (Or.inr (Or.inr h₅)))
    else isFalse (by {
      unfold minimal_ramsey_conditions
      simp_all only [not_and, not_forall, forall_exists_index, Set.mem_range, not_exists,
        Decidable.not_not, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        Subtype.exists, exists_prop, ne_eq, exists_and_right, Subtype.mk.injEq, Classical.not_imp,
        and_imp, not_nonempty_iff, Subtype.coe_prop, exists_false, false_or, not_or, implies_true,
        not_false_eq_true, and_self]
    })

def DGraph_isoClass_minimal_ramsey_conditions {V U : Type} (G : Quotient (DGraph.hasIso (V:=V))) (S : SimpleGraph U)
  : Prop := by {
  apply Quotient.lift (s:=DGraph.hasIso (V:=V)) (fun G : DGraph V ↦  (minimal_ramsey_conditions G.toSimpleGraph S)) ?_ G
  intro G H iso
  unfold HasEquiv.Equiv instHasEquivOfSetoid at iso;simp only at iso
  unfold DGraph.hasIso at iso;simp_all only [eq_iff_iff];obtain ⟨iso⟩ := iso
  unfold minimal_ramsey_conditions
  constructor;rename DGraph V => G;rename_i H;have iso := iso.symm
  all_goals {
    intro h;cases h with
    | inl h => {
      left
      sorry/-prove that each condition is invariant-/
    }
    | inr h => cases h with
    | inl h => {
      right;left
      sorry/-prove that each condition is invariant-/
    }
    | inr h => {
      right;right
      sorry/-prove that each condition is invariant-/
    }
  }
}

lemma DGraph_isoClass.minimal_ramsey_conditions_iff {V U : Type} (G : DGraph V) (S : SimpleGraph U)
  : (minimal_ramsey_conditions G.toSimpleGraph S) ↔ (DGraph_isoClass_minimal_ramsey_conditions ⟦G⟧ S)
  := by unfold DGraph_isoClass_minimal_ramsey_conditions;simp_all only [Quotient.lift_mk]

instance DGraph_isoClass.minimal_ramsey_conditions_decidable {V U : Type} (G : Quotient (DGraph.hasIso (V:=V))) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Decidable (DGraph_isoClass_minimal_ramsey_conditions G S) := by {
    revert G;apply Quotient.rec;subsingleton
    intro G
    exact decidable_of_decidable_of_iff (DGraph_isoClass.minimal_ramsey_conditions_iff G S)
  }



lemma SimpleGraph.lowMinDegree_imp_minimal_ramsey_conditions {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [DecidableRel G.Adj] [Fintype U] [DecidableRel S.Adj] (Ssufficient : 2≤S.minDegree)
  : (G.minDegree ≤ S.minDegree)
  → minimal_ramsey_conditions G S  := by {
    intro h
    by_cases ne : Nonempty V
    {
      by_cases lt2 : G.minDegree<2
      {
        unfold minimal_ramsey_conditions;left
        apply strictLowMinDegree_imp_isolatedVertex
        calc
          _ < 2 := lt2
          2 ≤ _ := Ssufficient
      }
      {
        unfold minimal_ramsey_conditions;right;right;left
        apply lowMinDegree_imp_connectedEdges'
        simp only [not_lt] at lt2;exact lt2
        exact h
      }
    }
    {
      have Ue : Nonempty U := by {
        contrapose Ssufficient
        simp_all only [not_nonempty_iff, minDegree_of_isEmpty, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true]
      }
      simp_all only [not_nonempty_iff, minDegree_of_isEmpty, zero_le]
      unfold minimal_ramsey_conditions;right;right;right;exact ⟨ne, Ue⟩
    }
  }




end minimal_ramsey
