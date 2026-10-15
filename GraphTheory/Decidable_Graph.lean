

import Test.GraphTheory
import Test.Fin_Function

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Multiset.Functor

variable {n : ℕ} {V : Type}

section specific_examples

instance emptyGraphDecidable (G : Graph (Fin 0)) : DecidableRel G.Adj := by intro v;apply finZeroElim v

instance singletonGraphDecidable (G : Graph (Fin 1)) : DecidableRel G.Adj := by intro v u;refine isFalse ?_;finCases v;apply finZeroElim v;finCases u;apply finZeroElim u;exact SimpleGraph.irrefl G

instance bottomDecidable : DecidableRel (⊥ : Graph V).Adj := by intro v u;refine isFalse ?_;simp_all only [SimpleGraph.bot_adj, not_false_eq_true]

instance topDecidable [d : DecidableEq V] : DecidableRel (⊤ : Graph V).Adj := by
  intro v u;by_cases h : v=u;refine isFalse ?_;simp_all only [SimpleGraph.irrefl, not_false_eq_true];refine isTrue ?_;simp_all only [SimpleGraph.top_adj, ne_eq, not_false_eq_true]

end specific_examples
section edgeSet

def Decidable_Graph_edgeSet_dec (G : Graph V) [dec : DecidableRel G.Adj] : (x : (V×V))→Decidable (G.edgeSet (Sym2.mk x)) := by {
  intro x
  cases x with
  | mk x y =>
  have test : SimpleGraph.edgeSet G s(x, y) ↔ s(x,y)∈G.edgeSet := by {
    exact Eq.to_iff rfl
  }
  rw [test]
  simp_all only [SimpleGraph.mem_edgeSet]
  exact dec x y
}

def Graph.edgeList {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] : List ((Fin n)×(Fin n)) := (fun x => G.edgeSet (Sym2.mk x)).filt (δ := Decidable_Graph_edgeSet_dec G) (Complete_UnorderedPairFin_List n)

lemma mem_Graph_edgeList {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] (v u : Fin n) : (⟨v,u⟩∈G.edgeList ∨ ⟨u,v⟩∈G.edgeList)↔G.Adj v u := by {
  unfold Graph.edgeList;simp_all only [mem_funcFilt]
  trans SimpleGraph.edgeSet G s(v, u)
  trans ((v, u) ∈ Complete_UnorderedPairFin_List n ∨ (u, v) ∈ Complete_UnorderedPairFin_List n) ∧ SimpleGraph.edgeSet G s(u, v)
  constructor
  {
    intro h;cases h with
    | inl h => constructor;left;exact h.left;have t : s(v,u)=s(u,v) := Sym2.eq_swap;rw [t] at h;exact h.right
    | inr h => constructor;right;exact h.left;exact h.right
  }
  {
    intro ⟨h,t⟩;cases h with
    | inl h => left;constructor;exact h;have t1 : s(v,u)=s(u,v) := Sym2.eq_swap;rw [t1];exact t
    | inr h => right;constructor;exact h;exact t
  }
  trans SimpleGraph.edgeSet G s(u, v)
  {
    constructor;intro h;exact h.right;intro h
    constructor
    exact unorderedPairFin_List_complete_noQuot v u
    exact h
  }
  have t1 : s(v,u)=s(u,v) := Sym2.eq_swap;rw [t1]
  exact Eq.to_iff rfl
}

lemma mem_Graph_edgeList' {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] (v u : Fin n) (h : ⟨v,u⟩∈G.edgeList) : G.Adj v u := by rw [← mem_Graph_edgeList];left;exact h

def Graph.edgeList_symm {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] : List ((Fin n)×(Fin n)) := G.edgeList ++ ((fun x => ⟨x.2,x.1⟩).lf G.edgeList)

@[simp]lemma mem_Graph_edgeList_symm {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] (v u : Fin n) : ⟨v,u⟩∈G.edgeList_symm ↔ G.Adj v u := by {
  trans (⟨v,u⟩∈G.edgeList ∨ ⟨u,v⟩∈G.edgeList)
  unfold Graph.edgeList_symm;simp_all only [List.mem_append, mem_listFun, Prod.mk.injEq, Prod.exists]
  have t : (∃ a b, (a, b) ∈ G.edgeList ∧ v = b ∧ u = a) ↔ (u, v)∈G.edgeList := by constructor;intro ⟨a,b,h,s,t⟩;subst s t;exact h;intro h;use u;use v
  rw [t]
  exact mem_Graph_edgeList G v u
}

@[simp]lemma Graph_edgeList_symm_length {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] : G.edgeList_symm.length= 2 * G.edgeList.length := by
  unfold Graph.edgeList_symm;simp_all only [List.length_append, listFun_length];exact Eq.symm (Nat.two_mul G.edgeList.length)


def List.to_graph {n : ℕ} (E : List ((Fin n)×(Fin n))) : Graph (Fin n) where
  Adj (v u : Fin n) := by by_cases v=u;exact False;exact ⟨v,u⟩∈E ∨ ⟨u,v⟩∈E

instance List_to_graph_Decidable {n : ℕ} (E : List ((Fin n)×(Fin n))) : DecidableRel E.to_graph.Adj := by {
  intro v u;unfold List.to_graph
  simp_all only [dite_eq_ite, if_false_left]
  refine decidable_and ?_ ?_
  refine decidable_not ?_;simp_all only [Decidable.not_not];exact decEq v u
  refine decidable_or ?_ ?_
  exact List.instDecidableMemOfLawfulBEq (v, u) E
  exact List.instDecidableMemOfLawfulBEq (u, v) E
}

@[simp]lemma List_to_graph_Adj {n : ℕ} (E : List ((Fin n)×(Fin n))) (v u : Fin n) : E.to_graph.Adj v u ↔ ¬v=u ∧ (⟨v,u⟩∈E ∨ ⟨u,v⟩∈E) := by unfold List.to_graph;simp_all only [dite_eq_ite, if_false_left]

lemma graph_edgeList_identity {n : ℕ} (G : Graph (Fin n)) [DecidableRel G.Adj] : G.edgeList.to_graph=G := by {
  rw [← SimpleGraph.adj_inj];ext v u;simp_all only [List_to_graph_Adj];rw [mem_Graph_edgeList]
  constructor;intro h;exact h.right;intro h;constructor;exact SimpleGraph.Adj.ne' (id (SimpleGraph.adj_symm G h));exact h
}

end edgeSet
section equal_decidable

def Graph_DecidableEq {n : ℕ} (G H : Graph (Fin n)) [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] : Decidable (G=H) := by {
  rw [← SimpleGraph.adj_inj]
  replace t : Decidable (∀ v u, G.Adj v u = H.Adj v u) := by infer_instance
  cases t with
  | isFalse h => refine isFalse ?_;contrapose h;simp_all only [SimpleGraph.adj_inj, not_not, implies_true, not_true_eq_false, not_false_eq_true]
  | isTrue h => refine isTrue ?_;ext v u;specialize h v u;simp_all only [eq_iff_iff]
}

end equal_decidable
section isomorphism_decidable


def local_homomorphismDecidable {n : ℕ} {m : ℕ} (f : (Fin n)→(Fin m)) (G : Graph (Fin n)) (H : Graph (Fin m)) [Gdec : DecidableRel G.Adj] [Hdec : DecidableRel H.Adj]: (v u : Fin n)→(Decidable ((H.Adj (f v) (f u))↔ (G.Adj v u))) := by {
  intro v u
  cases Gdec v u with
  | isFalse Gadj => {
    cases Hdec (f v) (f u) with
    | isFalse Hadj => {
      refine isTrue ?_
      simp_all only
    }
    | isTrue Hadj => {
      refine isFalse ?_
      simp_all only [iff_false, not_true_eq_false, not_false_eq_true]
    }
  }
  | isTrue Gadj => {
    cases Hdec (f v) (f u) with
    | isFalse h => {
      refine isFalse ?_
      simp_all only [iff_true, not_false_eq_true]
    }
    | isTrue h => {
      refine isTrue ?_
      simp_all only
    }
  }
}

/-completeForallDecidable-/
def homomorphismDecidable {n : ℕ} {m : ℕ} (f : (Fin n)→(Fin m)) (G : Graph (Fin n)) (H : Graph (Fin m)) [DecidableRel G.Adj] [DecidableRel H.Adj]: Decidable (∀ v u : Fin n, ((H.Adj (f v) (f u))↔ (G.Adj v u))) := forall_fin_decidable

def iso_Cexists_decidable {n : ℕ} (G H : Graph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (f : (Fin n)→(Fin n)) : Cexists_Decidable (fun iso : G ≃g H => iso.toFun=f) := by {
  have isEquiv := finEquivCexists_Decidable f
  cases isEquiv with
    | CE_isFalse h => {
      refine .CE_isFalse ?_
      simp_all only [Equiv.toFun_as_coe, not_exists, RelIso.coe_fn_toEquiv]
      intro iso
      replace h := h iso.toEquiv
      simp_all only [RelIso.coe_fn_toEquiv, not_false_eq_true]
    }
    | CE_isTrue equiv equivIsF => {
      have homoDec := homomorphismDecidable f G H
      cases homoDec with
      | isFalse homoDec => {
        refine .CE_isFalse ?_
        simp_all only [Equiv.toFun_as_coe, not_forall, RelIso.coe_fn_toEquiv, not_exists]
        intro iso
        obtain ⟨v,u,homoDec⟩ := homoDec
        have test := (iso.map_rel_iff' (a := v) (b := u))
        contrapose homoDec
        simp_all only [RelIso.coe_fn_toEquiv, ne_eq, Decidable.not_not, not_not]
      }
      | isTrue isHomo => {
        refine .CE_isTrue ?_ ?_
        use equiv
        intro v u
        replace isHomo := isHomo v u
        rw [← equivIsF] at isHomo
        simp_all only [Equiv.toFun_as_coe]
        rw [equivIsF]
      }
    }
}

instance iso_decidable {n : ℕ} (G H : Graph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (f : (Fin n)→(Fin n)) : Decidable (∃iso : G ≃g H, iso.toFun=f) := by {
    have isEquiv := finEquivDecidable f
    cases isEquiv with
    | isFalse h => {
      refine isFalse ?_
      simp_all only [Equiv.toFun_as_coe, not_exists, RelIso.coe_fn_toEquiv]
      intro iso
      replace h := h iso.toEquiv
      simp_all only [RelIso.coe_fn_toEquiv, not_false_eq_true]
    }
    | isTrue isEquiv => {
      have homoDec := homomorphismDecidable f G H
      cases homoDec with
      | isFalse homoDec => {
        refine isFalse ?_
        simp_all only [Equiv.toFun_as_coe, not_forall, RelIso.coe_fn_toEquiv, not_exists]
        intro iso
        obtain ⟨v,u,homoDec⟩ := homoDec
        have test := (iso.map_rel_iff' (a := v) (b := u))
        contrapose homoDec
        simp_all only [RelIso.coe_fn_toEquiv, ne_eq, Decidable.not_not, not_not]
      }
      | isTrue isHomo => {
        refine isTrue ?_
        obtain ⟨equiv,equivIsF⟩ := isEquiv
        use ⟨equiv,?_⟩
        intro v u
        replace isHomo := isHomo v u
        rw [← equivIsF] at isHomo
        simp_all only [Equiv.toFun_as_coe]
      }
    }
}

def check_list_for_iso_help {n : ℕ} (list : List ((Fin n)→(Fin n))) (G H : Graph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (comp : List ((Fin n)→(Fin n))) (compₕ : ¬(∃f ∈ comp,(∃iso : G ≃g H, iso.toFun=f)))
  : Decidable (∃f∈(comp++list),(∃iso : G ≃g H, iso.toFun=f)) := match list with
  | [] => by refine isFalse ?_;simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, not_exists, not_and, List.append_nil, exists_false, not_false_eq_true, implies_true]
  | head :: tail => if h : ∃iso : G ≃g H,iso.toFun = head
  then isTrue (by use head;constructor;exact List.mem_append_cons_self;exact h)
  else let t := check_list_for_iso_help tail G H (comp++[head]) (by {
    simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, not_exists, not_and, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro f h;cases h with
    | inl h => exact compₕ f h
    | inr h => subst h;exact h
  });by rw [List.append_cons];exact t


instance check_list_for_iso {n : ℕ} (list : List ((Fin n)→(Fin n))) (G H : Graph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] : Decidable (∃f∈list,(∃iso : G ≃g H, iso.toFun=f))
  := check_list_for_iso_help list G H [] (by {simp_all only [List.not_mem_nil, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, false_and, exists_false, not_false_eq_true]})

instance check_finset_for_iso {n : ℕ} (list : Finset ((Fin n)→(Fin n))) (G H : Graph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] : Decidable (∃f∈list,(∃iso : G ≃g H, iso.toFun=f))
  := by {
    obtain ⟨list,nd⟩ := list;revert list;apply Quotient.rec;subsingleton;intro list nd;
    exact check_list_for_iso_help list G H [] (by {simp_all only [List.not_mem_nil, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, false_and, exists_false, not_false_eq_true]})
  }

instance iso_exists_decidable {n : ℕ} (G H : Graph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] : Decidable (graphIsoExists G H) := by {
    have test := check_finset_for_iso Finset.univ G H
    cases test with
    | isFalse h => {
      refine isFalse ?_
      simp_all only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, not_exists, not_and,
        not_true_eq_false]
      intro iso
      obtain ⟨iso,_⟩ := iso
      specialize h iso (Finset.mem_univ ⇑iso) iso
      contrapose h
      simp_all only [not_false_eq_true, not_true_eq_false]
    }
    | isTrue h => {
      refine isTrue ?_
      obtain ⟨trash,trash,iso,trash⟩ := h
      use iso

    }

  }

end isomorphism_decidable
section decidable_representative

noncomputable def Graph.noncomp_edgeList {n : ℕ} (G : Graph (Fin n)) : List ((Fin n)×(Fin n)) := by have t : DecidableRel G.Adj := Classical.decRel G.Adj;exact G.edgeList

noncomputable def Graph.dec_rep {n : ℕ} (G : Graph (Fin n)) : (Graph (Fin n)) := G.noncomp_edgeList.to_graph

lemma Graph.dec_rep_equal {n : ℕ} (G : Graph (Fin n)) : G.dec_rep=G := by {
  unfold Graph.dec_rep Graph.noncomp_edgeList
  have t : DecidableRel G.Adj := Classical.decRel G.Adj;simp_all only
  rw [← SimpleGraph.adj_inj];ext v u;simp_all only [List_to_graph_Adj];rw [mem_Graph_edgeList]
  constructor;intro h;exact h.right;intro h;constructor;exact SimpleGraph.Adj.ne' (id (SimpleGraph.adj_symm G h));exact h
}



end decidable_representative
section decidable_graph_image



/-
def listMultiunion_decidable_graph_domain_mod {n : ℕ} {l : List (List (Graph (Fin n)))} (preDec : (X : List (Graph (Fin n)))→(X∈l)→(G : Graph (Fin n))→(G∈X)→(DecidableRel G.Adj))
  : List (List ((G : Graph (Fin n))×(DecidableRel G.Adj))) := by {
    induction l with
    | nil => exact []
    | cons head tail ih => {
      have f : {G : Graph (Fin n) // G∈head}→((G : Graph (Fin n))×(DecidableRel G.Adj)) := fun x => ⟨x,?_⟩
      case cons.refine_1 => exact preDec head (by simp_all only [List.mem_cons, true_or]) x.val x.property
      have temp : (fun x => x∈head).pass head := by intro x;simp_all only [implies_true]
      have t := f.lf (toSubtypeList head temp)
      refine (t :: (ih ?_))
      clear t temp f ih
      intro X Xi G Gi;exact preDec X (by simp_all only [List.mem_cons, or_true]) G Gi
    }
  }

lemma test1 {n : ℕ} {l : List (List (Graph (Fin n)))} (preDec : (X : List (Graph (Fin n)))→(X∈l)→(G : Graph (Fin n))→(G∈X)→(DecidableRel G.Adj))
  : (fun x => x.val).lf (listMultiunion (listMultiunion_decidable_graph_domain_mod preDec)) = (listMultiunion l) := by {
   unfold listMultiunion_decidable_graph_domain_mod
   simp_all only [Function.const_apply]
   induction l with
   | nil => simp_all only [listMultiunion_nil, listFun_nil]
   | cons head tail ih => {
    simp_all only [listMultiunion_cons]
   }
  }

def listMultiunion_decidable_graph {n : ℕ} {l : List (List (Graph (Fin n)))} (preDec : (X : List (Graph (Fin n)))→(X∈l)→(G : Graph (Fin n))→(G∈X)→(DecidableRel G.Adj)) {H : Graph (Fin n)} (h : H∈listMultiunion l)
  : DecidableRel H.Adj := by {
    simp_all only [mem_listMultiunion]
    const_cases h;rename_i h



    have t : DecidableEq { x // x ∈ listMultiunion l } := by {
      clear h H
      intro ⟨x,xh⟩ ⟨y,yh⟩
      simp_all only [mem_listMultiunion, Subtype.mk.injEq]
      simp_all only [mem_listMultiunion, Subtype.mk.injEq]
      have t : DecidablePred fun (x_1 : {m : List (Graph (Fin n)) // m∈l}) ↦ x ∈ x_1.val := by {
        clear xh yh
        intro ⟨m,mh⟩;simp_all only
        specialize preDec m mh x
      }
      const_cases xh;rename_i xh
      have t : DecidablePred fun (x_1 : {m : List (Graph (Fin n)) // m∈l}) ↦ y ∈ x_1.val := sorry
      const_cases yh;rename_i yh
      have xd : DecidableRel x.Adj := preDec xh.val xh.property.left x xh.property.right
      have yd : DecidableRel y.Adj := preDec yh.val yh.property.left y yh.property.right
      exact FD_Graph_DecidableEq x y
    }
    have t : DecidablePred (fun (X : {X : List (Graph (Fin n)) // X∈l}) => H∈X.val) := fun X => memDecidable' H X (ε := fun A => A∈listMultiunion l) h ?_
    simp_all only [mem_listMultiunion]
    const_cases h;rename_i x
    exact preDec x.val x.property.left H x.property.right
    {
      clear h;obtain ⟨X,h⟩ := X
      simp_all only [mem_listMultiunion]
      intro G GiX;use X
    }
  }
-/

/-def listMultiunion_decidable_graph {n : ℕ} {l : List (List (Graph (Fin n)))} (preDec : (X : {X : List (Graph (Fin n)) //X∈l})→(G : {G : Graph (Fin n) // G∈X.val})→(DecidableRel G.val.Adj))
{H : Graph (Fin n)} (h : H ∈c listMultiunion l) : DecidableRel H.Adj := by {
    sorry
  }-/

end decidable_graph_image
section neighbors

def Graph.neighborList {n : ℕ} (G : Graph (Fin n)) [d : DecidableRel G.Adj] (v : Fin n) : List (Fin n):= (fun u => G.Adj v u).filt (Complete_Fin_List n)

@[simp]lemma mem_NeighborList {n : ℕ} (G : Graph (Fin n)) [d : DecidableRel G.Adj] (v : Fin n) (u : Fin n) : u∈(G.neighborList v) ↔ (G.Adj v u) := by
  unfold Graph.neighborList;simp_all only [mem_funcFilt, and_iff_right_iff_imp];intro v;exact CFL_complete u

/-funcFilt_list_func-/
@[simp]lemma neighborList_mapped_iso {G H : Graph (Fin n)} [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H) (v : Fin n) : (f.lf (G.neighborList v)) ≅l (H.neighborList (f v)) := by {
  unfold Graph.neighborList SimpleGraph.Iso.lf
  have t : (Complete_Fin_List n)=f.lf (f.symm.lf (Complete_Fin_List n)) := by {
    simp_all only [listFun_composition, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv]
    have t : ⇑f ∘ ⇑f.symm = id := by ext x;simp_all only [Function.comp_apply, RelIso.apply_symm_apply, id_eq]
    rw [t,listFun_id]
  }
  conv => rhs;rw [t]
  rw [funcFilt_list_func]


  have e : (Function.filt (fun u ↦ G.Adj v u) (Complete_Fin_List n)) ≅l (Function.filt (fun x ↦ H.Adj (f v) (f.toFun x)) (f.symm.lf (Complete_Fin_List n))) := by {
    have e : (fun u ↦ G.Adj v u) = (fun x ↦ H.Adj (f v) (f.toFun x)) := by ext u;rw [← f.map_rel_iff'];rfl

    conv => rhs; lhs;rw [← e]
    have e : (Complete_Fin_List n) ≅l (f.symm.lf (Complete_Fin_List n)) := by {
      intro u;have t : u=f.symm (f u) :=  Eq.symm (RelIso.symm_apply_apply f u)
      conv => rhs;rw [t]
      have inj := (isoIsBijective f.symm).injective
      have c := mem_listFun_injective f.symm (f u) (Complete_Fin_List n) inj
      unfold SimpleGraph.Iso.lf;have s : (⇑f.symm)=f.symm.toFun := by rfl;;rw [s] at c;have s : f.symm (f u)=f.symm.toFun (f u) := inj (inj (inj (inj rfl)));rw [s]
      rw [c];constructor;intro h;exact CFL_complete (f u);intro h;exact CFL_complete u
    }
    intro u
    constructor
    {
      intro h;rw [mem_funcFilt];constructor
      {
        have t : u=f.symm (f u) :=  Eq.symm (RelIso.symm_apply_apply f u)
        rw [t]
        have inj := (isoIsBijective f.symm).injective
        have c := mem_listFun_injective f.symm (f u) (Complete_Fin_List n) inj
        unfold SimpleGraph.Iso.lf;have s : (⇑f.symm)=f.symm.toFun := by rfl;;rw [s] at c;have s : f.symm (f u)=f.symm.toFun (f u) := inj (inj (inj (inj rfl)));rw [s]
        rw [c];exact CFL_complete (f u)
      }
      rw [mem_funcFilt] at h;exact h.right
    }
    {
      intro h;rw [mem_funcFilt];constructor;exact CFL_complete u;rw [mem_funcFilt] at h;exact h.right
    }
  }
  intro u;rw [mem_listFun];conv => rhs;rw [mem_listFun];;
  constructor
  intro ⟨y,⟨hl,hr⟩⟩;rw [e] at hl;use y
  intro ⟨y,⟨hl,hr⟩⟩;rw [← e] at hl;use y
}

lemma neighborList_nodup {n : ℕ} (G : Graph (Fin n)) [d : DecidableRel G.Adj] (v : Fin n) : (G.neighborList v).Nodup := by
  unfold Graph.neighborList;refine funcFilt_Nodup (fun u ↦ G.Adj v u) Complete_Fin_List_Nodup


end neighbors
section reduce_graph

def Graph.reduce_by_last (G : Graph (Fin (n+1))) : Graph (Fin n) :=
  ⟨fun u v => G.Adj u.castSucc v.castSucc,by intro u v h;symm;exact h,by intro v;simp_all only [SimpleGraph.irrefl, not_false_eq_true]⟩

@[simp]lemma Graph.reduce_by_last_Adj (G : Graph (Fin (n+1))) (v u : Fin n) : G.reduce_by_last.Adj v u ↔ G.Adj v.castSucc u.castSucc := by
  unfold Graph.reduce_by_last;simp_all only

instance reduce_by_last_decidable (G : Graph (Fin (n+1))) [Gd : DecidableRel G.Adj] : DecidableRel G.reduce_by_last.Adj := by intro v u; rw [G.reduce_by_last_Adj];apply Gd

end reduce_graph

section DGraph

structure DGraph (V : Type) extends (SimpleGraph V) where
  dec : DecidableRel Adj

lemma DGraph_eq {V : Type} (G H : DGraph V) : (G.toSimpleGraph=H.toSimpleGraph) ↔ (G=H) := by
  obtain ⟨G,Gd⟩ := G;obtain ⟨H,Hd⟩ := H;simp_all only [DGraph.mk.injEq, iff_self_and];intro s;subst s;simp_all only [heq_eq_eq];subsingleton

instance SimpleGraph.Dcast {V : Type} (G : SimpleGraph V) [D : DecidableRel G.Adj]: CoeDep (SimpleGraph V) G (DGraph V) := ⟨⟨G,D⟩⟩
@[simp]lemma SimpleGraph.Dcast.Scast {V : Type} (G : SimpleGraph V) [D : DecidableRel G.Adj] : (⟨G,D⟩ : DGraph V).toSimpleGraph = G := by simp only
instance DGraph.Scast {V : Type} : Coe (DGraph V) (SimpleGraph V) := ⟨fun G ↦ G.toSimpleGraph⟩
instance DGraph.toSimpleGraphDec {V : Type} (G : DGraph V) : DecidableRel G.toSimpleGraph.Adj := G.dec
@[simp]lemma DGraph.Scast.Dcast {V : Type} (G : DGraph V)  : (G.toSimpleGraph : DGraph V)=G  := by
  obtain ⟨G,D⟩ := G;simp_all only [mk.injEq, heq_eq_eq, true_and];subsingleton
@[simp]lemma eq_DGraph {V : Type} (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] : ((G : DGraph V)=(H : DGraph V)) ↔ (G=H) := by rw [← DGraph_eq]

instance DGraph_Finset.Scast {V : Type} : Coe (Finset (DGraph V)) (Finset (SimpleGraph V)) := by {
  refine ⟨fun ⟨S,nd⟩ ↦ ⟨S,?_⟩⟩
  simp_all only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  revert S
  apply Quotient.rec
  case f => intro l nd; {
    simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_nodup, Multiset.map_coe];
    induction l with
    | nil => simp_all only [List.nodup_nil, List.map_nil]
    | cons head tail ih => {
      simp_all only [List.nodup_cons, List.map_cons, List.mem_map, not_exists, not_and, and_true, forall_const]
      intro G Gi;rw [DGraph_eq];contrapose Gi;simp_all only [not_not, not_false_eq_true]
    }
  }
  simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_nodup, Multiset.map_coe, implies_true]
}

instance SimpleGraphFintype {V : Type} [F : Fintype (DGraph V)] : Fintype (SimpleGraph V) := by {
  obtain ⟨S,C⟩ := F
  refine ⟨S,?_⟩
  simp_all only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Finset.mem_mk, Multiset.mem_map, Finset.mem_val, true_and]
  intro G;have t := fun v u ↦ Classical.propDecidable (G.Adj v u);use G
}

lemma assumeDGraph_forall {V : Type} {φ : SimpleGraph V → Prop} : ∀G : SimpleGraph V, φ G ↔ ∀G : DGraph V, φ G := by {
  sorry
}

section DGraph_iso

instance DGraph.hasIso {V : Type} : Setoid (DGraph V) where
  r (G H : DGraph V) := Nonempty ((G : Graph V) ≃g (H : Graph V))
  iseqv := ⟨fun G ↦ ⟨SimpleGraph.Iso.refl⟩,by intro G H ⟨i⟩;exact ⟨i.symm⟩,by intro G H I ⟨GiH⟩ ⟨HiI⟩;exact ⟨HiI ∘gi GiH⟩⟩

instance DGraph.hasIso_dec {n : ℕ} : DecidableRel (DGraph.hasIso (V:=Fin n)) := by {
  intro G H
  by_cases iso : (graphIsoExists (G : SimpleGraph (Fin n)) H)
  refine isTrue ?_;obtain ⟨iso,_⟩ := iso;exact ⟨iso⟩
  refine isFalse ?_;contrapose iso;simp_all only [not_not];obtain ⟨iso⟩ := iso;exact ⟨iso,by trivial⟩;
  }

instance DGraph.quot_decEq {n : ℕ} : DecidableEq (Quotient (DGraph.hasIso (V:=Fin n))) := by {
  apply Quotient.rec;subsingleton;intro G;apply Quotient.rec;subsingleton;intro H;
  have d := DGraph.hasIso_dec G H
  cases d with
  | isFalse h => refine isFalse ?_;simp_all only [Quotient.eq, not_false_eq_true]
  | isTrue h => refine isTrue ?_;simp_all only [Quotient.eq]
}

end DGraph_iso
end DGraph

variable {n : ℕ} (G : Graph (Fin n))

section extend

variable (N : Set (Fin n))

def Graph.extend : Graph (Fin (n+1)) where
  Adj := by {
    intro x y
    by_cases xln : x.val<n
    by_cases yln : y.val<n
    exact (G.Adj ⟨x.val,xln⟩ ⟨y.val,yln⟩)
    exact (⟨x.val,xln⟩∈N)
    by_cases yln : y.val<n
    exact (⟨y.val,yln⟩∈N)
    exact False
   }
  symm := by {
    simp_all only [dite_else_false]
    intro x y a
    split
    {
      rename_i h
      simp_all only [dite_true, exists_true_left]
      split
      {
        simp_all only [dite_true]
        symm
        exact a
      }
      {
        simp_all only [dite_false, not_lt]
      }
    }
    {
      simp_all only [dite_false, IsEmpty.exists_iff, dite_else_false, not_lt]
    }
   }

@[simp]lemma Graph.extend_bothCastSucc (x y : (Fin n)) : (G.extend N).Adj x.castSucc y.castSucc ↔ G.Adj x y := by
  simp only [Graph.extend, Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]

@[simp]lemma extend_fd_graph_by_neighborhood_adj_onelt (x : Fin n) : (G.extend N).Adj x.castSucc (Fin.last n) ↔ x∈N := by
    simp_all only [Graph.extend, Fin.coe_castSucc, Fin.is_lt, Fin.val_last, lt_self_iff_false, Fin.eta, dite_false, dite_eq_ite, ite_true]
@[simp]lemma extend_fd_graph_by_neighborhood_adj_onelt' (x : Fin n) : (G.extend N).Adj (Fin.last n) x.castSucc ↔ x∈N := by
    simp_all only [Graph.extend, Fin.coe_castSucc, Fin.is_lt, Fin.val_last, lt_self_iff_false, Fin.eta, dite_false, dite_eq_ite, ite_true]

@[simp]lemma extend_fd_graph_by_neighborhood_adj_bothLast  : ¬((G.extend N).Adj (Fin.last n) (Fin.last n)) :=
  SimpleGraph.irrefl (G.extend N)

instance Graph.extend_decidable [DecidableRel G.Adj] [DecidablePred (fun x ↦ x ∈ N)] : DecidableRel (G.extend N).Adj := by {
  intro v u;finCases v;all_goals finCases u
  simp_all only [extend_bothCastSucc];infer_instance
  simp_all only [extend_fd_graph_by_neighborhood_adj_onelt];infer_instance
  simp_all only [extend_fd_graph_by_neighborhood_adj_onelt'];infer_instance
  apply isFalse;simp_all only [SimpleGraph.irrefl, not_false_eq_true]
}

def Graph.extend_by_iso_N {n : ℕ} {G H : Graph (Fin n)} (i : G ≃g H) (N : Set (Fin n)) : G.extend (N.preimage i) ≃g H.extend N where
  toFun (v : Fin (n+1)) := by finCases v;exact (i v).castSucc;exact Fin.last n
  invFun (v : Fin (n+1)) := by finCases v;exact (i.symm v).castSucc;exact Fin.last n
  left_inv (v : Fin (n+1)) := by
    finCases v
    simp_all only;rw [finCases_lemma_cs];rw [finCases_lemma_cs];simp_all only [RelIso.symm_apply_apply]
    simp_all only;rw [finCases_lemma_last];rw [finCases_lemma_last]
  right_inv (v : Fin (n+1)) := by
    finCases v
    simp_all only;rw [finCases_lemma_cs];rw [finCases_lemma_cs];simp_all only [RelIso.apply_symm_apply]
    simp_all only;rw [finCases_lemma_last];rw [finCases_lemma_last]
  map_rel_iff' := by {
    intro v u;simp_all only [Equiv.coe_fn_mk]
    finCases v;all_goals finCases u
    simp_all only [finCases_lemma_cs, extend_bothCastSucc];exact i.map_rel_iff'
    simp_all only [finCases_lemma_cs, finCases_lemma_last, extend_fd_graph_by_neighborhood_adj_onelt, Set.mem_preimage]
    simp_all only [finCases_lemma_last, finCases_lemma_cs, extend_fd_graph_by_neighborhood_adj_onelt', Set.mem_preimage]
    simp_all only [finCases_lemma_last, SimpleGraph.irrefl]
  }

end extend
section reduce

def Graph.reduce {n : ℕ} (G : Graph (Fin (n+1))) : Graph (Fin n) :=
  ⟨fun u v => G.Adj u.castSucc v.castSucc,by intro u v h;symm;exact h,by intro v;simp_all only [SimpleGraph.irrefl, not_false_eq_true]⟩

@[simp]lemma Graph.reduce_Adj {n : ℕ} (G : Graph (Fin (n+1))) (v u : Fin n) : G.reduce.Adj v u ↔ G.Adj v.castSucc u.castSucc := by
  unfold Graph.reduce;simp_all only
instance Graph.reduce_dec {n : ℕ} (G : Graph (Fin (n+1))) [Gd : DecidableRel G.Adj] : DecidableRel G.reduce.Adj := by {
  intro v u;specialize Gd v u;rw [Graph.reduce_Adj]
  cases Gd with
  | isFalse h => apply isFalse;contrapose h;simp_all only [not_not, Fin.coe_eq_castSucc, not_true_eq_false, not_false_eq_true]
  | isTrue h => apply isTrue;simp_all only [Fin.coe_eq_castSucc]
}

@[simp]lemma Graph.reduce_extend {n : ℕ} (G : Graph (Fin n)) (N : Set (Fin n)) : (G.extend N).reduce=G := by ext v u;simp_all only [reduce_Adj, extend_bothCastSucc]


@[simp]lemma Graph.extend_reduce {n : ℕ} (G : Graph (Fin (n+1))) : G.reduce.extend ((G.neighborSet (Fin.last n)).preimage Fin.castSucc) = G := by {
  ext v u
  finCases v;all_goals finCases u
  {
    simp_all only [extend_bothCastSucc, reduce_Adj]
  }
  case Adj.h.h.a.refine_2.refine_2 => simp_all only [SimpleGraph.irrefl]
  rename Fin n => u;rw [@SimpleGraph.adj_comm];conv => rhs;rw [@SimpleGraph.adj_comm]/-wlog-/
  all_goals {
    rw [@SimpleGraph.adj_comm];conv => rhs;rw [@SimpleGraph.adj_comm]
    simp_all only [extend_fd_graph_by_neighborhood_adj_onelt]
    trans (SimpleGraph.neighborSet G (Fin.last n) ∘ Fin.castSucc) u;exact Set.mem_def
    simp_all only [Function.comp_apply];trans u.castSucc ∈ (SimpleGraph.neighborSet G (Fin.last n));rfl
    simp_all only [SimpleGraph.mem_neighborSet];exact SimpleGraph.adj_comm G (Fin.last n) u.castSucc
  }
}

end reduce
section movingBetweenSizes

instance finGraph_to_natGraph {n : ℕ} (G : SimpleGraph (Fin n)) : CoeDep (SimpleGraph (Fin n)) G (SimpleGraph ℕ) := by {
  refine ⟨⟨λ v u : ℕ ↦ if h : (v<n) ∧ (u<n) then G.Adj ⟨v,h.1⟩ ⟨u,h.2⟩ else false,λ v u a ↦ ?_,by aesop_graph⟩⟩
  simp_all only [Bool.false_eq_true, dite_else_false];obtain ⟨l,a⟩ := a;use l.symm;use a.symm
}

instance finGraph_to_natGraph_dec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : DecidableRel (G : SimpleGraph ℕ).Adj := by
  simp_all only [Bool.false_eq_true, dite_else_false];infer_instance

instance natGraph_to_finGraph {n : ℕ} : Coe (SimpleGraph ℕ) (SimpleGraph (Fin n)) := ⟨fun G ↦ ⟨λ v u ↦ G.Adj v.val u.val,λ v u a ↦ a.symm,by aesop_graph⟩⟩

instance natGraph_to_finGraph_dec (n : ℕ) (G : SimpleGraph ℕ) [DecidableRel G.Adj] : DecidableRel (G : SimpleGraph (Fin n)).Adj := by
  simp_all only;infer_instance

end movingBetweenSizes
section embeddingFintype

instance embeddings.fintypeBad (D C : Type) [Fintype D] [Fintype C] [DecidableEq D] [DecidableEq C] : Fintype (D ↪ C) := by {
  exact Fintype.ofEquiv { f : D → C // Function.Injective f } (Equiv.subtypeInjectiveEquivEmbedding D C)
}

instance SimpleGraph.Embedding_equiv_subtype {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  : {x : U ↪ V // ∀ {v u : U}, G.Adj (x v) (x u) ↔ S.Adj v u} ≃ (S ↪g G) where
  toFun (x : {x : U ↪ V // ∀ {v u : U}, G.Adj (x v) (x u) ↔ S.Adj v u}) := by show S.Adj ↪r G.Adj;refine ⟨x.val,x.property⟩
  invFun (x : S ↪g G) := ⟨x.1,x.2⟩
  left_inv := by intro x;simp_all only [id_eq, Subtype.coe_eta]
  right_inv := by intro x;simp_all only [id_eq]

instance SimpleGraph.Embedding.fintype {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U)
  [Fintype V] [Fintype U] [DecidableRel G.Adj] [DecidableRel S.Adj] [DecidableEq V] [DecidableEq U]
  : Fintype (S ↪g G) := by {
    refine Fintype.ofEquiv {x : U ↪ V // ∀ {v u : U}, G.Adj (x v) (x u) ↔ S.Adj v u} (SimpleGraph.Embedding_equiv_subtype G S)
  }

def equivSubgraph {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U) : Setoid (S ↪g G) where
  r S₀ S₁ := ∃i : S ≃g S,S₀=S₁∘i
  iseqv := by {
    refine ⟨?_,?_,?_⟩
    {
      intro x;use ⟨id_equiv,?_⟩;simp_all only [id_equiv_apply, implies_true, RelIso.coe_fn_mk];rfl
      simp_all only [id_equiv_apply, implies_true]
    }
    {
      intro S₀ S₁ ⟨i,ih⟩;use i.symm;rw [ih]
      trans ⇑S₁ ∘ (⇑i ∘ ⇑i.symm)
      any_goals rfl
      have t : ⇑i ∘ ⇑i.symm = id := by ext x;simp_all only [Function.comp_apply, RelIso.apply_symm_apply, id_eq]
      rw [t];simp_all only [CompTriple.comp_eq]
    }
    {
      intro x y z ⟨i0,i0h⟩ ⟨i1,i1h⟩;rw [i0h,i1h];clear i0h i1h;use i1 ∘gi i0
      rfl
    }
  }

def inducedSubgraph {V U : Type} (G : SimpleGraph V) (S : SimpleGraph U) : Type := Quotient (equivSubgraph G S)


end embeddingFintype
