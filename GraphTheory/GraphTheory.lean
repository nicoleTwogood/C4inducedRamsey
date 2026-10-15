
import Test.Function

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

assert_not_exists complete FD_Graph

variable {V U T : Type} (v v' : V) (G : SimpleGraph V) (H : SimpleGraph U) (I : SimpleGraph T) {A : SimpleGraph V} {B : SimpleGraph U} {C : SimpleGraph T} (g : B≃g C)

section Notation

abbrev Graph := SimpleGraph

section homomorphisms


instance (f : A ≃g B) : CoeDep (A ≃g B) f (A ↪g B) := ⟨f.toEquiv.toEmbedding,fun {_ _} ↦ f.map_rel_iff'⟩

instance (h : A ↪g B) : CoeDep (A ↪g B) h (V ↪ U) := ⟨⟨h,RelEmbedding.injective h⟩⟩

instance (h : A ↪g B) : CoeDep (A ↪g B) h (A →g B) := ⟨⟨h.toEmbedding,fun e ↦ h.map_rel_iff'.mpr e⟩⟩

instance (f : A ≃g B) : CoeDep (A ≃g B) f (A →g B) := ⟨((f : A ↪g B) : A →g B)⟩

def composeHomos {X : SimpleGraph V} {Y : SimpleGraph U} {Z : SimpleGraph T} (gₕ : Y →g Z) (fₕ : X →g Y) : X →g Z := by {
  refine ⟨gₕ ∘ fₕ,?_⟩
  intro _ _ e;apply gₕ.map_rel';apply fₕ.map_rel';exact e
}

infixl:25 " ∘g " => composeHomos

def graph_composeEmbed {X : SimpleGraph V} {Y : SimpleGraph U} {Z : SimpleGraph T} (gₕ : Y ↪g Z) (fₕ : X ↪g Y) : X ↪g Z := by {
  refine ⟨gₕ.toEmbedding ∘e fₕ.toEmbedding,?_⟩
  intro v u;trans Y.Adj (fₕ.toEmbedding v) (fₕ.toEmbedding u)
  exact RelEmbedding.map_rel_iff gₕ
  exact RelEmbedding.map_rel_iff fₕ
}

infixl:25 " ∘ge " => graph_composeEmbed

end homomorphisms

variable (f : A ≃g B)

section composeIsos


/-check with variable and clean that to make sure order is correct here.-/
def composeIsos : A ≃g C := by
  refine ⟨?_,?_⟩
  next => refine ⟨g ∘ f,f.symm ∘ g.symm,?_,?_⟩;all_goals intro x;simp_all only [Function.comp_apply, RelIso.symm_apply_apply, RelIso.apply_symm_apply]
  intro u v;simp_all only [Equiv.coe_fn_mk, Function.comp_apply]
  constructor;(all_goals intro h);rw [← f.map_rel_iff',← g.map_rel_iff'];(any_goals rw [← f.map_rel_iff',← g.map_rel_iff'] at h);all_goals simp_all only [RelIso.coe_fn_toEquiv]

infixl:25 " ∘gi " => composeIsos

@[simp]lemma composeIsos_apply : ((g ∘gi f) v)=(g (f v)) := by unfold composeIsos;simp_all only [RelIso.coe_fn_mk, Equiv.coe_fn_mk, Function.comp_apply]
@[simp]lemma composeIsos_symm : (g ∘gi f).symm = (f.symm ∘gi g.symm) := by
  ext x;simp_all only [composeIsos_apply];unfold composeIsos;simp_all only [RelIso.coe_fn_symm_mk, Equiv.coe_fn_symm_mk, Function.comp_apply]

def id_iso : G ≃g G where
  toFun := id
  invFun := id
  left_inv := by intro x;simp_all only [id_eq]
  right_inv := by intro x;simp_all only [id_eq]
  map_rel_iff' := by intro v u;simp_all only [Equiv.coe_fn_mk, id_eq]
@[simp]lemma id_iso_apply (v : V) : (id_iso A) v = v := by {
  unfold id_iso;simp_all only [RelIso.coe_fn_mk, Equiv.coe_fn_mk, id_eq]
}
@[simp]lemma id_iso_symm : (id_iso A).symm = id_iso A := by {
  ext v;simp_all only [id_iso_apply];unfold id_iso;simp_all only [RelIso.coe_fn_symm_mk, Equiv.coe_fn_symm_mk, id_eq]
}
@[simp]lemma compoesIsos_symm_iso : (f.symm ∘gi f) = (id_iso A) := by {
  ext v;simp_all only [composeIsos_apply, RelIso.symm_apply_apply, id_iso_apply]
}

end composeIsos
section graphIsoExists
variable (G H I : SimpleGraph V)

instance graphIsoExists : Setoid (Graph V) where
  r (G H : Graph V) := ∃iso : G ≃g H,True
  iseqv := ⟨(by intro _;use ⟨id_equiv,(by intro _ _;constructor;all_goals intro _;simp_all only [id_equiv_apply])⟩),(by intro _ _ ⟨iso,_⟩;use iso.symm),(by intro _ _ _ ⟨f,_⟩ ⟨g,_⟩;use g ∘gi f)⟩

infixl:25 " ≅g " => graphIsoExists

@[refl]lemma graphIsoExists_refl : ∀G : Graph V, G ≅g G := (graphIsoExists).iseqv.refl
@[symm]lemma graphIsoExists_symm : G ≅g H → H ≅g G := (graphIsoExists).iseqv.symm
instance graphIsoExists_trans : Trans (α:=Graph V) graphIsoExists graphIsoExists graphIsoExists where trans := graphIsoExists.iseqv.trans

end graphIsoExists
end Notation
section iso_lemmas

lemma isoIsBijective (f : A ≃g B) : Function.Bijective f := equivIsBijective f.toEquiv

@[simp]abbrev SimpleGraph.Iso.lf {G : Graph V} {H : Graph U} (f : G ≃g H) : (List V)→(List U) := f.toFun.lf

end iso_lemmas
section creating_graphs

def SimpleGraph.restrict {V : Type} (S : Set V) (G : SimpleGraph V) : SimpleGraph S := by {
  refine ⟨?_,?_,?_⟩
  intro v u;exact G.Adj v.val u.val
  intro v u h;exact id (adj_symm G h)
  intro v;exact SimpleGraph.irrefl G
}

@[simp]lemma SimpleGraph.restrict_Adj {V : Type} (S : Set V) (G : SimpleGraph V) (v u : {v : V // v ∈ S}) : (G.restrict S).Adj v u ↔ G.Adj v.val u.val := by {
  unfold SimpleGraph.restrict;simp_all only
}

@[simp]lemma SimpleGraph.restrict_edgeInc {V : Type} (S : Set V) (G : SimpleGraph V) (e : Sym2 {v : V // v ∈ S})
  : e ∈ (G.restrict S).edgeSet ↔ (e.map Subtype.val) ∈ G.edgeSet := by induction e with
    | h x y => simp_all only [mem_edgeSet, restrict_Adj, Sym2.map_pair_eq]

@[simp]lemma SimpleGraph.induce_edgeInc {V : Type} (S : Set V) (G : SimpleGraph V) (e : Sym2 {v : V // v ∈ S})
  : e ∈ (G.induce S).edgeSet ↔ (e.map Subtype.val) ∈ G.edgeSet := by induction e with
    | h x y => simp_all only [mem_edgeSet, comap_adj, Function.Embedding.coe_subtype, Sym2.map_pair_eq]

def SimpleGraph.restrict_subgraph {V : Type} (S : Set V) (G : SimpleGraph V) : (G.restrict S) →g G := by use ·.val;intro v u h;simp_all only [restrict_Adj]

@[simp]lemma SimpleGraph.restrict_subgraph_toFun {V : Type} (S : Set V) (G : SimpleGraph V) : (G.restrict_subgraph S).toFun = (λ x : ↑S ↦ x.val) := by
  unfold SimpleGraph.restrict_subgraph;simp_all only

@[simp]lemma SimpleGraph.restrict_subgraph_funCoe {V : Type} (S : Set V) (G : SimpleGraph V) : ⇑(G.restrict_subgraph S) = (λ x : ↑S ↦ x.val) := by
  unfold SimpleGraph.restrict_subgraph DFunLike.coe RelHom.instFunLike;simp_all only

def SimpleGraph.induce_subgraph {V : Type} (S : Set V) (G : SimpleGraph V) : (G.induce S) →g G := by use ·.val;intro v u h;simp_all only [comap_adj, Function.Embedding.coe_subtype]

@[simp]lemma SimpleGraph.induce_subgraph_toFun {V : Type} (S : Set V) (G : SimpleGraph V) : (G.induce_subgraph S).toFun = (λ x : ↑S ↦ x.val) := by
  unfold SimpleGraph.induce_subgraph;simp_all only

@[simp]lemma SimpleGraph.induce_subgraph_funCoe {V : Type} (S : Set V) (G : SimpleGraph V) : ⇑(G.induce_subgraph S) = (λ x : ↑S ↦ x.val) := by
  unfold SimpleGraph.induce_subgraph DFunLike.coe RelHom.instFunLike;simp_all only

end creating_graphs
