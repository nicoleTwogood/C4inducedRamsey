
import Prelim.List

import Mathlib.Data.Sym.Sym2

assert_not_exists SimpleGraph

variable {n m : ℕ} {T : Type} (x y head : Fin n) (x1 y1 head1 : Fin (n+1)) (j k l tail : List (Fin n)) (j1 k1 l1 tail1 : List (Fin (n+1)))

section lists

section drop_fin_list

def drop_fin_list : List (Fin n) := by induction l1 with
  | nil => exact []
  | cons head tail dropTail => finCases head;exact (head :: dropTail);exact dropTail

@[simp]lemma drop_fin_list_nil : drop_fin_list ([] : List (Fin (n+1)))=([] : List (Fin n)) := by unfold drop_fin_list;simp_all only

@[simp]lemma drop_fin_list_cons_headlast : drop_fin_list (Fin.last n :: tail1) = (drop_fin_list tail1) := by unfold drop_fin_list;simp_all only [finCases_lemma_last]

@[simp]lemma drop_fin_list_cons_headLow : drop_fin_list (head.castSucc :: tail1) = (head :: (drop_fin_list tail1)) := by
    rw [drop_fin_list];simp_all only [finCases_lemma_cs, List.cons.injEq, true_and];rw [← drop_fin_list]

@[simp]lemma mem_drop_fin_list : x∈(drop_fin_list l1)↔x.castSucc∈l1 := by induction l1 with
  | nil => simp_all only [drop_fin_list_nil, List.not_mem_nil]
  | cons head tail ih =>
  simp_all only [List.mem_cons];finCases head
  simp_all only [drop_fin_list_cons_headLow, List.mem_cons, Fin.castSucc_inj]
  simp_all only [drop_fin_list_cons_headlast, iff_or_self];intro h;rw [← Fin.val_inj] at h;simp_all only [Fin.coe_castSucc, Fin.val_last];obtain ⟨x,xln⟩ := x;simp_all only [Fin.castSucc_mk]
  revert xln;simp_all only [lt_self_iff_false, isEmpty_Prop, not_true_eq_false, IsEmpty.forall_iff, implies_true]

lemma length_drop_fin_list : (drop_fin_list l1).length+(l1.EqCount (Fin.last n))=l1.length := by induction l1 with
  | nil => simp_all only [drop_fin_list_nil, List.length_nil, EqCount_nil, add_zero]
  | cons head tail ih =>
    simp_all only [List.length_cons];finCases head
    simp_all only [drop_fin_list_cons_headLow, List.length_cons];have t := succ_not_last head;simp_all only [not_false_eq_true, EqCount_cons_headFail]
    trans ((drop_fin_list tail).length + List.EqCount (Fin.last n) tail)+1;exact Nat.add_right_comm (drop_fin_list tail).length 1 (List.EqCount (Fin.last n) tail);rw [ih]
    simp_all only [drop_fin_list_cons_headlast, EqCount_cons_headPass]
    trans ((drop_fin_list tail).length + List.EqCount (Fin.last n) tail)+1;rfl;rw [ih]


lemma drop_fin_list_list_invariant {n : ℕ} {X Y : List (Fin (n+1))} (equiv : X ≅l Y) : (drop_fin_list X) ≅l (drop_fin_list Y) := by {
  intro k
  constructor
  {
    intro h
    simp_all only [mem_drop_fin_list]
    rw [← equiv]
    exact h
  }
  {
    intro h
    simp_all only [mem_drop_fin_list]
    rw [equiv]
    exact h
  }
}

end drop_fin_list
section drop_lift_fin_list_relation

@[simp]lemma drop_lift_identity_0 {n : ℕ} (list : List (Fin n)) : drop_fin_list (Fin.castSucc.lf list) = list := by induction list with
  | nil => simp_all only [listFun_nil, drop_fin_list_nil]
  | cons head tail ih => simp_all only [listFun_cons, drop_fin_list_cons_headLow]

@[simp]lemma drop_lift_identity_1 : drop_fin_list (Fin.last n :: (Fin.castSucc.lf l)) = l := by simp_all only [drop_fin_list_cons_headlast, drop_lift_identity_0]

@[simp]lemma lift_drop_identity_0 (h : (Fin.last n)∉l1) : Fin.castSucc.lf (drop_fin_list l1)=l1 := by induction l1 with
  | nil => simp_all only [List.not_mem_nil, not_false_eq_true, drop_fin_list_nil, listFun_nil]
  | cons x _ _ => simp_all only [List.mem_cons, not_or, not_false_eq_true, forall_const];finCases x;simp_all only [drop_fin_list_cons_headLow,
    listFun_cons];simp_all only [not_true_eq_false, false_and]

lemma lift_drop_identity_1 (h : (Fin.last n)∈l1) : Fin.last n :: Fin.castSucc.lf (drop_fin_list l1) ≅l l1 := by
  intro x;finCases x;all_goals simp_all only [List.mem_cons, mem_listFun, mem_drop_fin_list,
    Fin.castSucc_inj, exists_eq_right', or_iff_right_iff_imp, implies_true,true_or]

end drop_lift_fin_list_relation

lemma shortFinListIncomplete (lengthShort : l.length<n) : ∃x : Fin n,¬x∈l := by induction n with
  | zero => simp_all only [not_lt_zero']
  | succ n ih =>
    replace ih := ih (drop_fin_list l);contrapose ih
    simp_all only [not_exists, Decidable.not_not, mem_drop_fin_list, not_true_eq_false, exists_false, imp_false, not_lt, not_le]
    rw [← length_drop_fin_list] at lengthShort;contrapose lengthShort;simp_all only [not_lt]
    trans (drop_fin_list l).length+1;simp_all only [add_le_add_iff_right];contrapose lengthShort;simp_all only [add_le_add_iff_left, not_le, Nat.lt_one_iff, EqCount_zero, not_true_eq_false]

end lists
section complete_fin_list

def Complete_Fin_List (n : ℕ) : List (Fin n) := by induction n with
  | zero =>  exact []
  | succ n i => exact 0 :: (Fin.succ.lf i)

@[simp]lemma Complete_Fin_List_zero : Complete_Fin_List 0=[] := by unfold Complete_Fin_List;simp_all only [Nat.rec_zero]

@[simp]lemma Complete_Fin_List_succ : (Complete_Fin_List (n+1)) = 0 :: Fin.succ.lf (Complete_Fin_List n) := by unfold Complete_Fin_List;simp_all only

@[simp]lemma Complete_Fin_List_length (n : ℕ) : (Complete_Fin_List n).length=n := by {
  induction n with
  | zero => simp_all only [Complete_Fin_List_zero, List.length_nil]
  | succ n i => simp_all only [Complete_Fin_List_succ];simp_all only [List.length_cons, listFun_length]
}

@[simp]lemma Complete_Fin_List_get {n : ℕ} (i : Fin n)
  : (Complete_Fin_List n)[i] = i := by {
  induction n with
  | zero => apply finZeroElim i
  | succ n ih => {
    finCasez i
    simp_all only [Fin.getElem_fin, Complete_Fin_List_succ, Fin.val_succ, List.getElem_cons_succ, listFun_index'']
    simp_all only [Fin.getElem_fin, Complete_Fin_List_succ, Fin.val_zero, List.getElem_cons_zero]
  }
}

lemma CFL_complete {n : ℕ} : ∀x : Fin n, x∈ (Complete_Fin_List n) := by induction n with
  | zero => simp_all only [Complete_Fin_List_zero];intro x;apply finZeroElim x
  | succ n ih =>
    simp_all only [Complete_Fin_List_succ];intro x;finCasez x
    simp_all only [List.mem_cons, mem_listFun, Fin.succ_inj, exists_eq_right'];right;trivial
    simp_all only [List.mem_cons, true_or]

lemma Complete_Fin_List_Nodup : (Complete_Fin_List n).Nodup := by {
  induction n with
  | zero => simp_all only [Complete_Fin_List_zero, List.nodup_nil]
  | succ n i => {
    simp_all only [Complete_Fin_List_succ];simp_all only [List.nodup_cons]
    constructor
    simp_all only [mem_listFun, not_exists, not_and];intro x h;exact ne_of_beq_false rfl
    revert i
    induction (Complete_Fin_List n) with
    | nil => simp_all only [List.nodup_nil, listFun_nil, imp_self]
    | cons head tail ih => simp_all only [List.nodup_cons, listFun_cons, mem_listFun, Fin.succ_inj, exists_eq_right', not_false_eq_true, and_self, implies_true]
  }
}

end complete_fin_list
section filter_fin

def filter_fin (p : (Fin n)→Prop) [DecidablePred p] : List (Fin n) := p.filt (Complete_Fin_List n)

lemma mem_filter_fin (p : (Fin n)→Prop) [DecidablePred p] (x : Fin n) : x∈(filter_fin p)↔(p x) := by unfold filter_fin;simp_all only [mem_funcFilt, and_iff_right_iff_imp];intro h;exact CFL_complete x

end filter_fin
section Decidable

def forall_fin_decidable {n : ℕ} {φ : Fin n→Prop} [DecidablePred φ] : Decidable (∀x : Fin n,φ x) := by infer_instance
def exists_fin_decidable {n : ℕ} {φ : Fin n→Prop} [DecidablePred φ] : Decidable (∃x : Fin n,φ x) := by infer_instance

end Decidable
section Fin_set_to_list

def Fin_set_to_list {n : ℕ} (set : Set (Fin n)) [dec : DecidablePred set] : List (Fin n) := set.filt (Complete_Fin_List n)

lemma mem_Fin_set_to_list {n : ℕ} (set : Set (Fin n)) [dec : DecidablePred set] (x : Fin n): x∈(Fin_set_to_list set)↔x∈set := by {
  unfold Fin_set_to_list
  simp_all only [mem_funcFilt]
  constructor
  {
    simp_all only [and_imp]
    intro trash h
    exact h
  }
  {
    intro h
    constructor
    {
      exact CFL_complete x
    }
    {
      exact h
    }
  }
}

end Fin_set_to_list
section Fin_pairs



def Complete_UnorderedPairFin_List (n : ℕ) : List ((Fin n)×(Fin n))
  := listMultiunion ((fun k => ((fun x => (k,x.castLT (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ x.isLt) k.isLt))).lf (Complete_Fin_List (k.val+1)))).lf (Complete_Fin_List n))


@[simp]lemma Complete_UnorderedPairFin_List_zero : Complete_UnorderedPairFin_List 0=[] := by {
  unfold Complete_UnorderedPairFin_List
  simp_all only [Complete_Fin_List_zero, listFun_nil, listMultiunion_nil]
}


lemma mem_Complete_Sym2Fin_List {n : ℕ} (x : Sym2 (Fin n)) : x∈((fun (a,b) => s(a,b)).lf (Complete_UnorderedPairFin_List n)) := by {
  unfold Complete_UnorderedPairFin_List
  simp_all only [Prod.mk.eta, Complete_Fin_List_succ, mem_listFun, mem_listMultiunion,
    Prod.exists]
  induction x with
  | h a b =>
  have wlog {v u : Fin n} (vlu : v≤u)
  : ∃ a_1 b_1,(∃ X,(∃ y ∈ Complete_Fin_List n, X = (fun x => (y, x.castLT (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ x.isLt) y.isLt))).lf
    (0 :: Fin.succ.lf (Complete_Fin_List ↑y)))
    ∧ (a_1, b_1) ∈ X) ∧ s(v, u) = s(a_1, b_1) := by {
      clear a b
      use u
      use v
      constructor
      {
        use ((fun x => (u, x.castLT (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ x.isLt) u.isLt))).lf (Complete_Fin_List (u.val+1)))
        constructor
        {
          use u
          constructor
          {
            exact CFL_complete u
          }
          {
            simp_all only [Complete_Fin_List_succ]
          }
        }
        {
          simp_all only [mem_listFun, Prod.mk.injEq, true_and]
          use ⟨v.val,?_⟩
          {
            constructor
            {
              refine CFL_complete ⟨↑v, ?_⟩
            }
            {
              rw [← Fin.val_inj]
              simp_all only [Fin.coe_castLT]
              exact Order.lt_add_one_iff.mpr vlu
            }
          }
        }
      }
      {
        simp_all only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, or_true]
      }
    }

  by_cases alb : a≤b
  apply wlog
  exact alb
  simp_all only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, Complete_Fin_List_succ,
    not_le]
  have bla : b≤a := Fin.le_of_lt alb
  clear alb
  replace wlog := wlog bla
  obtain ⟨a1,b1,⟨⟨wlog1,wlog2⟩,wlog3⟩⟩ := wlog
  use a1
  use b1
  constructor
  {
    constructor
    {
      exact wlog2
    }
  }
  {
    cases wlog3 with
    | inl h => {
      right
      symm
      exact h
    }
    | inr h => {
      left
      symm
      exact h
    }
  }


}

@[simp]lemma unorderedPairFin_List_complete_noQuot {n : ℕ} (x y : Fin n) : ⟨x,y⟩∈(Complete_UnorderedPairFin_List n) ∨ ⟨y,x⟩∈(Complete_UnorderedPairFin_List n) := by {
  have t := mem_Complete_Sym2Fin_List s(x,y);simp_all only [Prod.mk.eta, mem_listFun, Sym2.eq, Sym2.rel_iff', Prod.exists, Prod.mk.injEq, Prod.swap_prod_mk];obtain ⟨a,b,h1,h2⟩ := t
  cases h2 with
  | inl h => {
    obtain ⟨a,b⟩ := h;subst a;subst b
    left;exact h1
  }
  | inr h => {
    obtain ⟨a,b⟩ := h;subst a;subst b
    right;exact h1
  }
}

def Sym2Fin_set_to_list {n : ℕ} (set : Set ((Fin n)×(Fin n))) [dec : (x : ((Fin n)×(Fin n)))→Decidable (set x)] : List ((Fin n)×(Fin n)) := set.filt (Complete_UnorderedPairFin_List n)


end Fin_pairs
section embedding_implies_lt

lemma embedding_lt {n k : ℕ} (e : (Fin n) ↪ (Fin k)) : n ≤ k := by {
  match n, k with
  | 0, k => exact Nat.zero_le k
  | n + 1, 0 => exfalso;have t := e 0;apply finZeroElim t
  | n + 1, k + 1 => {
    simp_all only [add_le_add_iff_right, ge_iff_le];apply embedding_lt
    refine ⟨?_,?_⟩
    intro x;by_cases h : e x.castSucc = Fin.last k
    refine ⟨(e (Fin.last n)).val,?_⟩
    have ne : (e (Fin.last n)) ≠ Fin.last k := by rw [← h];by_contra c;apply e.injective at c;contrapose c;exact succ_not_last' x
    contrapose ne;simp_all only [gt_iff_lt, not_lt, ne_eq, Decidable.not_not];exact Fin.last_le_iff.mp ne
    refine ⟨(e x.castSucc).val,?_⟩;contrapose h;simp_all only [not_lt, Decidable.not_not];exact Fin.last_le_iff.mp h
    intro x y h;simp_all only
    split at h;all_goals rename_i h₂;all_goals split at h;;all_goals rename_i h₃
    have c : x.castSucc = y.castSucc := by apply e.injective;trans Fin.last k;exact h₂;symm;exact h₃
    exact Fin.castSucc_inj.mp c
    exfalso;rename_i h₃;simp_all only [Fin.mk.injEq];rw [Fin.val_inj] at h;apply e.injective at h;contrapose h;exact succ_not_last' y
    exfalso;rename_i h₃;simp_all only [Fin.mk.injEq];rw [Fin.val_inj] at h;apply e.injective at h;contrapose h;exact succ_not_last x
    rw [← Fin.castSucc_inj];apply e.injective;rw [← Fin.val_inj];simp only [Fin.mk.injEq] at h;exact h
  }
}


/-should be in a different file. Probably Fin-/
lemma inj_implies_fin {n : ℕ} {T : Type} {f : T → (Fin n)} (inj : f.Injective) (nsurj : ¬f.Surjective) : ∃k<n,Nonempty (T ≃ (Fin k)) := by {
  have t : T ≃ {x : Fin n // ∃y : T,f y = x} := by {
    refine ⟨?_,?_,?_,?_⟩
    intro y;use f y;use y
    intro ⟨x,xh⟩;exact Classical.choose xh
    intro x;simp_all only;
    have h (t : ∃ y, f y = f x) : f (Classical.choose t) = f x := Classical.choose_spec t
    apply inj;apply h
    intro y;simp_all only;obtain ⟨x,xh⟩ := y;simp_all only [Subtype.mk.injEq];apply Classical.choose_spec xh
  }
  have ⟨k,t₂⟩ : ∃k : ℕ,Nonempty ({x : Fin n // ∃y : T,f y = x} ≃ Fin k) := by {
    exact Finite.exists_equiv_fin { x // ∃ y, f y = x }
  }
  obtain ⟨t₂⟩ := t₂
  use k;constructor
  case h.right => refine ⟨?_⟩;exact ((id t₂.symm).trans (id t.symm)).symm
  have ginj : (f ∘ t.symm ∘ t₂.symm).Injective := by {
    simp_all only [Function.Injective.of_comp_iff, EquivLike.injective_comp]
    exact Equiv.injective t.symm
  }
  have g : Fin k ↪ Fin n := ⟨f ∘ t.symm ∘ t₂.symm,ginj⟩
  have lte := embedding_lt g
  refine Nat.lt_of_le_of_ne lte ?_;by_contra eq;subst eq;clear lte;clear g
  have gsurj : (f ∘ t.symm ∘ t₂.symm).Surjective := (Function.Injective.bijective_of_finite ginj).surjective
  clear ginj;
  have tsurj : (⇑t.symm).Surjective := Equiv.surjective t.symm
  have t₂surj : (⇑t₂.symm).Surjective := Equiv.surjective t₂.symm
  simp_all only [Function.Surjective.of_comp_iff]
}

end embedding_implies_lt
