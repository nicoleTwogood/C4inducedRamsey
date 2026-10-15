
import Test.Fin
import Test.Function

assert_not_exists SimpleGraph

variable {n m : ℕ} {D C T : Type}

section extendFinFun

def extendFinFun {n m : ℕ} (f : (Fin n)→(Fin m)) (x : Fin m) : (Fin (n+1))→(Fin m) := fun y => if h : y.val<n then f ⟨y.val,h⟩ else x

end extendFinFun
section extend_drop_relation

@[simp]lemma drop_extend_leftInverse (n : ℕ) (x : Fin m) : Function.LeftInverse (α := (Fin n)→(Fin m)) (fun f ↦ f ∘ Fin.castSucc) (fun f => extendFinFun f x) := by {
  intro f
  simp_all only
  unfold extendFinFun
  ext x;simp_all only [Function.comp_apply, Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
}

@[simp]lemma drop_extend_leftInverse'  (f : (Fin n)→(Fin m)) (x : Fin m) : (extendFinFun f x) ∘ Fin.castSucc=f := by {
  have test := drop_extend_leftInverse n x
  replace test := test f
  simp_all only
}


@[simp]lemma extend_drop_semiInverse' {n m : ℕ} (f : (Fin (n+1))→(Fin m)) : extendFinFun (f ∘ Fin.castSucc) (f (Fin.last n))=f := by
  unfold extendFinFun;ext x;simp_all only [Function.comp_apply, Fin.castSucc_mk, Fin.eta, dite_eq_ite]
  finCases x;simp_all only [Fin.coe_castSucc, Fin.is_lt, ite_true];simp_all only [Fin.val_last, lt_self_iff_false, ite_self]


@[simp]lemma extend_drop_semiInverse {n m : ℕ} (f : (Fin (n+1))→(Fin m)) : ∃x : Fin m,(extendFinFun (f ∘ Fin.castSucc) x)=f := by {
  use f (Fin.last n)
  simp_all only [extend_drop_semiInverse']
}

end extend_drop_relation
section finFunToList

@[coe]def Function.toList {n : ℕ} {type : Type} (f : (Fin n)→type) : List type := by exact List.ofFn f

@[simp]lemma Function.toList_zero {type : Type} (f : (Fin 0)→type) : (Function.toList f)=[] := by {
  unfold Function.toList
  simp_all only [List.ofFn_zero]
}

@[simp]lemma Function.toList_succ {n : ℕ} {type : Type} (f : (Fin (n+1))→type) : (Function.toList f)=((f 0) :: Function.toList (f ∘ Fin.succ)) := by {
  unfold Function.toList
  simp_all only [List.ofFn_succ, List.cons.injEq, List.ofFn_inj, true_and]
  ext x;simp_all only [comp_apply]
}

@[simp]lemma Function.toList_length {n : ℕ} {type : Type} (f : (Fin n)→type) : (Function.toList f).length = n := by {
  induction n with
  | zero => simp_all only [Function.toList_zero, List.length_nil]
  | succ n _ => simp_all only [Function.toList_succ, List.length_cons]
}

@[simp]lemma listFun_finFunToList  {n : ℕ} {D C : Type} (f : (Fin n)→D) (g : D→C) : g.lf (Function.toList f) = Function.toList (g ∘ f) := by {
  induction n with
  | zero => simp_all only [Function.toList_zero, listFun_nil]
  | succ n ih => simp_all only [Function.toList_succ, listFun_cons, Function.comp_apply, List.cons.injEq, true_and];rfl
}

@[simp]lemma Function.mem_toList {n : ℕ} {type : Type} (f : (Fin n)→type) (x : type) : x∈(Function.toList f) ↔ ∃y : Fin n,(f y)=x := by {
  constructor
  {
    intro h
    induction n with
    | zero => {
      simp_all only [Function.toList_zero, List.not_mem_nil]
    }
    | succ n ih => {
      simp_all only [Function.toList_succ, Fin.natCast_eq_last, List.mem_cons]
      cases h with
      | inl h => {
        subst h
        use 0
      }
      | inr h => {
        replace ih := ih (f ∘ Fin.succ) h
        obtain ⟨y,ih⟩ := ih
        have yln1 : y.val < n+1 := by {
          obtain ⟨y,yln⟩ := y
          simp_all only [Function.comp_apply, Fin.castSucc_mk]
          exact Nat.lt_add_right 1 yln
        }
        use y.succ
        simp_all only [Function.comp_apply]
      }
    }
  }
  {
    intro h
    obtain ⟨y,h⟩ := h
    induction n with
    | zero => {
      simp_all only [Function.toList_zero, List.not_mem_nil]
      apply finZeroElim y
    }
    | succ n ih => {
      simp_all only [Function.toList_succ, Fin.natCast_eq_last, List.mem_cons];finCasez y
      right;apply ih (f ∘ Fin.succ) y;simp_all only [Function.comp_apply]
      left;rw [← h]
    }
  }
}

lemma finFunInjective_toList {n : ℕ} {type : Type} (f : (Fin n)→type) : (Function.Injective f) ↔ (Function.toList f).Nodup := by {
  induction n with
  | zero => simp_all only [Function.toList_zero, List.nodup_nil, iff_true];intro x;apply finZeroElim x
  | succ n ih => {
    simp_all only [Function.toList_succ, List.nodup_cons, Function.mem_toList, Function.comp_apply, not_exists]
    specialize ih (f ∘ Fin.succ);rw [← ih];clear ih
    constructor
    intro i;constructor;intro x;by_contra c;exact Fin.succ_ne_zero x (i c);intro x y e;simp_all only [Function.comp_apply];specialize i e;exact Fin.succ_inj.mp i
    intro i x y e;finCasez x;all_goals finCasez y
    unfold Function.Injective at i;simp_all only [Function.comp_apply];have t : x=y := by apply i.right;exact e;;rw [t]
    case succ.mpr.refine_2.refine_2 => rfl
    symm at e;symm;rename Fin n => y;all_goals symm at e;contrapose e;exact (i.left y)
  }
}

@[simp]lemma List.toFinFun_toList  {type : Type} (l : List type) : (l.get.toList)=l := by {
  induction l with
  | nil => simp_all only [length_nil, Function.toList_zero]
  | cons head tail ih => simp_all only [length_cons, Function.toList_succ, get_eq_getElem, Fin.val_zero, getElem_cons_zero, cons.injEq, true_and];exact ih
}

/-I do not know how casts work.-/
@[simp]lemma Function.toList_toFinFun {n : ℕ} {type : Type} (f : Fin n → type) : f.toList.get/-consider modifying get?-/
  =f ∘ (fun x ↦ ((by rw [f.toList_length]) : Fin f.toList.length = Fin n).mp x) := by {

  induction n with
  | zero => ext x;apply finZeroElim x
  | succ n ih => {
    sorry
  }
}

/-This lemma statement is wip
lemma list_equiv_iff_toFinFun_comp_equiv {T : Type} {l₁ l₂ : List T} (nd₁ : l₁.Nodup) (nd₂ : l₂.Nodup) (e : (l₁ ≅l l₂))
  :∃aut : (Fin l₁.length) ≃ (Fin l₂.length),(l₁.get (by rfl) = l₂.get (by rfl) ∘ aut ) := by {
    sorry
  }
  -/

end finFunToList
section Finset_recDisj

universe α

def Finset.recDisj {T : Type} {C : Finset T → Sort α} (C_0 : C ∅)
  (C_cons : (head : T) → (tail : Finset T) → (nd : head ∉ tail) → C tail → C (Finset.cons head tail nd))
  (C_cons_heq : ∀ (h h' : T) (l : Finset T) (b : C l), (hi : h∉l) → (hi' : h'∉l) → (ne : h≠h')  →
    HEq (C_cons h (Finset.cons h' l hi') (by simp_all only [ne_eq, mem_cons, or_self, not_false_eq_true]) (C_cons h' l hi' b))
    (C_cons h' (Finset.cons h l hi) (by simp_all only [ne_eq, mem_cons, or_false];contrapose ne;simp_all only [not_not,
     not_true_eq_false, not_false_eq_true]) (C_cons h l hi b)))
  (l : Finset T)
  : C l := by {
    obtain ⟨l,nd⟩ := l;revert l;apply Multiset.rec
    case mk.C_0 => intro nd;simp_all only [mk_zero];exact C_0
    case mk.C_cons => intro head tail ih nd;{
      simp_all only [mk_cons]
      simp only [Multiset.nodup_cons] at nd
      apply C_cons head ⟨tail,nd.2⟩ nd.1;apply ih
    }
    case mk.C_cons_heq => intro head₁ head₂ tail ih;{
      simp_all only [mk_cons, eq_mp_eq_cast, id_eq]
      refine Function.hfunext ?_ ?_
      {
        simp_all only [ne_eq, eq_mpr_eq_cast, Multiset.nodup_cons, Multiset.mem_cons, not_or, eq_iff_iff]
        apply Iff.intro
        · intro a
          simp_all only [not_false_eq_true, and_true, and_self]
          obtain ⟨left, right⟩ := a
          obtain ⟨left, right_1⟩ := left
          obtain ⟨left_1, right⟩ := right
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_false_eq_true, not_true_eq_false]
        · intro a
          simp_all only [not_false_eq_true, and_true, and_self]
          obtain ⟨left, right⟩ := a
          obtain ⟨left, right_1⟩ := left
          obtain ⟨left_1, right⟩ := right
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_false_eq_true, not_true_eq_false]
      }
      intro nd₁ nd₂ heq;simp only [Multiset.nodup_cons, Multiset.mem_cons, not_or] at nd₁
      specialize C_cons_heq head₁ head₂ ⟨tail,nd₁.right.right⟩ (ih ?_) nd₁.left.right nd₁.right.left nd₁.left.left
      exact C_cons_heq
    }
  }

end Finset_recDisj
section Finset_flatMap
section Finset_flatMap_tail_recursive
def Finset.flatMap_tr_helper {D C : Type} [DecidableEq C] (f : D → Finset C) (l : Finset D) : Finset C := by {
  sorry
}

def Finset.flatMap_tr {D C : Type} [DecidableEq C] (f : D → Finset C) (l : Finset D) : Finset C := by {
  sorry
}
end Finset_flatMap_tail_recursive

def Finset.flatMap {D C : Type} [DecidableEq C] (f : D → Finset C) (l : Finset D) : Finset C := by {
  obtain ⟨l,nd⟩ := l;revert l;apply Quotient.rec
  case mk.f => intro l nd;{
    induction l with
    | nil => refine ⟨⟦[]⟧,?_⟩;simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_nil, Multiset.nodup_zero]
    | cons head tail ih => {
      simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_nodup, List.nodup_cons]
      have t : Multiset.Nodup ⟦tail⟧ := by simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_nodup]
      specialize ih t;exact (f head) ∪ ih
    }
  }
  {
    sorry/-prove that flatMap is permutation invariant.-/
  }
}

@[simp]lemma Finset.flatMap_mem {D C : Type} [DecidableEq C] (f : D → Finset C) (l : Finset D) (x : C)
  : x ∈ (l.flatMap f) ↔ ∃X ∈ l,x ∈ f X := by {
    sorry
  }


def Fintype.flatMapDisj {D C : Type} (f : D → Finset C) (l : Fintype D) (surj : ∀c : C,∃!d : D,c ∈ f d)
  : Finset C := by {
    revert l;
    sorry
}

end Finset_flatMap
section Fin_Bijection


section showing_bijectivity

lemma upwardFuncNotSurj {n m : ℕ} (f : Fin n→Fin m) (nlm : n<m) : ∃x : Fin m,∀y : Fin n,¬x=f y := by {
  have test : (∃x : Fin m,¬(∃y : Fin n,x=f y))↔(∃x : Fin m,∀y : Fin n,¬x=f y) := by simp_all only [not_exists]
  rw [← test]
  replace test (x : Fin m): (∃ y, x = f y)↔(x∈List.ofFn f) := by {
    simp_all only [not_exists, List.mem_ofFn]
    constructor
    {
      intro h
      obtain ⟨h,hi⟩ := h
      use h
      symm
      exact hi
    }
    {
      intro h
      obtain ⟨h,hi⟩ := h
      use h
      symm
      exact hi
    }
  }
  replace test :  (∃ x : Fin m, ¬∃ y : Fin n, x = f y)↔(∃x : Fin m,¬(x ∈ List.ofFn f)) := by {
    constructor
    {
      intro h
      obtain ⟨h1,h2⟩ := h
      use h1
      contrapose h2
      simp_all only [List.mem_ofFn, not_exists, not_forall, Decidable.not_not, not_true_eq_false,
        not_false_eq_true]
    }
    {
      intro h
      obtain ⟨h1,h2⟩ := h
      use h1
      contrapose h2
      simp_all only [List.mem_ofFn, not_exists, not_forall, Decidable.not_not, not_true_eq_false,
        not_false_eq_true]
    }
  }
  rw [test]
  replace test : (List.ofFn f).length<m := by {
    simp_all only [not_exists, List.mem_ofFn, List.length_ofFn]
  }
  exact (shortFinListIncomplete (List.ofFn f) test)

}

end showing_bijectivity
section dropFinFun_around

def dropFinFun_around_lil {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) (h : f (Fin.last n)=Fin.last n) : (Fin n)→(Fin n) := by {
  refine fun x => ⟨(f x.castSucc).val,?_⟩
  {/-proofs from here-/
    have t : (f x.castSucc)≠(Fin.last n) := by {
      by_contra c
      conv at h=>
        rhs
        rw [← c]
      apply bij.injective at h
      rw [← Fin.val_inj] at h
      simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
        Fin.val_last, Fin.coe_castSucc]
      obtain ⟨x,xln⟩ := x
      simp_all only [Fin.castSucc_mk]
      rw [h] at xln
      simp_all only [lt_self_iff_false]
    }
    contrapose t
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
      gt_iff_lt, not_lt, ne_eq, Decidable.not_not]
    exact Fin.last_le_iff.mp t
  }
}


def dropFinFun_around {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) : (Fin n)→(Fin n) := by {
  refine dropFinFun_around_lil ((transposition (f (Fin.last n)) (Fin.last n)) ∘ f) ?_ ?_
  /-proofs from here-/
  {
    exact Function.Bijective.comp  (transposition_bijective (f (Fin.last n)) (Fin.last n)) bij
  }
  {
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ, Function.comp_apply, transposition_apply_1]
  }
}

@[simp]lemma dropFinFun_around_id {n : ℕ} {h : Function.Bijective (id (α:=(Fin (n+1))))} : dropFinFun_around id h = id := by {
  unfold dropFinFun_around;simp_all only [id_eq, Function.comp_id];have t := transposition_id (Fin.last n);conv => lhs;congr;rw [t];;
  unfold dropFinFun_around_lil;simp_all only [id_eq, Fin.coe_castSucc, Fin.eta];ext x;simp_all only [Multiset.bijective_iff_map_univ_eq_univ,
    id_eq, Multiset.map_id', transposition_id]
}

lemma dropFinFun_around_zero (f : (Fin 1)→(Fin 1)) (bij : Function.Bijective f) : dropFinFun_around f bij = (fun x => by apply finZeroElim x) := by
  ext x;apply finZeroElim x


lemma dropFinFun_around_lil_bijective {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) (h : f (Fin.last n)=Fin.last n) : Function.Bijective (dropFinFun_around_lil f bij h) := by {
  unfold dropFinFun_around_lil
  refine Function.Surjective.bijective_of_finite ?_
  intro x
  obtain ⟨y,yh⟩ := bij.surjective x.castSucc
  have yln : y.val<n := by {
    have ynl : y≠Fin.last n := by {
      by_contra c
      subst c
      rw [h] at yh
      clear h bij
      rw [← Fin.val_inj] at yh
      simp_all only [Fin.val_last, Fin.coe_castSucc]
      obtain ⟨x,xln⟩ := x
      simp_all only
      subst yh
      exact (lt_self_iff_false n).mp xln
    }
    exact finNotMaxImpln y ynl
  }
  use ⟨y.val,yln⟩
  simp_all only [Fin.castSucc_mk, Fin.eta, Fin.coe_castSucc]
}

lemma dropFinFun_around_bijective {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) : Function.Bijective (dropFinFun_around f bij) := by {
  unfold dropFinFun_around
  exact
    dropFinFun_around_lil_bijective (transposition (f (Fin.last n)) (Fin.last n) ∘ f)
      (dropFinFun_around.proof_1 f bij) (dropFinFun_around.proof_2 f)
}

end dropFinFun_around
section liftFinFun_around


def liftFinFun_around {n : ℕ} (f : (Fin n)→(Fin n)) : (Fin (n+1))→(Fin (n+1)) := fun x => if h : x.val<n then (f ⟨x.val,h⟩).castSucc else Fin.last n

@[simp]lemma liftFinFun_around_id {n : ℕ} : liftFinFun_around (n:=n) id = id := by
  unfold liftFinFun_around;simp_all only [id_eq, Fin.castSucc_mk, Fin.eta, dite_eq_ite];ext x;finCases x;
  simp_all only [Fin.coe_castSucc, Fin.is_lt, ite_true, id_eq];simp_all only [Fin.val_last, lt_self_iff_false, ite_self, id_eq]


lemma liftFinFun_around_bijective {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : Function.Bijective (liftFinFun_around f) := by {
  refine Finite.surjective_iff_bijective.mp ?_
  intro x
  by_cases h : x=Fin.last n
  unfold liftFinFun_around
  simp_all only [dite_eq_right_iff]
  use Fin.last n
  intro c
  simp only [Fin.val_last, lt_self_iff_false] at c
  unfold liftFinFun_around
  have xln : x.val<n := by {
    contrapose h
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, not_lt,
      Decidable.not_not]
    exact Fin.last_le_iff.mp h
  }
  obtain ⟨y,yh⟩ := bij.surjective ⟨x,xln⟩
  use y
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, Fin.coe_eq_castSucc,
    Fin.coe_castSucc, Fin.is_lt, Fin.eta, Fin.castSucc_mk, dite_eq_ite, ite_true]
}

@[simp]lemma liftFinFun_around_lil {n : ℕ} (f : (Fin n)→(Fin n)) : (liftFinFun_around f) (Fin.last n)=Fin.last n := by {
  unfold liftFinFun_around
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
    Fin.val_last, lt_self_iff_false, dite_false]
}

@[simp]lemma liftFinFun_around_lowRun {n : ℕ} (f : (Fin n)→(Fin n)) (x : Fin n) : (liftFinFun_around f) x.castSucc=(f x).castSucc := by {
  unfold liftFinFun_around
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, Fin.coe_castSucc,
    Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
}
@[simp]lemma liftFinFun_around_lowRun' {n : ℕ} (f : (Fin n)→(Fin n)) (x : Fin (n+1)) (xln : x.val<n) : (liftFinFun_around f ) x=(f ⟨x,xln⟩).castSucc := by {
  have t : x=(⟨x,xln⟩ : Fin n).castSucc := by rfl
  conv => {lhs;rw [t]};exact liftFinFun_around_lowRun f ⟨x,xln⟩
}

lemma Inverse_liftFinFun_around {n : ℕ} {f g : (Fin n)→(Fin n)} (inv : Inverse f g) : Inverse (liftFinFun_around f) (liftFinFun_around g) := by {
  constructor
  {
    intro x
    by_cases xln : x.val<n
    {
      unfold liftFinFun_around
      simp_all only [dite_true, Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
      rw [inv.left]
      simp_all only [Fin.castSucc_mk, Fin.eta]
    }
    {
      unfold liftFinFun_around
      have xil : x=Fin.last n := by {
        exact Fin.eq_last_of_not_lt xln
      }
      subst xil
      simp_all only [Fin.val_last, lt_self_iff_false, not_false_eq_true, dite_false, dite_true,
        Fin.coe_castSucc, Fin.eta]
    }
  }
  {
    intro x
    by_cases xln : x.val<n
    {
      unfold liftFinFun_around
      simp_all only [dite_true, Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
      rw [inv.right]
      simp_all only [Fin.castSucc_mk, Fin.eta]
    }
    {
      unfold liftFinFun_around
      have xil : x=Fin.last n := by {
        exact Fin.eq_last_of_not_lt xln
      }
      subst xil
      simp_all only [Fin.val_last, lt_self_iff_false, not_false_eq_true, dite_false, dite_true,
        Fin.coe_castSucc, Fin.eta]
    }
  }
}

section liftFinEquiv

def liftFinEquiv_around {n : ℕ} (f : (Fin n)≃(Fin n)) : (Fin (n+1))≃(Fin (n+1)) where
  toFun := liftFinFun_around f.toFun
  invFun := liftFinFun_around f.invFun
  left_inv := (Inverse_liftFinFun_around (equiv_symm_inverse f)).right
  right_inv := (Inverse_liftFinFun_around (equiv_symm_inverse f)).left

@[simp]lemma liftFinEquiv_around_lil {n : ℕ} (f : (Fin n)≃(Fin n)) : (liftFinEquiv_around f) (Fin.last n)=Fin.last n := by {
  unfold liftFinEquiv_around
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Multiset.map_univ_val_equiv,
    Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_mk, liftFinFun_around_lil]
}

@[simp]lemma liftFinEquiv_around_lowRun {n : ℕ} (f : (Fin n)≃(Fin n)) (x : Fin n) : (liftFinEquiv_around f) x.castSucc=(f x).castSucc := by {
  unfold liftFinEquiv_around
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Multiset.map_univ_val_equiv,
    Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_mk, Fin.coe_castSucc, Fin.is_lt,
    liftFinFun_around_lowRun', Fin.eta]
}
@[simp]lemma liftFinEquiv_around_lowRun' {n : ℕ} (f : (Fin n)≃(Fin n)) (x : Fin (n+1)) (xln : x.val<n) : (liftFinEquiv_around f) x=(f ⟨x,xln⟩).castSucc := by {
  have t : x=(⟨x,xln⟩ : Fin n).castSucc := by rfl
  conv => {lhs;rw [t]};exact liftFinEquiv_around_lowRun f ⟨x,xln⟩
}

end liftFinEquiv
end liftFinFun_around
section drop_lift_around


@[simp]lemma liftDropFinFun_lil_inverse {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f)
  : dropFinFun_around_lil (liftFinFun_around f) (liftFinFun_around_bijective f bij) (liftFinFun_around_lil f) = f := by {
    unfold liftFinFun_around dropFinFun_around_lil
    simp_all only [Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
  }

@[simp]lemma liftDropFinFun_inverse {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : dropFinFun_around (liftFinFun_around f) (liftFinFun_around_bijective f bij) = f := by {
  unfold dropFinFun_around liftFinFun_around dropFinFun_around_lil
  simp_all only [Fin.val_last, lt_self_iff_false, dite_false, transposition_id, Function.comp_apply,
    Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true, id_eq]
}


lemma dropLiftFinFun_inverse' {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) (lil : (f (Fin.last n))=Fin.last n)
 : liftFinFun_around (dropFinFun_around f bij)=f := by {
  unfold dropFinFun_around liftFinFun_around dropFinFun_around_lil
  simp_all only [transposition_id, Fin.castSucc_mk, Fin.eta, Function.comp_apply, id_eq, dite_eq_ite]
  ext x
  clear bij
  split
  {
    rfl
  }
  {
    have xil : x=Fin.last n := by {
      rename_i h
      exact Fin.eq_last_of_not_lt h
    }
    subst xil
    rw [lil]
  }
}

lemma dropLiftFinFun_inverse {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f)
: (transposition (f (Fin.last n)) (Fin.last n)) ∘ (liftFinFun_around (dropFinFun_around f bij))=f  := by {
  unfold dropFinFun_around liftFinFun_around dropFinFun_around_lil
  simp_all only [Fin.castSucc_mk, Fin.eta, Function.comp_apply, dite_eq_ite]
  ext x
  clear bij
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
    Function.comp_apply]

  split
  {
    rename_i h
    simp_all only [transposition_selfInverse_a]
  }
  {
    rename_i h
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
      not_lt, Fin.val_last, Function.comp_apply]
    have xil : x=Fin.last n := by {
      exact Fin.last_le_iff.mp h
    }
    subst xil
    simp_all only [Fin.val_last, le_refl, transposition_apply_2]
  }

}

lemma dropLiftFinFun_inverse'' {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f)
: ((liftFinFun_around (dropFinFun_around f bij))=(transposition (f (Fin.last n)) (Fin.last n)) ∘ f)  := by {
  unfold dropFinFun_around liftFinFun_around dropFinFun_around_lil
  simp_all only [Fin.castSucc_mk, Fin.eta, Function.comp_apply, dite_eq_ite]
  ext x
  clear bij
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
    Function.comp_apply]

  split
  {
    rename_i h
    simp_all only
  }
  {
    rename_i h
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, List.ofFn_succ,
      not_lt, Fin.val_last, Function.comp_apply]
    have xil : x=Fin.last n := by {
      exact Fin.last_le_iff.mp h
    }
    subst xil
    simp_all only [Fin.val_last, le_refl, transposition_apply_1]
  }
}

end drop_lift_around
section swap_sequence

def swapSequence_to_fun {n : ℕ} (ss : List ((Fin n)×(Fin n))) : Fin n→Fin n := by induction ss with
  | nil => exact id
  | cons h _ i => exact (transposition h.1 h.2)∘i

@[simp]lemma swapSequence_to_fun_nil {n : ℕ} : swapSequence_to_fun (n:=n) []=id := by simp_all only [swapSequence_to_fun]
@[simp]lemma swapSequence_to_fun_cons {n : ℕ} (h : (Fin n)×(Fin n)) (t : List ((Fin n)×(Fin n))) :
  swapSequence_to_fun (h :: t)=(transposition h.1 h.2)∘(swapSequence_to_fun t) := by simp_all only [swapSequence_to_fun]
@[simp]lemma swapSequence_to_fun_addLast {n : ℕ} (h : (Fin n)×(Fin n)) (t : List ((Fin n)×(Fin n))) :
  swapSequence_to_fun (t++[h])=(swapSequence_to_fun t)∘(transposition h.1 h.2) := by induction t with
    | nil => simp_all only [List.nil_append, swapSequence_to_fun_cons, swapSequence_to_fun_nil, CompTriple.comp_eq]
    | cons head tail ih => simp_all only [List.cons_append, swapSequence_to_fun_cons];rfl


lemma swapSequence_reverse_inverse {n : ℕ} (ss : List ((Fin n)×(Fin n))) : Inverse (swapSequence_to_fun ss) (swapSequence_to_fun ss.reverse) := by induction ss with
  | nil => simp_all only [swapSequence_to_fun_nil, List.reverse_nil];exact Inverse_id
  | cons head tail ih =>
    simp_all only [swapSequence_to_fun_cons, List.reverse_cons, swapSequence_to_fun_addLast];exact Inverse_circ ih (transposition_inverse head.1 head.2)

lemma swapSequence_to_fun_bijective {n : ℕ} (ss : List ((Fin n)×(Fin n))) : Function.Bijective (swapSequence_to_fun ss) := Inverse_givesBijective (swapSequence_reverse_inverse ss)

@[simp]lemma swapSequence_castSucc {n : ℕ} (ss : List ((Fin n)×(Fin n))) :
  swapSequence_to_fun (Function.lf (fun x ↦ (x.1.castSucc, x.2.castSucc)) ss)=liftFinFun_around (swapSequence_to_fun ss) := by {
    induction ss with
    | nil =>  simp_all only [listFun_nil, swapSequence_to_fun_nil,liftFinFun_around_id]
    | cons head tail ih => {
      simp_all only [listFun_cons, swapSequence_to_fun_cons]
      ext x;simp_all only [Function.comp_apply]
      finCases x
      simp_all only [Fin.coe_castSucc, Fin.is_lt, liftFinFun_around_lowRun', Fin.eta, transposition_castSucc, Function.comp_apply]
      simp_all only [liftFinFun_around_lil, Fin.val_last]
      have t (x : Fin n): Fin.last n ≠ x.castSucc := Ne.symm (succ_not_last x)
      simp_all only [ne_eq, not_false_eq_true, transposition_apply_o, Fin.val_last]
    }
  }

def Fun_to_swapSequence_step {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) (prev : (f : (Fin n)→(Fin n))→(Function.Bijective f)→(List ((Fin n)×(Fin n))))
  (prevGivesSeq : ∀g h,g = (swapSequence_to_fun (prev g h))) : {l : List ((Fin (n+1))×(Fin (n+1))) // (swapSequence_to_fun l)=f} := by {
    use if (f (Fin.last n)) = Fin.last n then (fun x => (⟨x.1.castSucc,x.2.castSucc⟩ : (Fin (n+1))×(Fin (n+1)))).lf (prev (dropFinFun_around f bij) (dropFinFun_around_bijective f bij))
      else ⟨(f (Fin.last n)),(Fin.last n)⟩ :: (fun x => (⟨x.1.castSucc,x.2.castSucc⟩ : (Fin (n+1))×(Fin (n+1)))).lf (prev (dropFinFun_around f bij) (dropFinFun_around_bijective f bij))
    by_cases eq : (f (Fin.last n)) = Fin.last n
    {
      simp_all only [ite_true, swapSequence_castSucc]
      have t := prevGivesSeq (dropFinFun_around f bij);conv => lhs;congr;rw [← t]
      exact dropLiftFinFun_inverse' f bij eq
    }
    simp_all only [ite_false]
    rw [swapSequence_to_fun_cons];
    have t : (((f (Fin.last n)), Fin.last n) : Fin (n+1) × Fin (n+1)).1=(f (Fin.last n)) := by rfl;;rw [t];clear t
    have t : (f (Fin.last n), Fin.last n).2=Fin.last n := by rfl;;rw [t];clear t
    rw [swapSequence_castSucc,← prevGivesSeq,dropLiftFinFun_inverse'' f bij]
    ext x;simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, Function.comp_apply, transposition_selfInverse_a]
  }

lemma Fun_to_swapSequence_step_val  {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f) (prev : (f : (Fin n)→(Fin n))→(Function.Bijective f)→(List ((Fin n)×(Fin n))))
  (prevGivesSeq : ∀g h,g = (swapSequence_to_fun (prev g h)))
  : (Fun_to_swapSequence_step f bij prev prevGivesSeq).val =
    if (f (Fin.last n)) = Fin.last n then (fun x => (⟨x.1.castSucc,x.2.castSucc⟩ : (Fin (n+1))×(Fin (n+1)))).lf (prev (dropFinFun_around f bij) (dropFinFun_around_bijective f bij))
      else ⟨(f (Fin.last n)),(Fin.last n)⟩ :: (fun x => (⟨x.1.castSucc,x.2.castSucc⟩ : (Fin (n+1))×(Fin (n+1)))).lf (prev (dropFinFun_around f bij) (dropFinFun_around_bijective f bij))
      := by
      unfold Fun_to_swapSequence_step;simp_all only


def Function.to_swapSequence' {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : {l : List ((Fin n)×(Fin n)) // (swapSequence_to_fun l)=f} := by
  induction n with
  | zero => refine ⟨[],?_⟩;simp_all only [swapSequence_to_fun_nil];ext x;apply finZeroElim x
  | succ n i => exact Fun_to_swapSequence_step f bij (fun g b => (i g b).val) (fun g b => (i g b).property.symm)

@[simp]lemma Function.to_swapSequence'_zero (f : (Fin 0)→(Fin 0)) (bij : Function.Bijective f) : (f.to_swapSequence' bij).val = [] := by
  unfold Function.to_swapSequence';simp_all only [Nat.rec_zero]

lemma Function.to_swapSequence'_succ {n : ℕ} (f : (Fin (n+1))→(Fin (n+1))) (bij : Function.Bijective f)
  : (f.to_swapSequence' bij).val = (Fun_to_swapSequence_step f bij (fun g b => (g.to_swapSequence' b).val) (fun g b => (g.to_swapSequence' b).property.symm)).val := by
  unfold Function.to_swapSequence';simp_all only

def Function.to_swapSequence {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : List ((Fin n)×(Fin n)) := (f.to_swapSequence' bij).val

@[simp]lemma Function.to_swapSequence_toFunc {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : (swapSequence_to_fun (f.to_swapSequence bij))=f
  := (f.to_swapSequence' bij).property

@[simp]lemma to_swapSequence_id {n : ℕ} {h : Function.Bijective id} : (id (α := (Fin n))).to_swapSequence h =[] := by {
  unfold Function.to_swapSequence
  induction n with
  | zero => simp_all only [Function.to_swapSequence'_zero]
  | succ n i => {
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, id_eq, Multiset.map_id', forall_true_left, Function.to_swapSequence'_succ, Fun_to_swapSequence_step_val, id_eq]
    have t {h₁ : Function.Bijective (dropFinFun_around id h)}: (Function.to_swapSequence' (dropFinFun_around id h) h₁).val =
      (Function.to_swapSequence' (id (α:= (Fin n))) Function.bijective_id).val
      := by {
         rw [← Function.to_swapSequence];conv => rhs;rw [← Function.to_swapSequence]
         simp_all only [dropFinFun_around_id]
    }
    rw [t,i];simp_all only [dropFinFun_around_id, id_eq, listFun_nil, ite_true]
  }
}


end swap_sequence
section Fin_InvFun

def Fin_InvFun {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : (Fin n)→(Fin n) := swapSequence_to_fun (f.to_swapSequence bij).reverse

lemma Fin_InvFun_Bijective {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : Function.Bijective (Fin_InvFun f bij)  := by
  unfold Fin_InvFun;exact swapSequence_to_fun_bijective (Function.to_swapSequence f bij).reverse

lemma Fin_InvFun_Inverse  {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : Inverse f (Fin_InvFun f bij) := by
  unfold Fin_InvFun;have t := f.to_swapSequence_toFunc bij;conv => lhs;rw [← t]
  exact swapSequence_reverse_inverse (Function.to_swapSequence f bij)


def Fin_InvFun' {n : ℕ} (f : (Fin n)→(Fin n)) (bij : Function.Bijective f) : {g : Fin n→Fin n
  // (Function.Bijective g)∧Inverse f g} := ⟨Fin_InvFun f bij,⟨Fin_InvFun_Bijective f bij,Fin_InvFun_Inverse f bij⟩⟩

end Fin_InvFun
section finEquiv


def finEquivCexists_Decidable {n : ℕ} (f : (Fin n)→(Fin n)) : Cexists_Decidable (fun equiv : (Fin n)≃(Fin n) => equiv.toFun=f) := by {
  have bijectiveDecidable : Decidable f.Bijective := by infer_instance
  cases bijectiveDecidable with
  | isFalse h => {
    refine .CE_isFalse ?_
    intro equiv
    have test := equivIsBijective equiv
    simp_all only [Fin.univ_val_map, Multiset.map_univ_val_equiv, ne_eq]
    contrapose h
    simp_all only [Decidable.not_not]
    rw [← h]
    exact test
  }
  | isTrue bijective => {
    refine .CE_isTrue ?_ ?_
    {
      exact ⟨f,(Fin_InvFun' f bijective).val,(Fin_InvFun' f bijective).property.right.right,(Fin_InvFun' f bijective).property.right.left⟩
    }
    {
      simp_all only
    }
  }
}

def finEquivDecidable {n : ℕ} (f : (Fin n)→(Fin n)) : Decidable (∃equiv : (Fin n)≃(Fin n), equiv.toFun=f) := CED_to_Decidable (finEquivCexists_Decidable f)

end finEquiv


end Fin_Bijection

section Permutations


lemma swapGivesPerm' (l : List T) (x y : Fin l.length) : l.Perm ((l.get ∘ (transposition x y)).toList) := by {
  by_cases eq : x=y
  subst eq;simp_all only [transposition_id, CompTriple.comp_eq, List.toFinFun_toList, List.Perm.refl]
  by_cases le : ¬ (x<y)
  any_goals simp_all only [not_not]
  replace le : y<x := by contrapose eq;simp_all only [not_lt, Decidable.not_not];exact Fin.le_antisymm eq le
  all_goals clear eq
  rw [transposition_comm];rename Fin l.length => x;rename_i y
  all_goals {
    match l with
    | [] => simp_all only [List.length_nil, Function.toList_zero, List.Perm.refl]
    | head :: [] => simp_all only [List.length_cons, List.length_nil, Function.toList_succ, Function.comp_apply, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero,
      Function.toList_zero, List.Perm.refl]
    | head₁ :: head₂ :: tail => {
      finCasez y;case refine_2 => exfalso;simp_all only [Fin.not_lt_zero]
      finCasez x
      {
        finCasez y
        case refine_1.refine_1.refine_2 => exfalso;simp_all only [Fin.succ_zero_eq_one, Fin.lt_one_iff];exact Fin.succ_ne_zero x le

        rw [Function.toList_succ]
        refine .trans (l₂ := head₁ :: (((head₁ :: head₂ :: tail).get ∘ transposition x.succ y.succ.succ) ∘ Fin.succ).toList) ?_ ?_
        {
          refine .cons head₁ ?_
          sorry
        }
        {
          exact List.Perm.refl (head₁ :: (((head₁ :: head₂ :: tail).get ∘ transposition x.succ y.succ.succ) ∘ Fin.succ).toList)
        }
      }
      {
        sorry
      }


    }
  }

  /-old code from here-/
  all_goals {
    match l with
    | [] => simp_all only [List.length_nil, List.rInd_nil, eq_mp_eq_cast, cast_eq, finFunToList_zero, List.Perm.refl]
    | head :: [] => simp_all only [List.length_cons, List.length_nil, List.rInd_cons, Fin.val_eq_zero, lt_self_iff_false, neZero_zero_iff_false, Fin.mk_zero', List.rInd_nil,
      eq_mp_eq_cast, cast_eq, dite_false, finFunToList_succ, Nat.cast_zero, Function.comp_apply, finFunToList_zero, List.Perm.refl]
    | head₁ :: head₂ :: tail => {
      rw [List.rInd_cons];rw [finFunToList_succ,Function.comp_apply]
      finCases y
      {
        finCases x
        {
          split
          {
            rename_i h
            exfalso;contrapose h;simp_all only [List.length_cons, Fin.castSucc_lt_castSucc_iff, not_false_eq_true, not_lt]
            have e : ↑(transposition x.castSucc y.castSucc (Fin.last (tail.length + 1))) = (Fin.last (tail.length + 1)) := by {
              have e (a : Fin (head₂ :: tail).length) : (Fin.last (tail.length + 1)) ≠ a.castSucc := succ_not_last' a
              simp_all only [List.length_cons, ne_eq, not_false_eq_true, transposition_apply_dif]
            }
            rw [e];simp_all only [List.length_cons, Fin.val_last, le_refl]
          }
          {
            refine .cons head₁ ?_
            have t : (((fun i : Fin (head₁ :: head₂ :: tail).length ↦ if lt : ↑i < (head₂ :: tail).length then (head₂ :: tail).rInd (Eq.refl (head₂ :: tail).length) ⟨↑i, lt⟩ else head₁)
              ∘ transposition x.castSucc y.castSucc) ∘ Fin.castSucc)
              = ((head₂ :: tail).rInd (Eq.refl (head₂ :: tail).length)) ∘ transposition x y := by {
                ext i;simp_all only [List.length_cons, Fin.castSucc_lt_castSucc_iff, not_lt,
                  List.rInd_cons, Function.comp_apply, transposition_castSucc, Fin.coe_castSucc,
                  Fin.is_lt, dite_true]
              }
            rw [t]
            exact swapGivesPerm' (head₂ :: tail) x y
          }
        }
        {
          exfalso;have lt : (Fin.last tail.length).val + 1 < tail.length + 1 := by trans y.val;exact le;exact y.isLt
          simp_all only [List.length_cons, Fin.val_last, lt_self_iff_false]
        }
      }
      {
        have s : (transposition x (Fin.last (head₂ :: tail).length) (Fin.last (head₂ :: tail).length)) = x := by simp_all only [List.length_cons, transposition_apply_same']
        rw [s]

        finCases x
        {
          finCases x
          {
            simp_all only [List.length_cons, transposition_apply_same', Fin.coe_castSucc, List.rInd_cons, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true, finFunToList_succ, Function.comp_apply]
            have h₁ : ↑x < tail.length + 1 := by trans tail.length;exact x.isLt;simp_all only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]
            simp_all only [ite_true]
            have h₂ : (transposition x.castSucc.castSucc (Fin.last (tail.length + 1)) (Fin.last tail.length).castSucc) = (Fin.last tail.length).castSucc := by {
              rw [transposition_apply_dif]
              by_contra c;simp_all only [Fin.castSucc_inj];contrapose c;exact succ_not_last' x
              exact succ_not_last (Fin.last tail.length)
            }
            simp_all only [Fin.coe_castSucc, Fin.val_last, lt_add_iff_pos_right, Nat.lt_one_iff,
              pos_of_gt, lt_self_iff_false, dite_false, dite_eq_ite, ite_true]
            refine .trans (.swap head₂ head₁ tail) ?_
            refine .trans ?_ (.swap (tail.rInd (Eq.refl tail.length) x) head₂ (finFunToList ((((fun i : Fin (tail.length + 1 + 1) ↦ if h : ↑i < tail.length + 1 then if h_1 : ↑i < tail.length
              then tail.rInd (Eq.refl tail.length) ⟨↑i, (Eq.mpr_prop (Eq.refl (↑i < tail.length)) h_1)⟩ else head₂ else head₁)
              ∘ transposition x.castSucc.castSucc (Fin.last (tail.length + 1))) ∘ Fin.castSucc) ∘ Fin.castSucc)))
            refine (.cons head₂ ?_)
            have s : tail.rInd (Eq.refl tail.length) x :: finFunToList ((((fun i : Fin (tail.length + 1 + 1) ↦ if h : ↑i < tail.length + 1 then if h_1 : ↑i < tail.length
              then tail.rInd (Eq.refl tail.length) ⟨↑i, (Eq.mpr_prop (Eq.refl (↑i < tail.length)) h_1)⟩ else head₂ else head₁)
              ∘ transposition x.castSucc.castSucc (Fin.last (tail.length + 1))) ∘ Fin.castSucc) ∘ Fin.castSucc) = (finFunToList (((head₁ :: tail).rInd (by rfl)) ∘ (transposition x.castSucc (Fin.last tail.length))))
              := by {
                clear h₁ h₂
                simp_all only [dite_eq_ite, List.rInd_cons, finFunToList_succ, Function.comp_apply,
                  transposition_apply_same', Fin.coe_castSucc, Fin.is_lt, Fin.eta, ite_true,
                  List.cons.injEq, true_and]
                have s : ((((fun i : Fin (tail.length + 1 + 1) ↦ if ↑i < tail.length + 1 then if h_1 : ↑i < tail.length
                  then tail.rInd (Eq.refl tail.length) ⟨↑i, Eq.mpr_prop (Eq.refl (↑i < tail.length)) h_1⟩ else head₂ else head₁) ∘
                  transposition x.castSucc.castSucc (Fin.last (tail.length + 1))) ∘ Fin.castSucc) ∘ Fin.castSucc) =
                  (((fun i : Fin (tail.length + 1) ↦ if lt : ↑i < tail.length then tail.rInd (Eq.refl tail.length) ⟨↑i, lt⟩ else head₁) ∘ transposition x.castSucc (Fin.last tail.length)) ∘ Fin.castSucc)
                  := by {
                    ext i;simp_all only [Function.comp_apply]
                    by_cases iix : i=x
                    {
                      subst iix;simp_all only [transposition_apply_same, Fin.val_last, lt_self_iff_false,
                        ne_eq, not_true_eq_false, add_lt_iff_neg_left, not_lt_zero', dite_true,
                        dite_false, ite_false]
                    }
                    {
                      have t : (transposition x.castSucc.castSucc (Fin.last (tail.length + 1)) i.castSucc.castSucc) = i.castSucc.castSucc := by {
                        rw [transposition_apply_dif];contrapose iix;simp_all only [ne_eq, Fin.castSucc_inj, Decidable.not_not, not_true_eq_false, not_false_eq_true]
                        exact succ_not_last i.castSucc
                      }
                      rw [t];
                      have t : (transposition x.castSucc (Fin.last tail.length) i.castSucc) = i.castSucc := by {
                        rw [transposition_apply_dif];contrapose iix;simp_all only [ne_eq, Fin.castSucc_inj, Decidable.not_not, not_true_eq_false, not_false_eq_true]
                        exact succ_not_last i
                      }
                      rw [t]
                      simp_all only [ne_eq, Fin.castSucc_inj, not_false_eq_true, Fin.coe_castSucc,
                        Fin.is_lt, Fin.eta, dite_eq_ite, ite_true, ite_eq_left_iff, not_lt]
                      intro gt;exfalso;obtain ⟨i,lt⟩ := i;simp_all only [Fin.castSucc_mk];contrapose gt;simp_all only [not_false_eq_true, not_le]
                      trans tail.length;exact lt;simp_all only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]
                    }
                  }
                rw [s]
              }
            rw [s]
            exact swapGivesPerm' (head₁ :: tail) x.castSucc (Fin.last tail.length)


          }
          {
            simp_all only [List.length_cons, transposition_apply_same', Fin.coe_castSucc, Fin.val_last,
              lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, List.rInd_cons, lt_self_iff_false,
              dite_false, dite_eq_ite, ite_true, finFunToList_succ, Function.comp_apply,
              transposition_apply_same, ne_eq, not_true_eq_false, add_lt_iff_neg_left, not_lt_zero',
              dite_true]
            refine .trans (.swap head₂ head₁ tail) (.cons head₂ (.cons head₁ ?_))
            have s : ((((fun i : (Fin (tail.length + 1 + 1)) ↦ if h : ↑i < tail.length + 1 then if h_1 : ↑i < tail.length then tail.rInd (Eq.refl tail.length) ⟨↑i, Eq.mpr_prop (Eq.refl (↑i < tail.length)) h_1⟩
              else head₂ else head₁) ∘ transposition (Fin.last tail.length).castSucc (Fin.last (tail.length + 1))) ∘ Fin.castSucc) ∘ Fin.castSucc)
               = ((fun i : (Fin tail.length) ↦ tail.rInd (Eq.refl tail.length) i)) := by {
                ext i;simp_all only [dite_eq_ite, Function.comp_apply]
                have s : ↑(transposition (Fin.last tail.length).castSucc (Fin.last (tail.length + 1)) i.castSucc.castSucc) = i.castSucc.castSucc := by {
                  rw [transposition_apply_dif]
                  by_contra c;rw [← Fin.val_inj] at c;simp_all only [Fin.coe_castSucc, Fin.val_last];obtain ⟨i,ln⟩ := i;simp_all only
                  contrapose ln;simp_all only [not_false_eq_true, lt_self_iff_false]
                  exact succ_not_last i.castSucc
                }
                rw [s]
                have t : ↑i.castSucc.castSucc < tail.length + 1 := by
                  simp_all only [Fin.coe_castSucc];trans tail.length;exact i.isLt;simp_all only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]
                simp_all only [Fin.coe_castSucc, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true]
               }
            rw [s];simp_all only [dite_eq_ite, List.toFinFun_toList, List.Perm.refl]
          }
        }
        {
          exfalso;simp_all only [List.length_cons, lt_self_iff_false]
        }
      }
    }
  }
}

lemma swapGivesPerm (l : List T) (x y : Fin l.length) : l.Perm ((l.get) ∘ (transposition x y)).toList := swapGivesPerm' l x y

lemma swapSequenceGivesPerm (l : List T) (ss : List ((Fin l.length)×(Fin l.length))) : l.Perm ((l.get ∘ (swapSequence_to_fun ss)).toList) := by {
  have ssr : {ssr : List (Fin l.length × Fin l.length) // ss.reverse=ssr} := by use ss.reverse
  obtain ⟨ssr,ssrh⟩ := ssr
  revert ss
  induction ssr with
  | nil => {
    intro ss ssrh;
    have sse : ss = [] := List.reverse_eq_nil_iff.mp ssrh
    subst sse;simp_all only [List.reverse_nil, swapSequence_to_fun_nil, CompTriple.comp_eq, List.toFinFun_toList, List.Perm.refl]
  }
  | cons head tail ih => {
    intro ss ssrh;simp_all only [List.reverse_eq_cons_iff, swapSequence_to_fun_addLast]
    specialize ih tail.reverse (by simp_all only [List.reverse_reverse])
    refine .trans ih ?_
    have t : l.get ∘ swapSequence_to_fun tail.reverse ∘ transposition head.1 head.2 = (l.get ∘ swapSequence_to_fun tail.reverse) ∘ transposition head.1 head.2 := by rfl
    conv => rhs;congr;rw [t]

    sorry
  }
}

/-Don't know how to implement the statement.
lemma Equiv.perm {n : ℕ} (f : Equiv (Fin n) (Fin n)) : (l : List T)→(h : l.length = n)→l.Perm (((l.get) ∘ f).toList) := by {
  intro l h;subst h
  have t : ⇑f = swapSequence_to_fun (f.toFun.to_swapSequence (equivIsBijective f)) := by simp_all only [toFun_as_coe, Function.to_swapSequence_toFunc]
  rw [t];exact swapSequenceGivesPerm l (Function.to_swapSequence f.toFun (equivIsBijective f))
}
-/

end Permutations
