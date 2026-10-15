import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

import Test.Decidable_Graph

import Test.g6complete7
import Test.g6complete8
import Test.g6complete9

/--stores a list of 6 bools in a character in the style of graph6-/
def bin6ToChar (l : List Bool) (h : l.length = 6) : Char := by {
  refine Char.ofNat ?_
  have mapBoolToNat := (λ (x : Bool) ↦ if x then 1 else 0)

  exact (((mapBoolToNat l[0] <<< 5) + (mapBoolToNat l[1] <<< 4) + (mapBoolToNat l[2] <<< 3) + (mapBoolToNat l[3] <<< 2)
    + (mapBoolToNat l[4] <<< 1) + (mapBoolToNat l[5])))+63
}

/--takes a list of 6 bools from a character in the style of graph6-/
def charToBin6 (c : Char) : List Bool := by {
  replace c := c.toNat
  have mapNatToBool := (λ (x : Nat) ↦ if Odd x then true else false)

  exact [mapNatToBool ((c - 63) >>> 5),mapNatToBool ((c - 63) >>> 4),mapNatToBool ((c - 63) >>> 3),
    mapNatToBool ((c - 63) >>> 2),mapNatToBool ((c - 63) >>> 1),mapNatToBool (c - 63)]
}
lemma charToBin6_length6 (c : Char) : (charToBin6 c).length = 6 := by {
  unfold charToBin6;simp_all only [Bool.if_false_right, Bool.and_true, List.length_cons, List.length_nil, zero_add]
}


lemma bin6ToChar_charToBin6 (c : Char) (lt : c.toNat < 127) (gt : c.toNat > 62) (h : (charToBin6 c).length=6 := charToBin6_length6 c)
  : bin6ToChar (charToBin6 c) h = c := by {

  have conc (x : Fin 64) (xh : (charToBin6 (Char.ofNat (x.val+63))).length = 6)
    : bin6ToChar (charToBin6 (Char.ofNat (x.val+63))) xh = (Char.ofNat (x.val+63)) := by {
      revert x
      clear h gt lt c
      decide +native
    }

  have fh : c.toNat - 63 < 64 := Nat.sub_lt_left_of_lt_add gt lt

  have r : (Char.ofNat ((⟨c.toNat - 63,fh⟩: Fin 64).val+63))=c := by {
    simp_all only [gt_iff_lt]
    have r : (c.toNat - 63 + 63) = c.toNat := Nat.sub_add_cancel gt
    rw [r]
    exact Char.ofNat_toNat c
  }
  have t := conc ⟨c.toNat - 63,fh⟩
  rw [r] at t;specialize t h;exact t
}

instance limitedLengthList_fintype (n : ℕ) : Fintype {l : List Bool // l.length = n} := by {
  cases n with
  | zero => {
    refine ⟨?_,?_⟩
    refine ⟨⟦[⟨[],?_⟩]⟧,?_⟩
    simp_all only [List.length_nil]
    simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_singleton, Multiset.nodup_singleton]

    intro l
    simp_all only [Multiset.quot_mk_to_coe, Multiset.coe_singleton, Finset.mem_mk, Multiset.mem_singleton]
    obtain ⟨l,l0⟩ := l
    rw [← Subtype.val_inj];simp_all only
    simp_all only [List.length_eq_zero]
  }
  | succ n => {
    have t := limitedLengthList_fintype n
    refine ⟨?_,?_⟩
    refine (Finset.univ : Finset {l : List Bool // l.length = n}).map ⟨λ l ↦ ⟨(true :: l.val),?_⟩,?_⟩ ⊔ (Finset.univ : Finset {l : List Bool // l.length = n}).map ⟨λ l ↦ ⟨(false :: l.val),?_⟩,?_⟩
    simp_all only [List.length_cons, List.Vector.length_val]
    intro l k me;simp_all only [Subtype.mk.injEq, List.cons.injEq, true_and];rw [Subtype.val_inj] at me;exact me
    simp_all only [List.length_cons, List.Vector.length_val]
    intro l k me;simp_all only [Subtype.mk.injEq, List.cons.injEq, true_and];rw [Subtype.val_inj] at me;exact me

    intro ⟨l,ll⟩
    cases l with
    | nil => exfalso;simp_all only [List.length_nil, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false]
    | cons head tail => {
      simp_all only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_map, Finset.mem_univ,
        Function.Embedding.coeFn_mk, Subtype.mk.injEq, List.cons.injEq, Bool.true_eq, true_and,
        exists_and_left, Subtype.exists, exists_prop, exists_eq_right, Bool.false_eq]
      by_cases het : head=true
      {
        left;simp_all only [List.length_cons, add_left_inj, and_self]
      }
      {
        right;simp_all only [List.length_cons, add_left_inj, Bool.not_eq_true, and_self]
      }
    }
  }
}

lemma charToBin6_bin6ToChar (l : List Bool) (h : l.length = 6) : charToBin6 (bin6ToChar l h) = l := by {
  have conc (t : {l : List Bool // l.length = 6}) : charToBin6 (bin6ToChar t.val t.property) = t.val := by {
    clear l h
    revert t
    decide +native
  }
  exact conc ⟨l,h⟩
}

/--stores a list of  bools in a list of characters in the style of graph6-/
def binToChars (l : List Bool)  : List Char := if l.length=0
  then []
  else if h : l.length<6
  then [bin6ToChar (l.rightpad 6 false) (by {
      simp_all only [List.rightpad, List.length_append, List.length_replicate]
      omega
    })]
  else (bin6ToChar (l.take 6) (by {
    replace h : l.length≥6 := by simp_all only [not_lt, ge_iff_le]
    exact List.length_take_of_le h
  })) :: (binToChars (l.drop 6))
termination_by l.length

/--takes a list of bools from a list of character in the style of graph6-/
def charsToBin (c : List Char) : List Bool := match c with
  | [] => []
  | (head :: tail) => (charToBin6 head) ++ (charsToBin tail)

lemma binToChars_charsToBin (c : List Char) (ir : ∀c₀ ∈ c,c₀.toNat>62 ∧ c₀.toNat<127): binToChars (charsToBin c) = c := by {
  unfold charsToBin binToChars
  simp_all only [List.rightpad]
  match c with
  | [] => {
    simp_all only [List.length_nil, Nat.ofNat_pos, tsub_zero, List.nil_append, List.take_nil, List.drop_nil, dite_false, dite_true, ite_true]
  }
  | (head :: tail) => {
    simp_all only [List.length_eq_zero, List.length_append, AddLeftCancelMonoid.add_eq_zero, List.append_assoc]
    have ne : ¬ (charToBin6 head = []) := by {
      exact List.getLast?_isSome.mp rfl
    }
    simp_all only [false_and, ite_false]
    have t : binToChars (List.drop 6 (charToBin6 head ++ charsToBin tail)) = tail := by {
      have t : List.drop 6 (charToBin6 head ++ charsToBin tail) = charsToBin tail := by {
        rfl
      }
      rw [t];refine binToChars_charsToBin tail ?_
      intro c₀ c₀i;specialize ir c₀ ?_
      simp_all only [List.mem_cons, gt_iff_lt, forall_eq_or_imp, or_true]
      exact ir
    }
    rw [t];clear t
    have t : ¬((charToBin6 head).length + (charsToBin tail).length < 6) := by {
      have t : (charToBin6 head).length = 6 := by rfl
      rw [t];by_contra c;simp_all only [List.mem_cons, gt_iff_lt, forall_eq_or_imp, add_lt_iff_neg_left, not_lt_zero']
    }
    simp_all only [dite_false, List.cons.injEq, and_true]
    have t : (List.take 6 (charToBin6 head ++ charsToBin tail)) = charToBin6 head := by {
      rfl
    }
    conv => lhs;lhs;rw [t]
    specialize ir head;simp_all only [not_lt, List.mem_cons, true_or, gt_iff_lt, forall_const]
    apply bin6ToChar_charToBin6
    exact ir.right
    exact ir.left
  }
}

@[simp]lemma prefixAppend {T : Type} (l k j : List T) : l ++ k <+: l ++ j ↔ k <+:j := by {
  match l with
  | [] => simp_all only [List.nil_append]
  | (head :: tail) => simp_all only [List.cons_append, List.cons_prefix_cons, List.prefix_append_right_inj, true_and]
}


lemma List.replicateEq {T : Type} (n k : ℕ) (t : T) : (List.replicate n t) = (List.replicate k t) ↔ n=k := by {
  simp_all only [replicate_inj, or_true, and_true]
}

lemma charsToBin_binToChars (l : List Bool) : (charsToBin (binToChars l))
  = l ++ (List.replicate (if l.length%6=0 then 0 else (6-l.length%6)) false)  := by {
  unfold binToChars
  by_cases l0 : l.length=0
  {
    simp_all only [List.length_eq_zero, List.length_nil, Nat.ofNat_pos, List.rightpad, tsub_zero,
      List.nil_append, List.take_nil, List.drop_nil, dite_false, dite_true, ite_true, Nat.zero_mod,
      List.replicate_zero, List.append_nil]
    rfl
  }
  by_cases ls : l.length<6
  {
    simp_all only [List.length_eq_zero, List.rightpad, dite_true, ite_false]
    unfold charsToBin
    simp_all only
    have t : charsToBin [] = [] := by rfl
    rw [t];clear t
    simp_all only [List.append_nil]
    rw [charToBin6_bin6ToChar]
    simp_all only [List.append_cancel_left_eq, List.replicate_inj, or_true, and_true]
    have me : l.length % 6 = l.length := by {
      have me (n : Fin 6) : n.val % 6 = n := by clear l l0 ls;revert n;decide
      specialize me ⟨l.length,ls⟩
      simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
    }
    have nz : l.length % 6 ≠ 0 := by {
      rw [me];contrapose l0;simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, ne_eq,
       List.length_eq_zero, Decidable.not_not, not_true_eq_false, not_false_eq_true]
    }
    rw [me]
    simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, ne_eq, List.length_eq_zero, ite_false]
  }
  {
    simp_all only [List.length_eq_zero, not_lt, List.rightpad, Nat.sub_eq_zero_of_le, List.replicate_zero, List.append_nil, ite_false]
    unfold charsToBin
    simp_all only [dite_false]
    rw [charToBin6_bin6ToChar]
    have t₂ : l = (l.take 6) ++ (l.drop 6) := Eq.symm (List.take_append_drop 6 l)
    conv => rhs;rw [t₂];rw [List.append_assoc]
    rw [List.append_cancel_left_eq,charsToBin_binToChars,List.append_cancel_left_eq,List.replicate_inj]
    constructor
    rw [(id (Eq.symm t₂)),List.length_drop,(Eq.symm (Nat.mod_eq_sub_mod ls))]
    right;rfl
  }
}
termination_by l.length

lemma charsToBin_binToChars' (l : List Bool) : l <+: (charsToBin (binToChars l))  := by {
  rw [charsToBin_binToChars];exact List.prefix_append l ?_
}

def g6_ind_pairToSingle (v u : ℕ) (dif : v ≠ u) : ℕ := if v < u
  then v + ((u * (u-1))/2)
  else g6_ind_pairToSingle u v dif.symm

lemma g6_ind_pairToSingle_symm (v u : ℕ) (dif : v ≠ u) (dif' : u ≠ v) : g6_ind_pairToSingle v u dif = g6_ind_pairToSingle u v dif' := by {
  unfold g6_ind_pairToSingle
  by_cases h : v<u
  {
    have h' : ¬u < v := by contrapose h;simp_all only [ne_eq, not_lt, not_le];exact Nat.le_of_succ_le h
    unfold g6_ind_pairToSingle
    simp_all only [ite_false,ite_true]
  }
  {
    have h' : u < v := by contrapose h;simp_all only [ne_eq, not_lt, not_le];exact Nat.lt_of_le_of_ne h dif
    unfold g6_ind_pairToSingle
    simp_all only [ite_false,ite_true]
  }
}


def g6_ind_singleToPair (k : ℕ) : ℕ × ℕ :=
  ⟨k - (((((Nat.sqrt (1 + 8*k))+1)/2)*((((Nat.sqrt (1 + 8*k))+1)/2) - 1))/2),(((Nat.sqrt (1 + 8*k))+1)/2)⟩

lemma g6_ind_singleToPair_lt (k : ℕ) : (g6_ind_singleToPair k).1 < (g6_ind_singleToPair k).2 := by {
  unfold g6_ind_singleToPair
  simp_all only
  rw [← Nat.add_lt_add_iff_right (k:= ((1 + 8 * k).sqrt + 1) / 2 * (((1 + 8 * k).sqrt + 1) / 2 - 1) / 2)]
  rw [(Nat.sub_add_cancel ?m)]
  case m => rename' k => n;{
    rw [← mul_le_mul_right (a:=2)];any_goals decide


    trans ((1 + 8 * n).sqrt + 1) / 2 * (((1 + 8 * n).sqrt + 1) / 2 - 1)
    omega
    rw [← mul_le_mul_right (a:=2)];any_goals decide

    conv => lhs;rw [← Nat.mul_comm,← Nat.mul_assoc]
    conv => lhs;lhs;rw [Nat.mul_comm]

    trans ((1 + 8 * n).sqrt + 1) * (((1 + 8 * n).sqrt + 1) / 2 - 1)
    {
      cases n with
      | zero => decide +native
      | succ n => cases n with
      | zero => decide +native
      | succ n => {
        rw [mul_le_mul_right];exact Nat.div_mul_le_self ((1 + 8 * (n + 1 + 1)).sqrt + 1) 2
        simp_all only [tsub_pos_iff_lt]
        have t : 3 ≤  (1 + 8 * (n + 1 + 1 )).sqrt := by {
          have t : (1 + 8 * (n + 1 + 1)) = 17+8*n := by omega
          rw [t];trans (17 : ℕ).sqrt
          clear n t;decide +native
          apply Nat.sqrt_le_sqrt
          simp_all only [le_add_iff_nonneg_right, zero_le]
        }

        calc
        _ < 2 := by omega
        _ ≤ (3 + 1) / 2 := by omega
        _ ≤ ((1 + 8 * (n + 1 + 1)).sqrt + 1) / 2 := by {
          apply Nat.div_le_div_right
          apply Nat.add_le_add_right
          exact t
        }
      }
    }
    {
      rw [← mul_le_mul_right (a:=2)];any_goals decide
      have t : ((1 + 8 * n).sqrt + 1) * (((1 + 8 * n).sqrt + 1) / 2 - 1) * 2
        = ((1 + 8 * n).sqrt + 1) * ((((1 + 8 * n).sqrt + 1) / 2 - 1) * 2) := Nat.mul_assoc ((1 + 8 * n).sqrt + 1) (((1 + 8 * n).sqrt + 1) / 2 - 1) 2
      rw [t];clear t
      have t : ((((1 + 8 * n).sqrt + 1) / 2 - 1) * 2) = ((((1 + 8 * n).sqrt + 1) / 2)*2 - 1*2) :=
        Nat.mul_sub_right_distrib (((1 + 8 * n).sqrt + 1) / 2) 1 2
      rw [t];clear t
      trans ((1 + 8 * n).sqrt + 1) * (((1 + 8 * n).sqrt + 1) - 1 * 2)
      simp_all only [one_mul, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, mul_le_mul_left, tsub_le_iff_right]
      trans ((1 + 8 * n).sqrt + 1)
      exact Nat.div_mul_le_self ((1 + 8 * n).sqrt + 1) 2
      exact le_tsub_add
      have t :   ((1 + 8 * n).sqrt + 1 - 1 * 2)=((1 + 8 * n).sqrt - 1) := by omega
      rw [t];clear t
      calc
      _ = ((1 + 8 * n).sqrt * ((1 + 8 * n).sqrt - 1)+ 1 * ((1 + 8 * n).sqrt - 1)) :=
        Nat.add_mul (1 + 8 * n).sqrt 1 ((1 + 8 * n).sqrt - 1)
      _ = ((1 + 8 * n).sqrt * ((1 + 8 * n).sqrt - 1)+ ((1 + 8 * n).sqrt - 1)) :=
        by simp_all only [one_mul]
      _ = (((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt * 1)+ ((1 + 8 * n).sqrt - 1)) :=
        by simp_all only [mul_one, add_left_inj];exact Nat.mul_sub_one (1 + 8 * n).sqrt (1 + 8 * n).sqrt
      _ = (((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt) + ((1 + 8 * n).sqrt - 1)) :=
        by simp_all only [mul_one]
      _ = ((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt + (1 + 8 * n).sqrt) - 1 :=
        by {
          refine Eq.symm (Nat.add_sub_assoc ?_ ((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt))
          trans (1 : ℕ).sqrt
          rfl
          apply Nat.sqrt_le_sqrt
          simp_all only [le_add_iff_nonneg_right, zero_le]
        }
      _ ≤ _ := by {
        simp_all only [tsub_le_iff_right]
        have t : (1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt + (1 + 8 * n).sqrt = (1 + 8 * n).sqrt * (1 + 8 * n).sqrt := by {
          refine Nat.sub_add_cancel ?_
          exact Nat.le_mul_self (1 + 8 * n).sqrt
        }
        rw [t];clear t
        calc
        _ ≤ 1+8*n := Nat.sqrt_le (1 + 8 * n)
        _ = _ := by omega
      }
    }
  }
  sorry
}

lemma g6_ind_singleToPair_ne (k : ℕ) : (g6_ind_singleToPair k).1 ≠ (g6_ind_singleToPair k).2 := by {
  have h := g6_ind_singleToPair_lt k
  contrapose h;simp_all only [ne_eq, Decidable.not_not, lt_self_iff_false, not_false_eq_true]
}

lemma g6_ind_pairToSingle_singleToPair (n : ℕ)
  : g6_ind_pairToSingle (g6_ind_singleToPair n).1 (g6_ind_singleToPair n).2 (g6_ind_singleToPair_ne n) = n
  := by {
    unfold g6_ind_singleToPair g6_ind_pairToSingle
    simp_all only

    have cond := g6_ind_singleToPair_lt n
    unfold g6_ind_singleToPair at cond
    simp_all only [ite_true];clear cond
    apply Nat.sub_add_cancel
    rw [← mul_le_mul_right (a:=2)];any_goals decide


    trans ((1 + 8 * n).sqrt + 1) / 2 * (((1 + 8 * n).sqrt + 1) / 2 - 1)
    omega
    rw [← mul_le_mul_right (a:=2)];any_goals decide

    conv => lhs;rw [← Nat.mul_comm,← Nat.mul_assoc]
    conv => lhs;lhs;rw [Nat.mul_comm]

    trans ((1 + 8 * n).sqrt + 1) * (((1 + 8 * n).sqrt + 1) / 2 - 1)
    {
      cases n with
      | zero => decide +native
      | succ n => cases n with
      | zero => decide +native
      | succ n => {
        rw [mul_le_mul_right];exact Nat.div_mul_le_self ((1 + 8 * (n + 1 + 1)).sqrt + 1) 2
        simp_all only [tsub_pos_iff_lt]
        have t : 3 ≤  (1 + 8 * (n + 1 + 1 )).sqrt := by {
          have t : (1 + 8 * (n + 1 + 1)) = 17+8*n := by omega
          rw [t];trans (17 : ℕ).sqrt
          clear n t;decide +native
          apply Nat.sqrt_le_sqrt
          simp_all only [le_add_iff_nonneg_right, zero_le]
        }

        calc
        _ < 2 := by omega
        _ ≤ (3 + 1) / 2 := by omega
        _ ≤ ((1 + 8 * (n + 1 + 1)).sqrt + 1) / 2 := by {
          apply Nat.div_le_div_right
          apply Nat.add_le_add_right
          exact t
        }
      }
    }
    {
      rw [← mul_le_mul_right (a:=2)];any_goals decide
      have t : ((1 + 8 * n).sqrt + 1) * (((1 + 8 * n).sqrt + 1) / 2 - 1) * 2
        = ((1 + 8 * n).sqrt + 1) * ((((1 + 8 * n).sqrt + 1) / 2 - 1) * 2) := Nat.mul_assoc ((1 + 8 * n).sqrt + 1) (((1 + 8 * n).sqrt + 1) / 2 - 1) 2
      rw [t];clear t
      have t : ((((1 + 8 * n).sqrt + 1) / 2 - 1) * 2) = ((((1 + 8 * n).sqrt + 1) / 2)*2 - 1*2) :=
        Nat.mul_sub_right_distrib (((1 + 8 * n).sqrt + 1) / 2) 1 2
      rw [t];clear t
      trans ((1 + 8 * n).sqrt + 1) * (((1 + 8 * n).sqrt + 1) - 1 * 2)
      simp_all only [one_mul, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, mul_le_mul_left, tsub_le_iff_right]
      trans ((1 + 8 * n).sqrt + 1)
      exact Nat.div_mul_le_self ((1 + 8 * n).sqrt + 1) 2
      exact le_tsub_add
      have t :   ((1 + 8 * n).sqrt + 1 - 1 * 2)=((1 + 8 * n).sqrt - 1) := by omega
      rw [t];clear t
      calc
      _ = ((1 + 8 * n).sqrt * ((1 + 8 * n).sqrt - 1)+ 1 * ((1 + 8 * n).sqrt - 1)) :=
        Nat.add_mul (1 + 8 * n).sqrt 1 ((1 + 8 * n).sqrt - 1)
      _ = ((1 + 8 * n).sqrt * ((1 + 8 * n).sqrt - 1)+ ((1 + 8 * n).sqrt - 1)) :=
        by simp_all only [one_mul]
      _ = (((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt * 1)+ ((1 + 8 * n).sqrt - 1)) :=
        by simp_all only [mul_one, add_left_inj];exact Nat.mul_sub_one (1 + 8 * n).sqrt (1 + 8 * n).sqrt
      _ = (((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt) + ((1 + 8 * n).sqrt - 1)) :=
        by simp_all only [mul_one]
      _ = ((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt + (1 + 8 * n).sqrt) - 1 :=
        by {
          refine Eq.symm (Nat.add_sub_assoc ?_ ((1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt))
          trans (1 : ℕ).sqrt
          rfl
          apply Nat.sqrt_le_sqrt
          simp_all only [le_add_iff_nonneg_right, zero_le]
        }
      _ ≤ _ := by {
        simp_all only [tsub_le_iff_right]
        have t : (1 + 8 * n).sqrt * (1 + 8 * n).sqrt - (1 + 8 * n).sqrt + (1 + 8 * n).sqrt = (1 + 8 * n).sqrt * (1 + 8 * n).sqrt := by {
          refine Nat.sub_add_cancel ?_
          exact Nat.le_mul_self (1 + 8 * n).sqrt
        }
        rw [t];clear t
        calc
        _ ≤ 1+8*n := Nat.sqrt_le (1 + 8 * n)
        _ = _ := by omega
    }
  }
}

def graph6_to_NatGraph (g6 : String) : SimpleGraph ℕ where
  Adj (v u : ℕ) := if ne : v = u
    then False
    else (charsToBin g6.data.tail!)[g6_ind_pairToSingle v u ne]!
  symm (v u : ℕ) a := by {
    simp_all only [List.getElem!_eq_getElem?_getD, Bool.default_bool, dite_then_false]
    obtain ⟨ne,a⟩ := a
    have ne' : ¬u = v := by clear a g6;contrapose ne;simp_all only [Decidable.not_not, not_true_eq_false, not_false_eq_true]
    use ne'
    rw [g6_ind_pairToSingle_symm];exact a
  }

instance : Coe String (SimpleGraph ℕ) := ⟨fun s ↦ graph6_to_NatGraph s⟩

instance graph6_to_NatGraph_dec (g6 : String) : DecidableRel (graph6_to_NatGraph g6).Adj := by {
  unfold graph6_to_NatGraph;simp_all only [List.getElem!_eq_getElem?_getD, Bool.default_bool, dite_then_false]
  intro v u
  simp_all only
  infer_instance
}

def graph6_to_NatDGraph (g6 : String) : DGraph ℕ := graph6_to_NatGraph g6

def g6List_to_graphList (g6 : String) : List (SimpleGraph ℕ) := (g6.splitOn "\n").map graph6_to_NatGraph

def g6List_to_DGraphList (g6 : String) : List (DGraph ℕ) := (g6.splitOn "\n").map graph6_to_NatDGraph

def FinGraph_to_graph6 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : String := by {
  refine List.asString ?_
  refine ((Char.ofNat (63+n)) :: ?_)
  have f : Fin (((n-1) * (n-1)+(n-1))/2) → Bool := by {
    intro x;
    cases n with
    | zero => simp only [zero_le, Nat.sub_eq_zero_of_le, mul_zero, Nat.zero_div] at x;apply finZeroElim x
    | succ n =>
    exact ((G.Adj (g6_ind_singleToPair x).1 (g6_ind_singleToPair x).2) : Bool)
  }
  have t := List.ofFn f
  exact binToChars t
}

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  : CoeDep (SimpleGraph (Fin n)) G String := ⟨FinGraph_to_graph6 G⟩
instance DGraphToString {n : ℕ} : ToString (DGraph (Fin n)) := ⟨λ G ↦ (G : SimpleGraph (Fin n))⟩

#eval FinGraph_to_graph6 ((λ G : DGraph ℕ ↦ (G : SimpleGraph (Fin 3))) (graph6_to_NatGraph "B?"))

section actualLists

def graph0String : String := "?"
def graph1String : String := "@"
def graph2String : String := "A?\nA_"
def graph3String : String := "B?\nBO\nBW\nBw"
def graph4String : String := "C?\nCC\nCE\nCF\nCQ\nCU\nCT\nCV\nC]\nC^\nC~"
/-tests passed-/def graph5String : String := "D??\nD?_\nD?o\nD?w\nD?{\nDCO\nDCo\nDCW\nDCc\nDCw\nDCs\nDC{\nDEo\nDEw\nDEs\nDEk\nDE{\nDFw\nDF{\nDQo\nDQg\nDQw\nDQ{\nDUW\nDUw\nDU{\nDTw\nDTk\nDT{\nDV{\nD]w\nD]{\nD^{\nD~{"
def graph6String : String := "E???\nE?A?\nE?B?\nE?B_\nE?Bo\nE?Bw\nE?`?\nE?b?\nE?`_\nE?aG\nE?b_\nE?`o\nE?bG\nE?bo\nE?bg\nE?bw\nE?r?\nE?oo\nE?r_\nE?qo\nE?rG\nE?qg\nE?ow\nE?ro\nE?rg\nE?qw\nE?rw\nE?z_\nE?zO\nE?zo\nE?zg\nE?zW\nE?zw\nE?~o\nE?~w\nECO_\nECR?\nECQ_\nECQO\nECR_\nECRO\nECQo\nECRo\nECRW\nECRw\nECpO\nECr_\nECrO\nECpo\nECrG\nECqg\nECro\nECrg\nECrW\nECrw\nECZ?\nECX_\nECYO\nECZ_\nECZO\nECZG\nECXg\nECYW\nECZo\nECZg\nECZW\nECZw\nECeW\nECfo\nECfW\nECfw\nECxo\nECzo\nECzg\nECzW\nECxw\nECzw\nECvo\nECvW\nECuw\nECvw\nEC~o\nEC~w\nEEr_\nEErO\nEEro\nEErW\nEErw\nEEh_\nEEj_\nEEio\nEEho\nEEiW\nEEhW\nEEjo\nEEjW\nEEhw\nEEjw\nEEz_\nEEzO\nEEzo\nEEzg\nEEzw\nEEvo\nEEvW\nEEuw\nEEvw\nEEno\nEElw\nEEnw\nEE~w\nEFz_\nEFzo\nEFzW\nEFzw\nEF~w\nEQhO\nEQj_\nEQjO\nEQig\nEQjo\nEQjg\nEQjw\nEQzO\nEQzo\nEQzg\nEQzW\nEQyw\nEQzw\nEQ~o\nEQ~w\nEUZ_\nEUZO\nEUZo\nEUZw\nEUxo\nEUzo\nEUzW\nEUzw\nEU~w\nETzo\nETzg\nETzw\nETno\nETmw\nETnw\nET~w\nEV~w\nE]zo\nE]zg\nE]yw\nE]zw\nE]~o\nE]~w\nE^~w\nE~~w"
/-graph7String and on already defined in g6complete7 and respective.-/

/-These functions assume that everything in the graph6 list is of correct size by sorry. This should be the case but since the string comes from nauty it cannot be proven-/
def graph0List : List (DGraph (Fin 0)) := (g6List_to_DGraphList graph0String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 0)) : DGraph (Fin 0)))
def graph1List : List (DGraph (Fin 1)) := (g6List_to_DGraphList graph1String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 1)) : DGraph (Fin 1)))
def graph2List : List (DGraph (Fin 2)) := (g6List_to_DGraphList graph2String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 2)) : DGraph (Fin 2)))
def graph3List : List (DGraph (Fin 3)) := (g6List_to_DGraphList graph3String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 3)) : DGraph (Fin 3)))
def graph4List : List (DGraph (Fin 4)) := (g6List_to_DGraphList graph4String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 4)) : DGraph (Fin 4)))
def graph5List : List (DGraph (Fin 5)) := (g6List_to_DGraphList graph5String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 5)) : DGraph (Fin 5)))
def graph6List : List (DGraph (Fin 6)) := (g6List_to_DGraphList graph6String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 6)) : DGraph (Fin 6)))
def graph7List : List (DGraph (Fin 7)) := (g6List_to_DGraphList graph7String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 7)) : DGraph (Fin 7)))
def graph8List : List (DGraph (Fin 8)) := (g6List_to_DGraphList graph8String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 8)) : DGraph (Fin 8)))
def graph9List : List (DGraph (Fin 9)) := (g6List_to_DGraphList graph9String).map (λ G : DGraph ℕ ↦ ((G : SimpleGraph (Fin 9)) : DGraph (Fin 9)))

instance graph0Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 0)))) := by {
  refine ⟨⟨⟦(graph0List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph1Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 1)))) := by {
  refine ⟨⟨⟦(graph1List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph2Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 2)))) := by {
  refine ⟨⟨⟦(graph2List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph3Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 3)))) := by {
  refine ⟨⟨⟦(graph3List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph4Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 4)))) := by {
  refine ⟨⟨⟦(graph4List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph5Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 5)))) := by {
  refine ⟨⟨⟦(graph5List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph6Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 6)))) := by {
  refine ⟨⟨⟦(graph6List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph7Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 7)))) := by {
  refine ⟨⟨⟦(graph7List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph8Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 8)))) := by {
  refine ⟨⟨⟦(graph8List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}
instance graph9Fintype : Fintype (Quotient (DGraph.hasIso (V:=(Fin 9)))) := by {
  refine ⟨⟨⟦(graph9List.map (λ G ↦ ⟦G⟧))⟧,?_⟩,?_⟩
  sorry/-This is the statement that there are nodups. This is computable but slow and true if we trust nauty-/
  sorry/-This cannot be easily proven. This is the statement that the graph6 string contains all graphs. It's true if we trust nauty.-/
}



end actualLists
