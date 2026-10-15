/-this started at 800 lines, let's see post optimization-/
import C4inducedRamsey.Prelim.Decidable
import C4inducedRamsey.Prelim.Setoid
import C4inducedRamsey.Prelim.FinBasics

assert_not_exists complete SimpleGraph

variable {D C B : Type} (f : D → C) (g : C→B) (x head : D) {a : D} {X Y Z : List D} (j k l tail : List D) (ε : D→Prop) [δ : ∀x : D,Decidable (ε x)] (s : Setoid D) (q : Quotient s)

section list_function

/-Function list function-/
def Function.lf (f : D → C) : (List D)→(List C) := fun l => l.map f

@[simp]abbrev Equiv.lf (f : Equiv D C) : (List D)→(List C) := f.toFun.lf

@[simp]lemma listFun_nil : (f.lf [])=[] := by unfold Function.lf;simp_all only [List.map_nil]

@[simp]lemma listFun_cons : (f.lf (head :: tail)) = (f head) :: (f.lf tail) := by unfold Function.lf;simp_all only [List.map_cons]

@[simp]lemma mem_listFun (x : C) : x∈(f.lf l)↔∃y∈l,x=(f y) := by induction l with
  | nil => simp_all only [listFun_nil, List.not_mem_nil, false_and, exists_false]
  | cons _ _ _ => simp_all only [listFun_cons, List.mem_cons, exists_eq_or_imp]

@[simp]lemma listFun_length : (f.lf l).length=l.length := by induction l with
  | nil => simp_all only [listFun_nil, List.length_nil]
  | cons head tail ih => simp_all only [listFun_cons, List.length_cons]

@[simp]lemma listFun_index (i : Fin (l.length)) : (f.lf l)[i] = f l[i] := by {
  induction l with
  | nil => have t : ([] : List D).length=0 := by rfl;;rw [t] at i;apply finZeroElim i
  | cons head tail ih => {
    simp_all only [Fin.getElem_fin, List.length_cons, listFun_cons]
    obtain ⟨i,lt⟩ := i
    simp_all only [List.length_cons, Fin.getElem_fin]
    cases i with
    | zero => simp_all only [List.getElem_cons_zero]
    | succ n => {
      simp_all only [List.length_cons, List.getElem_cons_succ]
      refine ih ⟨n,?_⟩
      simp_all only [List.length_cons, add_lt_add_iff_right]
    }
  }
}
@[simp]lemma listFun_index' (i : Fin ((f.lf l).length)) : (f.lf l)[i] = f l[i] := by {
  induction l with
  | nil => have t : ([] : List D).length=0 := by rfl;;rw [listFun_length,t] at i;apply finZeroElim i
  | cons head tail ih => {
    simp_all only [Fin.getElem_fin, List.length_cons, listFun_cons]
    obtain ⟨i,lt⟩ := i
    simp_all only [List.length_cons, Fin.getElem_fin]
    cases i with
    | zero => simp_all only [List.getElem_cons_zero]
    | succ n => {
      simp_all only [List.length_cons, List.getElem_cons_succ]
      refine ih ⟨n,?_⟩
      simp_all only [listFun_cons, List.length_cons, listFun_length, add_lt_add_iff_right]
    }
  }
}
@[simp]lemma listFun_index'' (i : ℕ) (h : i < ((f.lf l).length)) : (f.lf l)[i]'h = f (l[i]'(by rw [listFun_length] at h;exact h)) := by {
  have ⟨idx,idxii⟩ : {fin : Fin (f.lf l).length // fin = ⟨i,h⟩} := ⟨⟨i,h⟩,by rfl⟩
  trans (f.lf l)[idx]
  rw [idxii];rfl
  trans f l[idx]
  any_goals rw [idxii];rfl
  clear i idxii h
  exact listFun_index' f l idx
}


@[simp]lemma mem_listFun_injective' (inj : Function.Injective f) : (∃y∈l,(f x)=(f y))↔x∈l := ⟨fun ⟨_,h,i⟩ => by rw [inj i];exact h,fun h => ⟨x,by trivial⟩⟩

@[simp]lemma mem_listFun_injective (inj : Function.Injective f) : (f x)∈(f.lf l)↔(x∈l) := by trans (∃y∈l,(f x)=(f y));exact mem_listFun f l (f x);exact mem_listFun_injective' f x l inj

@[simp]lemma listFun_composition : (g.lf (f.lf l)) = ((g∘f).lf l) := by induction l with | nil => simp_all only [listFun_nil];| cons head tail ih => simp_all only [listFun_cons, Function.comp_apply]

@[simp]lemma listFun_id : (id.lf l)=l := by induction l with
  | nil => simp_all only [listFun_nil]
  | cons head tail ih => simp_all only [listFun_cons, id_eq]

lemma listFun_Nodup (inj : Function.Injective f) (nod : X.Nodup) : (f.lf X).Nodup := by {
  induction X with
  | nil => simp_all only [List.nodup_nil, listFun_nil]
  | cons head tail ih => simp_all only [List.nodup_cons, listFun_cons, mem_listFun, mem_listFun_injective', not_false_eq_true, and_self]
}

lemma listFun_injective (inj : Function.Injective f) : Function.Injective f.lf := by {
  intro X Y
  match X, Y with
  | [], [] => simp_all only [listFun_nil, imp_self]
  | [], (head :: tail) => {
    intro h;simp_all only [listFun_nil, listFun_cons, List.nil_eq];have t : (f head) ∈ (f head :: Function.lf f tail) := by exact List.mem_cons_self (f head) (Function.lf f tail)
    rw [h] at t;simp_all only [List.not_mem_nil]
  }
  | (head :: tail), [] => {
    intro h;simp_all only [listFun_nil, listFun_cons, List.nil_eq];have t : (f head) ∈ (f head :: Function.lf f tail) := by exact List.mem_cons_self (f head) (Function.lf f tail)
    rw [h] at t;simp_all only [List.not_mem_nil]
  }
  | (headX :: tailX), (headY :: tailY) => {
    intro h
    simp_all only [listFun_cons, List.cons.injEq];constructor
    apply inj;exact h.left
    apply listFun_injective inj;exact h.right
  }
}

lemma mem_listFun_domain (xInList : a∈X) : (f a)∈(f.lf X) := by simp_all only [mem_listFun];use a

lemma mem_listFun_inj [nonempty : Nonempty D] (x : C) (inj : Function.Injective f) : x∈(f.lf l)→((Function.invFun f) x)∈l := by
  simp_all only [mem_listFun];intro ⟨y,⟨yil,s⟩⟩;subst s;rw [Function.leftInverse_invFun inj];exact yil

lemma mem_listFun_surj [nonempty : Nonempty D] (x : C) (surj : Function.Surjective f) : ((Function.invFun f) x)∈l→x∈(f.lf l) := by
    simp_all only [mem_listFun];intro h;use Function.invFun f x;exact ⟨h,by rw [Function.rightInverse_invFun surj]⟩

@[simp]lemma mem_listFun_biject [nonempty : Nonempty D] (x : C) (biject : Function.Bijective f) : x∈(f.lf l)↔((Function.invFun f) x)∈l :=
  ⟨mem_listFun_inj f l x biject.injective,mem_listFun_surj f l x biject.surjective⟩

end list_function
section filter_list

/-Function filter list-/
def Function.filt (ε : D→Prop) [δ : ∀x : D,Decidable (ε x)] : List D→List D
  | [] => []
  | (head :: tail) => if ε head then (head :: Function.filt ε tail) else Function.filt ε tail

@[simp]lemma funcFilt_nil : ε.filt []=[] := by unfold Function.filt;simp_all only

@[simp]lemma funcFilt_cons_headPass (headPass : ε head) : ε.filt (head :: tail) = (head :: (ε.filt tail)) := by rw [Function.filt];simp_all only [ite_true]

@[simp]lemma funcFilt_cons_headFail (headFail :¬ε head)
  : ε.filt (head :: tail) = ε.filt tail := by rw [Function.filt];simp_all only [ite_false]

@[simp]lemma funcFilt_cons : ε.filt (head :: tail) = (if ε head then head :: ε.filt tail else ε.filt tail) :=
  by by_cases h : ε head;simp_all only [funcFilt_cons_headPass, ite_true];simp_all only [not_false_eq_true, funcFilt_cons_headFail, ite_false]

@[simp]lemma mem_funcFilt : x∈(ε.filt l)↔(x∈l ∧ ε x) := by induction l with
    | nil => simp_all only [funcFilt_nil, List.not_mem_nil, false_and]
    | cons head tail ih =>
      by_cases headPass : ε head
      simp_all only [List.mem_cons,funcFilt_cons_headPass, List.mem_cons];constructor
      exact fun a => Or.rec (by intro h;subst h;simp_all only [and_true, true_or, and_self]) (by intro h;simp_all only [and_self, iff_true, or_true]) a
      exact fun a => Or.rec (by intro h;left;exact h) (by intro h;right;simp_all only [and_self, iff_true, or_true, true_and]) a.left
      simp_all only [List.mem_cons,not_false_eq_true, funcFilt_cons_headFail, and_congr_left_iff, iff_or_self];intro a b;subst b;simp_all only

@[simp]lemma funcFilt_list_func {ε : Set C} [DecidablePred ε] : ε.filt (f.lf l) = f.lf ((fun x => ε (f x)).filt l) := by {
  induction l with
  | nil => simp_all only [listFun_nil, funcFilt_nil]
  | cons head tail ih => {
    simp_all only [listFun_cons]
    by_cases headPass : (fun x => ε (f x)) head
    simp_all only [funcFilt_cons_headPass, listFun_cons]
    simp_all only [not_false_eq_true, funcFilt_cons_headFail]
  }
}

lemma funcFilt_Nodup (nod : X.Nodup) : (ε.filt X).Nodup := by {
  induction X with
  | nil => simp_all only [List.nodup_nil, funcFilt_nil]
  | cons head tail ih => {
    simp_all only [List.nodup_cons, forall_const]
    by_cases h : ε head
    simp_all only [funcFilt_cons_headPass, List.nodup_cons, mem_funcFilt, and_true, not_false_eq_true, and_self]
    simp_all only [not_false_eq_true, funcFilt_cons_headFail]
  }
}

/-list delete-/
abbrev List.del [δ : DecidableEq D] := (· ≠ x).filt l

def Function.pass (ε : D→Prop) : Prop := ∀x∈l,ε x

omit δ in
lemma func_pass_nil : ε.pass [] := by unfold Function.pass;intro x h;simp_all only [List.not_mem_nil]

omit δ in
@[simp]lemma func_pass_cons : ε.pass (head :: tail) ↔ (ε head) ∧ (ε.pass tail) := by unfold Function.pass;simp_all only [List.mem_cons, forall_eq_or_imp]

omit δ in
lemma mem_func_pass (h : ε.pass l) (xil : x∈l) : ε x := by induction l with
| nil => simp_all only [List.not_mem_nil]
| cons head tail ih => simp_all only [func_pass_cons, List.mem_cons, forall_const];cases xil with | inl xil => subst xil;exact h.left | inr xil => exact ih xil

lemma filterPasses : ε.pass (ε.filt l) := by induction l with
  | nil => simp_all only [funcFilt_nil];exact func_pass_nil ε
  | cons head tail ih => {
    by_cases hh : ε head
    simp_all only [funcFilt_cons_headPass, func_pass_cons, and_self]
    simp_all only [not_false_eq_true, funcFilt_cons_headFail]
  }

def toSubtypeList {ε : D → Prop} (h : ε.pass l) : List {x : D // ε x} := by induction l with
  | nil => exact []
  | cons head tail ih => simp_all only [func_pass_cons];specialize ih h.right;exact (⟨head,h.left⟩ :: ih)

omit δ in
@[simp]lemma toSubstypeList_nil (h : Function.pass [] ε) : toSubtypeList [] h = [] := by unfold toSubtypeList;simp_all only

omit δ in
@[simp]lemma toSubtypeList_cons (h : ε.pass (head :: tail)) : toSubtypeList (head :: tail) h = ⟨head,by simp_all only [func_pass_cons]⟩ :: (toSubtypeList tail (by simp_all only [func_pass_cons])) := by
  unfold toSubtypeList;simp_all only

omit δ in
@[simp]lemma mem_toSubtypeList (xh : ε x) (h : ε.pass l) : ⟨x,xh⟩∈toSubtypeList l h ↔ x∈l := by {
  induction l with
  | nil => simp_all only [toSubstypeList_nil, List.not_mem_nil]
  | cons head tail ih => simp_all only [toSubtypeList_cons, List.mem_cons, Subtype.mk.injEq]
}

end filter_list

section list_equiv

instance list_equiv {D : Type} : Setoid (List D) where
  r (X Y : List D) := ∀k : D,k∈X↔k∈Y
  iseqv := by
    refine ⟨?_,?_,?_⟩
    intro _ _;rfl
    intro _ _ h k;symm;revert k;exact h
    intro _ Y _ _ _ k;trans k∈Y;all_goals revert k;assumption

infixl:25 " ≅l " => list_equiv

@[refl]lemma list_equiv_reflexive : ∀l : List D, l ≅l l := list_equiv.iseqv.refl
instance list_equiv_transitive_test : Trans (α:=(List D)) list_equiv list_equiv list_equiv where trans := list_equiv.iseqv.trans
@[symm]lemma list_equiv_symmetric : X ≅l Y → Y ≅l X := list_equiv.iseqv.symm

@[simp]lemma list_equiv_nil : [] ≅l l ↔ l=[] := by
  constructor;intro h;cases l with
  | nil => rfl
  | cons he t => have o := (List.mem_cons_self he t);rw [← h] at o;simp_all only [List.not_mem_nil]
  intro h;subst h;rfl
@[simp]lemma list_equiv_nil' : l ≅l [] ↔ l=[] := by trans [] ≅l l;constructor;repeat {exact list_equiv.symm};exact list_equiv_nil l

@[simp]lemma list_equiv_cons : (head :: tail) ≅l l ↔ (head∈l ∧ ∀ x : D,¬x=head → (x∈tail↔x∈l)) := by
  constructor;intro h;constructor
  rw [← h];simp_all only [List.mem_cons, true_or]
  intro x xnh;rw [← h];constructor;repeat simp_all only [List.mem_cons, or_true, false_or, implies_true]
  intro h x;constructor
  intro xic;by_cases xIsHead : x=head;subst xIsHead;exact h.left;simp_all only [List.mem_cons, not_false_eq_true, false_or]
  intro xInY;by_cases xIsHead : x=head;repeat simp_all only [List.mem_cons,true_or,not_false_eq_true, or_true]

@[simp]lemma list_equiv_cons' :  l ≅l (head :: tail) ↔ (head∈l ∧ ∀ x : D,¬x=head → (x∈tail↔x∈l)) := by trans (head :: tail) ≅l l;constructor;repeat {exact list_equiv.symm};simp_all only [list_equiv_cons]

@[simp]lemma not_list_equiv : (¬(X ≅l Y))↔(∃x : D,x∈X↔x∉Y) := by
  unfold list_equiv;simp_all only [not_forall];constructor
  intro ⟨x,_⟩;use x;constructor;repeat intro a;simp_all only [true_iff, not_false_eq_true,iff_false, not_not]
  intro ⟨x,_⟩;use x;simp_all only [not_iff_self, not_false_eq_true]

def list_equiv_split (h1 : ∀x,(x∈X)→(x∈Y)) (h2 : ∀x,(x∈Y)→(x∈X)) : X ≅l Y := fun x => ⟨(h1 x),(h2 x)⟩

instance list_equiv_dec [decEq : DecidableEq D] : DecidableRel (list_equiv (D := D)) := by
  have test (A B : List D): Decidable (∀x : D, (x∈A)→(x∈B)) := by induction A with
    | nil => exact isTrue (by  simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])
    | cons h _ ih => simp_all only [List.mem_cons, forall_eq_or_imp];exact decidable_and (List.instDecidableMemOfLawfulBEq h B) ih
  intro X Y;cases (test X Y) with
  | isFalse h => exact isFalse (by simp_all only [not_forall, Classical.not_imp,not_list_equiv];obtain ⟨x,_⟩ := h;use x;simp_all only [exists_prop, not_false_eq_true])
  | isTrue h1 => cases (test Y X) with
    | isFalse h2 => exact isFalse (by simp_all only [not_forall,exists_prop, not_list_equiv];obtain ⟨x,_⟩ := h2;use x;simp_all only [not_true_eq_false])
    | isTrue h2 => exact isTrue (list_equiv_split h1 h2)



end list_equiv
section disjoint

def disjoint : (List D)→(List D)→Prop := fun k l ↦ ∀x : D,x∉l ∨ x∉k

@[symm]lemma disjoint_symm : disjoint l k ↔ disjoint k l := by
  unfold disjoint;constructor;all_goals intro h x;symm;revert x;exact h

@[simp]lemma disjoint_nil : disjoint [] l := by unfold disjoint;simp_all only [List.not_mem_nil, not_false_eq_true, or_true, implies_true]

@[simp]lemma disjoint_nil' : disjoint l [] := by rw [disjoint_symm];revert l;exact disjoint_nil

@[simp]lemma disjoint_cons : disjoint (head :: tail) l ↔ (head ∉ l) ∧ (disjoint tail l) := by {
  unfold disjoint;simp_all only [List.mem_cons, not_or]
  constructor
  {
    intro h;constructor
    specialize h head;cases h;assumption;rename_i h;obtain ⟨hₗ,hᵣ⟩ := h;contrapose hₗ;simp_all only [not_not, not_true_eq_false, not_false_eq_true]
    intro x;specialize h x;cases h;left;assumption;rename_i h;simp_all only [not_false_eq_true, or_true]

  }
  {
    intro ⟨hnt,h⟩;intro x;specialize h x;by_cases hₗ : x∉l
    left;exact hₗ
    simp_all only [false_or, not_not, not_true_eq_false, not_false_eq_true, and_true];contrapose h;simp_all only [not_not]
  }
}
@[simp]lemma disjoint_cons' : disjoint l (head :: tail) ↔ (head ∉ l) ∧ (disjoint tail l) := by rw [disjoint_symm];rw [disjoint_cons]

end disjoint
section list_quotient

def Setoid.lq : List (Quotient s) := (fun x => ⟦x⟧).lf l

lemma mem_quotList : ⟦x⟧∈(s.lq l)↔(∃y∈l,s x y) := by unfold Setoid.lq;simp_all only [mem_listFun, Quotient.eq]

@[simp]lemma quotList_nil : s.lq []=[] := by unfold Setoid.lq;simp_all only [listFun_nil]

@[simp]lemma quotList_cons : s.lq (head :: tail) = (⟦head⟧ :: (s.lq tail)) := by unfold Setoid.lq;simp_all only [listFun_cons]

instance memDecidable [decEq : DecidableEq D] : Decidable (x∈l) := by
  induction l with
  | nil => exact isFalse (by simp_all only [List.not_mem_nil, not_false_eq_true])
  | cons head tail ih => cases ih with
    | isFalse h => cases (decEq x head) with
      | isFalse _ => exact isFalse (by simp_all only [List.mem_cons, or_self, not_false_eq_true])
      | isTrue xih => exact isTrue (by simp_all only [List.mem_cons, or_false])
    | isTrue h => exact isTrue (by simp_all only [List.mem_cons, or_true])
instance memDecidable'' [decEq : DecidableEq D] : DecidablePred l.Mem := by
  intro x;show Decidable (x ∈ l);infer_instance

lemma quot_listEquiv (iso : X ≅l Y) (s : Setoid D) : (s.lq X) ≅l (s.lq Y) := by {
  intro x;cases x using Quotient.ind;rename_i x;rw [mem_quotList];rw [mem_quotList]
  constructor;(all_goals intro ⟨y,⟨yi,yx⟩⟩;use y;constructor);rw [← iso];exact yi;any_goals rw [iso];exact yi
  all_goals exact yx
}

def memDecidable' {ε : D → Prop} [dec : DecidableEq {x : D // ε x}] (εx : ε x) (εl : ε.pass l) : Decidable (x∈l) := by rw [← mem_toSubtypeList];exact memDecidable ⟨x,εx⟩ (toSubtypeList l εl)

def quotHeadTailDecidable [dec : DecidableRel (s.subSetoid (p := fun x => x∈(head :: tail)))] : Decidable (⟦head⟧∈(s.lq tail)) := by {
  revert dec;induction tail with
  | nil => refine isFalse ?_;simp_all only [quotList_nil, List.not_mem_nil, not_false_eq_true]
  | cons x tail ih => {
    intro dec
    have temp : DecidableRel (Setoid.subSetoid (p:=(fun x ↦ x ∈ head :: tail)) s) := by {
      intro a b
      have ah : a.val∈(head :: x :: tail) := by obtain ⟨a,ah⟩ := a;simp_all only [List.mem_cons];rw [List.mem_cons] at ah;cases ah with | inl ah => left;exact ah | inr ah => right;right;exact ah
      have bh : b.val∈(head :: x :: tail) := by obtain ⟨b,bh⟩ := b;simp_all only [List.mem_cons];rw [List.mem_cons] at bh;cases bh with | inl bh => left;exact bh | inr bh => right;right;exact bh
      replace dec := dec ⟨a.val,ah⟩ ⟨b.val,bh⟩;simp_all only [preSetoid_apply]
      cases dec with
      | isFalse h =>
        simp_all only [preSetoid_apply]
        refine isFalse ?_;simp_all only [List.mem_cons, not_false_eq_true]
      | isTrue h =>
        simp_all only [preSetoid_apply]
        refine isTrue ?_;simp_all only [List.mem_cons]
    }

    cases ih with
    | isFalse ih => {
      have decEq : Decidable ((⟦head⟧ : Quotient s)=⟦x⟧) := by {
        have hih : head∈(head :: x :: tail) := by simp_all only [List.mem_cons, true_or]
        have xih : x∈(head :: x :: tail) := by simp_all only [List.mem_cons, true_or, or_true]
        replace dec := dec ⟨head,hih⟩ ⟨x,xih⟩;simp_all only [Quotient.eq]
        rw [subSetoid_apply] at dec;exact dec
      }
      cases decEq with
      | isFalse e => refine isFalse ?_;simp_all only [Quotient.eq, quotList_cons, List.mem_cons, or_self, not_false_eq_true]
      | isTrue e => refine isTrue ?_;simp_all only [Quotient.eq, quotList_cons, List.mem_cons, true_or]
    }
    | isTrue ih => refine isTrue ?_;simp_all only [quotList_cons, List.mem_cons, Quotient.eq, or_true]
  }
}

@[simp]lemma quotmem_listFun (x : C) (s : Setoid C) : ⟦x⟧∈ (s.lq (f.lf l)) ↔ ∃y∈l,s x (f y) := by unfold Setoid.lq;simp_all only [listFun_composition, mem_listFun, Function.comp_apply, Quotient.eq]

def quotList_setoid : Setoid (List D) where
  r (l k : List D) := (s.lq l)=(s.lq k)
  iseqv := by
    refine ⟨?_,?_,?_⟩
    intro l;simp_all only
    intro l k h;symm;exact h
    intro l k j h1 h2;trans (Setoid.lq k s);all_goals assumption

end list_quotient
section dupRemoved

def Setoid.dupRemove' [dec : DecidableRel s] : {k : List D // (s.lq k).Nodup ∧ ((s.lq l) ≅l (s.lq k))} := by induction l with
  | nil => use [];simp_all only [List.nodup_nil, quotList_nil, list_equiv_nil', and_self]
  | cons head tail ih => {
    by_cases h : ⟦head⟧∈(s.lq tail)
    {
      use ih
      constructor;exact ih.property.left
      simp_all only [quotList_cons, list_equiv_cons];rw [ih.property.right] at h;simp_all only [true_and]
      intro x xnh;rw [ih.property.right]
    }
    {
      use head :: ih
      simp_all only [quotList_cons, list_equiv_cons,List.nodup_cons, List.mem_cons, true_or, false_or, true_and]
      constructor;constructor
      {
        rw [ih.property.right] at h;exact h
      }
      {
        exact ih.property.left
      }
      {
        intro x xih;rw [ih.property.right]
      }
    }
  }

def Setoid.dupRemove [dec : DecidableRel s] : List D := (s.dupRemove' l).val

lemma Setoid.dupRemove_Nodup [dec : DecidableRel s] : (s.lq (s.dupRemove l)).Nodup := by unfold Setoid.dupRemove;exact (dupRemove' l s).property.left

lemma Setoid.dupRemove_listEquiv [dec : DecidableRel s] : (s.lq l) ≅l (s.lq (s.dupRemove l)) := by unfold Setoid.dupRemove;exact (dupRemove' l s).property.right

/-def Setoid.dupRemove_preSetoid (f : C→D) [dec : DecidableRel (s.preSetoid f)] -/

def Setoid.dupRemove_sub [dec : DecidableRel (s.subSetoid (p:=fun x => x∈l))] : List D := by revert dec;induction l with
  | nil => exact []
  | cons head tail ih => {
    intro dec
    have temp : DecidableRel ⇑(subSetoid (p:=(fun x ↦ x ∈ tail)) s) := by {
      intro x y
      have t (a : { x // x ∈ tail }) : a.val∈head :: tail := by obtain ⟨a,ah⟩ := a;simp_all only [List.mem_cons, or_true]
      replace dec := dec ⟨x.val,t x⟩ ⟨y.val,t y⟩
      cases dec with
      | isFalse h => refine isFalse ?_;simp_all only [preSetoid_apply, not_false_eq_true]
      | isTrue h => refine isTrue ?_;simp_all only [preSetoid_apply]
    }
    have by_cases_l : Decidable (⟦head⟧∈(s.lq tail)) := quotHeadTailDecidable head tail s
    by_cases ⟦head⟧∈(s.lq tail)
    exact ih
    exact head :: ih
  }

@[simp]lemma dupRemoved_nil [dec : DecidableRel s] : s.dupRemove [] = [] := by unfold Setoid.dupRemove Setoid.dupRemove';simp_all only

@[simp]lemma dupRemoved_cons_existLater [dec : DecidableRel s] (existLater : ⟦head⟧∈(s.lq tail)) : s.dupRemove (head :: tail)=s.dupRemove tail :=
  by unfold Setoid.dupRemove Setoid.dupRemove';simp_all only [dite_true]

@[simp]lemma dupRemoved_cons_unique [dec : DecidableRel s] (unique : ¬(⟦head⟧∈(s.lq tail))) : s.dupRemove (head :: tail)=(head :: (s.dupRemove tail))
  := by unfold Setoid.dupRemove Setoid.dupRemove';simp_all only [dite_false]

@[simp]lemma dupRemoved_cons [dec : DecidableRel s] : s.dupRemove (head :: tail) = if ⟦head⟧∈(s.lq tail) then s.dupRemove tail else (head :: s.dupRemove tail) := by {
  by_cases ⟦head⟧∈(s.lq tail)
  simp_all only [dupRemoved_cons_existLater, ite_true]
  simp_all only [not_false_eq_true, dupRemoved_cons_unique, ite_false]
}

@[simp]lemma dupRemoved_equivMem [dec : DecidableRel s] : (q∈(s.lq (s.dupRemove l)))↔(q∈(s.lq l)) := by induction l with
    | nil => simp_all only [dupRemoved_nil, quotList_nil, List.not_mem_nil]
    | cons head tail ih =>
      simp_all only [quotList_cons, List.mem_cons, Quotient.eq]
      have uniqueDecidable : Decidable (∃x∈tail,s head x) := decidable_list_exist tail (fun x => dec head x)
      by_cases unique : ⟦head⟧∈(s.lq tail);all_goals simp_all only [dupRemoved_cons_existLater, iff_or_self, implies_true, not_false_eq_true, dupRemoved_cons_unique, quotList_cons, List.mem_cons, Quotient.eq]

omit δ in
@[simp]lemma dupRemove_unattach [DecidableRel s] {ε : D→Prop} (l : List {d : D // ε d}) : (s.subSetoid.dupRemove l).unattach=s.dupRemove l.unattach := by {
  induction l with
  | nil => simp_all only [dupRemoved_nil, List.unattach_nil]
  | cons head tail ih => {
    simp_all only [dupRemoved_cons, List.unattach_cons]
    have h₂g : ⟦head⟧ ∈ Setoid.lq tail s.subSetoid ↔ ⟦↑head⟧ ∈ Setoid.lq tail.unattach s := by
      rw [mem_quotList];rw [mem_quotList];simp_all only [preSetoid_apply, Subtype.exists, exists_and_right];simp [List.unattach, -List.map_subtype]
    by_cases h : ⟦head⟧ ∈ Setoid.lq tail s.subSetoid
    have h₂ : ⟦↑head⟧ ∈ Setoid.lq tail.unattach s := by rw [← h₂g];exact h
    simp_all only [ite_true]
    have h₂ : ¬ ⟦↑head⟧ ∈ Setoid.lq tail.unattach s := by rw [← h₂g];exact h
    simp_all only [ite_false, List.unattach_cons]

  }
}

instance nodupDecidable [eqDec :  DecidableEq D] : Decidable (l.Nodup) := by induction l with
  | nil => exact isTrue (by simp_all only [List.nodup_nil])
  | cons head tail ih => have headDec := List.instDecidableMemOfLawfulBEq head tail;cases ih with
    | isFalse h => exact isFalse (by simp_all only [List.nodup_cons, and_false, not_false_eq_true])
    | isTrue ih => cases headDec with
      | isFalse h => exact isTrue (by simp_all only [List.nodup_cons, not_false_eq_true, and_self])
      | isTrue h => exact isFalse (by simp_all only [List.nodup_cons, not_true_eq_false, and_true, not_false_eq_true])

end dupRemoved
section append

lemma cons_is_singletonAppend : (head :: tail) = [head]++tail := by simp_all only [List.cons_append, List.nil_append]

@[simp]lemma listFun_listUnion : (f.lf k)++(f.lf l)=(f.lf (k++l)) := by induction k with
  | nil => simp_all only [listFun_nil, List.nil_append];| cons head tail ih => simp_all only [listFun_cons,
    List.cons_append]

@[simp]lemma quotList_listUnion {type : Type} (s : Setoid type) (list1 list2 : List type) : (s.lq list1)++(s.lq list2)=(s.lq (list1++list2)) := by unfold Setoid.lq;simp_all only [listFun_listUnion]


def listUnion_func [DecidableEq D] (f : {x : D // x∈X}→C) (g : {x : D // x∈Y}→C) : {x : D // x∈(X++Y)}→C := by {
  intro ⟨x,xi⟩;simp_all only [List.mem_append]
  const_cases xi;all_goals rename_i xi
  exact f ⟨x,xi⟩
  exact g ⟨x,xi⟩
}

lemma mem_givesMiddle (m : a∈X) : ∃l₁ l₂ : List D, X=l₁++[a]++l₂ := by {
  induction X with
  | nil => simp_all only [List.not_mem_nil]
  | cons head tail ih => {
    simp_all only [List.mem_cons]
    cases m with
    | inl m => subst m;use [];use tail;simp_all only [List.append_assoc, List.cons_append, List.nil_append]
    | inr m => {
      specialize ih m
      obtain ⟨l₁,l₂,h⟩ := ih
      use (head :: l₁); use l₂
      simp_all only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true]
    }
  }
}

@[simp]lemma listUnion_Nodup : (l ++ k).Nodup ↔ (disjoint l k) ∧ l.Nodup ∧ k.Nodup := by {
  induction l with
  | nil => simp_all only [List.nil_append, disjoint_nil, List.nodup_nil, true_and]
  | cons head tail ih => {
    simp_all only [List.cons_append, List.nodup_cons, List.mem_append, not_or, disjoint_cons]
    constructor;all_goals intro _;simp_all only [not_false_eq_true, implies_true, and_self, iff_true]
  }
}

section multiunion
variable (head : List D) (l tail : List (List D))
def listMultiunion (l : List (List D)) : List D := by induction l with | nil => exact [];| cons head tail ih => exact head++ih

@[simp]lemma listMultiunion_nil : (listMultiunion ([] : List (List D)))=[] := by unfold listMultiunion;simp_all only

@[simp]lemma listMultiunion_cons  : (listMultiunion (head :: tail)) = head ++ (listMultiunion tail) := by unfold listMultiunion;simp_all only

@[simp]lemma listMultiunion_singleton : listMultiunion [head] = head := by simp_all only [listMultiunion_cons, listMultiunion_nil, List.append_nil]

@[simp]lemma mem_listMultiunion :  x∈listMultiunion l ↔ ∃X∈l,x∈X := by induction l with
  | nil => simp_all only [listMultiunion_nil, List.not_mem_nil, false_and, exists_const]
  | cons head tail ih => simp_all only [listMultiunion_cons, List.mem_append, List.mem_cons, exists_eq_or_imp]
@[simp]lemma listFun_listMultiunion : (listMultiunion ((fun X => f.lf X).lf l))=f.lf (listMultiunion l) := by induction l with
    | nil => simp_all only [listFun_nil, listMultiunion_nil];| cons head tail ih => simp_all only [listFun_cons, listMultiunion_cons, listFun_listUnion]

@[simp]lemma equivMem_listMultiunion : ⟦x⟧∈(s.lq (listMultiunion l)) ↔ ∃X∈l,⟦x⟧∈(s.lq X) := by
  rw [mem_quotList];simp_all only [mem_listMultiunion];constructor;all_goals intro ⟨y,⟨h,i⟩⟩
  obtain ⟨l,il⟩ := h;use l;constructor;exact il.left;rw [mem_quotList];use y;constructor;exact il.right;exact i
  rw [mem_quotList] at i;obtain ⟨z,ziy⟩ := i;use z;constructor;use y;constructor;exact h;exact ziy.left;exact ziy.right

@[simp]lemma listMultiunion_length : (listMultiunion l).length = (List.length.lf l).sum := by {
  induction l with
  | nil => simp_all only [listMultiunion_nil, List.length_nil, listFun_nil, List.sum_nil]
  | cons head tail ih => simp_all only [listMultiunion_cons, List.length_append, listFun_cons, List.sum_cons]
}

@[simp]lemma listMultiunion_nodup : (listMultiunion l).Nodup ↔ (l.Pairwise disjoint) ∧ ∀x∈l,x.Nodup := by {
  constructor
  {
    induction l with
    | nil => simp_all only [listMultiunion_nil, List.nodup_nil, List.Pairwise.nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self, imp_self]
    | cons head tail ih => {
      simp_all only [listMultiunion_cons, listUnion_Nodup, List.pairwise_cons, and_true, List.mem_cons, forall_eq_or_imp, implies_true, and_self, and_imp]
      intro disjHeadTail headNodup tailNodup t tit
      simp_all only [forall_const]
      induction head with
      | nil => simp_all only [disjoint_nil, List.nodup_nil]
      | cons head tail ih => simp_all only [disjoint_cons, mem_listMultiunion, not_exists, not_and, List.nodup_cons, not_false_eq_true, and_self]
    }
  }
  {
    simp_all only [and_imp]
    induction l with
    | nil => simp_all only [List.Pairwise.nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self, listMultiunion_nil, List.nodup_nil, imp_self]
    | cons head tail ih => {
      simp_all only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, listMultiunion_cons, listUnion_Nodup, implies_true, and_self, and_true, and_imp]
      intro headDisjoint tailDisjoint headNodup tailNodup
      simp_all only [implies_true, forall_const]
      induction head with
      | nil => simp_all only [disjoint_nil, implies_true, List.nodup_nil]
      | cons head ta ih => simp_all only [disjoint_cons, List.nodup_cons, mem_listMultiunion, not_exists, not_and, not_false_eq_true, implies_true, and_self]
    }
  }
}

def multilength : ℕ := by induction l with
  | nil => exact 0
  | cons head tail ih => exact head.length+ih

lemma multiLength_gives_length : (multilength l) = (listMultiunion l).length := by unfold multilength;induction l with
  | nil => simp_all only [listMultiunion_nil, List.length_nil]
  | cons head tail ih => simp_all only [listMultiunion_length, listMultiunion_cons, List.length_append]

@[simp]lemma multilength_nil : (multilength ([] : List (List D))) = 0 := by unfold multilength;simp_all only

@[simp]lemma multilength_cons : (multilength (head :: tail)) = head.length + (multilength tail) := by unfold multilength;simp_all only

def multiGet (n : Fin (multilength l)) : (List D)×D := by {
  induction l with
  | nil => rw [multilength_nil] at n;apply finZeroElim n
  | cons head tail ih => {
    obtain ⟨n,nh⟩ := n;simp_all only [multilength_cons]
    by_cases nh' : n<head.length
    exact ⟨head,head[(⟨n,nh'⟩ : Fin (head.length))]⟩
    simp_all only [not_lt];have nh'' : n-head.length<(multilength tail) := by exact Nat.sub_lt_left_of_lt_add nh' nh;;exact ih ⟨n-head.length,nh''⟩
  }
}

end multiunion
end append
section count

def List.PropCount : ℕ := (ε.filt l).length

@[simp]lemma List.filtLength_is_PropCount : (ε.filt l).length = l.PropCount ε := by  unfold List.PropCount;simp_all only

def List.EqCount [δ : DecidableEq D] := l.PropCount (· = x)

@[simp]lemma listPropCount_nil : [].PropCount ε=0 := by unfold List.PropCount;simp_all only [funcFilt_nil, List.length_nil]

@[simp]lemma listPropCount_cons_headPass (headPass : ε head) : List.PropCount (head :: tail) ε=(tail.PropCount ε)+1 := by unfold List.PropCount;simp_all only [funcFilt_cons_headPass, List.length_cons]

@[simp]lemma listPropCount_cons_headFail (headFail :¬ε head) : List.PropCount (head :: tail) ε=tail.PropCount ε := by unfold List.PropCount;simp_all only [not_false_eq_true, funcFilt_cons_headFail]

@[simp]lemma listPropCount_cons : (head :: tail).PropCount ε = (tail.PropCount ε)+(if ε head then 1 else 0) := by
  unfold List.PropCount;simp_all only [funcFilt_cons, List.filtLength_is_PropCount]; by_cases h : ε head;simp_all only [ite_true, List.length_cons, List.filtLength_is_PropCount]
  simp_all only [ite_false, List.filtLength_is_PropCount, add_zero]

@[simp]lemma EqCount_nil  [δ : DecidableEq D]: [].EqCount x=0 := by unfold List.EqCount;simp_all only [listPropCount_nil]

@[simp]lemma EqCount_cons_headPass [δ : DecidableEq D] : (head :: tail).EqCount head=(tail.EqCount head)+1 := by unfold List.EqCount;simp_all only [listPropCount_cons_headPass]

@[simp]lemma EqCount_cons_headFail (xnh : ¬head=x) [δ : DecidableEq D] : (head :: tail).EqCount x=tail.EqCount x := by unfold List.EqCount;simp_all only [not_false_eq_true, listPropCount_cons_headFail]

@[simp]lemma listPropCount_zero : l.PropCount ε=0↔∀x∈l,¬ε x := by induction l with
    | nil => simp_all only [listPropCount_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    | cons head tail ih =>
      simp_all only [List.mem_cons, forall_eq_or_imp];constructor
      case cons.mpr => intro ⟨nφh,h⟩;simp_all only [not_false_eq_true, implies_true, iff_true, listPropCount_cons_headFail]
      intro h;constructor
      by_contra _;simp_all only [listPropCount_cons_headPass, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false]
      by_cases εh : ε head;all_goals simp_all only [listPropCount_cons_headPass, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, listPropCount_cons_headFail, implies_true]

@[simp]lemma EqCount_zero [δ : DecidableEq D] : l.EqCount x = 0↔x∉l := by
    unfold List.EqCount;simp_all only [listPropCount_zero];constructor
    all_goals intro h;contrapose h;simp_all only [not_not, not_forall, Classical.not_imp, Decidable.not_not, exists_eq_right, not_true_eq_false, not_false_eq_true]
    use x;obtain ⟨x',c,s⟩ := h;subst s;exact c

lemma length_is_delete_plus_count [δ : DecidableEq D] : l.length=(l.del x).length + (l.EqCount x) := by unfold List.EqCount List.PropCount;rw [← @List.length_append];induction l with
  | nil => simp_all only [List.length_nil, funcFilt_nil, List.append_nil]
  | cons head tail ih =>
    simp_all only [ne_eq, @List.length_append, List.length_cons];by_cases hex : head=x
    subst hex;simp_all only [ne_eq, not_true_eq_false, not_false_eq_true, funcFilt_cons_headFail, funcFilt_cons_headPass, List.length_cons];rfl
    simp_all only [ne_eq, not_false_eq_true, funcFilt_cons_headPass, List.length_cons, funcFilt_cons_headFail];rw [List.del];simp_all only [ne_eq]
    exact Nat.add_right_comm (Function.filt (fun x_1 ↦ ¬x_1 = x) tail).length (Function.filt (fun x_1 ↦ x_1 = x) tail).length 1

lemma PropCount_upperBound : l.PropCount ε < l.length+1 := by {
  induction l with
  | nil => simp_all only [listPropCount_nil, List.length_nil, zero_add, Nat.lt_one_iff, pos_of_gt]
  | cons head tail ih =>
    simp_all only [listPropCount_cons, List.length_cons]
    calc
      (tail.PropCount ε + if ε head then 1 else 0)≤(tail.PropCount ε + 1) := by simp_all only [add_le_add_iff_left];by_cases ε head;simp_all only [ite_true, le_refl];simp_all only [ite_false, zero_le]
      (tail.PropCount ε + 1)<tail.length + 1 + 1 := by exact Nat.add_lt_add_right ih 1
}

lemma EqCount_upperBound [DecidableEq D] : l.EqCount x < l.length+1 := by unfold List.EqCount;exact PropCount_upperBound l (fun x_1 ↦ x_1 = x)

end count
section constructive_membership

def const_mem : Type := {n : Fin (l.length) // l[n] = (some x)}

infixl:25 " ∈c " => const_mem

lemma not_const_mem_nil (m : a ∈c []) : False := by {
  unfold const_mem at m;obtain ⟨n,_⟩:= m
  have t : ([] : List D).length=0 := by rfl'
  rw [t] at n;apply finZeroElim n
}

def const_mem_cons_r {head : D} {tail : List D} (m : a ∈c (head :: tail)) : (a=head) ∨c (a ∈c tail) := by {
  clear B C f g x X Y Z j ε δ q s k l
  unfold const_mem;unfold const_mem at m
  obtain ⟨n,h⟩ := m
  simp only [List.length_cons, Option.some.injEq] at h
  simp_all only [List.length_cons, Fin.getElem_fin, Option.some.injEq];obtain ⟨n,lt⟩ := n;simp_all only [List.length_cons, Fin.getElem_fin]
  have d : Decidable (n=0) := decEq n 0
  by_cases z : n=0
  {
    subst z
    simp only [List.getElem_cons_zero] at h;symm at h
    exact .left h
  }
  {
    refine .right ?_
    use ⟨(n-1),?_⟩
    {
      simp_all only
      have t : n = n - 1 + 1 := Eq.symm (Nat.succ_pred_eq_of_ne_zero z)
      conv at h => lhs;lhs;rw [t]
      rw [t] at lt
      have s := List.getElem_cons_succ head tail (n-1) lt
      trans (head :: tail)[n - 1 + 1];symm;exact s;exact h
    }
    {
      simp only [List.length_cons] at lt
      have t : n - 1 + 1 < tail.length + 1 := by have t : n - 1 + 1 = n := Nat.succ_pred_eq_of_ne_zero z;rw [t];exact lt
      exact Nat.succ_lt_succ_iff.mp t
    }
  }
}

def const_mem_cons_l {head : D} {tail : List D} : head ∈c (head :: tail) := by {
  unfold const_mem;use ⟨0,(by simp_all only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true])⟩
  simp_all only [List.length_cons, Fin.zero_eta, Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero]
}

def const_mem_cons_l' {head : D} {tail : List D} (m : a ∈c tail) : a ∈c (head :: tail) := by {
  unfold const_mem at m;unfold const_mem;obtain ⟨n,m⟩ := m
  use ⟨n+1,(by simp_all only [Fin.getElem_fin, Option.some.injEq, List.length_cons, add_lt_add_iff_right, Fin.is_lt])⟩
  simp_all only [Fin.getElem_fin, Option.some.injEq, List.length_cons, List.getElem_cons_succ]
}

lemma const_mem_mem (m : x ∈c l): x ∈ l := by {
  induction l with
  | nil => simp_all only [List.not_mem_nil];apply not_const_mem_nil m
  | cons head tail ih => {
    simp_all only [List.mem_cons]
    have m1 := const_mem_cons_r m;cases m1 with
    | left m1 => left;exact m1
    | right m1 => right; exact ih m1
  }
}

def mem_const_mem (m : x ∈ l) [d : DecidableEq D] : x ∈c l := by {
  induction l with
  | nil => simp_all only [List.not_mem_nil]
  | cons head tail ih => {
    simp_all only [List.mem_cons]
    have de : Decidable (x=head) := decEq x head
    by_cases h : x=head
    subst h;apply const_mem_cons_l
    simp_all only [false_or];exact const_mem_cons_l' (ih m)
  }
}

end constructive_membership
section Nodup

lemma unionPart_Nodup (h : (X++Y).Nodup) : X.Nodup := by induction X with
  | nil => simp_all only [List.nil_append, List.nodup_nil]
  | cons head tail ih => simp_all only [listUnion_Nodup, implies_true, List.cons_append, List.nodup_cons, List.mem_append, not_or, not_false_eq_true, and_self]


lemma unionPart_Nodup' (h : (X++Y).Nodup) : Y.Nodup := by induction X with
  | nil => simp_all only [List.nil_append]
  | cons head tail ih => simp_all only [listUnion_Nodup, implies_true, List.cons_append, List.nodup_cons, List.mem_append, not_or]

lemma unionPart_Nodup'' (h : (X++Y++Z).Nodup) : (X++Z).Nodup := by induction X with
  | nil => simp_all only [List.nil_append, listUnion_Nodup]
  | cons head tail ih => simp_all only [List.append_assoc, listUnion_Nodup, and_self, and_true, and_imp, List.cons_append, List.nodup_cons,
  List.mem_append, not_or, or_self, not_false_eq_true]


lemma middle_Nodup {l₁ l₂ : List D} (h : (l₁ ++ [a] ++ l₂).Nodup) : a∉l₁ ∧ a∉l₂ := by {
  constructor
  {
    induction l₁ with
    | nil => simp_all only [List.nil_append, List.cons_append, List.nodup_cons, List.not_mem_nil,
      not_false_eq_true]
    | cons head tail ih => {
      simp_all only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, forall_const]
      have t := h.left.left.right
      contrapose t;simp_all only [ne_eq, not_not, not_true_eq_false, not_false_eq_true]
    }
  }
  {
    induction l₂ with
    | nil => simp_all only [List.append_nil, List.not_mem_nil, not_false_eq_true]
    | cons head tail ih => {
      have e : (l₁ ++ [a] ++ head :: tail)=((l₁++[a])++[head]++tail) := by simp_all only [List.append_assoc, List.cons_append, List.nil_append]
      rw [e] at h
      simp_all only [List.mem_cons, not_or]
      constructor
      {
        have e : (l₁ ++ [a] ++ [head] ++ tail)=(l₁ ++ [a,head] ++ tail) := by simp_all only [List.append_assoc, List.cons_append, List.nil_append]
        rw [e] at h
        have nd := unionPart_Nodup' (unionPart_Nodup h)
        simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, List.nodup_nil, and_self, and_true]
      }
      {
        have t := unionPart_Nodup'' h
        exact ih t
      }
    }
  }
}

lemma list_equiv_nodup_length_equal (e : X ≅l Y) (Xn : X.Nodup) (Yn : Y.Nodup) : X.length=Y.length := by {
  revert Y
  induction X with
  | nil => simp_all only [List.nodup_nil, list_equiv_nil, List.length_nil, imp_self, implies_true]
  | cons head tail ih => {
    intro Y e Yn
    have m : head ∈ (head :: tail) := List.mem_cons_self head tail
    rw [e] at m
    have ⟨l₁,l₂,m⟩ := mem_givesMiddle m;subst m
    simp_all only [List.nodup_cons, list_equiv_cons, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_self, or_false, true_and, or_true, true_or, List.length_cons, @List.length_append,
      List.length_nil, zero_add, forall_const]
    have alm : tail.length = (l₁++l₂).length := by {
      have iso : tail ≅l (l₁ ++ l₂) := by {
        intro x
        specialize e x
        simp_all only [List.mem_append]
        constructor
        {
          intro h;have t : ¬x=head := by obtain ⟨Xn1,Xn2⟩ := Xn;contrapose Xn1;simp_all only [true_iff, IsEmpty.forall_iff, not_not]
          specialize e t
          rw [← e];exact h
        }
        {
          intro h;have t := middle_Nodup Yn
          cases h;(all_goals rename_i h);replace t := t.left;(any_goals replace t := t.right)
          all_goals have t : ¬x=head := by obtain ⟨Xn1,Xn2⟩ := Xn;contrapose Xn1;simp_all only [true_or, or_true, iff_true, IsEmpty.forall_iff, not_not]
          all_goals specialize e t;rw [e];simp_all only [true_or, or_true, iff_true]
        }
      }
      exact ih iso (unionPart_Nodup'' Yn)
    }
    simp_all only [@List.length_append];exact Nat.add_right_comm l₁.length l₂.length 1
  }
}


end Nodup
section multiset

variable (j k l : Multiset D)

def Multiset.length : ℕ := by {
  revert l;refine Quotient.lift List.length ?_
  intro l k p
  induction p with
  | nil => simp_all only [List.length_nil]
  | cons x _ _ => simp_all only [List.length_cons]
  | swap x y l => simp_all only [List.length_cons]
  | trans _ _ _ _ => simp_all only
}

@[simp]lemma Multiset.length_run (l : List D) : (Multiset.ofList l).length = l.length := by unfold Multiset.length;simp_all only [Multiset.lift_coe]

section multiset_flatten

def List_Multiset_flatten_help (l : List (Multiset D)) (soFar : Multiset D) : Multiset D := match l with
  | [] => soFar
  | (head :: tail) => List_Multiset_flatten_help tail (head + soFar)

lemma List_Multiset_flatten_help_invariant {D : Type} (l k : List (Multiset D)) (i : l.Perm k) (t : Multiset D):
  List_Multiset_flatten_help l t = List_Multiset_flatten_help k t := by {
    revert t
    induction i with
    | nil => intro t;rfl
    | cons x i h => intro t;rename_i l k;unfold List_Multiset_flatten_help;exact h (x + t)
    | swap x y l => {
      intro t;unfold List_Multiset_flatten_help;unfold List_Multiset_flatten_help;
      have e {D : Type} (x y : Multiset D) (t : Multiset D) : (x + (y + t)) = (y + (x + t)) := add_left_comm x y t
      rw [e]
    }
    | trans i₁ i₂ ih₁ ih₂ => {
      rename_i l₃ l₂ l₁;intro t;specialize ih₁ t;specialize ih₂ t
      trans List_Multiset_flatten_help l₂ t
      exact ih₁;exact ih₂
    }
  }

def Multiset.flatten (l : Multiset (Multiset D)) : Multiset D := by {
  apply Quotient.liftOn l (λ l ↦ List_Multiset_flatten_help l ∅)
  intro l k i;unfold HasEquiv.Equiv instHasEquivOfSetoid List.isSetoid  at i;simp_all only
  exact List_Multiset_flatten_help_invariant l k i ∅
}

end multiset_flatten
section multiset_unattach

def Multiset.unattach {T : Type} {p : T → Prop} (l : Multiset {x // p x}) : Multiset T := by {
  apply Quotient.liftOn l (λ l ↦ ⟦l.unattach⟧)
  intro l k h;simp [List.unattach, -List.map_subtype];trans (Multiset.map (fun x ↦ x.val) ⟦l⟧)
  simp_all only [List.map_subtype, List.map_id_fun', id_eq, List.pure_def, List.bind_eq_flatMap, List.flatMap_subtype, List.flatMap_singleton', quot_mk_to_coe, map_coe]
  rw [Quotient.sound h];simp_all only [quot_mk_to_coe, map_coe, List.map_subtype, List.map_id_fun', id_eq]
}

@[simp]lemma Multiset.unattach_to_map {T : Type} {p : T → Prop} (l : Multiset {x // p x}) : l.unattach = (l.map (·.val)) := by
  unfold Multiset.unattach;induction l using Quotient.ind;rename_i l;simp_all only [quot_mk_to_coe, lift_coe, map_coe, List.map_subtype, List.map_id_fun', id_eq]

/-extend List.unattach's lemmas-/

def Finset.unattach {T : Type} {p : T → Prop} (l : Finset {x // p x}) : Finset T := by {
  obtain ⟨l,nd⟩ := l;refine ⟨l.unattach,?_⟩
  simp_all only [Multiset.unattach_to_map]
  refine Multiset.Nodup.map_on ?_ nd
  intro x xil y yil ve;exact Subtype.eq ve
}

@[simp]lemma Finset.unattach_to_map {T : Type} {p : T → Prop} (l : Finset {x // p x}) : l.unattach = (l.map ⟨(·.val),by {intro x y h;rw [← Subtype.val_inj];exact h}⟩) := by
  unfold Finset.unattach;obtain ⟨m,nd⟩ := l;simp_all only [Multiset.unattach_to_map];rfl

/-extend Multiset.unattach's lemmas-/

end multiset_unattach
end multiset
