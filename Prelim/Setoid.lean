/-This file is optimized-/

import Mathlib.Tactic


/-!
Some lemmas about Setoids
-/

assert_not_exists complete SimpleGraph


set_option linter.style.longLine.maxLineLength 150


section common_setoids

instance eqSetoid {type : Type} : Setoid type where
  r (x y : type) := x=y
  iseqv := ⟨((fun x ↦ rfl)),(·.symm),by intro _ y _ _ _; trans y;repeat assumption⟩

end common_setoids
section preSetoid

def Setoid.preSetoid {T U : Type} (f : T → U) (s : Setoid U) : Setoid T where
  r (x y : T) := s (f x) (f y)
  iseqv := ⟨by intro _;rfl,by intro _ _ h;symm;exact h,by intro _ _ _ h i;exact s.trans h i⟩

instance preSetoid_decidable {T U : Type} (f : T → U) (s : Setoid U) [d : DecidableRel s]
  : DecidableRel (s.preSetoid f) := by
  unfold Setoid.preSetoid;intro x y;replace d := d (f x) (f y);simp_all only;exact d

@[simp] lemma preSetoid_apply {T U : Type} (f : T → U) (s : Setoid U) (x y : T)
  : s.preSetoid f x y ↔ s (f x) (f y) := by unfold Setoid.preSetoid;simp_all only

def Setoid.subSetoid {T : Type} {p : T → Prop} (s : Setoid T) : Setoid {x : T // p x}
  := s.preSetoid (fun x => x.val)

instance subSetoid_decidable {T : Type} (p : T → Prop) (s : Setoid T) [d : DecidableRel s]
  : DecidableRel (s.subSetoid (p:=p)) := preSetoid_decidable (fun x : {x : T // p x} => x.val) s

@[simp] lemma subSetoid_apply {T : Type} (p : T → Prop) (s : Setoid T) (x y : T) (xh : p x) (yh : p y)
  : s.subSetoid ⟨x,xh⟩ ⟨y,yh⟩ ↔ s x y
  := preSetoid_apply (fun x : {x : T // p x} => x.val) s ⟨x,xh⟩ ⟨y,yh⟩

def Setoid.depSetoid {T : Type} {p : T → Type} (s : Setoid T) : Setoid ((x : T)×(p x))
  := s.preSetoid (fun x => x.1)

instance depSetoid_decidable {T : Type} (p : T → Type) (s : Setoid T) [d : DecidableRel s] : DecidableRel (s.depSetoid (p:=p))
  := preSetoid_decidable (fun x : ((x : T)×(p x)) => x.1) s

@[simp] lemma depSetoid_apply {T : Type} (p : T → Type) (s : Setoid T) (x y : T) (xh : p x) (yh : p y) : s.depSetoid ⟨x,xh⟩ ⟨y,yh⟩ ↔ s x y
  := preSetoid_apply (fun x : ((x : T)×(p x)) => x.1) s ⟨x,xh⟩ ⟨y,yh⟩

end preSetoid
