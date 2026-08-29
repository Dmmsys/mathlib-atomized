/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Even
/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/

public section

variable {α : Type*}

section CanonicallyOrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

/--
theorem `add_tsub_cancel_iff_le` / 定理 `add_tsub_cancel_iff_le`

English:
theorem add_tsub_cancel_iff_le
  statement: a + (b - a) = b ↔ a <= b
  proof: ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

中文:
定理 add_tsub_cancel_iff_le
  结论: a + (b - a) = b ↔ a <= b
  证明: ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

Depends on / 依赖: add_tsub_cancel_of_le, h.symm, le_iff_exists_add, le_iff_exists_add.mpr
-/
theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a <= b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

/--
theorem `tsub_add_cancel_iff_le` / 定理 `tsub_add_cancel_iff_le`

English:
theorem tsub_add_cancel_iff_le
  statement: b - a + a = b ↔ a <= b
  proof: by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

中文:
定理 tsub_add_cancel_iff_le
  结论: b - a + a = b ↔ a <= b
  证明: by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

Depends on / 依赖: add_comm, add_tsub_cancel_iff_le
-/
theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a <= b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

-- This was previously a `@[simp]` lemma, but it is not necessarily a good idea, e.g. in
-- `example (h : n - m = 0) : a + (n - m) = a := by simp_all`
/--
theorem `tsub_eq_zero_iff_le` / 定理 `tsub_eq_zero_iff_le`

English:
theorem tsub_eq_zero_iff_le
  statement: a - b = 0 ↔ a <= b
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [tsub_le_iff_left]; rw [add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le

@[simp]

中文:
定理 tsub_eq_zero_iff_le
  结论: a - b = 0 ↔ a <= b
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [tsub_le_iff_left]; rw [add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le

@[simp]

Depends on / 依赖: add_zero, nonpos_iff_eq_zero, tsub_le_iff_left
-/
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b := by
  rw [← nonpos_iff_eq_zero]; rw [tsub_le_iff_left]; rw [add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le

@[simp]
/--
theorem `tsub_self` / 定理 `tsub_self`

English:
theorem tsub_self
  given: (a : α)
  statement: a - a = 0
  proof: tsub_eq_zero_of_le le_rfl

中文:
定理 tsub_self
  条件: (a : α)
  结论: a - a = 0
  证明: tsub_eq_zero_of_le le_rfl

Depends on / 依赖: le_rfl, tsub_eq_zero_of_le
-/
theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl

/--
theorem `tsub_le_self` / 定理 `tsub_le_self`

English:
theorem tsub_le_self
  statement: a - b <= a
  proof: tsub_le_iff_left.mpr le_add_left le_rfl

@[simp]

中文:
定理 tsub_le_self
  结论: a - b <= a
  证明: tsub_le_iff_left.mpr le_add_left le_rfl

@[simp]

Depends on / 依赖: le_add_left, le_rfl, tsub_le_iff_left, tsub_le_iff_left.mpr
-/
theorem tsub_le_self : a - b <= a :=
tsub_le_iff_left.mpr le_add_left le_rfl

@[simp]
/--
theorem `zero_tsub` / 定理 `zero_tsub`

English:
theorem zero_tsub
  given: (a : α)
  statement: 0 - a = 0
  proof: tsub_eq_zero_of_le zero_le

中文:
定理 zero_tsub
  条件: (a : α)
  结论: 0 - a = 0
  证明: tsub_eq_zero_of_le zero_le

Depends on / 依赖: tsub_eq_zero_of_le, zero_le
-/
theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_of_le zero_le

/--
theorem `tsub_self_add` / 定理 `tsub_self_add`

English:
theorem tsub_self_add
  given: (a b : α)
  statement: a - (a + b) = 0
  proof: tsub_eq_zero_of_le self_le_add_right _ _

中文:
定理 tsub_self_add
  条件: (a b : α)
  结论: a - (a + b) = 0
  证明: tsub_eq_zero_of_le self_le_add_right _ _

Depends on / 依赖: self_le_add_right, tsub_eq_zero_of_le
-/
theorem tsub_self_add (a b : α) : a - (a + b) = 0 :=
tsub_eq_zero_of_le self_le_add_right _ _

/--
theorem `tsub_pos_iff_not_le` / 定理 `tsub_pos_iff_not_le`

English:
theorem tsub_pos_iff_not_le
  statement: 0 < a - b ↔ ¬a <= b
  proof: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [tsub_eq_zero_iff_le]

中文:
定理 tsub_pos_iff_not_le
  结论: 0 < a - b ↔ ¬a <= b
  证明: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [tsub_eq_zero_iff_le]

Depends on / 依赖: pos_iff_ne_zero, tsub_eq_zero_iff_le
-/
theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a <= b := by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [tsub_eq_zero_iff_le]

/--
theorem `tsub_pos_of_lt` / 定理 `tsub_pos_of_lt`

English:
theorem tsub_pos_of_lt
  given: (h : a < b)
  statement: 0 < b - a
  proof: tsub_pos_iff_not_le.mpr h.not_ge

中文:
定理 tsub_pos_of_lt
  条件: (h : a < b)
  结论: 0 < b - a
  证明: tsub_pos_iff_not_le.mpr h.not_ge

Depends on / 依赖: h.not_ge, not_ge, tsub_pos_iff_not_le, tsub_pos_iff_not_le.mpr
-/
theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_ge

/--
theorem `tsub_lt_of_lt` / 定理 `tsub_lt_of_lt`

English:
theorem tsub_lt_of_lt
  given: (h : a < b)
  statement: a - c < b
  proof: lt_of_le_of_lt tsub_le_self h

中文:
定理 tsub_lt_of_lt
  条件: (h : a < b)
  结论: a - c < b
  证明: lt_of_le_of_lt tsub_le_self h

Depends on / 依赖: lt_of_le_of_lt, tsub_le_self
-/
theorem tsub_lt_of_lt (h : a < b) : a - c < b :=
  lt_of_le_of_lt tsub_le_self h

namespace AddLECancellable

/--
theorem `tsub_le_tsub_iff_left` / 定理 `tsub_le_tsub_iff_left`

English:
theorem tsub_le_tsub_iff_left
  statement: (ha : AddLECancellable a) (hc : AddLECancellable c)
  proof: by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left]; rw [← hc.add_tsub_assoc_of_le h]; rw [hc.le_tsub_iff_right (h.trans le_add_self)]; rw [add_comm b]
  apply ha

中文:
定理 tsub_le_tsub_iff_left
  结论: (ha : AddLECancellable a) (hc : AddLECancellable c)
  证明: by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left]; rw [← hc.add_tsub_assoc_of_le h]; rw [hc.le_tsub_iff_right (h.trans le_add_self)]; rw [add_comm b]
  apply ha
-/
protected theorem tsub_le_tsub_iff_left (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h : c <= a) : a - b <= a - c ↔ c <= b := by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left]; rw [← hc.add_tsub_assoc_of_le h]; rw [hc.le_tsub_iff_right (h.trans le_add_self)]; rw [add_comm b]
  apply ha

/--
theorem `tsub_right_inj` / 定理 `tsub_right_inj`

English:
theorem tsub_right_inj
  statement: (ha : AddLECancellable a) (hb : AddLECancellable b)
  proof: by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]

中文:
定理 tsub_right_inj
  结论: (ha : AddLECancellable a) (hb : AddLECancellable b)
  证明: by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]
-/
protected theorem tsub_right_inj (ha : AddLECancellable a) (hb : AddLECancellable b)
    (hc : AddLECancellable c) (hba : b <= a) (hca : c <= a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [AddLeftReflectLE α]

/--
theorem `tsub_le_tsub_iff_left` / 定理 `tsub_le_tsub_iff_left`

English:
theorem tsub_le_tsub_iff_left
  given: (h : c <= a)
  statement: a - b <= a - c ↔ c <= b
  proof: Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h

中文:
定理 tsub_le_tsub_iff_left
  条件: (h : c <= a)
  结论: a - b <= a - c ↔ c <= b
  证明: Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.tsub_le_tsub_iff_left, tsub_le_tsub_iff_left
-/
theorem tsub_le_tsub_iff_left (h : c <= a) : a - b <= a - c ↔ c <= b :=
  Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h

/--
theorem `tsub_right_inj` / 定理 `tsub_right_inj`

English:
theorem tsub_right_inj
  given: (hba : b <= a) (hca : c <= a)
  statement: a - b = a - c ↔ b = c
  proof: Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca

中文:
定理 tsub_right_inj
  条件: (hba : b <= a) (hca : c <= a)
  结论: a - b = a - c ↔ b = c
  证明: Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.tsub_right_inj, tsub_right_inj
-/
theorem tsub_right_inj (hba : b <= a) (hca : c <= a) : a - b = a - c ↔ b = c :=
  Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca

variable (α)

/--
Definition of `CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid` / `CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid` 的定义

English:
abbreviation CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid
  signature: : AddCancelCommMonoid α
  body: { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }

中文:
缩写 CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid
  签名: : 加法消去交换幺半群 α
  定义体: { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }

Depends on / 依赖: AddCommMonoid, add_left_cancel, add_tsub_cancel_left, congr_arg, infer_instance
-/
abbrev CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid : AddCancelCommMonoid α :=
  { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }

end Contra

end CanonicallyOrderedAddCommMonoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/


section CanonicallyLinearOrderedAddCommMonoid

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

@[simp]
/--
theorem `tsub_pos_iff_lt` / 定理 `tsub_pos_iff_lt`

English:
theorem tsub_pos_iff_lt
  statement: 0 < a - b ↔ b < a
  proof: by rw [tsub_pos_iff_not_le, not_le]

中文:
定理 tsub_pos_iff_lt
  结论: 0 < a - b ↔ b < a
  证明: by rw [tsub_pos_iff_not_le, not_le]

Depends on / 依赖: not_le, tsub_pos_iff_not_le
-/
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]

/--
theorem `tsub_eq_tsub_min` / 定理 `tsub_eq_tsub_min`

English:
theorem tsub_eq_tsub_min
  given: (a b : α)
  statement: a - b = a - min a b
  proof: by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

中文:
定理 tsub_eq_tsub_min
  条件: (a b : α)
  结论: a - b = a - 最小值 a b
  证明: by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

Depends on / 依赖: le_total, min_eq_left, min_eq_right, tsub_eq_zero_of_le, tsub_self
-/
theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

namespace AddLECancellable

omit [CanonicallyOrderedAdd α] in
/--
theorem `lt_tsub_iff_right` / 定理 `lt_tsub_iff_right`

English:
theorem lt_tsub_iff_right
  given: (hc : AddLECancellable c)
  statement: a < b - c ↔ a + c < b
  proof: ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

omit [CanonicallyOrderedAdd α] in

中文:
定理 lt_tsub_iff_right
  条件: (hc : AddLECancellable c)
  结论: a < b - c ↔ a + c < b
  证明: ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

omit [CanonicallyOrderedAdd α] in
-/
protected theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

omit [CanonicallyOrderedAdd α] in
/--
theorem `lt_tsub_iff_left` / 定理 `lt_tsub_iff_left`

English:
theorem lt_tsub_iff_left
  given: (hc : AddLECancellable c)
  statement: a < b - c ↔ c + a < b
  proof: ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

中文:
定理 lt_tsub_iff_left
  条件: (hc : AddLECancellable c)
  结论: a < b - c ↔ c + a < b
  证明: ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩
-/
protected theorem lt_tsub_iff_left (hc : AddLECancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

/--
theorem `tsub_lt_tsub_iff_right` / 定理 `tsub_lt_tsub_iff_right`

English:
theorem tsub_lt_tsub_iff_right
  given: (hc : AddLECancellable c) (h : c <= a)
  proof: by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]

中文:
定理 tsub_lt_tsub_iff_right
  条件: (hc : AddLECancellable c) (h : c <= a)
  证明: by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]
-/
protected theorem tsub_lt_tsub_iff_right (hc : AddLECancellable c) (h : c <= a) :
    a - c < b - c ↔ a < b := by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]

/--
theorem `tsub_lt_self` / 定理 `tsub_lt_self`

English:
theorem tsub_lt_self
  given: (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b)
  statement: a - b < a
  proof: by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h]; rw [tsub_pos_iff_lt] at h₁
  exact h₂.not_ge (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)

中文:
定理 tsub_lt_self
  条件: (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b)
  结论: a - b < a
  证明: by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h]; rw [tsub_pos_iff_lt] at h₁
  exact h₂.not_ge (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)
-/
protected theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h]; rw [tsub_pos_iff_lt] at h₁
  exact h₂.not_ge (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)

/--
theorem `tsub_lt_self_iff` / 定理 `tsub_lt_self_iff`

English:
theorem tsub_lt_self_iff
  given: (ha : AddLECancellable a)
  statement: a - b < a ↔ 0 < a ∧ 0 < b
  proof: by
  refine ⟨fun h => ⟨h.pos, pos_of_ne_zero ?_⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false

中文:
定理 tsub_lt_self_iff
  条件: (ha : AddLECancellable a)
  结论: a - b < a ↔ 0 < a ∧ 0 < b
  证明: by
  refine ⟨fun h => ⟨h.pos, pos_of_ne_zero ?_⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false
-/
protected theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine ⟨fun h => ⟨h.pos, pos_of_ne_zero ?_⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false

/--
theorem `tsub_lt_tsub_iff_left_of_le` / 定理 `tsub_lt_tsub_iff_left_of_le`

English:
theorem tsub_lt_tsub_iff_left_of_le
  statement: (ha : AddLECancellable a) (hb : AddLECancellable b)
  proof: lt_iff_lt_of_le_iff_le ha.tsub_le_tsub_iff_left hb h

中文:
定理 tsub_lt_tsub_iff_left_of_le
  结论: (ha : AddLECancellable a) (hb : AddLECancellable b)
  证明: lt_iff_lt_of_le_iff_le ha.tsub_le_tsub_iff_left hb h
-/
protected theorem tsub_lt_tsub_iff_left_of_le (ha : AddLECancellable a) (hb : AddLECancellable b)
    (h : b <= a) : a - b < a - c ↔ c < b :=
lt_iff_lt_of_le_iff_le ha.tsub_le_tsub_iff_left hb h

end AddLECancellable

section Contra

variable [AddLeftReflectLE α]

/--
theorem `tsub_lt_tsub_iff_right` / 定理 `tsub_lt_tsub_iff_right`

English:
theorem tsub_lt_tsub_iff_right
  given: (h : c <= a)
  statement: a - c < b - c ↔ a < b
  proof: Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h

中文:
定理 tsub_lt_tsub_iff_right
  条件: (h : c <= a)
  结论: a - c < b - c ↔ a < b
  证明: Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_lt_tsub_iff_right, tsub_lt_tsub_iff_right
-/
theorem tsub_lt_tsub_iff_right (h : c <= a) : a - c < b - c ↔ a < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h

/--
theorem `tsub_lt_self` / 定理 `tsub_lt_self`

English:
theorem tsub_lt_self
  statement: 0 < a -> 0 < b -> a - b < a
  proof: Contravariant.AddLECancellable.tsub_lt_self

中文:
定理 tsub_lt_self
  结论: 0 < a -> 0 < b -> a - b < a
  证明: Contravariant.AddLECancellable.tsub_lt_self

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_lt_self, tsub_lt_self
-/
theorem tsub_lt_self : 0 < a -> 0 < b -> a - b < a :=
  Contravariant.AddLECancellable.tsub_lt_self

/--
theorem `tsub_lt_self_iff` / 定理 `tsub_lt_self_iff`

English:
theorem tsub_lt_self_iff
  statement: a - b < a ↔ 0 < a ∧ 0 < b
  proof: Contravariant.AddLECancellable.tsub_lt_self_iff

中文:
定理 tsub_lt_self_iff
  结论: a - b < a ↔ 0 < a ∧ 0 < b
  证明: Contravariant.AddLECancellable.tsub_lt_self_iff
-/
@[simp] theorem tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
  Contravariant.AddLECancellable.tsub_lt_self_iff

/--
theorem `tsub_lt_tsub_iff_left_of_le` / 定理 `tsub_lt_tsub_iff_left_of_le`

English:
theorem tsub_lt_tsub_iff_left_of_le
  given: (h : b <= a)
  statement: a - b < a - c ↔ c < b
  proof: Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h

中文:
定理 tsub_lt_tsub_iff_left_of_le
  条件: (h : b <= a)
  结论: a - b < a - c ↔ c < b
  证明: Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le, tsub_lt_tsub_iff_left_of_le
-/
theorem tsub_lt_tsub_iff_left_of_le (h : b <= a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h

/--
lemma `tsub_tsub_eq_min` / 引理 `tsub_tsub_eq_min`

English:
lemma tsub_tsub_eq_min
  given: (a b : α)
  statement: a - (a - b) = min a b
  proof: by
  rw [tsub_eq_tsub_min _ b]; rw [tsub_tsub_cancel_of_le (min_le_left a _)]

中文:
引理 tsub_tsub_eq_min
  条件: (a b : α)
  结论: a - (a - b) = 最小值 a b
  证明: by
  rw [tsub_eq_tsub_min _ b]; rw [tsub_tsub_cancel_of_le (min_le_left a _)]

Depends on / 依赖: min_le_left, tsub_eq_tsub_min, tsub_tsub_cancel_of_le
-/
lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b := by
  rw [tsub_eq_tsub_min _ b]; rw [tsub_tsub_cancel_of_le (min_le_left a _)]

end Contra



/--
theorem `tsub_add_eq_max` / 定理 `tsub_add_eq_max`

English:
theorem tsub_add_eq_max
  statement: a - b + b = max a b
  proof: by
  rcases le_total a b with h | h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]

中文:
定理 tsub_add_eq_max
  结论: a - b + b = 最大值 a b
  证明: by
  rcases le_total a b with h | h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]

Depends on / 依赖: le_total, max_eq_left, max_eq_right, tsub_add_cancel_of_le, tsub_eq_zero_of_le, zero_add
-/
theorem tsub_add_eq_max : a - b + b = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]

/--
theorem `add_tsub_eq_max` / 定理 `add_tsub_eq_max`

English:
theorem add_tsub_eq_max
  statement: a + (b - a) = max a b
  proof: by rw [add_comm, max_comm, tsub_add_eq_max]

中文:
定理 add_tsub_eq_max
  结论: a + (b - a) = 最大值 a b
  证明: by rw [add_comm, max_comm, tsub_add_eq_max]

Depends on / 依赖: add_comm, max_comm, tsub_add_eq_max
-/
theorem add_tsub_eq_max : a + (b - a) = max a b := by rw [add_comm, max_comm, tsub_add_eq_max]

/--
theorem `tsub_min` / 定理 `tsub_min`

English:
theorem tsub_min
  statement: a - min a b = a - b
  proof: (tsub_eq_tsub_min a b).symm

中文:
定理 tsub_min
  结论: a - 最小值 a b = a - b
  证明: (tsub_eq_tsub_min a b).symm

Depends on / 依赖: tsub_eq_tsub_min
-/
theorem tsub_min : a - min a b = a - b := (tsub_eq_tsub_min a b).symm

/--
theorem `tsub_add_min` / 定理 `tsub_add_min`

English:
theorem tsub_add_min
  statement: a - b + min a b = a
  proof: by
  rw [← tsub_min]; rw [@tsub_add_cancel_of_le]
  apply min_le_left

中文:
定理 tsub_add_min
  结论: a - b + 最小值 a b = a
  证明: by
  rw [← tsub_min]; rw [@tsub_add_cancel_of_le]
  apply min_le_left

Depends on / 依赖: min_le_left, tsub_add_cancel_of_le, tsub_min
-/
theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min]; rw [@tsub_add_cancel_of_le]
  apply min_le_left

-- TODO: Should we introduce `Odd.tsub`? It will probably only be used by `ℕ`.
/--
lemma `Even.tsub` / 引理 `Even.tsub`

English:
lemma Even.tsub
  given: [AddLeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n)
  proof: by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm

中文:
引理 Even.tsub
  条件: [加法LeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n)
  证明: by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm

Depends on / 依赖: add_le_add, add_zero, le_total, tsub_add_tsub_comm, tsub_eq_zero_of_le
-/
lemma Even.tsub [AddLeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm

end CanonicallyLinearOrderedAddCommMonoid

/-! ### `Sub` structure in linearly canonically ordered monoid using choice. -/

namespace CanonicallyOrderedAdd

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/--
Definition of `toSub` / `toSub` 的定义

English:
abbreviation toSub
  signature: : Sub α where
  body: if h : y <= x then (exists_add_of_le h).choose else 0

中文:
缩写 toSub
  签名: : 减法 α where
  定义体: if h : y <= x then (exists_add_of_le h).choose else 0

Depends on / 依赖: exists_add_of_le
-/
noncomputable abbrev toSub : Sub α where
  sub x y := if h : y <= x then (exists_add_of_le h).choose else 0

attribute [local instance] toSub

/--
theorem `toOrderedSub` / 定理 `toOrderedSub`

English:
theorem toOrderedSub
  given: [AddRightReflectLE α]
  statement: OrderedSub α where
  proof: by
    change dite _ _ _ <= c ↔ _
    split_ifs with h
    · have := (exists_add_of_le h).choose_spec
      rw [this] at h
      conv_rhs => rw [this, add_comm]
      rw [add_le_add_iff_right]
    · rw [not_le] at h
      constructor <;> intro h'
      · simpa using add_le_add h' h.le
      · exact 

中文:
定理 toOrderedSub
  条件: [加法RightReflectLE α]
  结论: OrderedSub α where
  证明: by
    change dite _ _ _ <= c ↔ _
    split_ifs with h
    · have := (exists_add_of_le h).choose_spec
      rw [this] at h
      conv_rhs => rw [this, add_comm]
      rw [add_le_add_iff_right]
    · rw [not_le] at h
      constructor <;> intro h'
      · simpa using add_le_add h' h.le
      · exact 

Depends on / 依赖: add_comm, add_le_add, add_le_add_iff_right, choose_spec, conv_rhs, exists_add_of_le, h.le, not_le, split_ifs, zero_le
-/
theorem toOrderedSub [AddRightReflectLE α] : OrderedSub α where
  tsub_le_iff_right a b c := by
    change dite _ _ _ <= c ↔ _
    split_ifs with h
    · have := (exists_add_of_le h).choose_spec
      rw [this] at h
      conv_rhs => rw [this, add_comm]
      rw [add_le_add_iff_right]
    · rw [not_le] at h
      constructor <;> intro h'
      · simpa using add_le_add h' h.le
      · exact zero_le

end CanonicallyOrderedAdd
