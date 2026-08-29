/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Lemmas about subtraction in an unbundled canonically ordered monoids
-/

public section

-- These are about *unbundled* canonically ordered monoids
assert_not_exists IsOrderedMonoid

variable {α : Type*}

section ExistsAddOfLE

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
/--
theorem `add_tsub_cancel_of_le` / 定理 `add_tsub_cancel_of_le`

English:
theorem add_tsub_cancel_of_le
  given: (h : a <= b)
  statement: a + (b - a) = b
  proof: by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  grw [add_tsub_le_left]

中文:
定理 add_tsub_cancel_of_le
  条件: (h : a <= b)
  结论: a + (b - a) = b
  证明: by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  grw [add_tsub_le_left]

Depends on / 依赖: add_tsub_le_left, exists_add_of_le, le_add_tsub, le_antisymm
-/
theorem add_tsub_cancel_of_le (h : a <= b) : a + (b - a) = b := by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  grw [add_tsub_le_left]

/--
theorem `tsub_add_cancel_of_le` / 定理 `tsub_add_cancel_of_le`

English:
theorem tsub_add_cancel_of_le
  given: (h : a <= b)
  statement: b - a + a = b
  proof: by
  rw [add_comm]
  exact add_tsub_cancel_of_le h

中文:
定理 tsub_add_cancel_of_le
  条件: (h : a <= b)
  结论: b - a + a = b
  证明: by
  rw [add_comm]
  exact add_tsub_cancel_of_le h

Depends on / 依赖: add_comm, add_tsub_cancel_of_le
-/
theorem tsub_add_cancel_of_le (h : a <= b) : b - a + a = b := by
  rw [add_comm]
  exact add_tsub_cancel_of_le h

/--
theorem `add_le_of_le_tsub_right_of_le` / 定理 `add_le_of_le_tsub_right_of_le`

English:
theorem add_le_of_le_tsub_right_of_le
  given: (h : b <= c) (h2 : a <= c - b)
  statement: a + b <= c
  proof: by
  grw [h2, tsub_add_cancel_of_le h]

中文:
定理 add_le_of_le_tsub_right_of_le
  条件: (h : b <= c) (h2 : a <= c - b)
  结论: a + b <= c
  证明: by
  grw [h2, tsub_add_cancel_of_le h]

Depends on / 依赖: tsub_add_cancel_of_le
-/
theorem add_le_of_le_tsub_right_of_le (h : b <= c) (h2 : a <= c - b) : a + b <= c := by
  grw [h2, tsub_add_cancel_of_le h]

/--
theorem `add_le_of_le_tsub_left_of_le` / 定理 `add_le_of_le_tsub_left_of_le`

English:
theorem add_le_of_le_tsub_left_of_le
  given: (h : a <= c) (h2 : b <= c - a)
  statement: a + b <= c
  proof: by
  grw [h2, add_tsub_cancel_of_le h]

中文:
定理 add_le_of_le_tsub_left_of_le
  条件: (h : a <= c) (h2 : b <= c - a)
  结论: a + b <= c
  证明: by
  grw [h2, add_tsub_cancel_of_le h]

Depends on / 依赖: add_tsub_cancel_of_le
-/
theorem add_le_of_le_tsub_left_of_le (h : a <= c) (h2 : b <= c - a) : a + b <= c := by
  grw [h2, add_tsub_cancel_of_le h]

/--
theorem `tsub_le_tsub_iff_right` / 定理 `tsub_le_tsub_iff_right`

English:
theorem tsub_le_tsub_iff_right
  given: (h : c <= b)
  statement: a - c <= b - c ↔ a <= b
  proof: by
  rw [tsub_le_iff_right]; rw [tsub_add_cancel_of_le h]

中文:
定理 tsub_le_tsub_iff_right
  条件: (h : c <= b)
  结论: a - c <= b - c ↔ a <= b
  证明: by
  rw [tsub_le_iff_right]; rw [tsub_add_cancel_of_le h]

Depends on / 依赖: tsub_add_cancel_of_le, tsub_le_iff_right
-/
theorem tsub_le_tsub_iff_right (h : c <= b) : a - c <= b - c ↔ a <= b := by
  rw [tsub_le_iff_right]; rw [tsub_add_cancel_of_le h]

/--
theorem `tsub_left_inj` / 定理 `tsub_left_inj`

English:
theorem tsub_left_inj
  given: (h1 : c <= a) (h2 : c <= b)
  statement: a - c = b - c ↔ a = b
  proof: by
  simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

中文:
定理 tsub_left_inj
  条件: (h1 : c <= a) (h2 : c <= b)
  结论: a - c = b - c ↔ a = b
  证明: by
  simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

Depends on / 依赖: le_antisymm_iff, simp_rw, tsub_le_tsub_iff_right
-/
theorem tsub_left_inj (h1 : c <= a) (h2 : c <= b) : a - c = b - c ↔ a = b := by
  simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

/--
theorem `tsub_inj_left` / 定理 `tsub_inj_left`

English:
theorem tsub_inj_left
  given: (h₁ : a <= b) (h₂ : a <= c)
  statement: b - a = c - a -> b = c
  proof: (tsub_left_inj h₁ h₂).1

中文:
定理 tsub_inj_left
  条件: (h₁ : a <= b) (h₂ : a <= c)
  结论: b - a = c - a -> b = c
  证明: (tsub_left_inj h₁ h₂).1

Depends on / 依赖: tsub_left_inj
-/
theorem tsub_inj_left (h₁ : a <= b) (h₂ : a <= c) : b - a = c - a -> b = c :=
  (tsub_left_inj h₁ h₂).1

/--
theorem `lt_of_tsub_lt_tsub_right_of_le` / 定理 `lt_of_tsub_lt_tsub_right_of_le`

English:
theorem lt_of_tsub_lt_tsub_right_of_le
  given: (h : c <= b) (h2 : a - c < b - c)
  statement: a < b
  proof: by
  refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne ?_
  rintro rfl
  exact h2.false

中文:
定理 lt_of_tsub_lt_tsub_right_of_le
  条件: (h : c <= b) (h2 : a - c < b - c)
  结论: a < b
  证明: by
  refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne ?_
  rintro rfl
  exact h2.false

Depends on / 依赖: h2.false, h2.le, lt_of_ne, tsub_le_tsub_iff_right
-/
theorem lt_of_tsub_lt_tsub_right_of_le (h : c <= b) (h2 : a - c < b - c) : a < b := by
  refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne ?_
  rintro rfl
  exact h2.false

/--
theorem `tsub_add_tsub_cancel` / 定理 `tsub_add_tsub_cancel`

English:
theorem tsub_add_tsub_cancel
  given: (hab : b <= a) (hcb : c <= b)
  statement: a - b + (b - c) = a - c
  proof: by
  convert! tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub]; rw [add_tsub_cancel_of_le hcb]

中文:
定理 tsub_add_tsub_cancel
  条件: (hab : b <= a) (hcb : c <= b)
  结论: a - b + (b - c) = a - c
  证明: by
  convert! tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub]; rw [add_tsub_cancel_of_le hcb]

Depends on / 依赖: add_tsub_cancel_of_le, convert, tsub_add_cancel_of_le, tsub_le_tsub_right, tsub_tsub
-/
theorem tsub_add_tsub_cancel (hab : b <= a) (hcb : c <= b) : a - b + (b - c) = a - c := by
  convert! tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub]; rw [add_tsub_cancel_of_le hcb]

/--
theorem `tsub_tsub_tsub_cancel_right` / 定理 `tsub_tsub_tsub_cancel_right`

English:
theorem tsub_tsub_tsub_cancel_right
  given: (h : c <= b)
  statement: a - c - (b - c) = a - b
  proof: by
  rw [tsub_tsub]; rw [add_tsub_cancel_of_le h]

中文:
定理 tsub_tsub_tsub_cancel_right
  条件: (h : c <= b)
  结论: a - c - (b - c) = a - b
  证明: by
  rw [tsub_tsub]; rw [add_tsub_cancel_of_le h]

Depends on / 依赖: add_tsub_cancel_of_le, tsub_tsub
-/
theorem tsub_tsub_tsub_cancel_right (h : c <= b) : a - c - (b - c) = a - b := by
  rw [tsub_tsub]; rw [add_tsub_cancel_of_le h]

/-! #### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

/--
theorem `eq_tsub_iff_add_eq_of_le` / 定理 `eq_tsub_iff_add_eq_of_le`

English:
theorem eq_tsub_iff_add_eq_of_le
  given: (hc : AddLECancellable c) (h : c <= b)
  proof: ⟨by
    rintro rfl
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩

中文:
定理 eq_tsub_iff_add_eq_of_le
  条件: (hc : AddLECancellable c) (h : c <= b)
  证明: ⟨by
    rintro rfl
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩
-/
protected theorem eq_tsub_iff_add_eq_of_le (hc : AddLECancellable c) (h : c <= b) :
    a = b - c ↔ a + c = b :=
  ⟨by
    rintro rfl
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩

/--
theorem `tsub_eq_iff_eq_add_of_le` / 定理 `tsub_eq_iff_eq_add_of_le`

English:
theorem tsub_eq_iff_eq_add_of_le
  given: (hb : AddLECancellable b) (h : b <= a)
  proof: by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]

中文:
定理 tsub_eq_iff_eq_add_of_le
  条件: (hb : AddLECancellable b) (h : b <= a)
  证明: by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]
-/
protected theorem tsub_eq_iff_eq_add_of_le (hb : AddLECancellable b) (h : b <= a) :
    a - b = c ↔ a = c + b := by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]

/--
theorem `add_tsub_assoc_of_le` / 定理 `add_tsub_assoc_of_le`

English:
theorem add_tsub_assoc_of_le
  given: (hc : AddLECancellable c) (h : c <= b) (a : α)
  proof: by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]

中文:
定理 add_tsub_assoc_of_le
  条件: (hc : AddLECancellable c) (h : c <= b) (a : α)
  证明: by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]
-/
protected theorem add_tsub_assoc_of_le (hc : AddLECancellable c) (h : c <= b) (a : α) :
    a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]

/--
theorem `tsub_add_eq_add_tsub` / 定理 `tsub_add_eq_add_tsub`

English:
theorem tsub_add_eq_add_tsub
  given: (hb : AddLECancellable b) (h : b <= a)
  proof: by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]

中文:
定理 tsub_add_eq_add_tsub
  条件: (hb : AddLECancellable b) (h : b <= a)
  证明: by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]
-/
protected theorem tsub_add_eq_add_tsub (hb : AddLECancellable b) (h : b <= a) :
    a - b + c = a + c - b := by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]

/--
theorem `tsub_tsub_assoc` / 定理 `tsub_tsub_assoc`

English:
theorem tsub_tsub_assoc
  given: (hbc : AddLECancellable (b - c)) (h₁ : b <= a) (h₂ : c <= b)
  proof: hbc.tsub_eq_of_eq_add by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]

中文:
定理 tsub_tsub_assoc
  条件: (hbc : AddLECancellable (b - c)) (h₁ : b <= a) (h₂ : c <= b)
  证明: hbc.tsub_eq_of_eq_add by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]
-/
protected theorem tsub_tsub_assoc (hbc : AddLECancellable (b - c)) (h₁ : b <= a) (h₂ : c <= b) :
    a - (b - c) = a - b + c :=
hbc.tsub_eq_of_eq_add by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]

/--
theorem `tsub_add_tsub_comm` / 定理 `tsub_add_tsub_comm`

English:
theorem tsub_add_tsub_comm
  statement: (hb : AddLECancellable b) (hd : AddLECancellable d)
  proof: by
  rw [hb.tsub_add_eq_add_tsub hba]; rw [← hd.add_tsub_assoc_of_le hdc]; rw [tsub_tsub]; rw [add_comm d]

中文:
定理 tsub_add_tsub_comm
  结论: (hb : AddLECancellable b) (hd : AddLECancellable d)
  证明: by
  rw [hb.tsub_add_eq_add_tsub hba]; rw [← hd.add_tsub_assoc_of_le hdc]; rw [tsub_tsub]; rw [add_comm d]
-/
protected theorem tsub_add_tsub_comm (hb : AddLECancellable b) (hd : AddLECancellable d)
    (hba : b <= a) (hdc : d <= c) : a - b + (c - d) = a + c - (b + d) := by
  rw [hb.tsub_add_eq_add_tsub hba]; rw [← hd.add_tsub_assoc_of_le hdc]; rw [tsub_tsub]; rw [add_comm d]

/--
theorem `le_tsub_iff_left` / 定理 `le_tsub_iff_left`

English:
theorem le_tsub_iff_left
  given: (ha : AddLECancellable a) (h : a <= c)
  statement: b <= c - a ↔ a + b <= c
  proof: ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩

中文:
定理 le_tsub_iff_left
  条件: (ha : AddLECancellable a) (h : a <= c)
  结论: b <= c - a ↔ a + b <= c
  证明: ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩
-/
protected theorem le_tsub_iff_left (ha : AddLECancellable a) (h : a <= c) : b <= c - a ↔ a + b <= c :=
  ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩

/--
theorem `le_tsub_iff_right` / 定理 `le_tsub_iff_right`

English:
theorem le_tsub_iff_right
  given: (ha : AddLECancellable a) (h : a <= c)
  proof: by
  rw [add_comm]
  exact ha.le_tsub_iff_left h

中文:
定理 le_tsub_iff_right
  条件: (ha : AddLECancellable a) (h : a <= c)
  证明: by
  rw [add_comm]
  exact ha.le_tsub_iff_left h
-/
protected theorem le_tsub_iff_right (ha : AddLECancellable a) (h : a <= c) :
    b <= c - a ↔ b + a <= c := by
  rw [add_comm]
  exact ha.le_tsub_iff_left h

/--
theorem `tsub_lt_iff_left` / 定理 `tsub_lt_iff_left`

English:
theorem tsub_lt_iff_left
  given: (hb : AddLECancellable b) (hba : b <= a)
  proof: by
  refine ⟨hb.lt_add_of_tsub_lt_left, ?_⟩
  intro h; refine (tsub_le_iff_left.mpr h.le).lt_of_ne ?_
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)

中文:
定理 tsub_lt_iff_left
  条件: (hb : AddLECancellable b) (hba : b <= a)
  证明: by
  refine ⟨hb.lt_add_of_tsub_lt_left, ?_⟩
  intro h; refine (tsub_le_iff_left.mpr h.le).lt_of_ne ?_
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)
-/
protected theorem tsub_lt_iff_left (hb : AddLECancellable b) (hba : b <= a) :
    a - b < c ↔ a < b + c := by
  refine ⟨hb.lt_add_of_tsub_lt_left, ?_⟩
  intro h; refine (tsub_le_iff_left.mpr h.le).lt_of_ne ?_
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)

/--
theorem `tsub_lt_iff_right` / 定理 `tsub_lt_iff_right`

English:
theorem tsub_lt_iff_right
  given: (hb : AddLECancellable b) (hba : b <= a)
  proof: by
  rw [add_comm]
  exact hb.tsub_lt_iff_left hba

中文:
定理 tsub_lt_iff_right
  条件: (hb : AddLECancellable b) (hba : b <= a)
  证明: by
  rw [add_comm]
  exact hb.tsub_lt_iff_left hba
-/
protected theorem tsub_lt_iff_right (hb : AddLECancellable b) (hba : b <= a) :
    a - b < c ↔ a < c + b := by
  rw [add_comm]
  exact hb.tsub_lt_iff_left hba

/--
theorem `tsub_lt_iff_tsub_lt` / 定理 `tsub_lt_iff_tsub_lt`

English:
theorem tsub_lt_iff_tsub_lt
  statement: (hb : AddLECancellable b) (hc : AddLECancellable c)
  proof: by
  rw [hb.tsub_lt_iff_left h₁]; rw [hc.tsub_lt_iff_right h₂]

中文:
定理 tsub_lt_iff_tsub_lt
  结论: (hb : AddLECancellable b) (hc : AddLECancellable c)
  证明: by
  rw [hb.tsub_lt_iff_left h₁]; rw [hc.tsub_lt_iff_right h₂]
-/
protected theorem tsub_lt_iff_tsub_lt (hb : AddLECancellable b) (hc : AddLECancellable c)
    (h₁ : b <= a) (h₂ : c <= a) : a - b < c ↔ a - c < b := by
  rw [hb.tsub_lt_iff_left h₁]; rw [hc.tsub_lt_iff_right h₂]

/--
theorem `le_tsub_iff_le_tsub` / 定理 `le_tsub_iff_le_tsub`

English:
theorem le_tsub_iff_le_tsub
  statement: (ha : AddLECancellable a) (hc : AddLECancellable c)
  proof: by
  rw [ha.le_tsub_iff_left h₁]; rw [hc.le_tsub_iff_right h₂]

中文:
定理 le_tsub_iff_le_tsub
  结论: (ha : AddLECancellable a) (hc : AddLECancellable c)
  证明: by
  rw [ha.le_tsub_iff_left h₁]; rw [hc.le_tsub_iff_right h₂]
-/
protected theorem le_tsub_iff_le_tsub (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h₁ : a <= b) (h₂ : c <= b) : a <= b - c ↔ c <= b - a := by
  rw [ha.le_tsub_iff_left h₁]; rw [hc.le_tsub_iff_right h₂]

/--
theorem `lt_tsub_iff_right_of_le` / 定理 `lt_tsub_iff_right_of_le`

English:
theorem lt_tsub_iff_right_of_le
  given: (hc : AddLECancellable c) (h : c <= b)
  proof: by
  refine ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne ?_, hc.lt_tsub_of_add_lt_right⟩
  rintro rfl
  exact h'.ne' hc.add_tsub_cancel_right

中文:
定理 lt_tsub_iff_right_of_le
  条件: (hc : AddLECancellable c) (h : c <= b)
  证明: by
  refine ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne ?_, hc.lt_tsub_of_add_lt_right⟩
  rintro rfl
  exact h'.ne' hc.add_tsub_cancel_right
-/
protected theorem lt_tsub_iff_right_of_le (hc : AddLECancellable c) (h : c <= b) :
    a < b - c ↔ a + c < b := by
  refine ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne ?_, hc.lt_tsub_of_add_lt_right⟩
  rintro rfl
  exact h'.ne' hc.add_tsub_cancel_right

/--
theorem `lt_tsub_iff_left_of_le` / 定理 `lt_tsub_iff_left_of_le`

English:
theorem lt_tsub_iff_left_of_le
  given: (hc : AddLECancellable c) (h : c <= b)
  proof: by
  rw [add_comm]
  exact hc.lt_tsub_iff_right_of_le h

中文:
定理 lt_tsub_iff_left_of_le
  条件: (hc : AddLECancellable c) (h : c <= b)
  证明: by
  rw [add_comm]
  exact hc.lt_tsub_iff_right_of_le h
-/
protected theorem lt_tsub_iff_left_of_le (hc : AddLECancellable c) (h : c <= b) :
    a < b - c ↔ c + a < b := by
  rw [add_comm]
  exact hc.lt_tsub_iff_right_of_le h

/--
theorem `tsub_inj_right` / 定理 `tsub_inj_right`

English:
theorem tsub_inj_right
  statement: (hab : AddLECancellable (a - b)) (h₁ : b <= a) (h₂ : c <= a)
  proof: by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁]; rw [h₃]; rw [tsub_add_cancel_of_le h₂]

中文:
定理 tsub_inj_right
  结论: (hab : AddLECancellable (a - b)) (h₁ : b <= a) (h₂ : c <= a)
  证明: by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁]; rw [h₃]; rw [tsub_add_cancel_of_le h₂]
-/
protected theorem tsub_inj_right (hab : AddLECancellable (a - b)) (h₁ : b <= a) (h₂ : c <= a)
    (h₃ : a - b = a - c) : b = c := by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁]; rw [h₃]; rw [tsub_add_cancel_of_le h₂]

/--
theorem `lt_of_tsub_lt_tsub_left_of_le` / 定理 `lt_of_tsub_lt_tsub_left_of_le`

English:
theorem lt_of_tsub_lt_tsub_left_of_le
  statement: [AddLeftReflectLT α]
  proof: by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)

中文:
定理 lt_of_tsub_lt_tsub_left_of_le
  结论: [AddLeftReflectLT α]
  证明: by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)
-/
protected theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α]
    (hb : AddLECancellable b) (hca : c <= a) (h : a - b < a - c) : c < b := by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)

/--
theorem `tsub_lt_tsub_left_of_le` / 定理 `tsub_lt_tsub_left_of_le`

English:
theorem tsub_lt_tsub_left_of_le
  statement: (hab : AddLECancellable (a - b)) (h₁ : b <= a)
  proof: (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' hab.tsub_inj_right h₁ (h.le.trans h₁) h'

中文:
定理 tsub_lt_tsub_left_of_le
  结论: (hab : AddLECancellable (a - b)) (h₁ : b <= a)
  证明: (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' hab.tsub_inj_right h₁ (h.le.trans h₁) h'
-/
protected theorem tsub_lt_tsub_left_of_le (hab : AddLECancellable (a - b)) (h₁ : b <= a)
    (h : c < b) : a - b < a - c :=
(tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' hab.tsub_inj_right h₁ (h.le.trans h₁) h'

/--
theorem `tsub_lt_tsub_right_of_le` / 定理 `tsub_lt_tsub_right_of_le`

English:
theorem tsub_lt_tsub_right_of_le
  given: (hc : AddLECancellable c) (h : c <= a) (h2 : a < b)
  proof: by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]

中文:
定理 tsub_lt_tsub_right_of_le
  条件: (hc : AddLECancellable c) (h : c <= a) (h2 : a < b)
  证明: by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]
-/
protected theorem tsub_lt_tsub_right_of_le (hc : AddLECancellable c) (h : c <= a) (h2 : a < b) :
    a - c < b - c := by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]

/--
theorem `tsub_lt_tsub_iff_left_of_le_of_le` / 定理 `tsub_lt_tsub_iff_left_of_le_of_le`

English:
theorem tsub_lt_tsub_iff_left_of_le_of_le
  statement: [AddLeftReflectLT α]
  proof: ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp]

中文:
定理 tsub_lt_tsub_iff_left_of_le_of_le
  结论: [AddLeftReflectLT α]
  证明: ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp]
-/
protected theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b <= a) (h₂ : c <= a) :
    a - b < a - c ↔ c < b :=
  ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp]
/--
lemma `add_add_tsub_cancel` / 引理 `add_add_tsub_cancel`

English:
lemma add_add_tsub_cancel
  given: (hc : AddLECancellable c) (hcb : c <= b)
  proof: by
  rw [← hc.add_tsub_assoc_of_le hcb]; rw [add_right_comm]; rw [hc.add_tsub_cancel_right]

@[simp]

中文:
引理 add_add_tsub_cancel
  条件: (hc : AddLECancellable c) (hcb : c <= b)
  证明: by
  rw [← hc.add_tsub_assoc_of_le hcb]; rw [add_right_comm]; rw [hc.add_tsub_cancel_right]

@[simp]
-/
protected lemma add_add_tsub_cancel (hc : AddLECancellable c) (hcb : c <= b) :
    a + c + (b - c) = a + b := by
  rw [← hc.add_tsub_assoc_of_le hcb]; rw [add_right_comm]; rw [hc.add_tsub_cancel_right]

@[simp]
/--
theorem `add_tsub_tsub_cancel` / 定理 `add_tsub_tsub_cancel`

English:
theorem add_tsub_tsub_cancel
  given: (hac : AddLECancellable (a - c)) (h : c <= a)
  proof: hac.tsub_eq_of_eq_add by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]

中文:
定理 add_tsub_tsub_cancel
  条件: (hac : AddLECancellable (a - c)) (h : c <= a)
  证明: hac.tsub_eq_of_eq_add by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]
-/
protected theorem add_tsub_tsub_cancel (hac : AddLECancellable (a - c)) (h : c <= a) :
    a + b - (a - c) = b + c :=
hac.tsub_eq_of_eq_add by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]

/--
theorem `tsub_tsub_cancel_of_le` / 定理 `tsub_tsub_cancel_of_le`

English:
theorem tsub_tsub_cancel_of_le
  given: (hba : AddLECancellable (b - a)) (h : a <= b)
  proof: hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm

中文:
定理 tsub_tsub_cancel_of_le
  条件: (hba : AddLECancellable (b - a)) (h : a <= b)
  证明: hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm
-/
protected theorem tsub_tsub_cancel_of_le (hba : AddLECancellable (b - a)) (h : a <= b) :
    b - (b - a) = a :=
  hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm

/--
theorem `tsub_tsub_tsub_cancel_left` / 定理 `tsub_tsub_tsub_cancel_left`

English:
theorem tsub_tsub_tsub_cancel_left
  given: (hab : AddLECancellable (a - b)) (h : b <= a)
  proof: by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]

中文:
定理 tsub_tsub_tsub_cancel_left
  条件: (hab : AddLECancellable (a - b)) (h : b <= a)
  证明: by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]
-/
protected theorem tsub_tsub_tsub_cancel_left (hab : AddLECancellable (a - b)) (h : b <= a) :
    a - c - (a - b) = b - c := by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]

end AddLECancellable

section Contra

/-! ### Lemmas where addition is order-reflecting. -/


variable [AddLeftReflectLE α]

/--
theorem `eq_tsub_iff_add_eq_of_le` / 定理 `eq_tsub_iff_add_eq_of_le`

English:
theorem eq_tsub_iff_add_eq_of_le
  given: (h : c <= b)
  statement: a = b - c ↔ a + c = b
  proof: Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h

中文:
定理 eq_tsub_iff_add_eq_of_le
  条件: (h : c <= b)
  结论: a = b - c ↔ a + c = b
  证明: Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le, eq_tsub_iff_add_eq_of_le
-/
theorem eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b - c ↔ a + c = b :=
  Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h

/--
theorem `tsub_eq_iff_eq_add_of_le` / 定理 `tsub_eq_iff_eq_add_of_le`

English:
theorem tsub_eq_iff_eq_add_of_le
  given: (h : b <= a)
  statement: a - b = c ↔ a = c + b
  proof: Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h

中文:
定理 tsub_eq_iff_eq_add_of_le
  条件: (h : b <= a)
  结论: a - b = c ↔ a = c + b
  证明: Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le, tsub_eq_iff_eq_add_of_le
-/
theorem tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b = c ↔ a = c + b :=
  Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h

/--
theorem `add_tsub_assoc_of_le` / 定理 `add_tsub_assoc_of_le`

English:
theorem add_tsub_assoc_of_le
  given: (h : c <= b) (a : α)
  statement: a + b - c = a + (b - c)
  proof: Contravariant.AddLECancellable.add_tsub_assoc_of_le h a

中文:
定理 add_tsub_assoc_of_le
  条件: (h : c <= b) (a : α)
  结论: a + b - c = a + (b - c)
  证明: Contravariant.AddLECancellable.add_tsub_assoc_of_le h a

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.add_tsub_assoc_of_le, add_tsub_assoc_of_le
-/
theorem add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b - c = a + (b - c) :=
  Contravariant.AddLECancellable.add_tsub_assoc_of_le h a

/--
theorem `tsub_add_eq_add_tsub` / 定理 `tsub_add_eq_add_tsub`

English:
theorem tsub_add_eq_add_tsub
  given: (h : b <= a)
  statement: a - b + c = a + c - b
  proof: Contravariant.AddLECancellable.tsub_add_eq_add_tsub h

中文:
定理 tsub_add_eq_add_tsub
  条件: (h : b <= a)
  结论: a - b + c = a + c - b
  证明: Contravariant.AddLECancellable.tsub_add_eq_add_tsub h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_add_eq_add_tsub, tsub_add_eq_add_tsub
-/
theorem tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a + c - b :=
  Contravariant.AddLECancellable.tsub_add_eq_add_tsub h

/--
theorem `tsub_tsub_assoc` / 定理 `tsub_tsub_assoc`

English:
theorem tsub_tsub_assoc
  given: (h₁ : b <= a) (h₂ : c <= b)
  statement: a - (b - c) = a - b + c
  proof: Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂

中文:
定理 tsub_tsub_assoc
  条件: (h₁ : b <= a) (h₂ : c <= b)
  结论: a - (b - c) = a - b + c
  证明: Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_tsub_assoc, tsub_tsub_assoc
-/
theorem tsub_tsub_assoc (h₁ : b <= a) (h₂ : c <= b) : a - (b - c) = a - b + c :=
  Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂

/--
theorem `tsub_add_tsub_comm` / 定理 `tsub_add_tsub_comm`

English:
theorem tsub_add_tsub_comm
  given: (hba : b <= a) (hdc : d <= c)
  statement: a - b + (c - d) = a + c - (b + d)
  proof: Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc

中文:
定理 tsub_add_tsub_comm
  条件: (hba : b <= a) (hdc : d <= c)
  结论: a - b + (c - d) = a + c - (b + d)
  证明: Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.tsub_add_tsub_comm, tsub_add_tsub_comm
-/
theorem tsub_add_tsub_comm (hba : b <= a) (hdc : d <= c) : a - b + (c - d) = a + c - (b + d) :=
  Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc

/--
theorem `le_tsub_iff_left` / 定理 `le_tsub_iff_left`

English:
theorem le_tsub_iff_left
  given: (h : a <= c)
  statement: b <= c - a ↔ a + b <= c
  proof: Contravariant.AddLECancellable.le_tsub_iff_left h

中文:
定理 le_tsub_iff_left
  条件: (h : a <= c)
  结论: b <= c - a ↔ a + b <= c
  证明: Contravariant.AddLECancellable.le_tsub_iff_left h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.le_tsub_iff_left, le_tsub_iff_left
-/
theorem le_tsub_iff_left (h : a <= c) : b <= c - a ↔ a + b <= c :=
  Contravariant.AddLECancellable.le_tsub_iff_left h

/--
theorem `le_tsub_iff_right` / 定理 `le_tsub_iff_right`

English:
theorem le_tsub_iff_right
  given: (h : a <= c)
  statement: b <= c - a ↔ b + a <= c
  proof: Contravariant.AddLECancellable.le_tsub_iff_right h

中文:
定理 le_tsub_iff_right
  条件: (h : a <= c)
  结论: b <= c - a ↔ b + a <= c
  证明: Contravariant.AddLECancellable.le_tsub_iff_right h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.le_tsub_iff_right, le_tsub_iff_right
-/
theorem le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <= c :=
  Contravariant.AddLECancellable.le_tsub_iff_right h

/--
theorem `tsub_lt_iff_left` / 定理 `tsub_lt_iff_left`

English:
theorem tsub_lt_iff_left
  given: (hbc : b <= a)
  statement: a - b < c ↔ a < b + c
  proof: Contravariant.AddLECancellable.tsub_lt_iff_left hbc

中文:
定理 tsub_lt_iff_left
  条件: (hbc : b <= a)
  结论: a - b < c ↔ a < b + c
  证明: Contravariant.AddLECancellable.tsub_lt_iff_left hbc

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_lt_iff_left, tsub_lt_iff_left
-/
theorem tsub_lt_iff_left (hbc : b <= a) : a - b < c ↔ a < b + c :=
  Contravariant.AddLECancellable.tsub_lt_iff_left hbc

/--
theorem `tsub_lt_iff_right` / 定理 `tsub_lt_iff_right`

English:
theorem tsub_lt_iff_right
  given: (hbc : b <= a)
  statement: a - b < c ↔ a < c + b
  proof: Contravariant.AddLECancellable.tsub_lt_iff_right hbc

中文:
定理 tsub_lt_iff_right
  条件: (hbc : b <= a)
  结论: a - b < c ↔ a < c + b
  证明: Contravariant.AddLECancellable.tsub_lt_iff_right hbc

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_lt_iff_right, tsub_lt_iff_right
-/
theorem tsub_lt_iff_right (hbc : b <= a) : a - b < c ↔ a < c + b :=
  Contravariant.AddLECancellable.tsub_lt_iff_right hbc

/--
theorem `tsub_lt_iff_tsub_lt` / 定理 `tsub_lt_iff_tsub_lt`

English:
theorem tsub_lt_iff_tsub_lt
  given: (h₁ : b <= a) (h₂ : c <= a)
  statement: a - b < c ↔ a - c < b
  proof: Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂

中文:
定理 tsub_lt_iff_tsub_lt
  条件: (h₁ : b <= a) (h₂ : c <= a)
  结论: a - b < c ↔ a - c < b
  证明: Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt, tsub_lt_iff_tsub_lt
-/
theorem tsub_lt_iff_tsub_lt (h₁ : b <= a) (h₂ : c <= a) : a - b < c ↔ a - c < b :=
  Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂

/--
theorem `le_tsub_iff_le_tsub` / 定理 `le_tsub_iff_le_tsub`

English:
theorem le_tsub_iff_le_tsub
  given: (h₁ : a <= b) (h₂ : c <= b)
  statement: a <= b - c ↔ c <= b - a
  proof: Contravariant.AddLECancellable.le_tsub_iff_le_tsub Contravariant.AddLECancellable h₁ h₂

中文:
定理 le_tsub_iff_le_tsub
  条件: (h₁ : a <= b) (h₂ : c <= b)
  结论: a <= b - c ↔ c <= b - a
  证明: Contravariant.AddLECancellable.le_tsub_iff_le_tsub Contravariant.AddLECancellable h₁ h₂

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.le_tsub_iff_le_tsub, le_tsub_iff_le_tsub
-/
theorem le_tsub_iff_le_tsub (h₁ : a <= b) (h₂ : c <= b) : a <= b - c ↔ c <= b - a :=
  Contravariant.AddLECancellable.le_tsub_iff_le_tsub Contravariant.AddLECancellable h₁ h₂

/--
theorem `lt_tsub_iff_right_of_le` / 定理 `lt_tsub_iff_right_of_le`

English:
theorem lt_tsub_iff_right_of_le
  given: (h : c <= b)
  statement: a < b - c ↔ a + c < b
  proof: Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h

中文:
定理 lt_tsub_iff_right_of_le
  条件: (h : c <= b)
  结论: a < b - c ↔ a + c < b
  证明: Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_tsub_iff_right_of_le, lt_tsub_iff_right_of_le
-/
theorem lt_tsub_iff_right_of_le (h : c <= b) : a < b - c ↔ a + c < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h

/--
theorem `lt_tsub_iff_left_of_le` / 定理 `lt_tsub_iff_left_of_le`

English:
theorem lt_tsub_iff_left_of_le
  given: (h : c <= b)
  statement: a < b - c ↔ c + a < b
  proof: Contravariant.AddLECancellable.lt_tsub_iff_left_of_le h

中文:
定理 lt_tsub_iff_left_of_le
  条件: (h : c <= b)
  结论: a < b - c ↔ c + a < b
  证明: Contravariant.AddLECancellable.lt_tsub_iff_left_of_le h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_tsub_iff_left_of_le, lt_tsub_iff_left_of_le
-/
theorem lt_tsub_iff_left_of_le (h : c <= b) : a < b - c ↔ c + a < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_left_of_le h

/--
theorem `lt_of_tsub_lt_tsub_left_of_le` / 定理 `lt_of_tsub_lt_tsub_left_of_le`

English:
theorem lt_of_tsub_lt_tsub_left_of_le
  statement: [AddLeftReflectLT α] (hca : c <= a)
  proof: Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h

中文:
定理 lt_of_tsub_lt_tsub_left_of_le
  结论: [AddLeftReflectLT α] (hca : c <= a)
  证明: Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le, lt_of_tsub_lt_tsub_left_of_le
-/
theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α] (hca : c <= a)
    (h : a - b < a - c) : c < b :=
  Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h

/--
theorem `tsub_lt_tsub_left_of_le` / 定理 `tsub_lt_tsub_left_of_le`

English:
theorem tsub_lt_tsub_left_of_le
  statement: b <= a -> c < b -> a - b < a - c
  proof: Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le

中文:
定理 tsub_lt_tsub_left_of_le
  结论: b <= a -> c < b -> a - b < a - c
  证明: Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le, tsub_lt_tsub_left_of_le
-/
theorem tsub_lt_tsub_left_of_le : b <= a -> c < b -> a - b < a - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le

/--
theorem `tsub_lt_tsub_right_of_le` / 定理 `tsub_lt_tsub_right_of_le`

English:
theorem tsub_lt_tsub_right_of_le
  given: (h : c <= a) (h2 : a < b)
  statement: a - c < b - c
  proof: Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2

中文:
定理 tsub_lt_tsub_right_of_le
  条件: (h : c <= a) (h2 : a < b)
  结论: a - c < b - c
  证明: Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le, tsub_lt_tsub_right_of_le
-/
theorem tsub_lt_tsub_right_of_le (h : c <= a) (h2 : a < b) : a - c < b - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2

/--
theorem `tsub_inj_right` / 定理 `tsub_inj_right`

English:
theorem tsub_inj_right
  given: (h₁ : b <= a) (h₂ : c <= a) (h₃ : a - b = a - c)
  statement: b = c
  proof: Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

中文:
定理 tsub_inj_right
  条件: (h₁ : b <= a) (h₂ : c <= a) (h₃ : a - b = a - c)
  结论: b = c
  证明: Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_inj_right, tsub_inj_right
-/
theorem tsub_inj_right (h₁ : b <= a) (h₂ : c <= a) (h₃ : a - b = a - c) : b = c :=
  Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

/--
theorem `tsub_lt_tsub_iff_left_of_le_of_le` / 定理 `tsub_lt_tsub_iff_left_of_le_of_le`

English:
theorem tsub_lt_tsub_iff_left_of_le_of_le
  statement: [AddLeftReflectLT α] (h₁ : b <= a)
  proof: Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

@[simp]

中文:
定理 tsub_lt_tsub_iff_left_of_le_of_le
  结论: [AddLeftReflectLT α] (h₁ : b <= a)
  证明: Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

@[simp]

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le, tsub_lt_tsub_iff_left_of_le_of_le
-/
theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α] (h₁ : b <= a)
    (h₂ : c <= a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

@[simp]
/--
lemma `add_add_tsub_cancel` / 引理 `add_add_tsub_cancel`

English:
lemma add_add_tsub_cancel
  given: (hcb : c <= b)
  statement: a + c + (b - c) = a + b
  proof: Contravariant.AddLECancellable.add_add_tsub_cancel hcb

@[simp]

中文:
引理 add_add_tsub_cancel
  条件: (hcb : c <= b)
  结论: a + c + (b - c) = a + b
  证明: Contravariant.AddLECancellable.add_add_tsub_cancel hcb

@[simp]

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.add_add_tsub_cancel, add_add_tsub_cancel
-/
lemma add_add_tsub_cancel (hcb : c <= b) : a + c + (b - c) = a + b :=
  Contravariant.AddLECancellable.add_add_tsub_cancel hcb

@[simp]
/--
theorem `add_tsub_tsub_cancel` / 定理 `add_tsub_tsub_cancel`

English:
theorem add_tsub_tsub_cancel
  given: (h : c <= a)
  statement: a + b - (a - c) = b + c
  proof: Contravariant.AddLECancellable.add_tsub_tsub_cancel h

中文:
定理 add_tsub_tsub_cancel
  条件: (h : c <= a)
  结论: a + b - (a - c) = b + c
  证明: Contravariant.AddLECancellable.add_tsub_tsub_cancel h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.add_tsub_tsub_cancel, add_tsub_tsub_cancel
-/
theorem add_tsub_tsub_cancel (h : c <= a) : a + b - (a - c) = b + c :=
  Contravariant.AddLECancellable.add_tsub_tsub_cancel h

/--
theorem `tsub_tsub_cancel_of_le` / 定理 `tsub_tsub_cancel_of_le`

English:
theorem tsub_tsub_cancel_of_le
  given: (h : a <= b)
  statement: b - (b - a) = a
  proof: Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h

中文:
定理 tsub_tsub_cancel_of_le
  条件: (h : a <= b)
  结论: b - (b - a) = a
  证明: Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_tsub_cancel_of_le, tsub_tsub_cancel_of_le
-/
theorem tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a) = a :=
  Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h

/--
theorem `tsub_tsub_tsub_cancel_left` / 定理 `tsub_tsub_tsub_cancel_left`

English:
theorem tsub_tsub_tsub_cancel_left
  given: (h : b <= a)
  statement: a - c - (a - b) = b - c
  proof: Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h

中文:
定理 tsub_tsub_tsub_cancel_left
  条件: (h : b <= a)
  结论: a - c - (a - b) = b - c
  证明: Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left, tsub_tsub_tsub_cancel_left
-/
theorem tsub_tsub_tsub_cancel_left (h : b <= a) : a - c - (a - b) = b - c :=
  Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h

-- note: not generalized to `AddLECancellable` because `add_tsub_add_eq_tsub_left` isn't
/--
theorem `tsub_tsub_eq_add_tsub_of_le` / 定理 `tsub_tsub_eq_add_tsub_of_le`

English:
theorem tsub_tsub_eq_add_tsub_of_le
  proof: by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c]; rw [add_comm a c]; rw [add_tsub_add_eq_tsub_left]

中文:
定理 tsub_tsub_eq_add_tsub_of_le
  证明: by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c]; rw [add_comm a c]; rw [add_tsub_add_eq_tsub_left]

Depends on / 依赖: add_comm, add_tsub_add_eq_tsub_left, add_tsub_cancel_left, exists_add_of_le
-/
theorem tsub_tsub_eq_add_tsub_of_le
    (h : c <= b) : a - (b - c) = a + c - b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c]; rw [add_comm a c]; rw [add_tsub_add_eq_tsub_left]

end Contra

end ExistsAddOfLE
