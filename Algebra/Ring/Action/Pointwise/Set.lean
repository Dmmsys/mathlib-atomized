/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

assert_not_exists IsOrderedMonoid Field

open Function
open scoped Pointwise

variable {α β : Type*}

namespace Set

section DistribSMul
variable [AddGroup β] [DistribSMul α β] (a : α) (s : Set α) (t : Set β)

@[simp]
/--
lemma `smul_set_neg` / 引理 `smul_set_neg`

English:
lemma smul_set_neg
  statement: a • -t = -(a • t)
  proof: by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

@[simp]

中文:
引理 smul_set_neg
  结论: a • -t = -(a • t)
  证明: by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

@[simp]

Depends on / 依赖: image_image, image_neg_eq_neg, image_smul, simp_rw, smul_neg
-/
lemma smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

@[simp]
/--
lemma `smul_neg` / 引理 `smul_neg`

English:
lemma smul_neg
  statement: s • -t = -(s • t)
  proof: by
  simp_rw [← image_neg_eq_neg]
  exact image_image2_right_comm smul_neg

中文:
引理 smul_neg
  结论: s • -t = -(s • t)
  证明: by
  simp_rw [← image_neg_eq_neg]
  exact image_image2_right_comm smul_neg
-/
protected lemma smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image_image2_right_comm smul_neg

end DistribSMul

section Semiring
variable [Semiring α] [AddCommMonoid β] [Module α β]

/--
lemma `add_smul_subset` / 引理 `add_smul_subset`

English:
lemma add_smul_subset
  given: (a b : α) (s : Set β)
  statement: (a + b) • s subseteq a • s + b • s
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

中文:
引理 add_smul_subset
  条件: (a b : α) (s : 集合 β)
  结论: (a + b) • s subseteq a • s + b • s
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

Depends on / 依赖: add_mem_add, add_smul, smul_mem_smul_set
-/
lemma add_smul_subset (a b : α) (s : Set β) : (a + b) • s subseteq a • s + b • s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

variable [IsDomain α] [Module.IsTorsionFree α β] {a : α} {s : Set α} {t : Set β}

/--
lemma `zero_mem_smul_set_iff` / 引理 `zero_mem_smul_set_iff`

English:
lemma zero_mem_smul_set_iff
  given: (ha : a != 0)
  statement: (0 : β) in a • t ↔ (0 : β) in t
  proof: by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(smul_eq_zero.1 h).resolve_left ha] at hb

中文:
引理 zero_mem_smul_set_iff
  条件: (ha : a != 0)
  结论: (0 : β) in a • t ↔ (0 : β) in t
  证明: by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(smul_eq_zero.1 h).resolve_left ha] at hb

Depends on / 依赖: resolve_left, smul_eq_zero, zero_mem_smul_set
-/
lemma zero_mem_smul_set_iff (ha : a != 0) : (0 : β) in a • t ↔ (0 : β) in t := by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(smul_eq_zero.1 h).resolve_left ha] at hb

/--
lemma `zero_mem_smul_iff` / 引理 `zero_mem_smul_iff`

English:
lemma zero_mem_smul_iff
  statement: 0 in s • t ↔ 0 in s ∧ t.Nonempty ∨ 0 in t ∧ s.Nonempty where
  proof: smul_eq_zero.1 h; exacts [.inl ⟨ha, b, hb⟩, .inr ⟨hb, a, ha⟩]
  mpr
  | .inl ⟨hs, b, hb⟩ => ⟨0, hs, b, hb, zero_smul _ _⟩
  | .inr ⟨ht, a, ha⟩ => ⟨a, ha, 0, ht, smul_zero _⟩

中文:
引理 zero_mem_smul_iff
  结论: 0 in s • t ↔ 0 in s ∧ t.非空 ∨ 0 in t ∧ s.非空 where
  证明: smul_eq_zero.1 h; exacts [.inl ⟨ha, b, hb⟩, .inr ⟨hb, a, ha⟩]
  mpr
  | .inl ⟨hs, b, hb⟩ => ⟨0, hs, b, hb, zero_smul _ _⟩
  | .inr ⟨ht, a, ha⟩ => ⟨a, ha, 0, ht, smul_zero _⟩

Depends on / 依赖: exacts, smul_eq_zero
-/
lemma zero_mem_smul_iff : 0 in s • t ↔ 0 in s ∧ t.Nonempty ∨ 0 in t ∧ s.Nonempty where
  mp | ⟨a, ha, b, hb, h⟩ => by
      obtain rfl | rfl := smul_eq_zero.1 h; exacts [.inl ⟨ha, b, hb⟩, .inr ⟨hb, a, ha⟩]
  mpr
  | .inl ⟨hs, b, hb⟩ => ⟨0, hs, b, hb, zero_smul _ _⟩
  | .inr ⟨ht, a, ha⟩ => ⟨a, ha, 0, ht, smul_zero _⟩

end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
/--
lemma `neg_smul_set` / 引理 `neg_smul_set`

English:
lemma neg_smul_set
  statement: -a • t = -(a • t)
  proof: by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

@[simp]

中文:
引理 neg_smul_set
  结论: -a • t = -(a • t)
  证明: by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

@[simp]

Depends on / 依赖: image_image, image_neg_eq_neg, image_smul, neg_smul, simp_rw
-/
lemma neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

@[simp]
/--
lemma `neg_smul` / 引理 `neg_smul`

English:
lemma neg_smul
  statement: -s • t = -(s • t)
  proof: by
  simp_rw [← image_neg_eq_neg]
  exact image2_image_left_comm neg_smul

中文:
引理 neg_smul
  结论: -s • t = -(s • t)
  证明: by
  simp_rw [← image_neg_eq_neg]
  exact image2_image_left_comm neg_smul
-/
protected lemma neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image2_image_left_comm neg_smul

end Ring
end Set
