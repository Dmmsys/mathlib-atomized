/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas about `min` and `max` in an ordered monoid.
-/

public section


open Function

variable {α β : Type*}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/

section CommSemigroup
variable [LinearOrder α] [CommSemigroup β]

@[to_additive]
/--
lemma `fn_min_mul_fn_max` / 引理 `fn_min_mul_fn_max`

English:
lemma fn_min_mul_fn_max
  given: (f : α -> β) (a b : α)
  statement: f (min a b) * f (max a b) = f a * f b
  proof: by
  grind

@[to_additive]

中文:
引理 fn_min_mul_fn_max
  条件: (f : α -> β) (a b : α)
  结论: f (min a b) * f (max a b) = f a * f b
  证明: by
  grind

@[to_additive]
-/
lemma fn_min_mul_fn_max (f : α -> β) (a b : α) : f (min a b) * f (max a b) = f a * f b := by
  grind

@[to_additive]
/--
lemma `fn_max_mul_fn_min` / 引理 `fn_max_mul_fn_min`

English:
lemma fn_max_mul_fn_min
  given: (f : α -> β) (a b : α)
  statement: f (max a b) * f (min a b) = f a * f b
  proof: by
  grind

中文:
引理 fn_max_mul_fn_min
  条件: (f : α -> β) (a b : α)
  结论: f (max a b) * f (min a b) = f a * f b
  证明: by
  grind
-/
lemma fn_max_mul_fn_min (f : α -> β) (a b : α) : f (max a b) * f (min a b) = f a * f b := by
  grind

variable [CommSemigroup α]

@[to_additive (attr := simp)]
/--
lemma `min_mul_max` / 引理 `min_mul_max`

English:
lemma min_mul_max
  given: (a b : α)
  statement: min a b * max a b = a * b
  proof: fn_min_mul_fn_max id _ _

@[to_additive (attr := simp)]

中文:
引理 min_mul_max
  条件: (a b : α)
  结论: min a b * max a b = a * b
  证明: fn_min_mul_fn_max id _ _

@[to_additive (attr := simp)]

Depends on / 依赖: fn_min_mul_fn_max
-/
lemma min_mul_max (a b : α) : min a b * max a b = a * b := fn_min_mul_fn_max id _ _

@[to_additive (attr := simp)]
/--
lemma `max_mul_min` / 引理 `max_mul_min`

English:
lemma max_mul_min
  given: (a b : α)
  statement: max a b * min a b = a * b
  proof: fn_max_mul_fn_min id _ _

中文:
引理 max_mul_min
  条件: (a b : α)
  结论: max a b * min a b = a * b
  证明: fn_max_mul_fn_min id _ _

Depends on / 依赖: fn_max_mul_fn_min
-/
lemma max_mul_min (a b : α) : max a b * min a b = a * b := fn_max_mul_fn_min id _ _

end CommSemigroup

section CovariantClassMulLe

variable [LinearOrder α]

section Mul

variable [Mul α]

section Left

variable [MulLeftMono α]

@[to_additive]
/--
theorem `min_mul_mul_left` / 定理 `min_mul_mul_left`

English:
theorem min_mul_mul_left
  given: (a b c : α)
  statement: min (a * b) (a * c) = a * min b c
  proof: (monotone_id.const_mul' a).map_min.symm

@[to_additive]

中文:
定理 min_mul_mul_left
  条件: (a b c : α)
  结论: min (a * b) (a * c) = a * min b c
  证明: (monotone_id.const_mul' a).map_min.symm

@[to_additive]

Depends on / 依赖: const_mul, map_min, map_min.symm, monotone_id, monotone_id.const_mul
-/
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[to_additive]
/--
theorem `max_mul_mul_left` / 定理 `max_mul_mul_left`

English:
theorem max_mul_mul_left
  given: (a b c : α)
  statement: max (a * b) (a * c) = a * max b c
  proof: (monotone_id.const_mul' a).map_max.symm

中文:
定理 max_mul_mul_left
  条件: (a b c : α)
  结论: max (a * b) (a * c) = a * max b c
  证明: (monotone_id.const_mul' a).map_max.symm

Depends on / 依赖: const_mul, map_max, map_max.symm, monotone_id, monotone_id.const_mul
-/
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm

end Left

section Right

variable [MulRightMono α]

@[to_additive]
/--
theorem `min_mul_mul_right` / 定理 `min_mul_mul_right`

English:
theorem min_mul_mul_right
  given: (a b c : α)
  statement: min (a * c) (b * c) = min a b * c
  proof: (monotone_id.mul_const' c).map_min.symm

@[to_additive]

中文:
定理 min_mul_mul_right
  条件: (a b c : α)
  结论: min (a * c) (b * c) = min a b * c
  证明: (monotone_id.mul_const' c).map_min.symm

@[to_additive]

Depends on / 依赖: map_min, map_min.symm, monotone_id, monotone_id.mul_const, mul_const
-/
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm

@[to_additive]
/--
theorem `max_mul_mul_right` / 定理 `max_mul_mul_right`

English:
theorem max_mul_mul_right
  given: (a b c : α)
  statement: max (a * c) (b * c) = max a b * c
  proof: (monotone_id.mul_const' c).map_max.symm

中文:
定理 max_mul_mul_right
  条件: (a b c : α)
  结论: max (a * c) (b * c) = max a b * c
  证明: (monotone_id.mul_const' c).map_max.symm

Depends on / 依赖: map_max, map_max.symm, monotone_id, monotone_id.mul_const, mul_const
-/
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

@[to_additive]
/--
theorem `lt_or_lt_of_mul_lt_mul` / 定理 `lt_or_lt_of_mul_lt_mul`

English:
theorem lt_or_lt_of_mul_lt_mul
  given: [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α}
  proof: by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

@[to_additive]

中文:
定理 lt_or_lt_of_mul_lt_mul
  条件: [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α}
  证明: by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

@[to_additive]

Depends on / 依赖: contrapose, mul_le_mul
-/
theorem lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

@[to_additive]
/--
theorem `le_or_lt_of_mul_le_mul` / 定理 `le_or_lt_of_mul_le_mul`

English:
theorem le_or_lt_of_mul_le_mul
  given: [MulLeftMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α}
  proof: by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2

@[to_additive]

中文:
定理 le_or_lt_of_mul_le_mul
  条件: [MulLeftMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α}
  证明: by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2

@[to_additive]

Depends on / 依赖: contrapose, mul_lt_mul_of_lt_of_le
-/
theorem le_or_lt_of_mul_le_mul [MulLeftMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ <= a₂ * b₂ -> a₁ <= a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2

@[to_additive]
/--
theorem `lt_or_le_of_mul_le_mul` / 定理 `lt_or_le_of_mul_le_mul`

English:
theorem lt_or_le_of_mul_le_mul
  given: [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α}
  proof: by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

@[to_additive]

中文:
定理 lt_or_le_of_mul_le_mul
  条件: [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α}
  证明: by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

@[to_additive]

Depends on / 依赖: contrapose, mul_lt_mul_of_le_of_lt
-/
theorem lt_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ <= a₂ * b₂ -> a₁ < a₂ ∨ b₁ <= b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

@[to_additive]
/--
theorem `le_or_le_of_mul_le_mul` / 定理 `le_or_le_of_mul_le_mul`

English:
theorem le_or_le_of_mul_le_mul
  given: [MulLeftStrictMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α}
  proof: by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2

@[to_additive]

中文:
定理 le_or_le_of_mul_le_mul
  条件: [MulLeftStrictMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α}
  证明: by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2

@[to_additive]

Depends on / 依赖: contrapose, mul_lt_mul_of_lt_of_lt
-/
theorem le_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ <= a₂ * b₂ -> a₁ <= a₂ ∨ b₁ <= b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2

@[to_additive]
/--
theorem `mul_lt_mul_iff_of_le_of_le` / 定理 `mul_lt_mul_iff_of_le_of_le`

English:
theorem mul_lt_mul_iff_of_le_of_le
  statement: [MulLeftMono α]
  proof: by
  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
  rcases h with ha' | hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

中文:
定理 mul_lt_mul_iff_of_le_of_le
  结论: [MulLeftMono α]
  证明: by
  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
  rcases h with ha' | hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

Depends on / 依赖: lt_or_lt_of_mul_lt_mul, mul_lt_mul_of_le_of_lt, mul_lt_mul_of_lt_of_le
-/
theorem mul_lt_mul_iff_of_le_of_le [MulLeftMono α]
    [MulRightMono α] [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ <= a₂)
    (hb : b₁ <= b₂) : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ := by
  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
  rcases h with ha' | hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

end Mul

variable [MulOneClass α]

@[to_additive]
/--
theorem `min_le_mul_of_one_le_right` / 定理 `min_le_mul_of_one_le_right`

English:
theorem min_le_mul_of_one_le_right
  given: [MulLeftMono α] {a b : α} (hb : 1 <= b)
  proof: min_le_iff.2 Or.inl le_mul_of_one_le_right' hb

@[to_additive]

中文:
定理 min_le_mul_of_one_le_right
  条件: [MulLeftMono α] {a b : α} (hb : 1 <= b)
  证明: min_le_iff.2 Or.inl le_mul_of_one_le_right' hb

@[to_additive]

Depends on / 依赖: Or.inl, le_mul_of_one_le_right, min_le_iff
-/
theorem min_le_mul_of_one_le_right [MulLeftMono α] {a b : α} (hb : 1 <= b) :
    min a b <= a * b :=
min_le_iff.2 Or.inl le_mul_of_one_le_right' hb

@[to_additive]
/--
theorem `min_le_mul_of_one_le_left` / 定理 `min_le_mul_of_one_le_left`

English:
theorem min_le_mul_of_one_le_left
  given: [MulRightMono α] {a b : α} (ha : 1 <= a)
  proof: min_le_iff.2 Or.inr le_mul_of_one_le_left' ha

@[to_additive]

中文:
定理 min_le_mul_of_one_le_left
  条件: [MulRightMono α] {a b : α} (ha : 1 <= a)
  证明: min_le_iff.2 Or.inr le_mul_of_one_le_left' ha

@[to_additive]

Depends on / 依赖: Or.inr, le_mul_of_one_le_left, min_le_iff
-/
theorem min_le_mul_of_one_le_left [MulRightMono α] {a b : α} (ha : 1 <= a) :
    min a b <= a * b :=
min_le_iff.2 Or.inr le_mul_of_one_le_left' ha

@[to_additive]
/--
theorem `max_le_mul_of_one_le` / 定理 `max_le_mul_of_one_le`

English:
theorem max_le_mul_of_one_le
  given: [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b)
  proof: max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

中文:
定理 max_le_mul_of_one_le
  条件: [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b)
  证明: max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

Depends on / 依赖: le_mul_of_one_le_left, le_mul_of_one_le_right, max_le_iff
-/
theorem max_le_mul_of_one_le [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b) :
    max a b <= a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe
