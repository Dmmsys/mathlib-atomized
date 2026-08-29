/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
module

public meta import Mathlib.Data.Ineq
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Ineq
public meta import Mathlib.Tactic.ToAdditive

/-!
# Lemmas for the `linear_combination` tactic

These should not be used directly in user code.
-/

public meta section

open Lean

namespace Mathlib.Tactic.LinearCombination

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}
variable {K : Type*} {t s : K}


/--
theorem `add_eq_eq` / 定理 `add_eq_eq`

English:
theorem add_eq_eq
  given: [Add α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂)
  statement: a₁ + a₂ = b₁ + b₂
  proof: p₁ ▸ p₂ ▸ rfl

中文:
定理 add_eq_eq
  条件: [Add α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂)
  结论: a₁ + a₂ = b₁ + b₂
  证明: p₁ ▸ p₂ ▸ rfl
-/
theorem add_eq_eq [Add α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

/--
theorem `add_le_eq` / 定理 `add_le_eq`

English:
theorem add_le_eq
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: p₂ ▸ add_le_add_left p₁ b₂

中文:
定理 add_le_eq
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  证明: p₂ ▸ add_le_add_left p₁ b₂

Depends on / 依赖: add_le_add_left
-/
theorem add_le_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (p₁ : (a₁ : α) <= b₁) (p₂ : a₂ = b₂) : a₁ + a₂ <= b₁ + b₂ :=
  p₂ ▸ add_le_add_left p₁ b₂

/--
theorem `add_eq_le` / 定理 `add_eq_le`

English:
theorem add_eq_le
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: p₁ ▸ add_le_add_right p₂ b₁

中文:
定理 add_eq_le
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  证明: p₁ ▸ add_le_add_right p₂ b₁

Depends on / 依赖: add_le_add_right
-/
theorem add_eq_le [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (p₁ : (a₁ : α) = b₁) (p₂ : a₂ <= b₂) : a₁ + a₂ <= b₁ + b₂ :=
  p₁ ▸ add_le_add_right p₂ b₁

/--
theorem `add_lt_eq` / 定理 `add_lt_eq`

English:
theorem add_lt_eq
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: p₂ ▸ add_lt_add_left p₁ b₂

中文:
定理 add_lt_eq
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: p₂ ▸ add_lt_add_left p₁ b₂

Depends on / 依赖: add_lt_add_left
-/
theorem add_lt_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p₁ : (a₁ : α) < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₂ ▸ add_lt_add_left p₁ b₂

/--
theorem `add_eq_lt` / 定理 `add_eq_lt`

English:
theorem add_eq_lt
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] {a₁ b₁ a₂ b₂ : α}
  proof: p₁ ▸ add_lt_add_right p₂ b₁

中文:
定理 add_eq_lt
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] {a₁ b₁ a₂ b₂ : α}
  证明: p₁ ▸ add_lt_add_right p₂ b₁

Depends on / 依赖: add_lt_add_right
-/
theorem add_eq_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] {a₁ b₁ a₂ b₂ : α}
    (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₁ ▸ add_lt_add_right p₂ b₁


/--
theorem `mul_eq_const` / 定理 `mul_eq_const`

English:
theorem mul_eq_const
  given: [Mul α] (p : a = b) (c : α)
  statement: a * c = b * c
  proof: p ▸ rfl

中文:
定理 mul_eq_const
  条件: [Mul α] (p : a = b) (c : α)
  结论: a * c = b * c
  证明: p ▸ rfl
-/
theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl

/--
theorem `mul_le_const` / 定理 `mul_le_const`

English:
theorem mul_le_const
  statement: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  proof: mul_le_mul_of_nonneg_right p ha

中文:
定理 mul_le_const
  结论: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  证明: mul_le_mul_of_nonneg_right p ha

Depends on / 依赖: mul_le_mul_of_nonneg_right
-/
theorem mul_le_const [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b <= c) {a : α} (ha : 0 <= a) :
    b * a <= c * a :=
  mul_le_mul_of_nonneg_right p ha

/--
theorem `mul_lt_const` / 定理 `mul_lt_const`

English:
theorem mul_lt_const
  statement: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
  proof: mul_lt_mul_of_pos_right p ha

中文:
定理 mul_lt_const
  结论: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
  证明: mul_lt_mul_of_pos_right p ha

Depends on / 依赖: mul_lt_mul_of_pos_right
-/
theorem mul_lt_const [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 < a) :
    b * a < c * a :=
  mul_lt_mul_of_pos_right p ha

/--
theorem `mul_lt_const_weak` / 定理 `mul_lt_const_weak`

English:
theorem mul_lt_const_weak
  statement: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  proof: mul_le_mul_of_nonneg_right p.le ha

中文:
定理 mul_lt_const_weak
  结论: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  证明: mul_le_mul_of_nonneg_right p.le ha

Depends on / 依赖: mul_le_mul_of_nonneg_right, p.le
-/
theorem mul_lt_const_weak [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b < c) {a : α} (ha : 0 <= a) :
    b * a <= c * a :=
  mul_le_mul_of_nonneg_right p.le ha

/--
theorem `mul_const_eq` / 定理 `mul_const_eq`

English:
theorem mul_const_eq
  given: [Mul α] (p : b = c) (a : α)
  statement: a * b = a * c
  proof: p ▸ rfl

中文:
定理 mul_const_eq
  条件: [Mul α] (p : b = c) (a : α)
  结论: a * b = a * c
  证明: p ▸ rfl
-/
theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl

/--
theorem `mul_const_le` / 定理 `mul_const_le`

English:
theorem mul_const_le
  statement: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  proof: mul_le_mul_of_nonneg_left p ha

中文:
定理 mul_const_le
  结论: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  证明: mul_le_mul_of_nonneg_left p ha

Depends on / 依赖: mul_le_mul_of_nonneg_left
-/
theorem mul_const_le [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b <= c) {a : α} (ha : 0 <= a) :
    a * b <= a * c :=
  mul_le_mul_of_nonneg_left p ha

/--
theorem `mul_const_lt` / 定理 `mul_const_lt`

English:
theorem mul_const_lt
  statement: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
  proof: mul_lt_mul_of_pos_left p ha

中文:
定理 mul_const_lt
  结论: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
  证明: mul_lt_mul_of_pos_left p ha

Depends on / 依赖: mul_lt_mul_of_pos_left
-/
theorem mul_const_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 < a) :
    a * b < a * c :=
  mul_lt_mul_of_pos_left p ha

/--
theorem `mul_const_lt_weak` / 定理 `mul_const_lt_weak`

English:
theorem mul_const_lt_weak
  statement: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  proof: mul_le_mul_of_nonneg_left p.le ha

中文:
定理 mul_const_lt_weak
  结论: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  证明: mul_le_mul_of_nonneg_left p.le ha

Depends on / 依赖: mul_le_mul_of_nonneg_left, p.le
-/
theorem mul_const_lt_weak [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b < c) {a : α} (ha : 0 <= a) :
    a * b <= a * c :=
  mul_le_mul_of_nonneg_left p.le ha


/--
theorem `smul_eq_const` / 定理 `smul_eq_const`

English:
theorem smul_eq_const
  given: [SMul K α] (p : t = s) (c : α)
  statement: t • c = s • c
  proof: p ▸ rfl

中文:
定理 smul_eq_const
  条件: [SMul K α] (p : t = s) (c : α)
  结论: t • c = s • c
  证明: p ▸ rfl
-/
theorem smul_eq_const [SMul K α] (p : t = s) (c : α) : t • c = s • c := p ▸ rfl

/--
theorem `smul_le_const` / 定理 `smul_le_const`

English:
theorem smul_le_const
  statement: [Ring K] [PartialOrder K] [IsOrderedRing K]
  proof: smul_le_smul_of_nonneg_right p ha

中文:
定理 smul_le_const
  结论: [Ring K] [PartialOrder K] [IsOrderedRing K]
  证明: smul_le_smul_of_nonneg_right p ha

Depends on / 依赖: smul_le_smul_of_nonneg_right
-/
theorem smul_le_const [Ring K] [PartialOrder K] [IsOrderedRing K]
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α]
    [IsOrderedModule K α] (p : t <= s) {a : α} (ha : 0 <= a) :
    t • a <= s • a :=
  smul_le_smul_of_nonneg_right p ha

/--
theorem `smul_lt_const` / 定理 `smul_lt_const`

English:
theorem smul_lt_const
  statement: [Ring K] [PartialOrder K] [IsOrderedRing K]
  proof: smul_lt_smul_of_pos_right p ha

中文:
定理 smul_lt_const
  结论: [Ring K] [PartialOrder K] [IsOrderedRing K]
  证明: smul_lt_smul_of_pos_right p ha

Depends on / 依赖: smul_lt_smul_of_pos_right
-/
theorem smul_lt_const [Ring K] [PartialOrder K] [IsOrderedRing K]
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α]
    [IsStrictOrderedModule K α] (p : t < s) {a : α} (ha : 0 < a) :
    t • a < s • a :=
  smul_lt_smul_of_pos_right p ha

/--
theorem `smul_lt_const_weak` / 定理 `smul_lt_const_weak`

English:
theorem smul_lt_const_weak
  statement: [Ring K] [PartialOrder K] [IsOrderedRing K]
  proof: smul_le_smul_of_nonneg_right p.le ha

中文:
定理 smul_lt_const_weak
  结论: [Ring K] [PartialOrder K] [IsOrderedRing K]
  证明: smul_le_smul_of_nonneg_right p.le ha

Depends on / 依赖: p.le, smul_le_smul_of_nonneg_right
-/
theorem smul_lt_const_weak [Ring K] [PartialOrder K] [IsOrderedRing K]
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α]
    [IsStrictOrderedModule K α] (p : t < s) {a : α} (ha : 0 <= a) :
    t • a <= s • a :=
  smul_le_smul_of_nonneg_right p.le ha

/--
theorem `smul_const_eq` / 定理 `smul_const_eq`

English:
theorem smul_const_eq
  given: [SMul K α] (p : b = c) (s : K)
  statement: s • b = s • c
  proof: p ▸ rfl

中文:
定理 smul_const_eq
  条件: [SMul K α] (p : b = c) (s : K)
  结论: s • b = s • c
  证明: p ▸ rfl
-/
theorem smul_const_eq [SMul K α] (p : b = c) (s : K) : s • b = s • c := p ▸ rfl

/--
theorem `smul_const_le` / 定理 `smul_const_le`

English:
theorem smul_const_le
  statement: [Semiring K] [PartialOrder K]
  proof: smul_le_smul_of_nonneg_left p hs

中文:
定理 smul_const_le
  结论: [Semiring K] [PartialOrder K]
  证明: smul_le_smul_of_nonneg_left p hs

Depends on / 依赖: smul_le_smul_of_nonneg_left
-/
theorem smul_const_le [Semiring K] [PartialOrder K]
    [AddCommMonoid α] [PartialOrder α] [Module K α]
    [PosSMulMono K α] (p : b <= c) {s : K} (hs : 0 <= s) :
    s • b <= s • c :=
  smul_le_smul_of_nonneg_left p hs

/--
theorem `smul_const_lt` / 定理 `smul_const_lt`

English:
theorem smul_const_lt
  statement: [Semiring K] [PartialOrder K]
  proof: smul_lt_smul_of_pos_left p hs

中文:
定理 smul_const_lt
  结论: [Semiring K] [PartialOrder K]
  证明: smul_lt_smul_of_pos_left p hs

Depends on / 依赖: smul_lt_smul_of_pos_left
-/
theorem smul_const_lt [Semiring K] [PartialOrder K]
    [AddCommMonoid α] [PartialOrder α] [Module K α]
    [PosSMulStrictMono K α] (p : b < c) {s : K} (hs : 0 < s) :
    s • b < s • c :=
  smul_lt_smul_of_pos_left p hs

/--
theorem `smul_const_lt_weak` / 定理 `smul_const_lt_weak`

English:
theorem smul_const_lt_weak
  statement: [Semiring K] [PartialOrder K]
  proof: smul_le_smul_of_nonneg_left p.le hs

中文:
定理 smul_const_lt_weak
  结论: [Semiring K] [PartialOrder K]
  证明: smul_le_smul_of_nonneg_left p.le hs

Depends on / 依赖: p.le, smul_le_smul_of_nonneg_left
-/
theorem smul_const_lt_weak [Semiring K] [PartialOrder K]
    [AddCommMonoid α] [PartialOrder α] [Module K α]
    [PosSMulMono K α] (p : b < c) {s : K} (hs : 0 <= s) :
    s • b <= s • c :=
  smul_le_smul_of_nonneg_left p.le hs


/--
theorem `div_eq_const` / 定理 `div_eq_const`

English:
theorem div_eq_const
  given: [Div α] (p : a = b) (c : α)
  statement: a / c = b / c
  proof: p ▸ rfl

中文:
定理 div_eq_const
  条件: [Div α] (p : a = b) (c : α)
  结论: a / c = b / c
  证明: p ▸ rfl
-/
theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

/--
theorem `div_le_const` / 定理 `div_le_const`

English:
theorem div_le_const
  statement: [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: div_le_div_of_nonneg_right p ha

中文:
定理 div_le_const
  结论: [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  证明: div_le_div_of_nonneg_right p ha

Depends on / 依赖: div_le_div_of_nonneg_right
-/
theorem div_le_const [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (p : b <= c) {a : α} (ha : 0 <= a) : b / a <= c / a :=
  div_le_div_of_nonneg_right p ha

/--
theorem `div_lt_const` / 定理 `div_lt_const`

English:
theorem div_lt_const
  statement: [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: div_lt_div_of_pos_right p ha

中文:
定理 div_lt_const
  结论: [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  证明: div_lt_div_of_pos_right p ha

Depends on / 依赖: div_lt_div_of_pos_right
-/
theorem div_lt_const [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 < a) : b / a < c / a :=
  div_lt_div_of_pos_right p ha

/--
theorem `div_lt_const_weak` / 定理 `div_lt_const_weak`

English:
theorem div_lt_const_weak
  statement: [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: div_le_div_of_nonneg_right p.le ha

中文:
定理 div_lt_const_weak
  结论: [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  证明: div_le_div_of_nonneg_right p.le ha

Depends on / 依赖: div_le_div_of_nonneg_right, p.le
-/
theorem div_lt_const_weak [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 <= a) :
    b / a <= c / a :=
  div_le_div_of_nonneg_right p.le ha


/--
theorem `eq_of_eq` / 定理 `eq_of_eq`

English:
theorem eq_of_eq
  given: [Add α] [IsRightCancelAdd α] (p : (a : α) = b) (H : a' + b = b' + a)
  proof: by
  rw [p] at H
  exact add_right_cancel H

中文:
定理 eq_of_eq
  条件: [Add α] [IsRightCancelAdd α] (p : (a : α) = b) (H : a' + b = b' + a)
  证明: by
  rw [p] at H
  exact add_right_cancel H

Depends on / 依赖: add_right_cancel
-/
theorem eq_of_eq [Add α] [IsRightCancelAdd α] (p : (a : α) = b) (H : a' + b = b' + a) :
    a' = b' := by
  rw [p] at H
  exact add_right_cancel H

/--
theorem `le_of_le` / 定理 `le_of_le`

English:
theorem le_of_le
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  grw [← add_le_add_iff_right b, H, p]

中文:
定理 le_of_le
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: by
  grw [← add_le_add_iff_right b, H, p]

Depends on / 依赖: add_le_add_iff_right
-/
theorem le_of_le [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) <= b) (H : a' + b <= b' + a) :
    a' <= b' := by
  grw [← add_le_add_iff_right b, H, p]

/--
theorem `le_of_eq` / 定理 `le_of_eq`

English:
theorem le_of_eq
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  rwa [p, add_le_add_iff_right] at H

中文:
定理 le_of_eq
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: by
  rwa [p, add_le_add_iff_right] at H

Depends on / 依赖: add_le_add_iff_right
-/
theorem le_of_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) = b) (H : a' + b <= b' + a) :
    a' <= b' := by
  rwa [p, add_le_add_iff_right] at H

/--
theorem `le_of_lt` / 定理 `le_of_lt`

English:
theorem le_of_lt
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: le_of_le p.le H

中文:
定理 le_of_lt
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: le_of_le p.le H

Depends on / 依赖: le_of_le, p.le
-/
theorem le_of_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) < b) (H : a' + b <= b' + a) :
    a' <= b' :=
  le_of_le p.le H

/--
theorem `lt_of_le` / 定理 `lt_of_le`

English:
theorem lt_of_le
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  grw [p] at H; simpa using H

中文:
定理 lt_of_le
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: by
  grw [p] at H; simpa using H
-/
theorem lt_of_le [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) <= b) (H : a' + b < b' + a) :
    a' < b' := by
  grw [p] at H; simpa using H

/--
theorem `lt_of_eq` / 定理 `lt_of_eq`

English:
theorem lt_of_eq
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  rwa [p, add_lt_add_iff_right] at H

中文:
定理 lt_of_eq
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: by
  rwa [p, add_lt_add_iff_right] at H

Depends on / 依赖: add_lt_add_iff_right
-/
theorem lt_of_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) = b) (H : a' + b < b' + a) :
    a' < b' := by
  rwa [p, add_lt_add_iff_right] at H

/--
theorem `lt_of_lt` / 定理 `lt_of_lt`

English:
theorem lt_of_lt
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  grw [← add_lt_add_iff_right b, H]
  gcongr

alias ⟨eq_rearrange, _⟩ := sub_eq_zero

中文:
定理 lt_of_lt
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  证明: by
  grw [← add_lt_add_iff_right b, H]
  gcongr

alias ⟨eq_rearrange, _⟩ := sub_eq_zero

Depends on / 依赖: add_lt_add_iff_right
-/
theorem lt_of_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) < b) (H : a' + b <= b' + a) :
    a' < b' := by
  grw [← add_lt_add_iff_right b, H]
  gcongr

alias ⟨eq_rearrange, _⟩ := sub_eq_zero

/--
theorem `le_rearrange` / 定理 `le_rearrange`

English:
theorem le_rearrange
  statement: {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: sub_nonpos.mp h

中文:
定理 le_rearrange
  结论: {α : 类型} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  证明: sub_nonpos.mp h

Depends on / 依赖: sub_nonpos, sub_nonpos.mp
-/
theorem le_rearrange {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b : α} (h : a - b <= 0) : a <= b :=
  sub_nonpos.mp h

/--
theorem `lt_rearrange` / 定理 `lt_rearrange`

English:
theorem lt_rearrange
  statement: {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: sub_neg.mp h

中文:
定理 lt_rearrange
  结论: {α : 类型} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  证明: sub_neg.mp h

Depends on / 依赖: sub_neg, sub_neg.mp
-/
theorem lt_rearrange {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b : α} (h : a - b < 0) : a < b :=
  sub_neg.mp h

/--
theorem `eq_of_add_pow` / 定理 `eq_of_add_pow`

English:
theorem eq_of_add_pow
  statement: [Ring α] [NoZeroDivisors α] (n : Nat) (p : (a : α) = b)
  proof: by
  rw [← sub_eq_zero] at p ⊢; apply eq_zero_of_pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

中文:
定理 eq_of_add_pow
  结论: [Ring α] [NoZeroDivisors α] (n : 自然数) (p : (a : α) = b)
  证明: by
  rw [← sub_eq_zero] at p ⊢; apply eq_zero_of_pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

Depends on / 依赖: eq_zero_of_pow_eq_zero, sub_eq_zero
-/
theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : Nat) (p : (a : α) = b)
    (H : (a' - b') ^ n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply eq_zero_of_pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

end Tactic.LinearCombination

/-! ### Lookup functions for lemmas by operation and relation(s) -/

open Tactic.LinearCombination

namespace Ineq

/--
Definition of `addRelRelData` / `addRelRelData` 的定义

English:
definition addRelRelData
  signature: : Ineq -> Ineq -> Name

中文:
定义 addRelRelData
  签名: : Ineq -> Ineq -> Name
-/
def addRelRelData : Ineq -> Ineq -> Name
  | eq, eq => ``add_eq_eq
  | eq, le => ``add_eq_le
  | eq, lt => ``add_eq_lt
  | le, eq => ``add_le_eq
  | le, le => ``add_le_add
  | le, lt => ``add_lt_add_of_le_of_lt
  | lt, eq => ``add_lt_eq
  | lt, le => ``add_lt_add_of_lt_of_le
  | lt, lt => ``add_lt_add

/--
Inductive type `WithStrictness` / 归纳类型 `WithStrictness`

English:
inductive WithStrictness
  parameters: : Type
  constructors (3):
    - eq: Ineq.WithStrictness
    - le: Ineq.WithStrictness
    - lt: (strict : Bool) : Ineq.WithStrictness

中文:
归纳类型 WithStrictness
  参数: : Type
  构造子 (3 个):
    - eq: Ineq.WithStrictness
    - le: Ineq.WithStrictness
    - lt: (strict : 布尔) : Ineq.WithStrictness
-/
protected inductive WithStrictness : Type
  | eq : Ineq.WithStrictness
  | le : Ineq.WithStrictness
  | lt (strict : Bool) : Ineq.WithStrictness

/--
Definition of `mulRelConstData` / `mulRelConstData` 的定义

English:
definition mulRelConstData
  signature: : Ineq.WithStrictness -> Name

中文:
定义 mulRelConstData
  签名: : Ineq.WithStrictness -> Name
-/
def mulRelConstData : Ineq.WithStrictness -> Name
  | .eq => ``mul_eq_const
  | .le => ``mul_le_const
  | .lt true => ``mul_lt_const
  | .lt false => ``mul_lt_const_weak

/--
Definition of `mulConstRelData` / `mulConstRelData` 的定义

English:
definition mulConstRelData
  signature: : Ineq.WithStrictness -> Name

中文:
定义 mulConstRelData
  签名: : Ineq.WithStrictness -> Name
-/
def mulConstRelData : Ineq.WithStrictness -> Name
  | .eq => ``mul_const_eq
  | .le => ``mul_const_le
  | .lt true => ``mul_const_lt
  | .lt false => ``mul_const_lt_weak

/--
Definition of `smulRelConstData` / `smulRelConstData` 的定义

English:
definition smulRelConstData
  signature: : Ineq.WithStrictness -> Name

中文:
定义 smulRelConstData
  签名: : Ineq.WithStrictness -> Name
-/
def smulRelConstData : Ineq.WithStrictness -> Name
  | .eq => ``smul_eq_const
  | .le => ``smul_le_const
  | .lt true => ``smul_lt_const
  | .lt false => ``smul_lt_const_weak

/--
Definition of `smulConstRelData` / `smulConstRelData` 的定义

English:
definition smulConstRelData
  signature: : Ineq.WithStrictness -> Name

中文:
定义 smulConstRelData
  签名: : Ineq.WithStrictness -> Name
-/
def smulConstRelData : Ineq.WithStrictness -> Name
  | .eq => ``smul_const_eq
  | .le => ``smul_const_le
  | .lt true => ``smul_const_lt
  | .lt false => ``smul_const_lt_weak

/--
Definition of `divRelConstData` / `divRelConstData` 的定义

English:
definition divRelConstData
  signature: : Ineq.WithStrictness -> Name

中文:
定义 divRelConstData
  签名: : Ineq.WithStrictness -> Name
-/
def divRelConstData : Ineq.WithStrictness -> Name
  | .eq => ``div_eq_const
  | .le => ``div_le_const
  | .lt true => ``div_lt_const
  | .lt false => ``div_lt_const_weak

/--
Definition of `relImpRelData` / `relImpRelData` 的定义

English:
definition relImpRelData
  signature: : Ineq -> Ineq -> Option (Name × Ineq)

中文:
定义 relImpRelData
  签名: : Ineq -> Ineq -> Option (Name × Ineq)
-/
def relImpRelData : Ineq -> Ineq -> Option (Name × Ineq)
  | eq, eq => some (``eq_of_eq, eq)
  | eq, le => some (``Tactic.LinearCombination.le_of_eq, le)
  | eq, lt => some (``lt_of_eq, lt)
  | le, eq => none
  | le, le => some (``le_of_le, le)
  | le, lt => some (``lt_of_le, lt)
  | lt, eq => none
  | lt, le => some (``Tactic.LinearCombination.le_of_lt, le)
  | lt, lt => some (``lt_of_lt, le)

/--
Definition of `rearrangeData` / `rearrangeData` 的定义

English:
definition rearrangeData
  signature: : Ineq -> Name

中文:
定义 rearrangeData
  签名: : Ineq -> Name
-/
def rearrangeData : Ineq -> Name
  | eq => ``eq_rearrange
  | le => ``le_rearrange
  | lt => ``lt_rearrange

end Mathlib.Ineq
