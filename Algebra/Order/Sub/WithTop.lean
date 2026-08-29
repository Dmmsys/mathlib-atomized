/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Lemma about subtraction in ordered monoids with a top element adjoined.

This file introduces a subtraction on `WithTop α` when `α` has a subtraction and a bottom element,
given by `x - ⊤ = ⊥` and `⊤ - x = ⊤`. This will be instantiated mostly for `ℕ∞` and `ℝ≥0∞`, where
the bottom element is zero.

Note that there is another subtraction on objects of the form `WithTop α` in the file
`Mathlib/Algebra/Order/AddGroupWithTop.lean`, setting `-⊤ = ⊤` as this corresponds to the
additivization of the usual convention `0⁻¹ = 0` and is relevant in valuation theory. Since that
other instance is only registered for `AddCommGroup α` (which doesn't have a bottom
element, unless the group is trivial), this shouldn't create diamonds.
-/

@[expose] public section

variable {α β : Type*}

namespace WithTop

section

variable [Sub α] [Bot α]

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: : forall _ _ : WithTop α, WithTop α

中文:
定义 sub
  签名: : 对任意 _ _ : WithTop α, WithTop α
-/
protected def sub : forall _ _ : WithTop α, WithTop α
  | _, ⊤ => (⊥ : α)
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (WithTop α)
  body: ⟨WithTop.sub⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 减法 (WithTop α)
  定义体: ⟨WithTop.sub⟩

@[simp, norm_cast]

Depends on / 依赖: WithTop, WithTop.sub
-/
instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: {a b : α}
  statement: (↑(a - b) : WithTop α) = ↑a - ↑b
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: {a b : α}
  结论: (↑(a - b) : WithTop α) = ↑a - ↑b
  证明: rfl

@[simp]
-/
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl

@[simp]
/--
theorem `top_sub_coe` / 定理 `top_sub_coe`

English:
theorem top_sub_coe
  given: {a : α}
  statement: (⊤ : WithTop α) - a = ⊤
  proof: rfl

@[simp]

中文:
定理 top_sub_coe
  条件: {a : α}
  结论: (⊤ : WithTop α) - a = ⊤
  证明: rfl

@[simp]
-/
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl

@[simp]
/--
theorem `sub_top` / 定理 `sub_top`

English:
theorem sub_top
  given: {a : WithTop α}
  statement: a - ⊤ = (⊥ : α)
  proof: by cases a <;> rfl

中文:
定理 sub_top
  条件: {a : WithTop α}
  结论: a - ⊤ = (⊥ : α)
  证明: by cases a <;> rfl
-/
theorem sub_top {a : WithTop α} : a - ⊤ = (⊥ : α) := by cases a <;> rfl

/--
theorem `sub_eq_top_iff` / 定理 `sub_eq_top_iff`

English:
theorem sub_eq_top_iff
  given: {a b : WithTop α}
  statement: a - b = ⊤ ↔ a = ⊤ ∧ b != ⊤
  proof: by
  induction a <;> induction b <;>
    simp only [← coe_sub, coe_ne_top, sub_top, top_sub_coe, false_and, Ne, not_true_eq_false,
      not_false_eq_true, and_false, and_self]

中文:
定理 sub_eq_top_iff
  条件: {a b : WithTop α}
  结论: a - b = ⊤ ↔ a = ⊤ ∧ b != ⊤
  证明: by
  induction a <;> induction b <;>
    simp only [← coe_sub, coe_ne_top, sub_top, top_sub_coe, false_and, Ne, not_true_eq_false,
      not_false_eq_true, and_false, and_self]
-/
@[simp] theorem sub_eq_top_iff {a b : WithTop α} : a - b = ⊤ ↔ a = ⊤ ∧ b != ⊤ := by
  induction a <;> induction b <;>
    simp only [← coe_sub, coe_ne_top, sub_top, top_sub_coe, false_and, Ne, not_true_eq_false,
      not_false_eq_true, and_false, and_self]

/--
lemma `sub_ne_top_iff` / 引理 `sub_ne_top_iff`

English:
lemma sub_ne_top_iff
  given: {a b : WithTop α}
  statement: a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤
  proof: by simp [or_iff_not_imp_left]

protected

中文:
引理 sub_ne_top_iff
  条件: {a b : WithTop α}
  结论: a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤
  证明: by simp [or_iff_not_imp_left]

protected

Depends on / 依赖: or_iff_not_imp_left
-/
lemma sub_ne_top_iff {a b : WithTop α} : a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤ := by simp [or_iff_not_imp_left]

protected
/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: [Sub β] [Bot β] {f : α -> β} (h : forall x y, f (x - y) = f x - f y) (h₀ : f ⊥ = ⊥)

中文:
定理 map_sub
  条件: [减法 β] [底元素 β] {f : α -> β} (h : 对任意 x y, f (x - y) = f x - f y) (h₀ : f ⊥ = ⊥)
-/
theorem map_sub [Sub β] [Bot β] {f : α -> β} (h : forall x y, f (x - y) = f x - f y) (h₀ : f ⊥ = ⊥) :
    forall x y : WithTop α, (x - y).map f = x.map f - y.map f
  | _, ⊤ => by simp only [sub_top, map_coe, h₀, map_top]
  | ⊤, (x : α) => rfl
  | (x : α), (y : α) => by simp only [← coe_sub, map_coe, h]

end

variable [Add α] [LE α] [OrderBot α] [Sub α] [OrderedSub α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderedSub (WithTop α)
  body: by
  constructor
  rintro x y z
  cases y
  · cases z <;> simp
  cases x
  · simp
  cases z
  · simp
  norm_cast
  exact tsub_le_iff_right

中文:
实例 :
  签名: OrderedSub (WithTop α)
  定义体: by
  constructor
  rintro x y z
  cases y
  · cases z <;> simp
  cases x
  · simp
  cases z
  · simp
  norm_cast
  exact tsub_le_iff_right

Depends on / 依赖: tsub_le_iff_right
-/
instance : OrderedSub (WithTop α) := by
  constructor
  rintro x y z
  cases y
  · cases z <;> simp
  cases x
  · simp
  cases z
  · simp
  norm_cast
  exact tsub_le_iff_right

end WithTop
