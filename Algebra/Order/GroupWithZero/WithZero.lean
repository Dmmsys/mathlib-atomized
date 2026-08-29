/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
/-!

# Covariant instances on `WithZero`

Adding a zero to a type with a preorder and multiplication which satisfies some
axiom, gives us a new type which satisfies some variant of the axiom.

## Example

If `α` satisfies `b₁ < b₂ → a * b₁ < a * b₂` for all `a`,
then `WithZero α` satisfies `b₁ < b₂ → a * b₁ < a * b₂` for all `a > 0`,
which is `PosMulStrictMono (WithZero α)`.

## Application

The type `ℤᵐ⁰ := WithZero (Multiplicative ℤ)` is used a lot in mathlib's valuation
theory. These instances enable lemmas such as `mul_pos` to fire on `ℤᵐ⁰`.

-/

@[expose] public section

assert_not_exists Ring

-- this makes `mul_lt_mul_iff_right₀`, `mul_pos` etc. work on `ℤᵐ⁰`
instance {α : Type*} [Mul α] [Preorder α] [MulLeftStrictMono α] :
    PosMulStrictMono (WithZero α) where
  mul_lt_mul_of_pos_left
  | (x : α), hx, 0, (b : α), _ => by simpa only [mul_zero] using! WithZero.zero_lt_coe _
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

open Function in
instance {α : Type*} [Mul α] [Preorder α] [MulRightStrictMono α] :
    MulPosStrictMono (WithZero α) where
  mul_lt_mul_of_pos_right
  | (x : α), hx, 0, (b : α), _ => by simpa only [mul_zero] using! WithZero.zero_lt_coe _
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

instance {α : Type*} [Mul α] [Preorder α] [MulLeftMono α] :
    PosMulMono (WithZero α) where
  mul_le_mul_of_nonneg_left
  | 0, _, a, b, _ => by simp
  | (x : α), _, 0, _, _ => by simp
  | (x : α), _, (a : α), 0, h => by simp at h
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

-- This makes `lt_mul_of_le_of_one_lt'` work on `ℤᵐ⁰`
open Function in
instance {α : Type*} [Mul α] [Preorder α] [MulRightMono α] :
    MulPosMono (WithZero α) where
  mul_le_mul_of_nonneg_right
  | 0, _, a, b, _ => by simp
  | (x : α), _, 0, _, _ => by simp
  | (x : α), _, (a : α), 0, h => by simp at h
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

section Units

variable {α : Type*} [LinearOrderedCommGroupWithZero α]

open WithZero

/--
lemma `WithZero.withZeroUnitsEquiv_strictMono` / 引理 `WithZero.withZeroUnitsEquiv_strictMono`

English:
lemma WithZero.withZeroUnitsEquiv_strictMono
  proof: by
  intro a b
  cases a <;> cases b <;>
  simp

中文:
引理 WithZero.withZeroUnitsEquiv_strictMono
  证明: by
  intro a b
  cases a <;> cases b <;>
  simp
-/
lemma WithZero.withZeroUnitsEquiv_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)) := by
  intro a b
  cases a <;> cases b <;>
  simp

/-- Given any linearly ordered commutative group with zero `α`, this is the order isomorphism
between `WithZero αˣ` with `α`. -/
@[simps!]
/--
Definition of `OrderIso.withZeroUnits` / `OrderIso.withZeroUnits` 的定义

English:
definition OrderIso.withZeroUnits
  signature: : WithZero αˣ ≃o α where
  body: withZeroUnitsEquiv
  map_rel_iff' := WithZero.withZeroUnitsEquiv_strictMono.le_iff_le

中文:
定义 OrderIso.withZeroUnits
  签名: : WithZero αˣ ≃o α where
  定义体: withZeroUnitsEquiv
  map_rel_iff' := WithZero.withZeroUnitsEquiv_strictMono.le_iff_le

Depends on / 依赖: withZeroUnitsEquiv
-/
def OrderIso.withZeroUnits : WithZero αˣ ≃o α where
  __ := withZeroUnitsEquiv
  map_rel_iff' := WithZero.withZeroUnitsEquiv_strictMono.le_iff_le

/--
lemma `WithZero.withZeroUnitsEquiv_symm_strictMono` / 引理 `WithZero.withZeroUnitsEquiv_symm_strictMono`

English:
lemma WithZero.withZeroUnitsEquiv_symm_strictMono
  proof: OrderIso.withZeroUnits.symm.strictMono

中文:
引理 WithZero.withZeroUnitsEquiv_symm_strictMono
  证明: OrderIso.withZeroUnits.symm.strictMono
-/
lemma WithZero.withZeroUnitsEquiv_symm_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)).symm :=
  OrderIso.withZeroUnits.symm.strictMono

end Units
