/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Ore Localization over nonZeroDivisors in monoids with zeros.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

/--
theorem `nontrivial_of_nonZeroDivisorsLeft` / 定理 `nontrivial_of_nonZeroDivisorsLeft`

English:
theorem nontrivial_of_nonZeroDivisorsLeft
  given: [Nontrivial R] (hS : S <= nonZeroDivisorsLeft R)
  proof: nontrivial_iff.mpr (fun e => one_ne_zero <| hS e 1 (zero_mul _))

中文:
定理 nontrivial_of_nonZeroDivisorsLeft
  条件: [非平凡 R] (hS : S <= nonZeroDivisorsLeft R)
  证明: nontrivial_iff.mpr (fun e => one_ne_zero <| hS e 1 (zero_mul _))

Depends on / 依赖: nontrivial_iff, nontrivial_iff.mpr, one_ne_zero, zero_mul
-/
theorem nontrivial_of_nonZeroDivisorsLeft [Nontrivial R] (hS : S <= nonZeroDivisorsLeft R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e => one_ne_zero <| hS e 1 (zero_mul _))

/--
theorem `nontrivial_of_nonZeroDivisorsRight` / 定理 `nontrivial_of_nonZeroDivisorsRight`

English:
theorem nontrivial_of_nonZeroDivisorsRight
  given: [Nontrivial R] (hS : S <= nonZeroDivisorsRight R)
  proof: nontrivial_iff.mpr (fun e => one_ne_zero <| hS e 1 (mul_zero _))

中文:
定理 nontrivial_of_nonZeroDivisorsRight
  条件: [非平凡 R] (hS : S <= nonZeroDivisorsRight R)
  证明: nontrivial_iff.mpr (fun e => one_ne_zero <| hS e 1 (mul_zero _))

Depends on / 依赖: mul_zero, nontrivial_iff, nontrivial_iff.mpr, one_ne_zero
-/
theorem nontrivial_of_nonZeroDivisorsRight [Nontrivial R] (hS : S <= nonZeroDivisorsRight R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e => one_ne_zero <| hS e 1 (mul_zero _))

/--
theorem `nontrivial_of_nonZeroDivisors` / 定理 `nontrivial_of_nonZeroDivisors`

English:
theorem nontrivial_of_nonZeroDivisors
  given: [Nontrivial R] (hS : S <= R⁰)
  proof: nontrivial_of_nonZeroDivisorsLeft (hS.trans inf_le_left)

中文:
定理 nontrivial_of_nonZeroDivisors
  条件: [非平凡 R] (hS : S <= R⁰)
  证明: nontrivial_of_nonZeroDivisorsLeft (hS.trans inf_le_left)

Depends on / 依赖: hS.trans, inf_le_left, nontrivial_of_nonZeroDivisorsLeft
-/
theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S <= R⁰) :
    Nontrivial R[S⁻¹] :=
  nontrivial_of_nonZeroDivisorsLeft (hS.trans inf_le_left)

variable [Nontrivial R] [OreSet R⁰]

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: : Nontrivial R[R⁰⁻¹]
  body: nontrivial_of_nonZeroDivisors (refl R⁰)

中文:
实例 nontrivial
  签名: : 非平凡 R[R⁰⁻¹]
  定义体: nontrivial_of_nonZeroDivisors (refl R⁰)

Depends on / 依赖: nontrivial_of_nonZeroDivisors
-/
instance nontrivial : Nontrivial R[R⁰⁻¹] :=
  nontrivial_of_nonZeroDivisors (refl R⁰)

variable [NoZeroDivisors R]

open scoped Classical in
/-- The inversion of Ore fractions for a ring without zero divisors, satisfying `0⁻¹ = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`. -/
@[irreducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inv
  body: liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero, smul_eq_mul]
          apply OreLocalization.expand)

中文:
定义 noncomputable
  签名: def inv
  定义体: liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero, smul_eq_mul]
          apply OreLocalization.expand)
-/
protected noncomputable def inv : R[R⁰⁻¹] -> R[R⁰⁻¹] :=
  liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero, smul_eq_mul]
          apply OreLocalization.expand)

/--
Instance `inv'` / 实例 `inv'`

English:
instance inv'
  signature: : Inv R[R⁰⁻¹]
  body: ⟨OreLocalization.inv⟩

中文:
实例 inv'
  签名: : 取逆 R[R⁰⁻¹]
  定义体: ⟨OreLocalization.inv⟩

Depends on / 依赖: OreLocalization, OreLocalization.inv
-/
noncomputable instance inv' : Inv R[R⁰⁻¹] :=
  ⟨OreLocalization.inv⟩

open scoped Classical in
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: {r : R} {s : R⁰}
  proof: by
  with_unfolding_all rfl

中文:
定理 inv_def
  条件: {r : R} {s : R⁰}
  证明: by
  with_unfolding_all rfl
-/
protected theorem inv_def {r : R} {s : R⁰} :
    (r /ₒ s)⁻¹ =
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ := by
  with_unfolding_all rfl

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (x : R[R⁰⁻¹]) (h : x != 0)
  statement: x * x⁻¹ = 1
  proof: by
  induction x with | _ r s
  rw [OreLocalization.inv_def]; rw [OreLocalization.one_def]
  have hr : r != 0 := by
    rintro rfl
    simp at h
  simp only [hr]
  with_unfolding_all apply OreLocalization.mul_inv ⟨r, _⟩

中文:
定理 mul_inv_cancel
  条件: (x : R[R⁰⁻¹]) (h : x != 0)
  结论: x * x⁻¹ = 1
  证明: by
  induction x with | _ r s
  rw [OreLocalization.inv_def]; rw [OreLocalization.one_def]
  have hr : r != 0 := by
    rintro rfl
    simp at h
  simp only [hr]
  with_unfolding_all apply OreLocalization.mul_inv ⟨r, _⟩
-/
protected theorem mul_inv_cancel (x : R[R⁰⁻¹]) (h : x != 0) : x * x⁻¹ = 1 := by
  induction x with | _ r s
  rw [OreLocalization.inv_def]; rw [OreLocalization.one_def]
  have hr : r != 0 := by
    rintro rfl
    simp at h
  simp only [hr]
  with_unfolding_all apply OreLocalization.mul_inv ⟨r, _⟩

/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: (0 : R[R⁰⁻¹])⁻¹ = 0
  proof: by
  rw [OreLocalization.zero_def]; rw [OreLocalization.inv_def]
  simp

中文:
定理 inv_zero
  结论: (0 : R[R⁰⁻¹])⁻¹ = 0
  证明: by
  rw [OreLocalization.zero_def]; rw [OreLocalization.inv_def]
  simp
-/
protected theorem inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 := by
  rw [OreLocalization.zero_def]; rw [OreLocalization.inv_def]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GroupWithZero R[R⁰⁻¹]
  body: OreLocalization.inv_zero
  mul_inv_cancel := OreLocalization.mul_inv_cancel

中文:
实例 :
  签名: 带零群 R[R⁰⁻¹]
  定义体: OreLocalization.inv_zero
  mul_inv_cancel := OreLocalization.mul_inv_cancel

Depends on / 依赖: OreLocalization, OreLocalization.inv_zero, inv_zero
-/
noncomputable instance : GroupWithZero R[R⁰⁻¹] where
  inv_zero := OreLocalization.inv_zero
  mul_inv_cancel := OreLocalization.mul_inv_cancel

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [OreSet R⁰] [NoZeroDivisors R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroupWithZero R[R⁰⁻¹]

中文:
实例 :
  签名: 带零交换群 R[R⁰⁻¹]
-/
noncomputable instance : CommGroupWithZero R[R⁰⁻¹] where

end CommMonoidWithZero

end OreLocalization
