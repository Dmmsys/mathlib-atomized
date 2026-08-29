/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Torsion-free monoids and groups

This file proves lemmas about torsion-free monoids.
A monoid `M` is *torsion-free* if `n • · : M → M` is injective for all non-zero natural numbers `n`.
-/

public section

open Function

variable {M G : Type*}

section Monoid
variable [Monoid M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: M] [IsAddTorsionFree M] : Lean.Grind.NoNatZeroDivisors M where
  body: IsAddTorsionFree.nsmul_right_injective hk habk

中文:
实例 [加法交换幺半群
  签名: M] [是加法无挠 M] : Lean.Grind.No自然数ZeroDivisors M where
  定义体: IsAddTorsionFree.nsmul_right_injective hk habk

Depends on / 依赖: IsAddTorsionFree, IsAddTorsionFree.nsmul_right_injective, nsmul_right_injective
-/
instance [AddCommMonoid M] [IsAddTorsionFree M] : Lean.Grind.NoNatZeroDivisors M where
  no_nat_zero_divisors _ _ _ hk habk := IsAddTorsionFree.nsmul_right_injective hk habk

/--
Instance `Subsingleton.to_isMulTorsionFree` / 实例 `Subsingleton.to_isMulTorsionFree`

English:
instance Subsingleton.to_isMulTorsionFree
  signature: [Subsingleton M]
  body: injective_of_subsingleton _

中文:
实例 子单例.to_isMulTorsionFree
  签名: [子单例 M]
  定义体: injective_of_subsingleton _
-/
@[to_additive] instance Subsingleton.to_isMulTorsionFree [Subsingleton M] : IsMulTorsionFree M where
  pow_left_injective _ _ := injective_of_subsingleton _

variable [IsMulTorsionFree M] {n : Nat} {a b : M}

@[to_additive nsmul_right_injective]
/--
lemma `pow_left_injective` / 引理 `pow_left_injective`

English:
lemma pow_left_injective
  given: (hn : n != 0)
  statement: Injective fun a : M => a ^ n
  proof: IsMulTorsionFree.pow_left_injective hn

@[to_additive nsmul_right_inj]

中文:
引理 pow_left_injective
  条件: (hn : n != 0)
  结论: 单射 fun a : M => a ^ n
  证明: IsMulTorsionFree.pow_left_injective hn

@[to_additive nsmul_right_inj]

Depends on / 依赖: IsMulTorsionFree, IsMulTorsionFree.pow_left_injective, pow_left_injective
-/
lemma pow_left_injective (hn : n != 0) : Injective fun a : M => a ^ n :=
  IsMulTorsionFree.pow_left_injective hn

@[to_additive nsmul_right_inj]
/--
lemma `pow_left_inj` / 引理 `pow_left_inj`

English:
lemma pow_left_inj
  given: (hn : n != 0)
  statement: a ^ n = b ^ n ↔ a = b
  proof: (pow_left_injective hn).eq_iff

@[to_additive nsmul_eq_zero_iff_right]

中文:
引理 pow_left_inj
  条件: (hn : n != 0)
  结论: a ^ n = b ^ n ↔ a = b
  证明: (pow_left_injective hn).eq_iff

@[to_additive nsmul_eq_zero_iff_right]

Depends on / 依赖: eq_iff, pow_left_injective
-/
lemma pow_left_inj (hn : n != 0) : a ^ n = b ^ n ↔ a = b := (pow_left_injective hn).eq_iff

@[to_additive nsmul_eq_zero_iff_right]
/--
lemma `pow_eq_one_iff_left` / 引理 `pow_eq_one_iff_left`

English:
lemma pow_eq_one_iff_left
  given: (hn : n != 0)
  statement: a ^ n = 1 ↔ a = 1
  proof: by
  rw [← pow_left_inj (a := a) hn]; rw [one_pow]

中文:
引理 pow_eq_one_iff_left
  条件: (hn : n != 0)
  结论: a ^ n = 1 ↔ a = 1
  证明: by
  rw [← pow_left_inj (a := a) hn]; rw [one_pow]

Depends on / 依赖: one_pow, pow_left_inj
-/
lemma pow_eq_one_iff_left (hn : n != 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← pow_left_inj (a := a) hn]; rw [one_pow]

-- We want to use `IsAddTorsion.nsmul_eq_zero_iff` earlier than `smul_eq_zero`.
@[to_additive (attr := simp high)]
/--
lemma `pow_eq_one_iff` / 引理 `pow_eq_one_iff`

English:
lemma pow_eq_one_iff
  statement: a ^ n = 1 ↔ a = 1 ∨ n = 0
  proof: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [pow_eq_one_iff_left, *]

@[to_additive nsmul_eq_zero_iff_left]

中文:
引理 pow_eq_one_iff
  结论: a ^ n = 1 ↔ a = 1 ∨ n = 0
  证明: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [pow_eq_one_iff_left, *]

@[to_additive nsmul_eq_zero_iff_left]

Depends on / 依赖: eq_or_ne, pow_eq_one_iff_left
-/
lemma pow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [pow_eq_one_iff_left, *]

@[to_additive nsmul_eq_zero_iff_left]
/--
lemma `pow_eq_one_iff_right` / 引理 `pow_eq_one_iff_right`

English:
lemma pow_eq_one_iff_right
  given: (ha : a != 1)
  statement: a ^ n = 1 ↔ n = 0
  proof: by simp [*]

中文:
引理 pow_eq_one_iff_right
  条件: (ha : a != 1)
  结论: a ^ n = 1 ↔ n = 0
  证明: by simp [*]
-/
lemma pow_eq_one_iff_right (ha : a != 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

/-- See `sq_eq_one_iff` for a version that holds in rings. -/
@[to_additive two_nsmul_eq_zero]
/--
lemma `sq_eq_one` / 引理 `sq_eq_one`

English:
lemma sq_eq_one
  statement: a ^ 2 = 1 ↔ a = 1
  proof: pow_eq_one_iff_left (by lia)

中文:
引理 sq_eq_one
  结论: a ^ 2 = 1 ↔ a = 1
  证明: pow_eq_one_iff_left (by lia)

Depends on / 依赖: pow_eq_one_iff_left
-/
lemma sq_eq_one : a ^ 2 = 1 ↔ a = 1 := pow_eq_one_iff_left (by lia)

end Monoid

section Group
variable [Group G] [IsMulTorsionFree G] {n : Int} {a b : G}

@[to_additive zsmul_right_injective]
/--
lemma `zpow_left_injective` / 引理 `zpow_left_injective`

English:
lemma zpow_left_injective
  statement: forall {n : Int}, n != 0 -> Injective fun a : G => a ^ n

中文:
引理 zpow_left_injective
  结论: 对任意 {n : 整数}, n != 0 -> 单射 fun a : G => a ^ n
-/
lemma zpow_left_injective : forall {n : Int}, n != 0 -> Injective fun a : G => a ^ n
  | (n + 1 : Nat), _ => by
    simpa [← Int.natCast_one, ← Int.natCast_add] using! pow_left_injective n.succ_ne_zero
  | .negSucc n, _ => by simpa using! inv_injective.comp (pow_left_injective n.succ_ne_zero)

@[to_additive zsmul_right_inj]
/--
lemma `zpow_left_inj` / 引理 `zpow_left_inj`

English:
lemma zpow_left_inj
  given: (hn : n != 0)
  statement: a ^ n = b ^ n ↔ a = b
  proof: (zpow_left_injective hn).eq_iff

中文:
引理 zpow_left_inj
  条件: (hn : n != 0)
  结论: a ^ n = b ^ n ↔ a = b
  证明: (zpow_left_injective hn).eq_iff

Depends on / 依赖: eq_iff, zpow_left_injective
-/
lemma zpow_left_inj (hn : n != 0) : a ^ n = b ^ n ↔ a = b := (zpow_left_injective hn).eq_iff

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive /-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'`
and `zsmul_lt_zsmul_iff'`. -/]
/--
lemma `zpow_eq_zpow_iff'` / 引理 `zpow_eq_zpow_iff'`

English:
lemma zpow_eq_zpow_iff'
  given: (hn : n != 0)
  statement: a ^ n = b ^ n ↔ a = b
  proof: zpow_left_inj hn

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_right]

中文:
引理 zpow_eq_zpow_iff'
  条件: (hn : n != 0)
  结论: a ^ n = b ^ n ↔ a = b
  证明: zpow_left_inj hn

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_right]

Depends on / 依赖: zpow_left_inj
-/
lemma zpow_eq_zpow_iff' (hn : n != 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_right]
/--
lemma `IsMulTorsionFree.zpow_eq_one_iff_left` / 引理 `IsMulTorsionFree.zpow_eq_one_iff_left`

English:
lemma IsMulTorsionFree.zpow_eq_one_iff_left
  given: (hn : n != 0)
  statement: a ^ n = 1 ↔ a = 1
  proof: by
  rw [← zpow_left_inj (a := a) hn]; rw [one_zpow]

中文:
引理 是MulTorsionFree.zpow_eq_one_iff_left
  条件: (hn : n != 0)
  结论: a ^ n = 1 ↔ a = 1
  证明: by
  rw [← zpow_left_inj (a := a) hn]; rw [one_zpow]

Depends on / 依赖: one_zpow, zpow_left_inj
-/
lemma IsMulTorsionFree.zpow_eq_one_iff_left (hn : n != 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← zpow_left_inj (a := a) hn]; rw [one_zpow]

-- We want to use `IsAddTorsion.zsmul_eq_zero_iff` earlier than `smul_eq_zero`.
@[to_additive (attr := simp high)]
/--
lemma `IsMulTorsionFree.zpow_eq_one_iff` / 引理 `IsMulTorsionFree.zpow_eq_one_iff`

English:
lemma IsMulTorsionFree.zpow_eq_one_iff
  statement: a ^ n = 1 ↔ a = 1 ∨ n = 0
  proof: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [zpow_eq_one_iff_left, *]

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_left]

中文:
引理 是MulTorsionFree.zpow_eq_one_iff
  结论: a ^ n = 1 ↔ a = 1 ∨ n = 0
  证明: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [zpow_eq_one_iff_left, *]

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_left]

Depends on / 依赖: eq_or_ne, zpow_eq_one_iff_left
-/
lemma IsMulTorsionFree.zpow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [zpow_eq_one_iff_left, *]

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_left]
/--
lemma `IsMulTorsionFree.zpow_eq_one_iff_right` / 引理 `IsMulTorsionFree.zpow_eq_one_iff_right`

English:
lemma IsMulTorsionFree.zpow_eq_one_iff_right
  given: (ha : a != 1)
  statement: a ^ n = 1 ↔ n = 0
  proof: by simp [*]

中文:
引理 是MulTorsionFree.zpow_eq_one_iff_right
  条件: (ha : a != 1)
  结论: a ^ n = 1 ↔ n = 0
  证明: by simp [*]
-/
lemma IsMulTorsionFree.zpow_eq_one_iff_right (ha : a != 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

/--
lemma `self_eq_inv` / 引理 `self_eq_inv`

English:
lemma self_eq_inv
  statement: a = a⁻¹ ↔ a = 1
  proof: by rw [← sq_eq_one, sq, mul_eq_one_iff_eq_inv]

中文:
引理 self_eq_inv
  结论: a = a⁻¹ ↔ a = 1
  证明: by rw [← sq_eq_one, sq, mul_eq_one_iff_eq_inv]
-/
@[to_additive] lemma self_eq_inv : a = a⁻¹ ↔ a = 1 := by rw [← sq_eq_one, sq, mul_eq_one_iff_eq_inv]
/--
lemma `inv_eq_self` / 引理 `inv_eq_self`

English:
lemma inv_eq_self
  statement: a⁻¹ = a ↔ a = 1
  proof: by rw [eq_comm, self_eq_inv]

中文:
引理 inv_eq_self
  结论: a⁻¹ = a ↔ a = 1
  证明: by rw [eq_comm, self_eq_inv]
-/
@[to_additive] lemma inv_eq_self : a⁻¹ = a ↔ a = 1 := by rw [eq_comm, self_eq_inv]
/--
lemma `self_ne_inv` / 引理 `self_ne_inv`

English:
lemma self_ne_inv
  statement: a != a⁻¹ ↔ a != 1
  proof: self_eq_inv.ne

中文:
引理 self_ne_inv
  结论: a != a⁻¹ ↔ a != 1
  证明: self_eq_inv.ne
-/
@[to_additive] lemma self_ne_inv : a != a⁻¹ ↔ a != 1 := self_eq_inv.ne
/--
lemma `inv_ne_self` / 引理 `inv_ne_self`

English:
lemma inv_ne_self
  statement: a⁻¹ != a ↔ a != 1
  proof: inv_eq_self.ne

中文:
引理 inv_ne_self
  结论: a⁻¹ != a ↔ a != 1
  证明: inv_eq_self.ne
-/
@[to_additive] lemma inv_ne_self : a⁻¹ != a ↔ a != 1 := inv_eq_self.ne

end Group
