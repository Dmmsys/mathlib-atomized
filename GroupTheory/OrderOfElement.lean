/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `IsOfFinOrder` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `IsOfFinAddOrder` is the additive analogue of `IsOfFinOrder`.
* `orderOf x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `addOrderOf` is the additive analogue of `orderOf`.

## Tags
order of an element
-/

@[expose] public section

assert_not_exists Field

open Function Fintype Nat Pointwise Subgroup Submonoid
open scoped Finset

variable {G H A α β : Type*}

section Monoid
variable [Monoid G] {a b x y : G} {n m : Nat}

section IsOfFinOrder

@[to_additive]
/--
theorem `isPeriodicPt_mul_iff_pow_eq_one` / 定理 `isPeriodicPt_mul_iff_pow_eq_one`

English:
theorem isPeriodicPt_mul_iff_pow_eq_one
  given: (x : G)
  statement: IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
  proof: by
  rw [IsPeriodicPt]; rw [IsFixedPt]; rw [mul_left_iterate_apply_one]

中文:
定理 isPeriodicPt_mul_iff_pow_eq_one
  条件: (x : G)
  结论: IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
  证明: by
  rw [IsPeriodicPt]; rw [IsFixedPt]; rw [mul_left_iterate_apply_one]

Depends on / 依赖: IsFixedPt, IsPeriodicPt, mul_left_iterate_apply_one
-/
theorem isPeriodicPt_mul_iff_pow_eq_one (x : G) : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1 := by
  rw [IsPeriodicPt]; rw [IsFixedPt]; rw [mul_left_iterate_apply_one]

/-- `IsOfFinOrder` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`. -/
@[to_additive /-- `IsOfFinAddOrder` is a predicate on an element `a` of an
additive monoid to be of finite order, i.e. there exists `n ≥ 1` such that `n • a = 0`. -/]
/--
Definition of `IsOfFinOrder` / `IsOfFinOrder` 的定义

English:
definition IsOfFinOrder
  signature: (x : G)
  body: (1 : G) in periodicPts (x * ·)

中文:
定义 IsOfFinOrder
  签名: (x : G)
  定义体: (1 : G) in periodicPts (x * ·)

Depends on / 依赖: periodicPts
-/
def IsOfFinOrder (x : G) : Prop :=
  (1 : G) in periodicPts (x * ·)

/--
theorem `isOfFinAddOrder_ofMul_iff` / 定理 `isOfFinAddOrder_ofMul_iff`

English:
theorem isOfFinAddOrder_ofMul_iff
  statement: IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x
  proof: Iff.rfl

中文:
定理 isOfFinAddOrder_ofMul_iff
  结论: IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOfFinAddOrder_ofMul_iff : IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x :=
  Iff.rfl

/--
theorem `isOfFinOrder_ofAdd_iff` / 定理 `isOfFinOrder_ofAdd_iff`

English:
theorem isOfFinOrder_ofAdd_iff
  given: {α : Type*} [AddMonoid α] {x : α}
  proof: Iff.rfl

@[to_additive]

中文:
定理 isOfFinOrder_ofAdd_iff
  条件: {α : 类型} [AddMonoid α] {x : α}
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem isOfFinOrder_ofAdd_iff {α : Type*} [AddMonoid α] {x : α} :
    IsOfFinOrder (Multiplicative.ofAdd x) ↔ IsOfFinAddOrder x := Iff.rfl

@[to_additive]
/--
theorem `isOfFinOrder_iff_pow_eq_one` / 定理 `isOfFinOrder_iff_pow_eq_one`

English:
theorem isOfFinOrder_iff_pow_eq_one
  statement: IsOfFinOrder x ↔ exists n, 0 < n ∧ x ^ n = 1
  proof: by
  simp [IsOfFinOrder, mem_periodicPts, isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.exists_pow_eq_one, _⟩ := isOfFinOrder_iff_pow_eq_one

@[to_additive]

中文:
定理 isOfFinOrder_iff_pow_eq_one
  结论: IsOfFinOrder x ↔ 存在 n, 0 < n ∧ x ^ n = 1
  证明: by
  simp [IsOfFinOrder, mem_periodicPts, isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.exists_pow_eq_one, _⟩ := isOfFinOrder_iff_pow_eq_one

@[to_additive]

Depends on / 依赖: IsOfFinOrder, isPeriodicPt_mul_iff_pow_eq_one, mem_periodicPts
-/
theorem isOfFinOrder_iff_pow_eq_one : IsOfFinOrder x ↔ exists n, 0 < n ∧ x ^ n = 1 := by
  simp [IsOfFinOrder, mem_periodicPts, isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.exists_pow_eq_one, _⟩ := isOfFinOrder_iff_pow_eq_one

@[to_additive]
/--
lemma `isOfFinOrder_iff_zpow_eq_one` / 引理 `isOfFinOrder_iff_zpow_eq_one`

English:
lemma isOfFinOrder_iff_zpow_eq_one
  given: {G} [DivisionMonoid G] {x : G}
  proof: by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn, hn'⟩ => ⟨n, Int.natCast_ne_zero_iff_pos.mpr hn, zpow_natCast x n ▸ hn'⟩,
    fun ⟨n, hn, hn'⟩ => ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩⟩
  rcases (Int.natAbs_eq_iff (a := n)).mp rfl with h | h
  · rwa [h, zpow_natCast] at hn'
  · rwa [h, zpo

中文:
引理 isOfFinOrder_iff_zpow_eq_one
  条件: {G} [DivisionMonoid G] {x : G}
  证明: by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn, hn'⟩ => ⟨n, Int.natCast_ne_zero_iff_pos.mpr hn, zpow_natCast x n ▸ hn'⟩,
    fun ⟨n, hn, hn'⟩ => ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩⟩
  rcases (Int.natAbs_eq_iff (a := n)).mp rfl with h | h
  · rwa [h, zpow_natCast] at hn'
  · rwa [h, zpo

Depends on / 依赖: Int.natAbs_eq_iff, Int.natAbs_pos.mpr, Int.natCast_ne_zero_iff_pos.mpr, inv_eq_one, isOfFinOrder_iff_pow_eq_one, n.natAbs, natAbs, natAbs_eq_iff, natAbs_pos, natCast_ne_zero_iff_pos, zpow_natCast, zpow_neg
-/
lemma isOfFinOrder_iff_zpow_eq_one {G} [DivisionMonoid G] {x : G} :
    IsOfFinOrder x ↔ exists (n : Int), n != 0 ∧ x ^ n = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn, hn'⟩ => ⟨n, Int.natCast_ne_zero_iff_pos.mpr hn, zpow_natCast x n ▸ hn'⟩,
    fun ⟨n, hn, hn'⟩ => ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩⟩
  rcases (Int.natAbs_eq_iff (a := n)).mp rfl with h | h
  · rwa [h, zpow_natCast] at hn'
  · rwa [h, zpow_neg, inv_eq_one, zpow_natCast] at hn'

/-- See also `injective_pow_iff_not_isOfFinOrder`. -/
@[to_additive /-- See also `injective_nsmul_iff_not_isOfFinAddOrder`. -/]
/--
theorem `not_isOfFinOrder_of_injective_pow` / 定理 `not_isOfFinOrder_of_injective_pow`

English:
theorem not_isOfFinOrder_of_injective_pow
  given: {x : G} (h : Injective fun n : Nat => x ^ n)
  proof: by
  simp_rw [isOfFinOrder_iff_pow_eq_one, not_exists, not_and]
  intro n hn_pos hnx
  rw [← pow_zero x] at hnx
  rw [h hnx] at hn_pos
  exact irrefl 0 hn_pos

中文:
定理 not_isOfFinOrder_of_injective_pow
  条件: {x : G} (h : Injective fun n : 自然数 => x ^ n)
  证明: by
  simp_rw [isOfFinOrder_iff_pow_eq_one, not_exists, not_and]
  intro n hn_pos hnx
  rw [← pow_zero x] at hnx
  rw [h hnx] at hn_pos
  exact irrefl 0 hn_pos

Depends on / 依赖: hn_pos, irrefl, isOfFinOrder_iff_pow_eq_one, not_and, not_exists, pow_zero, simp_rw
-/
theorem not_isOfFinOrder_of_injective_pow {x : G} (h : Injective fun n : Nat => x ^ n) :
    ¬IsOfFinOrder x := by
  simp_rw [isOfFinOrder_iff_pow_eq_one, not_exists, not_and]
  intro n hn_pos hnx
  rw [← pow_zero x] at hnx
  rw [h hnx] at hn_pos
  exact irrefl 0 hn_pos

/-- 1 is of finite order in any monoid. -/
@[to_additive (attr := simp) /-- 0 is of finite order in any additive monoid. -/]
/--
theorem `IsOfFinOrder.one` / 定理 `IsOfFinOrder.one`

English:
theorem IsOfFinOrder.one
  statement: IsOfFinOrder (1 : G)
  proof: isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩

@[to_additive]

中文:
定理 IsOfFinOrder.one
  结论: IsOfFinOrder (1 : G)
  证明: isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩

@[to_additive]

Depends on / 依赖: Nat.one_pos, isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr, one_pos, one_pow
-/
theorem IsOfFinOrder.one : IsOfFinOrder (1 : G) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩

@[to_additive]
/--
lemma `IsOfFinOrder.pow` / 引理 `IsOfFinOrder.pow`

English:
lemma IsOfFinOrder.pow
  given: {n : Nat}
  statement: IsOfFinOrder a -> IsOfFinOrder (a ^ n)
  proof: by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨m, hm, ha⟩
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩

@[to_additive]

中文:
引理 IsOfFinOrder.pow
  条件: {n : 自然数}
  结论: IsOfFinOrder a -> IsOfFinOrder (a ^ n)
  证明: by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨m, hm, ha⟩
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩

@[to_additive]

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one, pow_right_comm, simp_rw
-/
lemma IsOfFinOrder.pow {n : Nat} : IsOfFinOrder a -> IsOfFinOrder (a ^ n) := by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨m, hm, ha⟩
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩

@[to_additive]
/--
lemma `IsOfFinOrder.of_pow` / 引理 `IsOfFinOrder.of_pow`

English:
lemma IsOfFinOrder.of_pow
  given: {n : Nat} (h : IsOfFinOrder (a ^ n)) (hn : n != 0)
  statement: IsOfFinOrder a
  proof: by
  rw [isOfFinOrder_iff_pow_eq_one] at *
  rcases h with ⟨m, hm, ha⟩
  exact ⟨n * m, mul_pos hn.bot_lt hm, by rwa [pow_mul]⟩

@[to_additive (attr := simp)]

中文:
引理 IsOfFinOrder.of_pow
  条件: {n : 自然数} (h : IsOfFinOrder (a ^ n)) (hn : n != 0)
  结论: IsOfFinOrder a
  证明: by
  rw [isOfFinOrder_iff_pow_eq_one] at *
  rcases h with ⟨m, hm, ha⟩
  exact ⟨n * m, mul_pos hn.bot_lt hm, by rwa [pow_mul]⟩

@[to_additive (attr := simp)]

Depends on / 依赖: bot_lt, hn.bot_lt, isOfFinOrder_iff_pow_eq_one, mul_pos, pow_mul
-/
lemma IsOfFinOrder.of_pow {n : Nat} (h : IsOfFinOrder (a ^ n)) (hn : n != 0) : IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one] at *
  rcases h with ⟨m, hm, ha⟩
  exact ⟨n * m, mul_pos hn.bot_lt hm, by rwa [pow_mul]⟩

@[to_additive (attr := simp)]
/--
lemma `isOfFinOrder_pow` / 引理 `isOfFinOrder_pow`

English:
lemma isOfFinOrder_pow
  given: {n : Nat}
  statement: IsOfFinOrder (a ^ n) ↔ IsOfFinOrder a ∨ n = 0
  proof: by
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · simp
· exact ⟨fun h => .inl h.of_pow hn, fun h => (h.resolve_right hn).pow⟩

@[to_additive]

中文:
引理 isOfFinOrder_pow
  条件: {n : 自然数}
  结论: IsOfFinOrder (a ^ n) ↔ IsOfFinOrder a ∨ n = 0
  证明: by
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · simp
· exact ⟨fun h => .inl h.of_pow hn, fun h => (h.resolve_right hn).pow⟩

@[to_additive]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, eq_or_ne, h.of_pow, h.resolve_right, of_pow, resolve_right
-/
lemma isOfFinOrder_pow {n : Nat} : IsOfFinOrder (a ^ n) ↔ IsOfFinOrder a ∨ n = 0 := by
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · simp
· exact ⟨fun h => .inl h.of_pow hn, fun h => (h.resolve_right hn).pow⟩

@[to_additive]
/--
lemma `not_isOfFinOrder_of_isMulTorsionFree` / 引理 `not_isOfFinOrder_of_isMulTorsionFree`

English:
lemma not_isOfFinOrder_of_isMulTorsionFree
  given: [IsMulTorsionFree G] (ha : a != 1)
  proof: by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, han⟩
exact ha pow_left_injective hn.ne' by simpa using han

@[to_additive]

中文:
引理 not_isOfFinOrder_of_isMulTorsionFree
  条件: [IsMulTorsionFree G] (ha : a != 1)
  证明: by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, han⟩
exact ha pow_left_injective hn.ne' by simpa using han

@[to_additive]

Depends on / 依赖: hn.ne, isOfFinOrder_iff_pow_eq_one, pow_left_injective
-/
lemma not_isOfFinOrder_of_isMulTorsionFree [IsMulTorsionFree G] (ha : a != 1) :
    ¬ IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, han⟩
exact ha pow_left_injective hn.ne' by simpa using han

@[to_additive]
/--
lemma `IsOfFinOrder.eq_one'` / 引理 `IsOfFinOrder.eq_one'`

English:
lemma IsOfFinOrder.eq_one'
  given: [IsMulTorsionFree G] {a : G} (ha : IsOfFinOrder a)
  proof: by
  contrapose! ha
  apply not_isOfFinOrder_of_isMulTorsionFree ha

@[to_additive]

中文:
引理 IsOfFinOrder.eq_one'
  条件: [IsMulTorsionFree G] {a : G} (ha : IsOfFinOrder a)
  证明: by
  contrapose! ha
  apply not_isOfFinOrder_of_isMulTorsionFree ha

@[to_additive]

Depends on / 依赖: contrapose, not_isOfFinOrder_of_isMulTorsionFree
-/
lemma IsOfFinOrder.eq_one' [IsMulTorsionFree G] {a : G} (ha : IsOfFinOrder a) :
    a = 1 := by
  contrapose! ha
  apply not_isOfFinOrder_of_isMulTorsionFree ha

@[to_additive]
/--
lemma `isOfFinOrder_iff_eq_one` / 引理 `isOfFinOrder_iff_eq_one`

English:
lemma isOfFinOrder_iff_eq_one
  given: [IsMulTorsionFree G] (a : G)
  statement: IsOfFinOrder a ↔ a = 1
  proof: ⟨IsOfFinOrder.eq_one', fun h => h.symm ▸ IsOfFinOrder.one⟩

中文:
引理 isOfFinOrder_iff_eq_one
  条件: [IsMulTorsionFree G] (a : G)
  结论: IsOfFinOrder a ↔ a = 1
  证明: ⟨IsOfFinOrder.eq_one', fun h => h.symm ▸ IsOfFinOrder.one⟩

Depends on / 依赖: IsOfFinOrder, IsOfFinOrder.eq_one, IsOfFinOrder.one, eq_one, h.symm
-/
lemma isOfFinOrder_iff_eq_one [IsMulTorsionFree G] (a : G) : IsOfFinOrder a ↔ a = 1 :=
  ⟨IsOfFinOrder.eq_one', fun h => h.symm ▸ IsOfFinOrder.one⟩

/-- Elements of finite order are of finite order in submonoids. -/
@[to_additive /-- Elements of finite order are of finite order in submonoids. -/]
/--
theorem `Submonoid.isOfFinOrder_coe` / 定理 `Submonoid.isOfFinOrder_coe`

English:
theorem Submonoid.isOfFinOrder_coe
  given: {H : Submonoid G} {x : H}
  proof: by
  rw [isOfFinOrder_iff_pow_eq_one]; rw [isOfFinOrder_iff_pow_eq_one]
  norm_cast

中文:
定理 Submonoid.isOfFinOrder_coe
  条件: {H : Submonoid G} {x : H}
  证明: by
  rw [isOfFinOrder_iff_pow_eq_one]; rw [isOfFinOrder_iff_pow_eq_one]
  norm_cast

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one
-/
theorem Submonoid.isOfFinOrder_coe {H : Submonoid G} {x : H} :
    IsOfFinOrder (x : G) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one]; rw [isOfFinOrder_iff_pow_eq_one]
  norm_cast

/--
theorem `IsConj.isOfFinOrder` / 定理 `IsConj.isOfFinOrder`

English:
theorem IsConj.isOfFinOrder
  given: (h : IsConj x y)
  statement: IsOfFinOrder x -> IsOfFinOrder y
  proof: by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, n_gt_0, eq'⟩
  exact ⟨n, n_gt_0, by rw [← isConj_one_right, ← eq']; exact h.pow n⟩

中文:
定理 IsConj.isOfFinOrder
  条件: (h : IsConj x y)
  结论: IsOfFinOrder x -> IsOfFinOrder y
  证明: by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, n_gt_0, eq'⟩
  exact ⟨n, n_gt_0, by rw [← isConj_one_right, ← eq']; exact h.pow n⟩

Depends on / 依赖: h.pow, isConj_one_right, isOfFinOrder_iff_pow_eq_one, n_gt_0, simp_rw
-/
theorem IsConj.isOfFinOrder (h : IsConj x y) : IsOfFinOrder x -> IsOfFinOrder y := by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, n_gt_0, eq'⟩
  exact ⟨n, n_gt_0, by rw [← isConj_one_right, ← eq']; exact h.pow n⟩

/-- The image of an element of finite order has finite order. -/
@[to_additive /-- The image of an element of finite additive order has finite additive order. -/]
/--
theorem `MonoidHom.isOfFinOrder` / 定理 `MonoidHom.isOfFinOrder`

English:
theorem MonoidHom.isOfFinOrder
  given: [Monoid H] (f : G ->* H) {x : G} (h : IsOfFinOrder x)
  proof: isOfFinOrder_iff_pow_eq_one.mpr by
    obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
    exact ⟨n, npos, by rw [← f.map_pow, hn, f.map_one]⟩

中文:
定理 MonoidHom.isOfFinOrder
  条件: [Monoid H] (f : G ->* H) {x : G} (h : IsOfFinOrder x)
  证明: isOfFinOrder_iff_pow_eq_one.mpr by
    obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
    exact ⟨n, npos, by rw [← f.map_pow, hn, f.map_one]⟩

Depends on / 依赖: exists_pow_eq_one, f.map_one, f.map_pow, h.exists_pow_eq_one, isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr, map_one, map_pow
-/
theorem MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) {x : G} (h : IsOfFinOrder x) :
IsOfFinOrder f x :=
isOfFinOrder_iff_pow_eq_one.mpr by
    obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
    exact ⟨n, npos, by rw [← f.map_pow, hn, f.map_one]⟩

/-- If a direct product has finite order then so does each component. -/
@[to_additive /-- If a direct product has finite additive order then so does each component. -/]
/--
theorem `IsOfFinOrder.apply` / 定理 `IsOfFinOrder.apply`

English:
theorem IsOfFinOrder.apply
  statement: {η : Type*} {Gs : η -> Type*} [forall i, Monoid (Gs i)] {x : forall i, Gs i}
  proof: by
  obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
  exact fun _ => isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, (congr_fun hn.symm _).symm⟩

中文:
定理 IsOfFinOrder.apply
  结论: {η : 类型} {Gs : η -> 类型} [对任意 i, Monoid (Gs i)] {x : 对任意 i, Gs i}
  证明: by
  obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
  exact fun _ => isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, (congr_fun hn.symm _).symm⟩

Depends on / 依赖: congr_fun, exists_pow_eq_one, h.exists_pow_eq_one, hn.symm, isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr
-/
theorem IsOfFinOrder.apply {η : Type*} {Gs : η -> Type*} [forall i, Monoid (Gs i)] {x : forall i, Gs i}
    (h : IsOfFinOrder x) : forall i, IsOfFinOrder (x i) := by
  obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
  exact fun _ => isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, (congr_fun hn.symm _).symm⟩

/-- The submonoid generated by an element is a group if that element has finite order. -/
@[to_additive /-- The additive submonoid generated by an element is
an additive group if that element has finite order. -/]
/--
Definition of `IsOfFinOrder.groupPowers` / `IsOfFinOrder.groupPowers` 的定义

English:
abbreviation IsOfFinOrder.groupPowers
  signature: (hx : IsOfFinOrder x)
  body: by
  obtain ⟨hpos, hx⟩ := hx.exists_pow_eq_one.choose_spec
  exact Submonoid.groupPowers hpos hx

中文:
缩写 IsOfFinOrder.groupPowers
  签名: (hx : IsOfFinOrder x)
  定义体: by
  obtain ⟨hpos, hx⟩ := hx.exists_pow_eq_one.choose_spec
  exact Submonoid.groupPowers hpos hx

Depends on / 依赖: Submonoid, Submonoid.groupPowers, choose_spec, exists_pow_eq_one, groupPowers, hx.exists_pow_eq_one.choose_spec
-/
noncomputable abbrev IsOfFinOrder.groupPowers (hx : IsOfFinOrder x) :
    Group (Submonoid.powers x) := by
  obtain ⟨hpos, hx⟩ := hx.exists_pow_eq_one.choose_spec
  exact Submonoid.groupPowers hpos hx

end IsOfFinOrder

/-- `orderOf x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `orderOf x` is `0` by convention. -/
@[to_additive
  /-- `addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it
  exists. Otherwise, i.e. if `a` is of infinite order, then `addOrderOf a` is `0` by convention. -/]
/--
Definition of `orderOf` / `orderOf` 的定义

English:
definition orderOf
  signature: (x : G)
  body: minimalPeriod (x * ·) 1

@[to_additive (attr := nontriviality)]

中文:
定义 orderOf
  签名: (x : G)
  定义体: minimalPeriod (x * ·) 1

@[to_additive (attr := nontriviality)]

Depends on / 依赖: minimalPeriod
-/
noncomputable def orderOf (x : G) : Nat :=
  minimalPeriod (x * ·) 1

@[to_additive (attr := nontriviality)]
/--
theorem `Subsingleton.orderOf_eq` / 定理 `Subsingleton.orderOf_eq`

English:
theorem Subsingleton.orderOf_eq
  given: [Subsingleton G] (x : G)
  statement: orderOf x = 1
  proof: by
  simp [orderOf, nontriviality]

@[simp]

中文:
定理 Subsingleton.orderOf_eq
  条件: [Subsingleton G] (x : G)
  结论: orderOf x = 1
  证明: by
  simp [orderOf, nontriviality]

@[simp]

Depends on / 依赖: nontriviality, orderOf
-/
theorem Subsingleton.orderOf_eq [Subsingleton G] (x : G) : orderOf x = 1 := by
  simp [orderOf, nontriviality]

@[simp]
/--
theorem `addOrderOf_ofMul_eq_orderOf` / 定理 `addOrderOf_ofMul_eq_orderOf`

English:
theorem addOrderOf_ofMul_eq_orderOf
  given: (x : G)
  statement: addOrderOf (Additive.ofMul x) = orderOf x
  proof: rfl

@[simp]

中文:
定理 addOrderOf_ofMul_eq_orderOf
  条件: (x : G)
  结论: addOrderOf (Additive.ofMul x) = orderOf x
  证明: rfl

@[simp]
-/
theorem addOrderOf_ofMul_eq_orderOf (x : G) : addOrderOf (Additive.ofMul x) = orderOf x :=
  rfl

@[simp]
/--
lemma `orderOf_ofAdd_eq_addOrderOf` / 引理 `orderOf_ofAdd_eq_addOrderOf`

English:
lemma orderOf_ofAdd_eq_addOrderOf
  given: {α : Type*} [AddMonoid α] (a : α)
  proof: rfl

@[to_additive]

中文:
引理 orderOf_ofAdd_eq_addOrderOf
  条件: {α : 类型} [AddMonoid α] (a : α)
  证明: rfl

@[to_additive]
-/
lemma orderOf_ofAdd_eq_addOrderOf {α : Type*} [AddMonoid α] (a : α) :
    orderOf (Multiplicative.ofAdd a) = addOrderOf a := rfl

@[to_additive]
/--
lemma `IsOfFinOrder.orderOf_pos` / 引理 `IsOfFinOrder.orderOf_pos`

English:
lemma IsOfFinOrder.orderOf_pos
  given: (h : IsOfFinOrder x)
  statement: 0 < orderOf x
  proof: minimalPeriod_pos_of_mem_periodicPts h

@[to_additive (attr := simp) addOrderOf_nsmul_eq_zero]

中文:
引理 IsOfFinOrder.orderOf_pos
  条件: (h : IsOfFinOrder x)
  结论: 0 < orderOf x
  证明: minimalPeriod_pos_of_mem_periodicPts h

@[to_additive (attr := simp) addOrderOf_nsmul_eq_zero]
-/
protected lemma IsOfFinOrder.orderOf_pos (h : IsOfFinOrder x) : 0 < orderOf x :=
  minimalPeriod_pos_of_mem_periodicPts h

@[to_additive (attr := simp) addOrderOf_nsmul_eq_zero]
/--
theorem `pow_orderOf_eq_one` / 定理 `pow_orderOf_eq_one`

English:
theorem pow_orderOf_eq_one
  given: (x : G)
  statement: x ^ orderOf x = 1
  proof: by
  convert! Eq.trans _ (isPeriodicPt_minimalPeriod (x * ·) 1)
  rw [orderOf]; rw [mul_left_iterate_apply_one]

@[to_additive]

中文:
定理 pow_orderOf_eq_one
  条件: (x : G)
  结论: x ^ orderOf x = 1
  证明: by
  convert! Eq.trans _ (isPeriodicPt_minimalPeriod (x * ·) 1)
  rw [orderOf]; rw [mul_left_iterate_apply_one]

@[to_additive]

Depends on / 依赖: Eq.trans, convert, isPeriodicPt_minimalPeriod, mul_left_iterate_apply_one, orderOf
-/
theorem pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1 := by
  convert! Eq.trans _ (isPeriodicPt_minimalPeriod (x * ·) 1)
  rw [orderOf]; rw [mul_left_iterate_apply_one]

@[to_additive]
/--
theorem `orderOf_eq_zero` / 定理 `orderOf_eq_zero`

English:
theorem orderOf_eq_zero
  given: (h : ¬IsOfFinOrder x)
  statement: orderOf x = 0
  proof: by
  rwa [orderOf, minimalPeriod, dif_neg]

@[to_additive (attr := simp)]

中文:
定理 orderOf_eq_zero
  条件: (h : ¬IsOfFinOrder x)
  结论: orderOf x = 0
  证明: by
  rwa [orderOf, minimalPeriod, dif_neg]

@[to_additive (attr := simp)]

Depends on / 依赖: dif_neg, minimalPeriod, orderOf
-/
theorem orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0 := by
  rwa [orderOf, minimalPeriod, dif_neg]

@[to_additive (attr := simp)]
/--
theorem `orderOf_eq_zero_iff` / 定理 `orderOf_eq_zero_iff`

English:
theorem orderOf_eq_zero_iff
  statement: orderOf x = 0 ↔ ¬IsOfFinOrder x
  proof: ⟨fun h H => H.orderOf_pos.ne' h, orderOf_eq_zero⟩

@[to_additive]

中文:
定理 orderOf_eq_zero_iff
  结论: orderOf x = 0 ↔ ¬IsOfFinOrder x
  证明: ⟨fun h H => H.orderOf_pos.ne' h, orderOf_eq_zero⟩

@[to_additive]

Depends on / 依赖: H.orderOf_pos.ne, orderOf_eq_zero, orderOf_pos
-/
theorem orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder x :=
  ⟨fun h H => H.orderOf_pos.ne' h, orderOf_eq_zero⟩

@[to_additive]
/--
theorem `orderOf_eq_zero_iff'` / 定理 `orderOf_eq_zero_iff'`

English:
theorem orderOf_eq_zero_iff'
  statement: orderOf x = 0 ↔ forall n : Nat, 0 < n -> x ^ n != 1
  proof: by
  simp_rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one, not_exists, not_and]

@[to_additive]

中文:
定理 orderOf_eq_zero_iff'
  结论: orderOf x = 0 ↔ 对任意 n : 自然数, 0 < n -> x ^ n != 1
  证明: by
  simp_rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one, not_exists, not_and]

@[to_additive]

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one, not_and, not_exists, orderOf_eq_zero_iff, simp_rw
-/
theorem orderOf_eq_zero_iff' : orderOf x = 0 ↔ forall n : Nat, 0 < n -> x ^ n != 1 := by
  simp_rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one, not_exists, not_and]

@[to_additive]
/--
lemma `orderOf_ne_zero_iff` / 引理 `orderOf_ne_zero_iff`

English:
lemma orderOf_ne_zero_iff
  statement: orderOf x != 0 ↔ IsOfFinOrder x
  proof: orderOf_eq_zero_iff.not_left

中文:
引理 orderOf_ne_zero_iff
  结论: orderOf x != 0 ↔ IsOfFinOrder x
  证明: orderOf_eq_zero_iff.not_left

Depends on / 依赖: not_left, orderOf_eq_zero_iff, orderOf_eq_zero_iff.not_left
-/
lemma orderOf_ne_zero_iff : orderOf x != 0 ↔ IsOfFinOrder x := orderOf_eq_zero_iff.not_left

/-- In a nontrivial monoid with zero, the order of the zero element is zero. -/
@[simp]
/--
lemma `orderOf_zero` / 引理 `orderOf_zero`

English:
lemma orderOf_zero
  given: (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀]
  statement: orderOf (0 : M₀) = 0
  proof: by
  rw [orderOf_eq_zero_iff]; rw [isOfFinOrder_iff_pow_eq_one]
  simp +contextual [ne_of_gt]

中文:
引理 orderOf_zero
  条件: (M₀ : 类型) [MonoidWithZero M₀] [Nontrivial M₀]
  结论: orderOf (0 : M₀) = 0
  证明: by
  rw [orderOf_eq_zero_iff]; rw [isOfFinOrder_iff_pow_eq_one]
  simp +contextual [ne_of_gt]

Depends on / 依赖: contextual, isOfFinOrder_iff_pow_eq_one, ne_of_gt, orderOf_eq_zero_iff
-/
lemma orderOf_zero (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀] : orderOf (0 : M₀) = 0 := by
  rw [orderOf_eq_zero_iff]; rw [isOfFinOrder_iff_pow_eq_one]
  simp +contextual [ne_of_gt]

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `orderOf_eq_iff` / 定理 `orderOf_eq_iff`

English:
theorem orderOf_eq_iff
  given: {n} (h : 0 < n)
  proof: by
  simp_rw [Ne, ← isPeriodicPt_mul_iff_pow_eq_one, orderOf, minimalPeriod]
  split_ifs with h1
  · classical
    rw [find_eq_iff]
    simp only [h, true_and, not_and]
  · rw [iff_false_left h.ne]
    rintro ⟨h', -⟩
    exact h1 ⟨n, h, h'⟩

中文:
定理 orderOf_eq_iff
  条件: {n} (h : 0 < n)
  证明: by
  simp_rw [Ne, ← isPeriodicPt_mul_iff_pow_eq_one, orderOf, minimalPeriod]
  split_ifs with h1
  · classical
    rw [find_eq_iff]
    simp only [h, true_and, not_and]
  · rw [iff_false_left h.ne]
    rintro ⟨h', -⟩
    exact h1 ⟨n, h, h'⟩

Depends on / 依赖: classical, find_eq_iff, h.ne, iff_false_left, isPeriodicPt_mul_iff_pow_eq_one, minimalPeriod, not_and, orderOf, simp_rw, split_ifs, true_and
-/
theorem orderOf_eq_iff {n} (h : 0 < n) :
    orderOf x = n ↔ x ^ n = 1 ∧ forall m, m < n -> 0 < m -> x ^ m != 1 := by
  simp_rw [Ne, ← isPeriodicPt_mul_iff_pow_eq_one, orderOf, minimalPeriod]
  split_ifs with h1
  · classical
    rw [find_eq_iff]
    simp only [h, true_and, not_and]
  · rw [iff_false_left h.ne]
    rintro ⟨h', -⟩
    exact h1 ⟨n, h, h'⟩

/-- A group element has finite order iff its order is positive. -/
@[to_additive (attr := simp)
/-- A group element has finite additive order iff its order is positive. -/]
/--
theorem `orderOf_pos_iff` / 定理 `orderOf_pos_iff`

English:
theorem orderOf_pos_iff
  statement: 0 < orderOf x ↔ IsOfFinOrder x
  proof: by
  rw [iff_not_comm.mp orderOf_eq_zero_iff]; rw [pos_iff_ne_zero]

@[to_additive]

中文:
定理 orderOf_pos_iff
  结论: 0 < orderOf x ↔ IsOfFinOrder x
  证明: by
  rw [iff_not_comm.mp orderOf_eq_zero_iff]; rw [pos_iff_ne_zero]

@[to_additive]

Depends on / 依赖: iff_not_comm, iff_not_comm.mp, orderOf_eq_zero_iff, pos_iff_ne_zero
-/
theorem orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x := by
  rw [iff_not_comm.mp orderOf_eq_zero_iff]; rw [pos_iff_ne_zero]

@[to_additive]
/--
theorem `IsOfFinOrder.mono` / 定理 `IsOfFinOrder.mono`

English:
theorem IsOfFinOrder.mono
  given: [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y ∣ orderOf x)
  proof: by rw [← orderOf_pos_iff] at hx ⊢; exact Nat.pos_of_dvd_of_pos h hx

@[to_additive]

中文:
定理 IsOfFinOrder.mono
  条件: [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y ∣ orderOf x)
  证明: by rw [← orderOf_pos_iff] at hx ⊢; exact Nat.pos_of_dvd_of_pos h hx

@[to_additive]

Depends on / 依赖: Nat.pos_of_dvd_of_pos, orderOf_pos_iff, pos_of_dvd_of_pos
-/
theorem IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y ∣ orderOf x) :
    IsOfFinOrder y := by rw [← orderOf_pos_iff] at hx ⊢; exact Nat.pos_of_dvd_of_pos h hx

@[to_additive]
/--
theorem `pow_ne_one_of_lt_orderOf` / 定理 `pow_ne_one_of_lt_orderOf`

English:
theorem pow_ne_one_of_lt_orderOf
  given: (n0 : n != 0) (h : n < orderOf x)
  statement: x ^ n != 1
  proof: fun j =>
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod n0 h ((isPeriodicPt_mul_iff_pow_eq_one x).mpr j)
@[to_additive]

中文:
定理 pow_ne_one_of_lt_orderOf
  条件: (n0 : n != 0) (h : n < orderOf x)
  结论: x ^ n != 1
  证明: fun j =>
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod n0 h ((isPeriodicPt_mul_iff_pow_eq_one x).mpr j)
@[to_additive]
-/
theorem pow_ne_one_of_lt_orderOf (n0 : n != 0) (h : n < orderOf x) : x ^ n != 1 := fun j =>
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod n0 h ((isPeriodicPt_mul_iff_pow_eq_one x).mpr j)
@[to_additive]
/--
theorem `orderOf_le_of_pow_eq_one` / 定理 `orderOf_le_of_pow_eq_one`

English:
theorem orderOf_le_of_pow_eq_one
  given: (hn : 0 < n) (h : x ^ n = 1)
  statement: orderOf x <= n
  proof: IsPeriodicPt.minimalPeriod_le hn (by rwa [isPeriodicPt_mul_iff_pow_eq_one])

@[to_additive (attr := simp)]

中文:
定理 orderOf_le_of_pow_eq_one
  条件: (hn : 0 < n) (h : x ^ n = 1)
  结论: orderOf x <= n
  证明: IsPeriodicPt.minimalPeriod_le hn (by rwa [isPeriodicPt_mul_iff_pow_eq_one])

@[to_additive (attr := simp)]

Depends on / 依赖: IsPeriodicPt, IsPeriodicPt.minimalPeriod_le, isPeriodicPt_mul_iff_pow_eq_one, minimalPeriod_le
-/
theorem orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : orderOf x <= n :=
  IsPeriodicPt.minimalPeriod_le hn (by rwa [isPeriodicPt_mul_iff_pow_eq_one])

@[to_additive (attr := simp)]
/--
theorem `orderOf_one` / 定理 `orderOf_one`

English:
theorem orderOf_one
  statement: orderOf (1 : G) = 1
  proof: by
  rw [orderOf]; rw [← minimalPeriod_id (x := (1 : G))]; rw [← one_mul_eq_id]

@[to_additive (attr := simp) AddMonoid.addOrderOf_eq_one_iff]

中文:
定理 orderOf_one
  结论: orderOf (1 : G) = 1
  证明: by
  rw [orderOf]; rw [← minimalPeriod_id (x := (1 : G))]; rw [← one_mul_eq_id]

@[to_additive (attr := simp) AddMonoid.addOrderOf_eq_one_iff]

Depends on / 依赖: minimalPeriod_id, one_mul_eq_id, orderOf
-/
theorem orderOf_one : orderOf (1 : G) = 1 := by
  rw [orderOf]; rw [← minimalPeriod_id (x := (1 : G))]; rw [← one_mul_eq_id]

@[to_additive (attr := simp) AddMonoid.addOrderOf_eq_one_iff]
/--
theorem `orderOf_eq_one_iff` / 定理 `orderOf_eq_one_iff`

English:
theorem orderOf_eq_one_iff
  statement: orderOf x = 1 ↔ x = 1
  proof: by
  rw [orderOf]; rw [minimalPeriod_eq_one_iff_isFixedPt]; rw [IsFixedPt]; rw [mul_one]

@[to_additive (attr := simp) mod_addOrderOf_nsmul]

中文:
定理 orderOf_eq_one_iff
  结论: orderOf x = 1 ↔ x = 1
  证明: by
  rw [orderOf]; rw [minimalPeriod_eq_one_iff_isFixedPt]; rw [IsFixedPt]; rw [mul_one]

@[to_additive (attr := simp) mod_addOrderOf_nsmul]

Depends on / 依赖: IsFixedPt, minimalPeriod_eq_one_iff_isFixedPt, mul_one, orderOf
-/
theorem orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1 := by
  rw [orderOf]; rw [minimalPeriod_eq_one_iff_isFixedPt]; rw [IsFixedPt]; rw [mul_one]

@[to_additive (attr := simp) mod_addOrderOf_nsmul]
/--
lemma `pow_mod_orderOf` / 引理 `pow_mod_orderOf`

English:
lemma pow_mod_orderOf
  given: (x : G) (n : Nat)
  statement: x ^ (n % orderOf x) = x ^ n
  proof: calc
    x ^ (n % orderOf x) = x ^ (n % orderOf x + orderOf x * (n / orderOf x)) := by
        simp [pow_add, pow_mul, pow_orderOf_eq_one]
    _ = x ^ n := by rw [Nat.mod_add_div]

@[to_additive]

中文:
引理 pow_mod_orderOf
  条件: (x : G) (n : 自然数)
  结论: x ^ (n % orderOf x) = x ^ n
  证明: calc
    x ^ (n % orderOf x) = x ^ (n % orderOf x + orderOf x * (n / orderOf x)) := by
        simp [pow_add, pow_mul, pow_orderOf_eq_one]
    _ = x ^ n := by rw [Nat.mod_add_div]

@[to_additive]

Depends on / 依赖: Nat.mod_add_div, mod_add_div, orderOf, pow_add, pow_mul, pow_orderOf_eq_one
-/
lemma pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x) = x ^ n :=
  calc
    x ^ (n % orderOf x) = x ^ (n % orderOf x + orderOf x * (n / orderOf x)) := by
        simp [pow_add, pow_mul, pow_orderOf_eq_one]
    _ = x ^ n := by rw [Nat.mod_add_div]

@[to_additive]
/--
theorem `orderOf_dvd_of_pow_eq_one` / 定理 `orderOf_dvd_of_pow_eq_one`

English:
theorem orderOf_dvd_of_pow_eq_one
  given: (h : x ^ n = 1)
  statement: orderOf x ∣ n
  proof: IsPeriodicPt.minimalPeriod_dvd ((isPeriodicPt_mul_iff_pow_eq_one _).mpr h)

@[to_additive]

中文:
定理 orderOf_dvd_of_pow_eq_one
  条件: (h : x ^ n = 1)
  结论: orderOf x ∣ n
  证明: IsPeriodicPt.minimalPeriod_dvd ((isPeriodicPt_mul_iff_pow_eq_one _).mpr h)

@[to_additive]

Depends on / 依赖: IsPeriodicPt, IsPeriodicPt.minimalPeriod_dvd, isPeriodicPt_mul_iff_pow_eq_one, minimalPeriod_dvd
-/
theorem orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : orderOf x ∣ n :=
  IsPeriodicPt.minimalPeriod_dvd ((isPeriodicPt_mul_iff_pow_eq_one _).mpr h)

@[to_additive]
/--
theorem `orderOf_dvd_iff_pow_eq_one` / 定理 `orderOf_dvd_iff_pow_eq_one`

English:
theorem orderOf_dvd_iff_pow_eq_one
  given: {n : Nat}
  statement: orderOf x ∣ n ↔ x ^ n = 1
  proof: ⟨fun h => by rw [← pow_mod_orderOf, Nat.mod_eq_zero_of_dvd h, _root_.pow_zero],
    orderOf_dvd_of_pow_eq_one⟩

中文:
定理 orderOf_dvd_iff_pow_eq_one
  条件: {n : 自然数}
  结论: orderOf x ∣ n ↔ x ^ n = 1
  证明: ⟨fun h => by rw [← pow_mod_orderOf, Nat.mod_eq_zero_of_dvd h, _root_.pow_zero],
    orderOf_dvd_of_pow_eq_one⟩

Depends on / 依赖: Nat.mod_eq_zero_of_dvd, _root_, _root_.pow_zero, mod_eq_zero_of_dvd, orderOf_dvd_of_pow_eq_one, pow_mod_orderOf, pow_zero
-/
theorem orderOf_dvd_iff_pow_eq_one {n : Nat} : orderOf x ∣ n ↔ x ^ n = 1 :=
  ⟨fun h => by rw [← pow_mod_orderOf, Nat.mod_eq_zero_of_dvd h, _root_.pow_zero],
    orderOf_dvd_of_pow_eq_one⟩

/-- If `x ^ p = 1` for some odd `p`, then every power of `x` is an even power of `x`. -/
@[to_additive /-- If `p • x = 0` for some odd `p`, then every multiple of `x` is an even
multiple of `x`. -/]
/--
theorem `exists_pow_eq_pow_two_mul` / 定理 `exists_pow_eq_pow_two_mul`

English:
theorem exists_pow_eq_pow_two_mul
  given: {p : Nat} (hx : x ^ p = 1) (hp : Odd p) (n : Nat)
  proof: by
  obtain ⟨r, rfl⟩ := hp
  have key : x ^ (2 * (r + 1)) = x := by
    have h2 : 2 * (r + 1) = 2 * r + 1 + 1 := by omega
    rw [h2]; rw [pow_succ]; rw [hx]; rw [one_mul]
  exact ⟨(r + 1) * n, by rw [← mul_assoc, pow_mul, key]⟩

@[to_additive addOrderOf_smul_dvd]

中文:
定理 exists_pow_eq_pow_two_mul
  条件: {p : 自然数} (hx : x ^ p = 1) (hp : Odd p) (n : 自然数)
  证明: by
  obtain ⟨r, rfl⟩ := hp
  have key : x ^ (2 * (r + 1)) = x := by
    have h2 : 2 * (r + 1) = 2 * r + 1 + 1 := by omega
    rw [h2]; rw [pow_succ]; rw [hx]; rw [one_mul]
  exact ⟨(r + 1) * n, by rw [← mul_assoc, pow_mul, key]⟩

@[to_additive addOrderOf_smul_dvd]

Depends on / 依赖: mul_assoc, one_mul, pow_mul, pow_succ
-/
theorem exists_pow_eq_pow_two_mul {p : Nat} (hx : x ^ p = 1) (hp : Odd p) (n : Nat) :
    exists m, x ^ n = x ^ (2 * m) := by
  obtain ⟨r, rfl⟩ := hp
  have key : x ^ (2 * (r + 1)) = x := by
    have h2 : 2 * (r + 1) = 2 * r + 1 + 1 := by omega
    rw [h2]; rw [pow_succ]; rw [hx]; rw [one_mul]
  exact ⟨(r + 1) * n, by rw [← mul_assoc, pow_mul, key]⟩

@[to_additive addOrderOf_smul_dvd]
/--
theorem `orderOf_pow_dvd` / 定理 `orderOf_pow_dvd`

English:
theorem orderOf_pow_dvd
  given: (n : Nat)
  statement: orderOf (x ^ n) ∣ orderOf x
  proof: by
  rw [orderOf_dvd_iff_pow_eq_one]; rw [pow_right_comm]; rw [pow_orderOf_eq_one]; rw [one_pow]

@[to_additive]

中文:
定理 orderOf_pow_dvd
  条件: (n : 自然数)
  结论: orderOf (x ^ n) ∣ orderOf x
  证明: by
  rw [orderOf_dvd_iff_pow_eq_one]; rw [pow_right_comm]; rw [pow_orderOf_eq_one]; rw [one_pow]

@[to_additive]

Depends on / 依赖: one_pow, orderOf_dvd_iff_pow_eq_one, pow_orderOf_eq_one, pow_right_comm
-/
theorem orderOf_pow_dvd (n : Nat) : orderOf (x ^ n) ∣ orderOf x := by
  rw [orderOf_dvd_iff_pow_eq_one]; rw [pow_right_comm]; rw [pow_orderOf_eq_one]; rw [one_pow]

@[to_additive]
/--
lemma `pow_injOn_Iio_orderOf` / 引理 `pow_injOn_Iio_orderOf`

English:
lemma pow_injOn_Iio_orderOf
  statement: (Set.Iio <| orderOf x).InjOn (x ^ ·)
  proof: by
  simpa only [mul_left_iterate_apply_one]
    using! iterate_injOn_Iio_minimalPeriod (f := (x * ·)) (x := 1)

@[to_additive]

中文:
引理 pow_injOn_Iio_orderOf
  结论: (Set.Iio <| orderOf x).InjOn (x ^ ·)
  证明: by
  simpa only [mul_left_iterate_apply_one]
    using! iterate_injOn_Iio_minimalPeriod (f := (x * ·)) (x := 1)

@[to_additive]

Depends on / 依赖: iterate_injOn_Iio_minimalPeriod, mul_left_iterate_apply_one
-/
lemma pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).InjOn (x ^ ·) := by
  simpa only [mul_left_iterate_apply_one]
    using! iterate_injOn_Iio_minimalPeriod (f := (x * ·)) (x := 1)

@[to_additive]
/--
lemma `IsOfFinOrder.mem_powers_iff_mem_range_orderOf` / 引理 `IsOfFinOrder.mem_powers_iff_mem_range_orderOf`

English:
lemma IsOfFinOrder.mem_powers_iff_mem_range_orderOf
  statement: [DecidableEq G]
  proof: Finset.mem_range_iff_mem_finset_range_of_mod_eq' hx.orderOf_pos pow_mod_orderOf _

@[to_additive]

中文:
引理 IsOfFinOrder.mem_powers_iff_mem_range_orderOf
  结论: [DecidableEq G]
  证明: Finset.mem_range_iff_mem_finset_range_of_mod_eq' hx.orderOf_pos pow_mod_orderOf _

@[to_additive]
-/
protected lemma IsOfFinOrder.mem_powers_iff_mem_range_orderOf [DecidableEq G]
    (hx : IsOfFinOrder x) :
    y in Submonoid.powers x ↔ y in (Finset.range (orderOf x)).image (x ^ ·) :=
Finset.mem_range_iff_mem_finset_range_of_mod_eq' hx.orderOf_pos pow_mod_orderOf _

@[to_additive]
/--
lemma `IsOfFinOrder.powers_eq_image_range_orderOf` / 引理 `IsOfFinOrder.powers_eq_image_range_orderOf`

English:
lemma IsOfFinOrder.powers_eq_image_range_orderOf
  given: [DecidableEq G] (hx : IsOfFinOrder x)
  proof: Set.ext fun _ => hx.mem_powers_iff_mem_range_orderOf

@[to_additive]

中文:
引理 IsOfFinOrder.powers_eq_image_range_orderOf
  条件: [DecidableEq G] (hx : IsOfFinOrder x)
  证明: Set.ext fun _ => hx.mem_powers_iff_mem_range_orderOf

@[to_additive]
-/
protected lemma IsOfFinOrder.powers_eq_image_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) :
    (Submonoid.powers x : Set G) = (Finset.range (orderOf x)).image (x ^ ·) :=
  Set.ext fun _ => hx.mem_powers_iff_mem_range_orderOf

@[to_additive]
/--
theorem `pow_eq_pow_of_modEq` / 定理 `pow_eq_pow_of_modEq`

English:
theorem pow_eq_pow_of_modEq
  given: {a b : Nat} (h : a ≡ b [MOD n]) (hx : x ^ n = 1)
  statement: x ^ a = x ^ b
  proof: by
  obtain hle | hle := le_total a b
  all_goals
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hle
    obtain ⟨c, rfl⟩ : n ∣ c := by simpa using h
    simp [pow_add, pow_mul, hx]

@[to_additive]

中文:
定理 pow_eq_pow_of_modEq
  条件: {a b : 自然数} (h : a ≡ b [MOD n]) (hx : x ^ n = 1)
  结论: x ^ a = x ^ b
  证明: by
  obtain hle | hle := le_total a b
  all_goals
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hle
    obtain ⟨c, rfl⟩ : n ∣ c := by simpa using h
    simp [pow_add, pow_mul, hx]

@[to_additive]

Depends on / 依赖: all_goals, le_iff_exists_add, le_iff_exists_add.mp, le_total, pow_add, pow_mul
-/
theorem pow_eq_pow_of_modEq {a b : Nat} (h : a ≡ b [MOD n]) (hx : x ^ n = 1) : x ^ a = x ^ b := by
  obtain hle | hle := le_total a b
  all_goals
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hle
    obtain ⟨c, rfl⟩ : n ∣ c := by simpa using h
    simp [pow_add, pow_mul, hx]

@[to_additive]
/--
theorem `pow_eq_one_iff_modEq` / 定理 `pow_eq_one_iff_modEq`

English:
theorem pow_eq_one_iff_modEq
  statement: x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x]
  proof: by
  rw [modEq_zero_iff_dvd]; rw [orderOf_dvd_iff_pow_eq_one]

@[to_additive]

中文:
定理 pow_eq_one_iff_modEq
  结论: x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x]
  证明: by
  rw [modEq_zero_iff_dvd]; rw [orderOf_dvd_iff_pow_eq_one]

@[to_additive]

Depends on / 依赖: modEq_zero_iff_dvd, orderOf_dvd_iff_pow_eq_one
-/
theorem pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x] := by
  rw [modEq_zero_iff_dvd]; rw [orderOf_dvd_iff_pow_eq_one]

@[to_additive]
/--
theorem `orderOf_map_dvd` / 定理 `orderOf_map_dvd`

English:
theorem orderOf_map_dvd
  given: {H : Type*} [Monoid H] (ψ : G ->* H) (x : G)
  proof: by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow]; rw [pow_orderOf_eq_one]
  apply map_one

@[to_additive]

中文:
定理 orderOf_map_dvd
  条件: {H : 类型} [Monoid H] (ψ : G ->* H) (x : G)
  证明: by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow]; rw [pow_orderOf_eq_one]
  apply map_one

@[to_additive]

Depends on / 依赖: map_one, map_pow, orderOf_dvd_of_pow_eq_one, pow_orderOf_eq_one
-/
theorem orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G ->* H) (x : G) :
    orderOf (ψ x) ∣ orderOf x := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow]; rw [pow_orderOf_eq_one]
  apply map_one

@[to_additive]
/--
theorem `exists_pow_eq_self_of_coprime` / 定理 `exists_pow_eq_self_of_coprime`

English:
theorem exists_pow_eq_self_of_coprime
  given: (h : n.Coprime (orderOf x))
  statement: exists m : Nat, (x ^ n) ^ m = x
  proof: by
  by_cases h0 : orderOf x = 0
  · rw [h0, coprime_zero_right] at h
    exact ⟨1, by rw [h, pow_one, pow_one]⟩
  by_cases h1 : orderOf x = 1
  · exact ⟨0, by rw [orderOf_eq_one_iff.mp h1, one_pow, one_pow]⟩
  obtain ⟨m, -, h⟩ := exists_mul_mod_eq_one_of_coprime h (by lia)
  exact ⟨m, by rw [← pow_

中文:
定理 exists_pow_eq_self_of_coprime
  条件: (h : n.Coprime (orderOf x))
  结论: 存在 m : 自然数, (x ^ n) ^ m = x
  证明: by
  by_cases h0 : orderOf x = 0
  · rw [h0, coprime_zero_right] at h
    exact ⟨1, by rw [h, pow_one, pow_one]⟩
  by_cases h1 : orderOf x = 1
  · exact ⟨0, by rw [orderOf_eq_one_iff.mp h1, one_pow, one_pow]⟩
  obtain ⟨m, -, h⟩ := exists_mul_mod_eq_one_of_coprime h (by lia)
  exact ⟨m, by rw [← pow_

Depends on / 依赖: coprime_zero_right, exists_mul_mod_eq_one_of_coprime, one_pow, orderOf, orderOf_eq_one_iff, orderOf_eq_one_iff.mp, pow_mod_orderOf, pow_mul, pow_one
-/
theorem exists_pow_eq_self_of_coprime (h : n.Coprime (orderOf x)) : exists m : Nat, (x ^ n) ^ m = x := by
  by_cases h0 : orderOf x = 0
  · rw [h0, coprime_zero_right] at h
    exact ⟨1, by rw [h, pow_one, pow_one]⟩
  by_cases h1 : orderOf x = 1
  · exact ⟨0, by rw [orderOf_eq_one_iff.mp h1, one_pow, one_pow]⟩
  obtain ⟨m, -, h⟩ := exists_mul_mod_eq_one_of_coprime h (by lia)
  exact ⟨m, by rw [← pow_mul, ← pow_mod_orderOf, h, pow_one]⟩

/-- If `x^n = 1`, but `x^(n/p) ≠ 1` for all prime factors `p` of `n`,
then `x` has order `n` in `G`. -/
@[to_additive addOrderOf_eq_of_nsmul_and_div_prime_nsmul /-- If `n * x = 0`, but `n/p * x ≠ 0` for
all prime factors `p` of `n`, then `x` has order `n` in `G`. -/]
/--
theorem `orderOf_eq_of_pow_and_pow_div_prime` / 定理 `orderOf_eq_of_pow_and_pow_div_prime`

English:
theorem orderOf_eq_of_pow_and_pow_div_prime
  statement: (hn : 0 < n) (hx : x ^ n = 1)
  proof: by
  -- Let `a` be `n/(orderOf x)`, and show `a = 1`
  obtain ⟨a, ha⟩ := exists_eq_mul_right_of_dvd (orderOf_dvd_of_pow_eq_one hx)
  suffices a = 1 by simp [this, ha]
  -- Assume `a` is not one...
  by_contra h
  have a_min_fac_dvd_p_sub_one : a.minFac ∣ n := by
    obtain ⟨b, hb⟩ : exists b : Nat, 

中文:
定理 orderOf_eq_of_pow_and_pow_div_prime
  结论: (hn : 0 < n) (hx : x ^ n = 1)
  证明: by
  -- Let `a` be `n/(orderOf x)`, and show `a = 1`
  obtain ⟨a, ha⟩ := exists_eq_mul_right_of_dvd (orderOf_dvd_of_pow_eq_one hx)
  suffices a = 1 by simp [this, ha]
  -- Assume `a` is not one...
  by_contra h
  have a_min_fac_dvd_p_sub_one : a.minFac ∣ n := by
    obtain ⟨b, hb⟩ : exists b : Nat, 
-/
theorem orderOf_eq_of_pow_and_pow_div_prime (hn : 0 < n) (hx : x ^ n = 1)
    (hd : forall p : Nat, p.Prime -> p ∣ n -> x ^ (n / p) != 1) : orderOf x = n := by
  -- Let `a` be `n/(orderOf x)`, and show `a = 1`
  obtain ⟨a, ha⟩ := exists_eq_mul_right_of_dvd (orderOf_dvd_of_pow_eq_one hx)
  suffices a = 1 by simp [this, ha]
  -- Assume `a` is not one...
  by_contra h
  have a_min_fac_dvd_p_sub_one : a.minFac ∣ n := by
    obtain ⟨b, hb⟩ : exists b : Nat, a = b * a.minFac := exists_eq_mul_left_of_dvd a.minFac_dvd
    rw [hb]; rw [← mul_assoc] at ha
    exact Dvd.intro_left (orderOf x * b) ha.symm
  -- Use the minimum prime factor of `a` as `p`.
  refine hd a.minFac (Nat.minFac_prime h) a_min_fac_dvd_p_sub_one ?_
  rw [← orderOf_dvd_iff_pow_eq_one]; rw [Nat.dvd_div_iff_mul_dvd a_min_fac_dvd_p_sub_one]; rw [ha]; rw [mul_comm]; rw [Nat.mul_dvd_mul_iff_left (IsOfFinOrder.orderOf_pos _)]
  · exact Nat.minFac_dvd a
  · rw [isOfFinOrder_iff_pow_eq_one]
    exact Exists.intro n (id ⟨hn, hx⟩)

@[to_additive]
/--
theorem `orderOf_eq_orderOf_iff` / 定理 `orderOf_eq_orderOf_iff`

English:
theorem orderOf_eq_orderOf_iff
  given: {H : Type*} [Monoid H] {y : H}
  proof: by
  simp_rw [← isPeriodicPt_mul_iff_pow_eq_one, ← minimalPeriod_eq_minimalPeriod_iff, orderOf]

中文:
定理 orderOf_eq_orderOf_iff
  条件: {H : 类型} [Monoid H] {y : H}
  证明: by
  simp_rw [← isPeriodicPt_mul_iff_pow_eq_one, ← minimalPeriod_eq_minimalPeriod_iff, orderOf]

Depends on / 依赖: isPeriodicPt_mul_iff_pow_eq_one, minimalPeriod_eq_minimalPeriod_iff, orderOf, simp_rw
-/
theorem orderOf_eq_orderOf_iff {H : Type*} [Monoid H] {y : H} :
    orderOf x = orderOf y ↔ forall n : Nat, x ^ n = 1 ↔ y ^ n = 1 := by
  simp_rw [← isPeriodicPt_mul_iff_pow_eq_one, ← minimalPeriod_eq_minimalPeriod_iff, orderOf]

/-- An injective homomorphism of monoids preserves orders of elements. -/
@[to_additive /-- An injective homomorphism of additive monoids preserves orders of elements. -/]
/--
theorem `orderOf_injective` / 定理 `orderOf_injective`

English:
theorem orderOf_injective
  given: {H : Type*} [Monoid H] (f : G ->* H) (hf : Function.Injective f) (x : G)
  proof: by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]

中文:
定理 orderOf_injective
  条件: {H : 类型} [Monoid H] (f : G ->* H) (hf : Function.Injective f) (x : G)
  证明: by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]

Depends on / 依赖: eq_iff, f.map_one, f.map_pow, forall_const, hf.eq_iff, map_one, map_pow, orderOf_eq_orderOf_iff, simp_rw
-/
theorem orderOf_injective {H : Type*} [Monoid H] (f : G ->* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]

/-- A multiplicative equivalence preserves orders of elements. -/
@[to_additive (attr := simp) /-- An additive equivalence preserves orders of elements. -/]
/--
lemma `MulEquiv.orderOf_eq` / 引理 `MulEquiv.orderOf_eq`

English:
lemma MulEquiv.orderOf_eq
  given: {H : Type*} [Monoid H] (e : G ≃* H) (x : G)
  proof: orderOf_injective e.toMonoidHom e.injective x

@[to_additive]

中文:
引理 MulEquiv.orderOf_eq
  条件: {H : 类型} [Monoid H] (e : G ≃* H) (x : G)
  证明: orderOf_injective e.toMonoidHom e.injective x

@[to_additive]

Depends on / 依赖: e.injective, e.toMonoidHom, injective, orderOf_injective, toMonoidHom
-/
lemma MulEquiv.orderOf_eq {H : Type*} [Monoid H] (e : G ≃* H) (x : G) :
    orderOf (e x) = orderOf x :=
  orderOf_injective e.toMonoidHom e.injective x

@[to_additive]
/--
theorem `Function.Injective.isOfFinOrder_iff` / 定理 `Function.Injective.isOfFinOrder_iff`

English:
theorem Function.Injective.isOfFinOrder_iff
  given: [Monoid H] {f : G ->* H} (hf : Injective f)
  proof: by
  rw [← orderOf_pos_iff]; rw [orderOf_injective f hf x]; rw [← orderOf_pos_iff]

@[to_additive (attr := norm_cast, simp)]

中文:
定理 Function.Injective.isOfFinOrder_iff
  条件: [Monoid H] {f : G ->* H} (hf : Injective f)
  证明: by
  rw [← orderOf_pos_iff]; rw [orderOf_injective f hf x]; rw [← orderOf_pos_iff]

@[to_additive (attr := norm_cast, simp)]

Depends on / 依赖: orderOf_injective, orderOf_pos_iff
-/
theorem Function.Injective.isOfFinOrder_iff [Monoid H] {f : G ->* H} (hf : Injective f) :
    IsOfFinOrder (f x) ↔ IsOfFinOrder x := by
  rw [← orderOf_pos_iff]; rw [orderOf_injective f hf x]; rw [← orderOf_pos_iff]

@[to_additive (attr := norm_cast, simp)]
/--
theorem `orderOf_submonoid` / 定理 `orderOf_submonoid`

English:
theorem orderOf_submonoid
  given: {H : Submonoid G} (y : H)
  statement: orderOf (y : G) = orderOf y
  proof: orderOf_injective H.subtype Subtype.coe_injective y

@[to_additive (attr := norm_cast)]

中文:
定理 orderOf_submonoid
  条件: {H : Submonoid G} (y : H)
  结论: orderOf (y : G) = orderOf y
  证明: orderOf_injective H.subtype Subtype.coe_injective y

@[to_additive (attr := norm_cast)]

Depends on / 依赖: H.subtype, Subtype, Subtype.coe_injective, coe_injective, orderOf_injective, subtype
-/
theorem orderOf_submonoid {H : Submonoid G} (y : H) : orderOf (y : G) = orderOf y :=
  orderOf_injective H.subtype Subtype.coe_injective y

@[to_additive (attr := norm_cast)]
/--
theorem `orderOf_units` / 定理 `orderOf_units`

English:
theorem orderOf_units
  given: {y : Gˣ}
  statement: orderOf (y : G) = orderOf y
  proof: orderOf_injective (Units.coeHom G) Units.val_injective y

@[to_additive]

中文:
定理 orderOf_units
  条件: {y : Gˣ}
  结论: orderOf (y : G) = orderOf y
  证明: orderOf_injective (Units.coeHom G) Units.val_injective y

@[to_additive]

Depends on / 依赖: Units.coeHom, Units.val_injective, coeHom, orderOf_injective, val_injective
-/
theorem orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y :=
  orderOf_injective (Units.coeHom G) Units.val_injective y

@[to_additive]
/--
lemma `IsUnit.orderOf_eq_one` / 引理 `IsUnit.orderOf_eq_one`

English:
lemma IsUnit.orderOf_eq_one
  given: [Subsingleton Gˣ] {x : G} (h : IsUnit x)
  proof: by
  simp [isUnit_iff_eq_one.mp h]

@[to_additive (attr := norm_cast)]

中文:
引理 IsUnit.orderOf_eq_one
  条件: [Subsingleton Gˣ] {x : G} (h : IsUnit x)
  证明: by
  simp [isUnit_iff_eq_one.mp h]

@[to_additive (attr := norm_cast)]

Depends on / 依赖: isUnit_iff_eq_one, isUnit_iff_eq_one.mp
-/
lemma IsUnit.orderOf_eq_one [Subsingleton Gˣ] {x : G} (h : IsUnit x) :
    orderOf x = 1 := by
  simp [isUnit_iff_eq_one.mp h]

@[to_additive (attr := norm_cast)]
/--
theorem `Units.isOfFinOrder_val` / 定理 `Units.isOfFinOrder_val`

English:
theorem Units.isOfFinOrder_val
  given: {u : Gˣ}
  statement: IsOfFinOrder (u : G) ↔ IsOfFinOrder u
  proof: Units.coeHom_injective.isOfFinOrder_iff

中文:
定理 Units.isOfFinOrder_val
  条件: {u : Gˣ}
  结论: IsOfFinOrder (u : G) ↔ IsOfFinOrder u
  证明: Units.coeHom_injective.isOfFinOrder_iff

Depends on / 依赖: Units.coeHom_injective.isOfFinOrder_iff, coeHom_injective, isOfFinOrder_iff
-/
theorem Units.isOfFinOrder_val {u : Gˣ} : IsOfFinOrder (u : G) ↔ IsOfFinOrder u :=
  Units.coeHom_injective.isOfFinOrder_iff

/-- If the order of `x` is finite, then `x` is a unit with inverse `x ^ (orderOf x - 1)`. -/
@[to_additive (attr := simps) /-- If the additive order of `x` is finite, then `x` is an additive
unit with inverse `(addOrderOf x - 1) • x`. -/]
/--
Definition of `IsOfFinOrder.unit` / `IsOfFinOrder.unit` 的定义

English:
definition IsOfFinOrder.unit
  signature: {M} [Monoid M] {x : M} (hx : IsOfFinOrder x)
  body: ⟨x, x ^ (orderOf x - 1),
    by rw [← _root_.pow_succ', tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one],
    by rw [← _root_.pow_succ, tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one]⟩

@[to_additive]

中文:
定义 IsOfFinOrder.unit
  签名: {M} [Monoid M] {x : M} (hx : IsOfFinOrder x)
  定义体: ⟨x, x ^ (orderOf x - 1),
    by rw [← _root_.pow_succ', tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one],
    by rw [← _root_.pow_succ, tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one]⟩

@[to_additive]

Depends on / 依赖: _root_, _root_.pow_succ, hx.orderOf_pos, orderOf, orderOf_pos, pow_orderOf_eq_one, pow_succ, tsub_add_cancel_of_le
-/
noncomputable def IsOfFinOrder.unit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : Mˣ :=
  ⟨x, x ^ (orderOf x - 1),
    by rw [← _root_.pow_succ', tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one],
    by rw [← _root_.pow_succ, tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one]⟩

@[to_additive]
/--
lemma `IsOfFinOrder.isUnit` / 引理 `IsOfFinOrder.isUnit`

English:
lemma IsOfFinOrder.isUnit
  given: {M} [Monoid M] {x : M} (hx : IsOfFinOrder x)
  statement: IsUnit x
  proof: ⟨hx.unit, rfl⟩

中文:
引理 IsOfFinOrder.isUnit
  条件: {M} [Monoid M] {x : M} (hx : IsOfFinOrder x)
  结论: IsUnit x
  证明: ⟨hx.unit, rfl⟩

Depends on / 依赖: hx.unit
-/
lemma IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : IsUnit x := ⟨hx.unit, rfl⟩

variable (x)

@[to_additive]
/--
theorem `orderOf_pow'` / 定理 `orderOf_pow'`

English:
theorem orderOf_pow'
  given: (h : n != 0)
  statement: orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n
  proof: by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd h]; rw [mul_left_iterate]

@[to_additive]

中文:
定理 orderOf_pow'
  条件: (h : n != 0)
  结论: orderOf (x ^ n) = orderOf x / 自然数.gcd (orderOf x) n
  证明: by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd h]; rw [mul_left_iterate]

@[to_additive]

Depends on / 依赖: minimalPeriod_iterate_eq_div_gcd, mul_left_iterate, orderOf
-/
theorem orderOf_pow' (h : n != 0) : orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd h]; rw [mul_left_iterate]

@[to_additive]
/--
lemma `orderOf_pow_of_dvd` / 引理 `orderOf_pow_of_dvd`

English:
lemma orderOf_pow_of_dvd
  given: {x : G} {n : Nat} (hn : n != 0) (dvd : n ∣ orderOf x)
  proof: by rw [orderOf_pow' _ hn, Nat.gcd_eq_right dvd]

@[to_additive]

中文:
引理 orderOf_pow_of_dvd
  条件: {x : G} {n : 自然数} (hn : n != 0) (dvd : n ∣ orderOf x)
  证明: by rw [orderOf_pow' _ hn, Nat.gcd_eq_right dvd]

@[to_additive]

Depends on / 依赖: Nat.gcd_eq_right, gcd_eq_right, orderOf_pow
-/
lemma orderOf_pow_of_dvd {x : G} {n : Nat} (hn : n != 0) (dvd : n ∣ orderOf x) :
    orderOf (x ^ n) = orderOf x / n := by rw [orderOf_pow' _ hn, Nat.gcd_eq_right dvd]

@[to_additive]
/--
lemma `orderOf_pow_orderOf_div` / 引理 `orderOf_pow_orderOf_div`

English:
lemma orderOf_pow_orderOf_div
  given: {x : G} {n : Nat} (hx : orderOf x != 0) (hn : n ∣ orderOf x)
  proof: by
  rw [orderOf_pow_of_dvd _ (Nat.div_dvd_of_dvd hn)]; rw [Nat.div_div_self hn hx]
  rw [← Nat.div_mul_cancel hn] at hx; exact left_ne_zero_of_mul hx

中文:
引理 orderOf_pow_orderOf_div
  条件: {x : G} {n : 自然数} (hx : orderOf x != 0) (hn : n ∣ orderOf x)
  证明: by
  rw [orderOf_pow_of_dvd _ (Nat.div_dvd_of_dvd hn)]; rw [Nat.div_div_self hn hx]
  rw [← Nat.div_mul_cancel hn] at hx; exact left_ne_zero_of_mul hx

Depends on / 依赖: Nat.div_div_self, Nat.div_dvd_of_dvd, Nat.div_mul_cancel, div_div_self, div_dvd_of_dvd, div_mul_cancel, left_ne_zero_of_mul, orderOf_pow_of_dvd
-/
lemma orderOf_pow_orderOf_div {x : G} {n : Nat} (hx : orderOf x != 0) (hn : n ∣ orderOf x) :
    orderOf (x ^ (orderOf x / n)) = n := by
  rw [orderOf_pow_of_dvd _ (Nat.div_dvd_of_dvd hn)]; rw [Nat.div_div_self hn hx]
  rw [← Nat.div_mul_cancel hn] at hx; exact left_ne_zero_of_mul hx

variable (n)

@[to_additive]
/--
lemma `IsOfFinOrder.orderOf_pow` / 引理 `IsOfFinOrder.orderOf_pow`

English:
lemma IsOfFinOrder.orderOf_pow
  given: (h : IsOfFinOrder x)
  proof: by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd' h]; rw [mul_left_iterate]

@[to_additive]

中文:
引理 IsOfFinOrder.orderOf_pow
  条件: (h : IsOfFinOrder x)
  证明: by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd' h]; rw [mul_left_iterate]

@[to_additive]
-/
protected lemma IsOfFinOrder.orderOf_pow (h : IsOfFinOrder x) :
    orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd' h]; rw [mul_left_iterate]

@[to_additive]
/--
lemma `Nat.Coprime.orderOf_pow` / 引理 `Nat.Coprime.orderOf_pow`

English:
lemma Nat.Coprime.orderOf_pow
  given: (h : (orderOf y).Coprime m)
  statement: orderOf (y ^ m) = orderOf y
  proof: by
  by_cases hg : IsOfFinOrder y
  · rw [hg.orderOf_pow y m, h.gcd_eq_one, Nat.div_one]
  · rw [m.coprime_zero_left.1 (orderOf_eq_zero hg ▸ h), pow_one]

@[to_additive]

中文:
引理 Nat.Coprime.orderOf_pow
  条件: (h : (orderOf y).Coprime m)
  结论: orderOf (y ^ m) = orderOf y
  证明: by
  by_cases hg : IsOfFinOrder y
  · rw [hg.orderOf_pow y m, h.gcd_eq_one, Nat.div_one]
  · rw [m.coprime_zero_left.1 (orderOf_eq_zero hg ▸ h), pow_one]

@[to_additive]

Depends on / 依赖: IsOfFinOrder, Nat.div_one, coprime_zero_left, div_one, gcd_eq_one, h.gcd_eq_one, hg.orderOf_pow, m.coprime_zero_left, orderOf_eq_zero, orderOf_pow, pow_one
-/
lemma Nat.Coprime.orderOf_pow (h : (orderOf y).Coprime m) : orderOf (y ^ m) = orderOf y := by
  by_cases hg : IsOfFinOrder y
  · rw [hg.orderOf_pow y m, h.gcd_eq_one, Nat.div_one]
  · rw [m.coprime_zero_left.1 (orderOf_eq_zero hg ▸ h), pow_one]

@[to_additive]
/--
lemma `IsOfFinOrder.natCard_powers_le_orderOf` / 引理 `IsOfFinOrder.natCard_powers_le_orderOf`

English:
lemma IsOfFinOrder.natCard_powers_le_orderOf
  given: (ha : IsOfFinOrder a)
  proof: by
  classical
  simpa [ha.powers_eq_image_range_orderOf, Finset.card_range, Nat.Iio_eq_range]
    using Finset.card_image_le (s := Finset.range (orderOf a))

@[to_additive]

中文:
引理 IsOfFinOrder.natCard_powers_le_orderOf
  条件: (ha : IsOfFinOrder a)
  证明: by
  classical
  simpa [ha.powers_eq_image_range_orderOf, Finset.card_range, Nat.Iio_eq_range]
    using Finset.card_image_le (s := Finset.range (orderOf a))

@[to_additive]

Depends on / 依赖: Finset, Finset.card_image_le, Finset.card_range, Finset.range, Iio_eq_range, Nat.Iio_eq_range, card_image_le, card_range, classical, ha.powers_eq_image_range_orderOf, orderOf, powers_eq_image_range_orderOf
-/
lemma IsOfFinOrder.natCard_powers_le_orderOf (ha : IsOfFinOrder a) :
    Nat.card (powers a : Set G) <= orderOf a := by
  classical
  simpa [ha.powers_eq_image_range_orderOf, Finset.card_range, Nat.Iio_eq_range]
    using Finset.card_image_le (s := Finset.range (orderOf a))

@[to_additive]
/--
lemma `IsOfFinOrder.finite_powers` / 引理 `IsOfFinOrder.finite_powers`

English:
lemma IsOfFinOrder.finite_powers
  given: (ha : IsOfFinOrder a)
  statement: (powers a : Set G).Finite
  proof: by
  classical rw [ha.powers_eq_image_range_orderOf]; exact Finset.finite_toSet _

中文:
引理 IsOfFinOrder.finite_powers
  条件: (ha : IsOfFinOrder a)
  结论: (powers a : Set G).Finite
  证明: by
  classical rw [ha.powers_eq_image_range_orderOf]; exact Finset.finite_toSet _

Depends on / 依赖: Finset, Finset.finite_toSet, classical, finite_toSet, ha.powers_eq_image_range_orderOf, powers_eq_image_range_orderOf
-/
lemma IsOfFinOrder.finite_powers (ha : IsOfFinOrder a) : (powers a : Set G).Finite := by
  classical rw [ha.powers_eq_image_range_orderOf]; exact Finset.finite_toSet _

namespace Commute

variable {x}

@[to_additive]
/--
theorem `orderOf_mul_dvd_lcm` / 定理 `orderOf_mul_dvd_lcm`

English:
theorem orderOf_mul_dvd_lcm
  given: (h : Commute x y)
  proof: by
  rw [orderOf]; rw [← comp_mul_left]
  exact Function.Commute.minimalPeriod_of_comp_dvd_lcm h.function_commute_mul_left

@[to_additive]

中文:
定理 orderOf_mul_dvd_lcm
  条件: (h : Commute x y)
  证明: by
  rw [orderOf]; rw [← comp_mul_left]
  exact Function.Commute.minimalPeriod_of_comp_dvd_lcm h.function_commute_mul_left

@[to_additive]

Depends on / 依赖: Commute, Function, Function.Commute.minimalPeriod_of_comp_dvd_lcm, comp_mul_left, function_commute_mul_left, h.function_commute_mul_left, minimalPeriod_of_comp_dvd_lcm, orderOf
-/
theorem orderOf_mul_dvd_lcm (h : Commute x y) :
    orderOf (x * y) ∣ Nat.lcm (orderOf x) (orderOf y) := by
  rw [orderOf]; rw [← comp_mul_left]
  exact Function.Commute.minimalPeriod_of_comp_dvd_lcm h.function_commute_mul_left

@[to_additive]
/--
theorem `orderOf_dvd_lcm_mul` / 定理 `orderOf_dvd_lcm_mul`

English:
theorem orderOf_dvd_lcm_mul
  given: (h : Commute x y)
  proof: by
  by_cases h0 : orderOf x = 0
  · rw [h0, lcm_zero_left]
    apply dvd_zero
  conv_lhs =>
    rw [← one_mul y]; rw [← pow_orderOf_eq_one x]; rw [← succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)]; rw [_root_.pow_succ]; rw [mul_assoc]
  exact
    (((Commute.refl x).mul_right h).pow_left _).orderOf_mul

中文:
定理 orderOf_dvd_lcm_mul
  条件: (h : Commute x y)
  证明: by
  by_cases h0 : orderOf x = 0
  · rw [h0, lcm_zero_left]
    apply dvd_zero
  conv_lhs =>
    rw [← one_mul y]; rw [← pow_orderOf_eq_one x]; rw [← succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)]; rw [_root_.pow_succ]; rw [mul_assoc]
  exact
    (((Commute.refl x).mul_right h).pow_left _).orderOf_mul

Depends on / 依赖: Commute, Commute.refl, Nat.dvd_lcm_left, Nat.dvd_lcm_right, Nat.lcm_dvd_iff, Nat.pos_of_ne_zero, _root_, _root_.pow_succ, conv_lhs, dvd_lcm_left, dvd_lcm_right, dvd_zero, lcm_dvd_iff, lcm_zero_left, mul_assoc, mul_right, one_mul, orderOf, orderOf_mul_dvd_lcm, orderOf_mul_dvd_lcm.trans
-/
theorem orderOf_dvd_lcm_mul (h : Commute x y) :
    orderOf y ∣ Nat.lcm (orderOf x) (orderOf (x * y)) := by
  by_cases h0 : orderOf x = 0
  · rw [h0, lcm_zero_left]
    apply dvd_zero
  conv_lhs =>
    rw [← one_mul y]; rw [← pow_orderOf_eq_one x]; rw [← succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)]; rw [_root_.pow_succ]; rw [mul_assoc]
  exact
    (((Commute.refl x).mul_right h).pow_left _).orderOf_mul_dvd_lcm.trans
      (Nat.lcm_dvd_iff.2 ⟨(orderOf_pow_dvd _).trans (Nat.dvd_lcm_left _ _), Nat.dvd_lcm_right _ _⟩)

@[to_additive addOrderOf_add_dvd_mul_addOrderOf]
/--
theorem `orderOf_mul_dvd_mul_orderOf` / 定理 `orderOf_mul_dvd_mul_orderOf`

English:
theorem orderOf_mul_dvd_mul_orderOf
  given: (h : Commute x y)
  proof: dvd_trans h.orderOf_mul_dvd_lcm (Nat.lcm_dvd_mul _ _)

@[to_additive addOrderOf_add_eq_mul_addOrderOf_of_coprime]

中文:
定理 orderOf_mul_dvd_mul_orderOf
  条件: (h : Commute x y)
  证明: dvd_trans h.orderOf_mul_dvd_lcm (Nat.lcm_dvd_mul _ _)

@[to_additive addOrderOf_add_eq_mul_addOrderOf_of_coprime]

Depends on / 依赖: Nat.lcm_dvd_mul, dvd_trans, h.orderOf_mul_dvd_lcm, lcm_dvd_mul, orderOf_mul_dvd_lcm
-/
theorem orderOf_mul_dvd_mul_orderOf (h : Commute x y) :
    orderOf (x * y) ∣ orderOf x * orderOf y :=
  dvd_trans h.orderOf_mul_dvd_lcm (Nat.lcm_dvd_mul _ _)

@[to_additive addOrderOf_add_eq_mul_addOrderOf_of_coprime]
/--
theorem `orderOf_mul_eq_mul_orderOf_of_coprime` / 定理 `orderOf_mul_eq_mul_orderOf_of_coprime`

English:
theorem orderOf_mul_eq_mul_orderOf_of_coprime
  statement: (h : Commute x y)
  proof: by
  rw [orderOf]; rw [← comp_mul_left]
  exact h.function_commute_mul_left.minimalPeriod_of_comp_eq_mul_of_coprime hco

中文:
定理 orderOf_mul_eq_mul_orderOf_of_coprime
  结论: (h : Commute x y)
  证明: by
  rw [orderOf]; rw [← comp_mul_left]
  exact h.function_commute_mul_left.minimalPeriod_of_comp_eq_mul_of_coprime hco

Depends on / 依赖: comp_mul_left, function_commute_mul_left, h.function_commute_mul_left.minimalPeriod_of_comp_eq_mul_of_coprime, minimalPeriod_of_comp_eq_mul_of_coprime, orderOf
-/
theorem orderOf_mul_eq_mul_orderOf_of_coprime (h : Commute x y)
    (hco : (orderOf x).Coprime (orderOf y)) : orderOf (x * y) = orderOf x * orderOf y := by
  rw [orderOf]; rw [← comp_mul_left]
  exact h.function_commute_mul_left.minimalPeriod_of_comp_eq_mul_of_coprime hco

/-- Commuting elements of finite order are closed under multiplication. -/
@[to_additive /-- Commuting elements of finite additive order are closed under addition. -/]
/--
theorem `isOfFinOrder_mul` / 定理 `isOfFinOrder_mul`

English:
theorem isOfFinOrder_mul
  given: (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
  proof: orderOf_pos_iff.mp
pos_of_dvd_of_pos h.orderOf_mul_dvd_mul_orderOf mul_pos hx.orderOf_pos hy.orderOf_pos

中文:
定理 isOfFinOrder_mul
  条件: (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
  证明: orderOf_pos_iff.mp
pos_of_dvd_of_pos h.orderOf_mul_dvd_mul_orderOf mul_pos hx.orderOf_pos hy.orderOf_pos

Depends on / 依赖: h.orderOf_mul_dvd_mul_orderOf, hx.orderOf_pos, hy.orderOf_pos, mul_pos, orderOf_mul_dvd_mul_orderOf, orderOf_pos, orderOf_pos_iff, orderOf_pos_iff.mp, pos_of_dvd_of_pos
-/
theorem isOfFinOrder_mul (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) :
    IsOfFinOrder (x * y) :=
orderOf_pos_iff.mp
pos_of_dvd_of_pos h.orderOf_mul_dvd_mul_orderOf mul_pos hx.orderOf_pos hy.orderOf_pos

/-- If each prime factor of `orderOf x` has higher multiplicity in `orderOf y`, and `x` commutes
  with `y`, then `x * y` has the same order as `y`. -/
@[to_additive addOrderOf_add_eq_right_of_forall_prime_mul_dvd
  /-- If each prime factor of
  `addOrderOf x` has higher multiplicity in `addOrderOf y`, and `x` commutes with `y`,
  then `x + y` has the same order as `y`. -/]
/--
theorem `orderOf_mul_eq_right_of_forall_prime_mul_dvd` / 定理 `orderOf_mul_eq_right_of_forall_prime_mul_dvd`

English:
theorem orderOf_mul_eq_right_of_forall_prime_mul_dvd
  statement: (h : Commute x y) (hy : IsOfFinOrder y)
  proof: by
  have hoy := hy.orderOf_pos
  have hxy := dvd_of_forall_prime_mul_dvd hdvd
  apply orderOf_eq_of_pow_and_pow_div_prime hoy <;> simp only [Ne, ← orderOf_dvd_iff_pow_eq_one]
  · exact h.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd hxy dvd_rfl)
  refine fun p hp hpy hd => hp.ne_one ?_
  rw [← Nat.dvd_one

中文:
定理 orderOf_mul_eq_right_of_forall_prime_mul_dvd
  结论: (h : Commute x y) (hy : IsOfFinOrder y)
  证明: by
  have hoy := hy.orderOf_pos
  have hxy := dvd_of_forall_prime_mul_dvd hdvd
  apply orderOf_eq_of_pow_and_pow_div_prime hoy <;> simp only [Ne, ← orderOf_dvd_iff_pow_eq_one]
  · exact h.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd hxy dvd_rfl)
  refine fun p hp hpy hd => hp.ne_one ?_
  rw [← Nat.dvd_one

Depends on / 依赖: Nat.dvd_one, Nat.lcm_dvd, dvd_div_iff_mul_dvd, dvd_of_forall_prime_mul_dvd, dvd_one, dvd_rfl, exacts, h.orderOf_mul_dvd_lcm.trans, hoy.ne, hp.ne_one, hy.orderOf_pos, lcm_dvd, mul_dvd_mul_iff_right, ne_one, one_mul, orderOf, orderOf_dvd_iff_pow_eq_one, orderOf_dvd_lcm_mul, orderOf_eq_of_pow_and_pow_div_prime, orderOf_mul_dvd_lcm
-/
theorem orderOf_mul_eq_right_of_forall_prime_mul_dvd (h : Commute x y) (hy : IsOfFinOrder y)
    (hdvd : forall p : Nat, p.Prime -> p ∣ orderOf x -> p * orderOf x ∣ orderOf y) :
    orderOf (x * y) = orderOf y := by
  have hoy := hy.orderOf_pos
  have hxy := dvd_of_forall_prime_mul_dvd hdvd
  apply orderOf_eq_of_pow_and_pow_div_prime hoy <;> simp only [Ne, ← orderOf_dvd_iff_pow_eq_one]
  · exact h.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd hxy dvd_rfl)
  refine fun p hp hpy hd => hp.ne_one ?_
  rw [← Nat.dvd_one]; rw [← mul_dvd_mul_iff_right hoy.ne']; rw [one_mul]; rw [← dvd_div_iff_mul_dvd hpy]
  refine (orderOf_dvd_lcm_mul h).trans (Nat.lcm_dvd ((dvd_div_iff_mul_dvd hpy).2 ?_) hd)
  by_cases h : p ∣ orderOf x
  exacts [hdvd p hp h, (hp.coprime_iff_not_dvd.2 h).mul_dvd_of_dvd_of_dvd hpy hxy]

/-- If each prime factor of `orderOf y` has higher multiplicity in `orderOf x`, and `x` commutes
  with `y`, then `x * y` has the same order as `x`. -/
@[to_additive addOrderOf_add_eq_left_of_forall_prime_mul_dvd
  /-- If each prime factor of
  `addOrderOf y` has higher multiplicity in `addOrderOf x`, and `x` commutes with `y`,
  then `x + y` has the same order as `x`. -/]
/--
theorem `orderOf_mul_eq_left_of_forall_prime_mul_dvd` / 定理 `orderOf_mul_eq_left_of_forall_prime_mul_dvd`

English:
theorem orderOf_mul_eq_left_of_forall_prime_mul_dvd
  statement: (h : Commute x y) (hx : IsOfFinOrder x)
  proof: by
  simpa [h.eq] using
    orderOf_mul_eq_right_of_forall_prime_mul_dvd (x := y) (y := x) h.symm hx hdvd

中文:
定理 orderOf_mul_eq_left_of_forall_prime_mul_dvd
  结论: (h : Commute x y) (hx : IsOfFinOrder x)
  证明: by
  simpa [h.eq] using
    orderOf_mul_eq_right_of_forall_prime_mul_dvd (x := y) (y := x) h.symm hx hdvd

Depends on / 依赖: h.eq, h.symm, orderOf_mul_eq_right_of_forall_prime_mul_dvd
-/
theorem orderOf_mul_eq_left_of_forall_prime_mul_dvd (h : Commute x y) (hx : IsOfFinOrder x)
    (hdvd : forall p : Nat, p.Prime -> p ∣ orderOf y -> p * orderOf y ∣ orderOf x) :
    orderOf (x * y) = orderOf x := by
  simpa [h.eq] using
    orderOf_mul_eq_right_of_forall_prime_mul_dvd (x := y) (y := x) h.symm hx hdvd

end Commute

section PPrime
variable {x n} {p : Nat} [hp : Fact p.Prime]

@[to_additive]
/--
theorem `orderOf_eq_prime_iff` / 定理 `orderOf_eq_prime_iff`

English:
theorem orderOf_eq_prime_iff
  statement: orderOf x = p ↔ x ^ p = 1 ∧ x != 1
  proof: by
  rw [orderOf]; rw [minimalPeriod_eq_prime_iff]; rw [isPeriodicPt_mul_iff_pow_eq_one]; rw [IsFixedPt]; rw [mul_one]

中文:
定理 orderOf_eq_prime_iff
  结论: orderOf x = p ↔ x ^ p = 1 ∧ x != 1
  证明: by
  rw [orderOf]; rw [minimalPeriod_eq_prime_iff]; rw [isPeriodicPt_mul_iff_pow_eq_one]; rw [IsFixedPt]; rw [mul_one]

Depends on / 依赖: IsFixedPt, isPeriodicPt_mul_iff_pow_eq_one, minimalPeriod_eq_prime_iff, mul_one, orderOf
-/
theorem orderOf_eq_prime_iff : orderOf x = p ↔ x ^ p = 1 ∧ x != 1 := by
  rw [orderOf]; rw [minimalPeriod_eq_prime_iff]; rw [isPeriodicPt_mul_iff_pow_eq_one]; rw [IsFixedPt]; rw [mul_one]

/-- The backward direction of `orderOf_eq_prime_iff`. -/
@[to_additive /-- The backward direction of `addOrderOf_eq_prime_iff`. -/]
/--
theorem `orderOf_eq_prime` / 定理 `orderOf_eq_prime`

English:
theorem orderOf_eq_prime
  given: (hg : x ^ p = 1) (hg1 : x != 1)
  statement: orderOf x = p
  proof: orderOf_eq_prime_iff.mpr ⟨hg, hg1⟩

@[to_additive addOrderOf_eq_prime_pow]

中文:
定理 orderOf_eq_prime
  条件: (hg : x ^ p = 1) (hg1 : x != 1)
  结论: orderOf x = p
  证明: orderOf_eq_prime_iff.mpr ⟨hg, hg1⟩

@[to_additive addOrderOf_eq_prime_pow]

Depends on / 依赖: orderOf_eq_prime_iff, orderOf_eq_prime_iff.mpr
-/
theorem orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x != 1) : orderOf x = p :=
  orderOf_eq_prime_iff.mpr ⟨hg, hg1⟩

@[to_additive addOrderOf_eq_prime_pow]
/--
theorem `orderOf_eq_prime_pow` / 定理 `orderOf_eq_prime_pow`

English:
theorem orderOf_eq_prime_pow
  given: (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1)
  proof: by
  apply minimalPeriod_eq_prime_pow <;> rwa [isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive exists_addOrderOf_eq_prime_pow_iff]

中文:
定理 orderOf_eq_prime_pow
  条件: (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1)
  证明: by
  apply minimalPeriod_eq_prime_pow <;> rwa [isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive exists_addOrderOf_eq_prime_pow_iff]

Depends on / 依赖: isPeriodicPt_mul_iff_pow_eq_one, minimalPeriod_eq_prime_pow
-/
theorem orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) :
    orderOf x = p ^ (n + 1) := by
  apply minimalPeriod_eq_prime_pow <;> rwa [isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive exists_addOrderOf_eq_prime_pow_iff]
/--
theorem `exists_orderOf_eq_prime_pow_iff` / 定理 `exists_orderOf_eq_prime_pow_iff`

English:
theorem exists_orderOf_eq_prime_pow_iff
  proof: ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩, fun ⟨_, hm⟩ => by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.elim).mp (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩⟩

@[simp]

中文:
定理 exists_orderOf_eq_prime_pow_iff
  证明: ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩, fun ⟨_, hm⟩ => by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.elim).mp (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩⟩

@[simp]

Depends on / 依赖: Nat.dvd_prime_pow, dvd_prime_pow, hp.elim, orderOf_dvd_of_pow_eq_one, pow_orderOf_eq_one
-/
theorem exists_orderOf_eq_prime_pow_iff :
    (exists k : Nat, orderOf x = p ^ k) ↔ exists m : Nat, x ^ (p : Nat) ^ m = 1 :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩, fun ⟨_, hm⟩ => by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.elim).mp (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩⟩

@[simp]
/--
theorem `orderOf_neg_one` / 定理 `orderOf_neg_one`

English:
theorem orderOf_neg_one
  given: {R} [Ring R] [Nontrivial R]
  proof: by
  split_ifs with h
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h

中文:
定理 orderOf_neg_one
  条件: {R} [Ring R] [Nontrivial R]
  证明: by
  split_ifs with h
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h

Depends on / 依赖: neg_one_eq_one_iff, orderOf_eq_prime, orderOf_one, split_ifs
-/
theorem orderOf_neg_one {R} [Ring R] [Nontrivial R] :
    orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 := by
  split_ifs with h
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h

/--
lemma `CharP.orderOf_eq_two_iff` / 引理 `CharP.orderOf_eq_two_iff`

English:
lemma CharP.orderOf_eq_two_iff
  statement: {R} [Ring R] [Nontrivial R] [NoZeroDivisors R] (p : Nat)
  proof: by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h => hp ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))

中文:
引理 CharP.orderOf_eq_two_iff
  结论: {R} [Ring R] [Nontrivial R] [NoZeroDivisors R] (p : 自然数)
  证明: by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h => hp ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))

Depends on / 依赖: and_iff_left_iff_imp, and_not_self, false_or, ne_eq, neg_one_eq_one_iff, or_and_right, orderOf_eq_prime_iff, ringChar, ringChar.eq, sq_eq_one_iff
-/
lemma CharP.orderOf_eq_two_iff {R} [Ring R] [Nontrivial R] [NoZeroDivisors R] (p : Nat)
    (hp : p != 2) [CharP R p] {x : R} : orderOf x = 2 ↔ x = -1 := by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h => hp ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))

end PPrime

/-- The equivalence between `Fin (orderOf x)` and `Submonoid.powers x`, sending `i` to `x ^ i` -/
@[to_additive /-- The equivalence between `Fin (addOrderOf a)` and
`AddSubmonoid.multiples a`, sending `i` to `i • a` -/]
/--
Definition of `finEquivPowers` / `finEquivPowers` 的定义

English:
definition finEquivPowers
  signature: {x : G} (hx : IsOfFinOrder x)
  body: Equiv.ofBijective (fun n => ⟨x ^ (n : Nat), ⟨n, rfl⟩⟩) ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ ij =>
    Fin.ext (pow_injOn_Iio_orderOf h₁ h₂ (Subtype.mk_eq_mk.1 ij)), fun ⟨_, i, rfl⟩ =>
⟨⟨i % orderOf x, mod_lt _ hx.orderOf_pos⟩, Subtype.ext pow_mod_orderOf _ _⟩⟩

@[to_additive (attr := simp)]

中文:
定义 finEquivPowers
  签名: {x : G} (hx : IsOfFinOrder x)
  定义体: Equiv.ofBijective (fun n => ⟨x ^ (n : Nat), ⟨n, rfl⟩⟩) ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ ij =>
    Fin.ext (pow_injOn_Iio_orderOf h₁ h₂ (Subtype.mk_eq_mk.1 ij)), fun ⟨_, i, rfl⟩ =>
⟨⟨i % orderOf x, mod_lt _ hx.orderOf_pos⟩, Subtype.ext pow_mod_orderOf _ _⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.ofBijective, Fin.ext, Subtype, Subtype.ext, Subtype.mk_eq_mk, hx.orderOf_pos, mk_eq_mk, mod_lt, ofBijective, orderOf, orderOf_pos, pow_injOn_Iio_orderOf, pow_mod_orderOf
-/
noncomputable def finEquivPowers {x : G} (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ powers x :=
  Equiv.ofBijective (fun n => ⟨x ^ (n : Nat), ⟨n, rfl⟩⟩) ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ ij =>
    Fin.ext (pow_injOn_Iio_orderOf h₁ h₂ (Subtype.mk_eq_mk.1 ij)), fun ⟨_, i, rfl⟩ =>
⟨⟨i % orderOf x, mod_lt _ hx.orderOf_pos⟩, Subtype.ext pow_mod_orderOf _ _⟩⟩

@[to_additive (attr := simp)]
/--
lemma `finEquivPowers_apply` / 引理 `finEquivPowers_apply`

English:
lemma finEquivPowers_apply
  given: {x : G} (hx : IsOfFinOrder x) {n : Fin (orderOf x)}
  proof: rfl

中文:
引理 finEquivPowers_apply
  条件: {x : G} (hx : IsOfFinOrder x) {n : Fin (orderOf x)}
  证明: rfl
-/
lemma finEquivPowers_apply {x : G} (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
    finEquivPowers hx n = ⟨x ^ (n : Nat), n, rfl⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `finEquivPowers_symm_apply` / 引理 `finEquivPowers_symm_apply`

English:
lemma finEquivPowers_symm_apply
  given: {x : G} (hx : IsOfFinOrder x) (n : Nat)
  proof: by
  rw [Equiv.symm_apply_eq]; rw [finEquivPowers_apply]; rw [Subtype.mk_eq_mk]; rw [← pow_mod_orderOf]; rw [Fin.val_mk]

中文:
引理 finEquivPowers_symm_apply
  条件: {x : G} (hx : IsOfFinOrder x) (n : 自然数)
  证明: by
  rw [Equiv.symm_apply_eq]; rw [finEquivPowers_apply]; rw [Subtype.mk_eq_mk]; rw [← pow_mod_orderOf]; rw [Fin.val_mk]

Depends on / 依赖: Equiv.symm_apply_eq, Fin.val_mk, Subtype, Subtype.mk_eq_mk, finEquivPowers_apply, mk_eq_mk, pow_mod_orderOf, symm_apply_eq, val_mk
-/
lemma finEquivPowers_symm_apply {x : G} (hx : IsOfFinOrder x) (n : Nat) :
    (finEquivPowers hx).symm ⟨x ^ n, _, rfl⟩ = ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos⟩ := by
  rw [Equiv.symm_apply_eq]; rw [finEquivPowers_apply]; rw [Subtype.mk_eq_mk]; rw [← pow_mod_orderOf]; rw [Fin.val_mk]

variable {x n} (hx : IsOfFinOrder x)
include hx

@[to_additive]
/--
theorem `IsOfFinOrder.pow_eq_pow_iff_modEq` / 定理 `IsOfFinOrder.pow_eq_pow_iff_modEq`

English:
theorem IsOfFinOrder.pow_eq_pow_iff_modEq
  statement: x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
  proof: by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]; rw [(hx.isUnit.pow _).mul_eq_left]; rw [pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_left_cancel' _

中文:
定理 IsOfFinOrder.pow_eq_pow_iff_modEq
  结论: x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
  证明: by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]; rw [(hx.isUnit.pow _).mul_eq_left]; rw [pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_left_cancel' _

Depends on / 依赖: ModEq.comm, Nat.ModEq.add_left, Nat.ModEq.add_left_cancel, Nat.exists_eq_add_of_le, add_left, add_left_cancel, eq_comm, exists_eq_add_of_le, generalizing, hx.isUnit.pow, isUnit, le_of_not_ge, mul_eq_left, pow_add, pow_eq_one_iff_modEq
-/
theorem IsOfFinOrder.pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]; rw [(hx.isUnit.pow _).mul_eq_left]; rw [pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_left_cancel' _ h⟩

@[to_additive]
/--
lemma `IsOfFinOrder.pow_inj_mod` / 引理 `IsOfFinOrder.pow_inj_mod`

English:
lemma IsOfFinOrder.pow_inj_mod
  given: {n m : Nat}
  statement: x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
  proof: hx.pow_eq_pow_iff_modEq

中文:
引理 IsOfFinOrder.pow_inj_mod
  条件: {n m : 自然数}
  结论: x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
  证明: hx.pow_eq_pow_iff_modEq

Depends on / 依赖: hx.pow_eq_pow_iff_modEq, pow_eq_pow_iff_modEq
-/
lemma IsOfFinOrder.pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x :=
  hx.pow_eq_pow_iff_modEq

end Monoid

section CancelMonoid
variable [LeftCancelMonoid G] {x y : G} {a : G} {m n : Nat}

@[to_additive]
/--
theorem `pow_eq_pow_iff_modEq` / 定理 `pow_eq_pow_iff_modEq`

English:
theorem pow_eq_pow_iff_modEq
  statement: x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
  proof: by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← mul_one (x ^ m)]; rw [pow_add]; rw [mul_left_cancel_iff]; rw [pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_

中文:
定理 pow_eq_pow_iff_modEq
  结论: x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
  证明: by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← mul_one (x ^ m)]; rw [pow_add]; rw [mul_left_cancel_iff]; rw [pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_

Depends on / 依赖: ModEq.comm, Nat.ModEq.add_left, Nat.ModEq.add_left_cancel, Nat.exists_eq_add_of_le, add_left, add_left_cancel, eq_comm, exists_eq_add_of_le, generalizing, le_of_not_ge, mul_left_cancel_iff, mul_one, pow_add, pow_eq_one_iff_modEq
-/
theorem pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← mul_one (x ^ m)]; rw [pow_add]; rw [mul_left_cancel_iff]; rw [pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_left_cancel' _ h⟩

@[to_additive (attr := simp)]
/--
lemma `injective_pow_iff_not_isOfFinOrder` / 引理 `injective_pow_iff_not_isOfFinOrder`

English:
lemma injective_pow_iff_not_isOfFinOrder
  statement: Injective (fun n : Nat => x ^ n) ↔ ¬IsOfFinOrder x
  proof: by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, modEq_zero_iff] at hnm

@[to_additive]

中文:
引理 injective_pow_iff_not_isOfFinOrder
  结论: Injective (fun n : 自然数 => x ^ n) ↔ ¬IsOfFinOrder x
  证明: by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, modEq_zero_iff] at hnm

@[to_additive]

Depends on / 依赖: modEq_zero_iff, not_isOfFinOrder_of_injective_pow, orderOf_eq_zero_iff, orderOf_eq_zero_iff.mpr, pow_eq_pow_iff_modEq
-/
lemma injective_pow_iff_not_isOfFinOrder : Injective (fun n : Nat => x ^ n) ↔ ¬IsOfFinOrder x := by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, modEq_zero_iff] at hnm

@[to_additive]
/--
lemma `pow_inj_mod` / 引理 `pow_inj_mod`

English:
lemma pow_inj_mod
  given: {n m : Nat}
  statement: x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
  proof: pow_eq_pow_iff_modEq

@[to_additive]

中文:
引理 pow_inj_mod
  条件: {n m : 自然数}
  结论: x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
  证明: pow_eq_pow_iff_modEq

@[to_additive]

Depends on / 依赖: pow_eq_pow_iff_modEq
-/
lemma pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x := pow_eq_pow_iff_modEq

@[to_additive]
/--
theorem `pow_inj_iff_of_orderOf_eq_zero` / 定理 `pow_inj_iff_of_orderOf_eq_zero`

English:
theorem pow_inj_iff_of_orderOf_eq_zero
  given: (h : orderOf x = 0) {n m : Nat}
  statement: x ^ n = x ^ m ↔ n = m
  proof: by
  rw [pow_eq_pow_iff_modEq]; rw [h]; rw [modEq_zero_iff]

@[to_additive]

中文:
定理 pow_inj_iff_of_orderOf_eq_zero
  条件: (h : orderOf x = 0) {n m : 自然数}
  结论: x ^ n = x ^ m ↔ n = m
  证明: by
  rw [pow_eq_pow_iff_modEq]; rw [h]; rw [modEq_zero_iff]

@[to_additive]

Depends on / 依赖: modEq_zero_iff, pow_eq_pow_iff_modEq
-/
theorem pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : Nat} : x ^ n = x ^ m ↔ n = m := by
  rw [pow_eq_pow_iff_modEq]; rw [h]; rw [modEq_zero_iff]

@[to_additive]
/--
theorem `infinite_not_isOfFinOrder` / 定理 `infinite_not_isOfFinOrder`

English:
theorem infinite_not_isOfFinOrder
  given: {x : G} (h : ¬IsOfFinOrder x)
  proof: by
  let s := { n | 0 < n }.image fun n : Nat => x ^ n
  have hs : s subseteq { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos h

中文:
定理 infinite_not_isOfFinOrder
  条件: {x : G} (h : ¬IsOfFinOrder x)
  证明: by
  let s := { n | 0 < n }.image fun n : Nat => x ^ n
  have hs : s subseteq { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos h

Depends on / 依赖: Infinite, Injective, Ioi_infinite, IsOfFinOrder, Set.Ioi_infinite, Set.injOn_, Set.not_injOn_infinite_finite_image, contra, contrapose, injOn_, isOfFinOrder_iff_pow_eq_one, mul_pos, not_injOn_infinite_finite_image, pow_mul, s.Infinite, subseteq, this.mono
-/
theorem infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) :
    { y : G | ¬IsOfFinOrder y }.Infinite := by
  let s := { n | 0 < n }.image fun n : Nat => x ^ n
  have hs : s subseteq { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos hn hm, by rwa [pow_mul]⟩
  suffices s.Infinite by exact this.mono hs
  contrapose! h
  have : ¬Injective fun n : Nat => x ^ n := by
    have := Set.not_injOn_infinite_finite_image (Set.Ioi_infinite 0) h
    contrapose this
    exact Set.injOn_of_injective this
  rwa [injective_pow_iff_not_isOfFinOrder, Classical.not_not] at this

@[to_additive (attr := simp)]
/--
lemma `finite_powers` / 引理 `finite_powers`

English:
lemma finite_powers
  statement: (powers a : Set G).Finite ↔ IsOfFinOrder a
  proof: by
  refine ⟨fun h => ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => a ^ n)
    (fun n => by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  rw [← mul_left_cancel_iff (a := a ^ m)]; 

中文:
引理 finite_powers
  结论: (powers a : Set G).Finite ↔ IsOfFinOrder a
  证明: by
  refine ⟨fun h => ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => a ^ n)
    (fun n => by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  rw [← mul_left_cancel_iff (a := a ^ m)]; 

Depends on / 依赖: IsOfFinOrder, IsOfFinOrder.finite_powers, add_tsub_cancel_of_le, exists_lt_map_eq_of_forall_mem, finite_powers, h.exists_lt_map_eq_of_forall_mem, hmn.le, isOfFinOrder_iff_pow_eq_one, mem_powers_iff, mul_left_cancel_iff, mul_one, pow_add, tsub_pos_iff_lt
-/
lemma finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a := by
  refine ⟨fun h => ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => a ^ n)
    (fun n => by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  rw [← mul_left_cancel_iff (a := a ^ m)]; rw [← pow_add]; rw [add_tsub_cancel_of_le hmn.le]; rw [ha]; rw [mul_one]

@[to_additive (attr := simp)]
/--
lemma `infinite_powers` / 引理 `infinite_powers`

English:
lemma infinite_powers
  statement: (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a
  proof: finite_powers.not

中文:
引理 infinite_powers
  结论: (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a
  证明: finite_powers.not

Depends on / 依赖: finite_powers, finite_powers.not
-/
lemma infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a := finite_powers.not

/-- See also `orderOf_eq_card_powers`. -/
@[to_additive /-- See also `addOrder_eq_card_multiples`. -/]
/--
lemma `Nat.card_submonoidPowers` / 引理 `Nat.card_submonoidPowers`

English:
lemma Nat.card_submonoidPowers
  statement: Nat.card (powers a) = orderOf a
  proof: by
  by_cases ha : IsOfFinOrder a
· exact (Nat.card_congr (finEquivPowers ha).symm).trans by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha]; rw [Nat.card_eq_zero_of_infinite]

中文:
引理 Nat.card_submonoidPowers
  结论: 自然数.card (powers a) = orderOf a
  证明: by
  by_cases ha : IsOfFinOrder a
· exact (Nat.card_congr (finEquivPowers ha).symm).trans by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha]; rw [Nat.card_eq_zero_of_infinite]

Depends on / 依赖: IsOfFinOrder, Nat.card_congr, Nat.card_eq_zero_of_infinite, card_congr, card_eq_zero_of_infinite, finEquivPowers, infinite_powers, orderOf_eq_zero, to_subtype
-/
lemma Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a := by
  by_cases ha : IsOfFinOrder a
· exact (Nat.card_congr (finEquivPowers ha).symm).trans by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha]; rw [Nat.card_eq_zero_of_infinite]

end CancelMonoid

section RightCancelMonoid
variable [RightCancelMonoid G] {x y : G} {a : G} {m n : Nat}

namespace RightCancelMonoid

@[to_additive]
/--
theorem `pow_eq_pow_iff_modEq` / 定理 `pow_eq_pow_iff_modEq`

English:
theorem pow_eq_pow_iff_modEq
  statement: x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
  proof: by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, Nat.ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  constructor
  · intro h
    have hk : x ^ k = 1 := by
      apply (mul_right_cancel_iff (a := x ^ m)).1
      calc
        x ^ k * x ^ m = x ^ (k + m) 

中文:
定理 pow_eq_pow_iff_modEq
  结论: x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
  证明: by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, Nat.ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  constructor
  · intro h
    have hk : x ^ k = 1 := by
      apply (mul_right_cancel_iff (a := x ^ m)).1
      calc
        x ^ k * x ^ m = x ^ (k + m) 

Depends on / 依赖: Nat.ModEq.add_left, Nat.ModEq.comm, Nat.add_comm, Nat.exists_eq_add_of_le, add_comm, add_left, eq_comm, exists_eq_add_of_le, generalizing, le_of_not_ge, mul_right_cancel_iff, pow_add, pow_eq_one_iff_m, pow_eq_one_iff_modEq
-/
theorem pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m <= n generalizing m n
  · rw [eq_comm, Nat.ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  constructor
  · intro h
    have hk : x ^ k = 1 := by
      apply (mul_right_cancel_iff (a := x ^ m)).1
      calc
        x ^ k * x ^ m = x ^ (k + m) := (pow_add _ _ _).symm
        _ = x ^ (m + k) := by simp [Nat.add_comm]
        _ = x ^ m := h
        _ = 1 * x ^ m := by simp
    exact by simpa using Nat.ModEq.add_left m (pow_eq_one_iff_modEq.1 hk)
  · intro h
    have hk : x ^ k = 1 := by
      apply pow_eq_one_iff_modEq.2
      exact Nat.ModEq.add_left_cancel' m (by simpa using h)
    calc
      x ^ (m + k) = x ^ m * x ^ k := by rw [pow_add]
      _ = x ^ m := by simp [hk]

@[to_additive (attr := simp)]
/--
lemma `injective_pow_iff_not_isOfFinOrder` / 引理 `injective_pow_iff_not_isOfFinOrder`

English:
lemma injective_pow_iff_not_isOfFinOrder
  statement: Function.Injective (fun n : Nat => x ^ n) ↔
  proof: by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, Nat.modEq_zero_iff] at hnm

@[to_additive]

中文:
引理 injective_pow_iff_not_isOfFinOrder
  结论: Function.Injective (fun n : 自然数 => x ^ n) ↔
  证明: by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, Nat.modEq_zero_iff] at hnm

@[to_additive]

Depends on / 依赖: Nat.modEq_zero_iff, modEq_zero_iff, not_isOfFinOrder_of_injective_pow, orderOf_eq_zero_iff, orderOf_eq_zero_iff.mpr, pow_eq_pow_iff_modEq
-/
lemma injective_pow_iff_not_isOfFinOrder : Function.Injective (fun n : Nat => x ^ n) ↔
    ¬IsOfFinOrder x := by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, Nat.modEq_zero_iff] at hnm

@[to_additive]
/--
lemma `pow_inj_mod` / 引理 `pow_inj_mod`

English:
lemma pow_inj_mod
  given: {n m : Nat}
  statement: x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
  proof: pow_eq_pow_iff_modEq

@[to_additive]

中文:
引理 pow_inj_mod
  条件: {n m : 自然数}
  结论: x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
  证明: pow_eq_pow_iff_modEq

@[to_additive]

Depends on / 依赖: pow_eq_pow_iff_modEq
-/
lemma pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x :=
  pow_eq_pow_iff_modEq

@[to_additive]
/--
theorem `pow_inj_iff_of_orderOf_eq_zero` / 定理 `pow_inj_iff_of_orderOf_eq_zero`

English:
theorem pow_inj_iff_of_orderOf_eq_zero
  given: (h : orderOf x = 0) {n m : Nat}
  statement: x ^ n = x ^ m ↔ n = m
  proof: by
  rw [pow_eq_pow_iff_modEq]; rw [h]; rw [Nat.modEq_zero_iff]

@[to_additive]

中文:
定理 pow_inj_iff_of_orderOf_eq_zero
  条件: (h : orderOf x = 0) {n m : 自然数}
  结论: x ^ n = x ^ m ↔ n = m
  证明: by
  rw [pow_eq_pow_iff_modEq]; rw [h]; rw [Nat.modEq_zero_iff]

@[to_additive]

Depends on / 依赖: Nat.modEq_zero_iff, modEq_zero_iff, pow_eq_pow_iff_modEq
-/
theorem pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : Nat} : x ^ n = x ^ m ↔ n = m := by
  rw [pow_eq_pow_iff_modEq]; rw [h]; rw [Nat.modEq_zero_iff]

@[to_additive]
/--
theorem `infinite_not_isOfFinOrder` / 定理 `infinite_not_isOfFinOrder`

English:
theorem infinite_not_isOfFinOrder
  given: {x : G} (h : ¬IsOfFinOrder x)
  proof: by
  let s := { n | 0 < n }.image fun n : Nat => x ^ n
  have hs : s subseteq { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos h

中文:
定理 infinite_not_isOfFinOrder
  条件: {x : G} (h : ¬IsOfFinOrder x)
  证明: by
  let s := { n | 0 < n }.image fun n : Nat => x ^ n
  have hs : s subseteq { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos h

Depends on / 依赖: Function, Function.Injective, Infinite, Injective, Ioi_infinite, IsOfFinOrder, Set.Ioi_infinite, Set.not_injOn_infinite_finite_image, contra, contrapose, isOfFinOrder_iff_pow_eq_one, mul_pos, not_injOn_infinite_finite_image, pow_mul, s.Infinite, subseteq, this.mono
-/
theorem infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) :
    { y : G | ¬IsOfFinOrder y }.Infinite := by
  let s := { n | 0 < n }.image fun n : Nat => x ^ n
  have hs : s subseteq { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos hn hm, by rwa [pow_mul]⟩
  suffices s.Infinite by exact this.mono hs
  contrapose! h
  have : ¬Function.Injective fun n : Nat => x ^ n := by
    have := Set.not_injOn_infinite_finite_image (Set.Ioi_infinite 0) h
    contrapose this
    exact Set.injOn_of_injective this
  rwa [injective_pow_iff_not_isOfFinOrder, Classical.not_not] at this

@[to_additive (attr := simp)]
/--
lemma `finite_powers` / 引理 `finite_powers`

English:
lemma finite_powers
  statement: (powers a : Set G).Finite ↔ IsOfFinOrder a
  proof: by
  refine ⟨fun h => ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => a ^ n)
    (fun n => by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  apply (mul_right_cancel_iff (a := a ^ m))

中文:
引理 finite_powers
  结论: (powers a : Set G).Finite ↔ IsOfFinOrder a
  证明: by
  refine ⟨fun h => ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => a ^ n)
    (fun n => by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  apply (mul_right_cancel_iff (a := a ^ m))

Depends on / 依赖: IsOfFinOrder, IsOfFinOrder.finite_powers, exists_lt_map_eq_of_forall_mem, finite_powers, h.exists_lt_map_eq_of_forall_mem, ha.symm, hmn.le, isOfFinOrder_iff_pow_eq_one, mem_powers_iff, mul_right_cancel_iff, pow_add, tsub_add_cancel_of_le, tsub_pos_iff_lt
-/
lemma finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a := by
  refine ⟨fun h => ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : Nat => a ^ n)
    (fun n => by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  apply (mul_right_cancel_iff (a := a ^ m)).1
  calc
    a ^ (n - m) * a ^ m = a ^ (n - m + m) := (pow_add _ _ _).symm
    _ = a ^ n := by simp [tsub_add_cancel_of_le hmn.le]
    _ = a ^ m := ha.symm
    _ = 1 * a ^ m := by simp

@[to_additive (attr := simp)]
/--
lemma `infinite_powers` / 引理 `infinite_powers`

English:
lemma infinite_powers
  statement: (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a
  proof: finite_powers.not

中文:
引理 infinite_powers
  结论: (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a
  证明: finite_powers.not

Depends on / 依赖: finite_powers, finite_powers.not
-/
lemma infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a := finite_powers.not

/-- See also `orderOf_eq_card_powers`. -/
@[to_additive /-- See also `addOrder_eq_card_multiples`. -/]
/--
lemma `Nat.card_submonoidPowers` / 引理 `Nat.card_submonoidPowers`

English:
lemma Nat.card_submonoidPowers
  statement: Nat.card (powers a) = orderOf a
  proof: by
  by_cases ha : IsOfFinOrder a
· exact (Nat.card_congr (finEquivPowers ha).symm).trans by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha]; rw [Nat.card_eq_zero_of_infinite]

中文:
引理 Nat.card_submonoidPowers
  结论: 自然数.card (powers a) = orderOf a
  证明: by
  by_cases ha : IsOfFinOrder a
· exact (Nat.card_congr (finEquivPowers ha).symm).trans by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha]; rw [Nat.card_eq_zero_of_infinite]
-/
lemma Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a := by
  by_cases ha : IsOfFinOrder a
· exact (Nat.card_congr (finEquivPowers ha).symm).trans by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha]; rw [Nat.card_eq_zero_of_infinite]

end RightCancelMonoid

end RightCancelMonoid

section Group

variable [Group G] {x y : G} {i : Int}

/-- Inverses of elements of finite order have finite order. -/
@[to_additive (attr := simp) /-- Inverses of elements of finite additive order
have finite additive order. -/]
/--
theorem `isOfFinOrder_inv_iff` / 定理 `isOfFinOrder_inv_iff`

English:
theorem isOfFinOrder_inv_iff
  given: {x : G}
  statement: IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x
  proof: by
  simp [isOfFinOrder_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.of_inv, IsOfFinOrder.inv⟩ := isOfFinOrder_inv_iff

@[to_additive]

中文:
定理 isOfFinOrder_inv_iff
  条件: {x : G}
  结论: IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x
  证明: by
  simp [isOfFinOrder_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.of_inv, IsOfFinOrder.inv⟩ := isOfFinOrder_inv_iff

@[to_additive]

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one
-/
theorem isOfFinOrder_inv_iff {x : G} : IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x := by
  simp [isOfFinOrder_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.of_inv, IsOfFinOrder.inv⟩ := isOfFinOrder_inv_iff

@[to_additive]
/--
theorem `orderOf_dvd_iff_zpow_eq_one` / 定理 `orderOf_dvd_iff_zpow_eq_one`

English:
theorem orderOf_dvd_iff_zpow_eq_one
  statement: (orderOf x : Int) ∣ i ↔ x ^ i = 1
  proof: by
  rcases Int.eq_nat_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast]
  · rw [dvd_neg, Int.natCast_dvd_natCast, zpow_neg, inv_eq_one, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one]

@[to_additive (attr := simp)]

中文:
定理 orderOf_dvd_iff_zpow_eq_one
  结论: (orderOf x : 整数) ∣ i ↔ x ^ i = 1
  证明: by
  rcases Int.eq_nat_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast]
  · rw [dvd_neg, Int.natCast_dvd_natCast, zpow_neg, inv_eq_one, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one]

@[to_additive (attr := simp)]

Depends on / 依赖: Int.eq_nat_or_neg, Int.natCast_dvd_natCast, dvd_neg, eq_nat_or_neg, inv_eq_one, natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast, zpow_neg
-/
theorem orderOf_dvd_iff_zpow_eq_one : (orderOf x : Int) ∣ i ↔ x ^ i = 1 := by
  rcases Int.eq_nat_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast]
  · rw [dvd_neg, Int.natCast_dvd_natCast, zpow_neg, inv_eq_one, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one]

@[to_additive (attr := simp)]
/--
theorem `orderOf_inv` / 定理 `orderOf_inv`

English:
theorem orderOf_inv
  given: (x : G)
  statement: orderOf x⁻¹ = orderOf x
  proof: by simp [orderOf_eq_orderOf_iff]

@[to_additive]

中文:
定理 orderOf_inv
  条件: (x : G)
  结论: orderOf x⁻¹ = orderOf x
  证明: by simp [orderOf_eq_orderOf_iff]

@[to_additive]

Depends on / 依赖: orderOf_eq_orderOf_iff
-/
theorem orderOf_inv (x : G) : orderOf x⁻¹ = orderOf x := by simp [orderOf_eq_orderOf_iff]

@[to_additive]
/--
theorem `orderOf_dvd_sub_iff_zpow_eq_zpow` / 定理 `orderOf_dvd_sub_iff_zpow_eq_zpow`

English:
theorem orderOf_dvd_sub_iff_zpow_eq_zpow
  given: {a b : Int}
  statement: (orderOf x : Int) ∣ a - b ↔ x ^ a = x ^ b
  proof: by
  rw [orderOf_dvd_iff_zpow_eq_one]; rw [zpow_sub]; rw [mul_inv_eq_one]

中文:
定理 orderOf_dvd_sub_iff_zpow_eq_zpow
  条件: {a b : 整数}
  结论: (orderOf x : 整数) ∣ a - b ↔ x ^ a = x ^ b
  证明: by
  rw [orderOf_dvd_iff_zpow_eq_one]; rw [zpow_sub]; rw [mul_inv_eq_one]

Depends on / 依赖: mul_inv_eq_one, orderOf_dvd_iff_zpow_eq_one, zpow_sub
-/
theorem orderOf_dvd_sub_iff_zpow_eq_zpow {a b : Int} : (orderOf x : Int) ∣ a - b ↔ x ^ a = x ^ b := by
  rw [orderOf_dvd_iff_zpow_eq_one]; rw [zpow_sub]; rw [mul_inv_eq_one]

namespace Subgroup
variable {H : Subgroup G}

@[to_additive (attr := norm_cast)]
/--
lemma `orderOf_coe` / 引理 `orderOf_coe`

English:
lemma orderOf_coe
  given: (a : H)
  statement: orderOf (a : G) = orderOf a
  proof: orderOf_injective H.subtype Subtype.coe_injective _

@[to_additive (attr := simp)]

中文:
引理 orderOf_coe
  条件: (a : H)
  结论: orderOf (a : G) = orderOf a
  证明: orderOf_injective H.subtype Subtype.coe_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: H.subtype, Subtype, Subtype.coe_injective, coe_injective, orderOf_injective, subtype
-/
lemma orderOf_coe (a : H) : orderOf (a : G) = orderOf a :=
  orderOf_injective H.subtype Subtype.coe_injective _

@[to_additive (attr := simp)]
/--
lemma `orderOf_mk` / 引理 `orderOf_mk`

English:
lemma orderOf_mk
  given: (a : G) (ha)
  statement: orderOf (⟨a, ha⟩ : H) = orderOf a
  proof: (orderOf_coe _).symm

中文:
引理 orderOf_mk
  条件: (a : G) (ha)
  结论: orderOf (⟨a, ha⟩ : H) = orderOf a
  证明: (orderOf_coe _).symm

Depends on / 依赖: orderOf_coe
-/
lemma orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = orderOf a := (orderOf_coe _).symm

end Subgroup

@[to_additive mod_addOrderOf_zsmul]
/--
lemma `zpow_mod_orderOf` / 引理 `zpow_mod_orderOf`

English:
lemma zpow_mod_orderOf
  given: (x : G) (z : Int)
  statement: x ^ (z % (orderOf x : Int)) = x ^ z
  proof: calc
    x ^ (z % (orderOf x : Int)) = x ^ (z % orderOf x + orderOf x * (z / orderOf x) : Int) := by
        simp [zpow_add, zpow_mul, pow_orderOf_eq_one]
    _ = x ^ z := by rw [Int.emod_add_mul_ediv]

@[to_additive (attr := simp) zsmul_smul_addOrderOf]

中文:
引理 zpow_mod_orderOf
  条件: (x : G) (z : 整数)
  结论: x ^ (z % (orderOf x : 整数)) = x ^ z
  证明: calc
    x ^ (z % (orderOf x : Int)) = x ^ (z % orderOf x + orderOf x * (z / orderOf x) : Int) := by
        simp [zpow_add, zpow_mul, pow_orderOf_eq_one]
    _ = x ^ z := by rw [Int.emod_add_mul_ediv]

@[to_additive (attr := simp) zsmul_smul_addOrderOf]

Depends on / 依赖: Int.emod_add_mul_ediv, emod_add_mul_ediv, orderOf, pow_orderOf_eq_one, zpow_add, zpow_mul
-/
lemma zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf x : Int)) = x ^ z :=
  calc
    x ^ (z % (orderOf x : Int)) = x ^ (z % orderOf x + orderOf x * (z / orderOf x) : Int) := by
        simp [zpow_add, zpow_mul, pow_orderOf_eq_one]
    _ = x ^ z := by rw [Int.emod_add_mul_ediv]

@[to_additive (attr := simp) zsmul_smul_addOrderOf]
/--
theorem `zpow_pow_orderOf` / 定理 `zpow_pow_orderOf`

English:
theorem zpow_pow_orderOf
  statement: (x ^ i) ^ orderOf x = 1
  proof: by
  by_cases h : IsOfFinOrder x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [orderOf_eq_zero h, _root_.pow_zero]

@[to_additive]

中文:
定理 zpow_pow_orderOf
  结论: (x ^ i) ^ orderOf x = 1
  证明: by
  by_cases h : IsOfFinOrder x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [orderOf_eq_zero h, _root_.pow_zero]

@[to_additive]

Depends on / 依赖: IsOfFinOrder, _root_, _root_.pow_zero, mul_comm, one_zpow, orderOf_eq_zero, pow_orderOf_eq_one, pow_zero, zpow_mul, zpow_natCast
-/
theorem zpow_pow_orderOf : (x ^ i) ^ orderOf x = 1 := by
  by_cases h : IsOfFinOrder x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [orderOf_eq_zero h, _root_.pow_zero]

@[to_additive]
/--
theorem `IsOfFinOrder.zpow` / 定理 `IsOfFinOrder.zpow`

English:
theorem IsOfFinOrder.zpow
  given: (h : IsOfFinOrder x) {i : Int}
  statement: IsOfFinOrder (x ^ i)
  proof: isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf x, h.orderOf_pos, zpow_pow_orderOf⟩

@[to_additive]

中文:
定理 IsOfFinOrder.zpow
  条件: (h : IsOfFinOrder x) {i : 整数}
  结论: IsOfFinOrder (x ^ i)
  证明: isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf x, h.orderOf_pos, zpow_pow_orderOf⟩

@[to_additive]

Depends on / 依赖: h.orderOf_pos, isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr, orderOf, orderOf_pos, zpow_pow_orderOf
-/
theorem IsOfFinOrder.zpow (h : IsOfFinOrder x) {i : Int} : IsOfFinOrder (x ^ i) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf x, h.orderOf_pos, zpow_pow_orderOf⟩

@[to_additive]
/--
theorem `IsOfFinOrder.of_mem_zpowers` / 定理 `IsOfFinOrder.of_mem_zpowers`

English:
theorem IsOfFinOrder.of_mem_zpowers
  given: (h : IsOfFinOrder x) (h' : y in Subgroup.zpowers x)
  proof: by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h'
  exact h.zpow

@[to_additive]

中文:
定理 IsOfFinOrder.of_mem_zpowers
  条件: (h : IsOfFinOrder x) (h' : y in Subgroup.zpowers x)
  证明: by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h'
  exact h.zpow

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_zpowers_iff.mp, h.zpow, mem_zpowers_iff
-/
theorem IsOfFinOrder.of_mem_zpowers (h : IsOfFinOrder x) (h' : y in Subgroup.zpowers x) :
    IsOfFinOrder y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h'
  exact h.zpow

@[to_additive]
/--
theorem `orderOf_dvd_of_mem_zpowers` / 定理 `orderOf_dvd_of_mem_zpowers`

English:
theorem orderOf_dvd_of_mem_zpowers
  given: (h : y in Subgroup.zpowers x)
  statement: orderOf y ∣ orderOf x
  proof: by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zpow_pow_orderOf

中文:
定理 orderOf_dvd_of_mem_zpowers
  条件: (h : y in Subgroup.zpowers x)
  结论: orderOf y ∣ orderOf x
  证明: by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zpow_pow_orderOf

Depends on / 依赖: Subgroup, Subgroup.mem_zpowers_iff.mp, mem_zpowers_iff, orderOf_dvd_iff_pow_eq_one, zpow_pow_orderOf
-/
theorem orderOf_dvd_of_mem_zpowers (h : y in Subgroup.zpowers x) : orderOf y ∣ orderOf x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zpow_pow_orderOf

/--
theorem `smul_eq_self_of_mem_zpowers` / 定理 `smul_eq_self_of_mem_zpowers`

English:
theorem smul_eq_self_of_mem_zpowers
  statement: {α : Type*} [MulAction G α] (hx : x in Subgroup.zpowers y)
  proof: by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAction.toPerm_apply]; rw [← MulAction.toPermHom_apply]; rw [map_zpow _ y k]; rw [MulAction.toPermHom_apply]
  exact Function.IsFixedPt.perm_zpow (by exact hs) k -- Porting note: help elab'n with `by exact`

中文:
定理 smul_eq_self_of_mem_zpowers
  结论: {α : 类型} [MulAction G α] (hx : x in Subgroup.zpowers y)
  证明: by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAction.toPerm_apply]; rw [← MulAction.toPermHom_apply]; rw [map_zpow _ y k]; rw [MulAction.toPermHom_apply]
  exact Function.IsFixedPt.perm_zpow (by exact hs) k -- Porting note: help elab'n with `by exact`

Depends on / 依赖: Function, Function.IsFixedPt.perm_zpow, IsFixedPt, MulAction, MulAction.toPermHom_apply, MulAction.toPerm_apply, Porting, Subgroup, Subgroup.mem_zpowers_iff.mp, map_zpow, mem_zpowers_iff, perm_zpow, toPermHom_apply, toPerm_apply
-/
theorem smul_eq_self_of_mem_zpowers {α : Type*} [MulAction G α] (hx : x in Subgroup.zpowers y)
    {a : α} (hs : y • a = a) : x • a = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAction.toPerm_apply]; rw [← MulAction.toPermHom_apply]; rw [map_zpow _ y k]; rw [MulAction.toPermHom_apply]
  exact Function.IsFixedPt.perm_zpow (by exact hs) k -- Porting note: help elab'n with `by exact`

/--
theorem `vadd_eq_self_of_mem_zmultiples` / 定理 `vadd_eq_self_of_mem_zmultiples`

English:
theorem vadd_eq_self_of_mem_zmultiples
  statement: {G : Type*} [AddGroup G] {x y : G} {α : Type*}
  proof: @smul_eq_self_of_mem_zpowers (Multiplicative G) _ _ _ α _ hx a hs

中文:
定理 vadd_eq_self_of_mem_zmultiples
  结论: {G : 类型} [AddGroup G] {x y : G} {α : 类型}
  证明: @smul_eq_self_of_mem_zpowers (Multiplicative G) _ _ _ α _ hx a hs

Depends on / 依赖: Multiplicative, smul_eq_self_of_mem_zpowers
-/
theorem vadd_eq_self_of_mem_zmultiples {G : Type*} [AddGroup G] {x y : G} {α : Type*}
    [AddAction G α] (hx : x in AddSubgroup.zmultiples y) {a : α} (hs : y +ᵥ a = a) : x +ᵥ a = a :=
  @smul_eq_self_of_mem_zpowers (Multiplicative G) _ _ _ α _ hx a hs

attribute [to_additive existing] smul_eq_self_of_mem_zpowers

@[to_additive]
/--
lemma `IsOfFinOrder.mem_powers_iff_mem_zpowers` / 引理 `IsOfFinOrder.mem_powers_iff_mem_zpowers`

English:
lemma IsOfFinOrder.mem_powers_iff_mem_zpowers
  given: (hx : IsOfFinOrder x)
  proof: ⟨fun ⟨n, hn⟩ => ⟨n, by simp_all⟩, fun ⟨i, hi⟩ => ⟨(i % orderOf x).natAbs, by
    dsimp only
    rwa [← zpow_natCast, Int.natAbs_of_nonneg <| Int.emod_nonneg _ <|
Int.natCast_ne_zero_iff_pos.2 hx.orderOf_pos, zpow_mod_orderOf]⟩⟩

@[to_additive]

中文:
引理 IsOfFinOrder.mem_powers_iff_mem_zpowers
  条件: (hx : IsOfFinOrder x)
  证明: ⟨fun ⟨n, hn⟩ => ⟨n, by simp_all⟩, fun ⟨i, hi⟩ => ⟨(i % orderOf x).natAbs, by
    dsimp only
    rwa [← zpow_natCast, Int.natAbs_of_nonneg <| Int.emod_nonneg _ <|
Int.natCast_ne_zero_iff_pos.2 hx.orderOf_pos, zpow_mod_orderOf]⟩⟩

@[to_additive]

Depends on / 依赖: Int.emod_nonneg, Int.natAbs_of_nonneg, Int.natCast_ne_zero_iff_pos, emod_nonneg, hx.orderOf_pos, natAbs, natAbs_of_nonneg, natCast_ne_zero_iff_pos, orderOf, orderOf_pos, zpow_mod_orderOf, zpow_natCast
-/
lemma IsOfFinOrder.mem_powers_iff_mem_zpowers (hx : IsOfFinOrder x) :
    y in powers x ↔ y in zpowers x :=
  ⟨fun ⟨n, hn⟩ => ⟨n, by simp_all⟩, fun ⟨i, hi⟩ => ⟨(i % orderOf x).natAbs, by
    dsimp only
    rwa [← zpow_natCast, Int.natAbs_of_nonneg <| Int.emod_nonneg _ <|
Int.natCast_ne_zero_iff_pos.2 hx.orderOf_pos, zpow_mod_orderOf]⟩⟩

@[to_additive]
/--
lemma `IsOfFinOrder.powers_eq_zpowers` / 引理 `IsOfFinOrder.powers_eq_zpowers`

English:
lemma IsOfFinOrder.powers_eq_zpowers
  given: (hx : IsOfFinOrder x)
  statement: (powers x : Set G) = zpowers x
  proof: Set.ext fun _ => hx.mem_powers_iff_mem_zpowers

@[to_additive]

中文:
引理 IsOfFinOrder.powers_eq_zpowers
  条件: (hx : IsOfFinOrder x)
  结论: (powers x : Set G) = zpowers x
  证明: Set.ext fun _ => hx.mem_powers_iff_mem_zpowers

@[to_additive]

Depends on / 依赖: Set.ext, hx.mem_powers_iff_mem_zpowers, mem_powers_iff_mem_zpowers
-/
lemma IsOfFinOrder.powers_eq_zpowers (hx : IsOfFinOrder x) : (powers x : Set G) = zpowers x :=
  Set.ext fun _ => hx.mem_powers_iff_mem_zpowers

@[to_additive]
/--
lemma `IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf` / 引理 `IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf`

English:
lemma IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
  given: [DecidableEq G] (hx : IsOfFinOrder x)
  proof: hx.mem_powers_iff_mem_zpowers.symm.trans hx.mem_powers_iff_mem_range_orderOf

中文:
引理 IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
  条件: [DecidableEq G] (hx : IsOfFinOrder x)
  证明: hx.mem_powers_iff_mem_zpowers.symm.trans hx.mem_powers_iff_mem_range_orderOf

Depends on / 依赖: hx.mem_powers_iff_mem_range_orderOf, hx.mem_powers_iff_mem_zpowers.symm.trans, mem_powers_iff_mem_range_orderOf, mem_powers_iff_mem_zpowers
-/
lemma IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) :
    y in zpowers x ↔ y in (Finset.range (orderOf x)).image (x ^ ·) :=
  hx.mem_powers_iff_mem_zpowers.symm.trans hx.mem_powers_iff_mem_range_orderOf

/-- See `Subgroup.closure_toSubmonoid_of_finite` for a version for finite groups. -/
@[to_additive
/-- See `AddSubgroup.closure_toAddSubmonoid_of_finite` for a version for finite additive groups. -/]
/--
lemma `Subgroup.closure_toSubmonoid_of_isOfFinOrder` / 引理 `Subgroup.closure_toSubmonoid_of_isOfFinOrder`

English:
lemma Subgroup.closure_toSubmonoid_of_isOfFinOrder
  given: {s : Set G} (hs : forall x in s, IsOfFinOrder x)
  proof: by
  refine le_antisymm ?_ (le_closure_toSubmonoid s)
  rw [closure_toSubmonoid]
refine Submonoid.closure_le.mpr Set.union_subset Submonoid.subset_closure
    fun x (hx : x⁻¹ in s) => ?_
  apply Submonoid.powers_le.mpr (Submonoid.subset_closure hx)
  simp [(hs _ hx).mem_powers_iff_mem_zpowers]

中文:
引理 Subgroup.closure_toSubmonoid_of_isOfFinOrder
  条件: {s : Set G} (hs : 对任意 x in s, IsOfFinOrder x)
  证明: by
  refine le_antisymm ?_ (le_closure_toSubmonoid s)
  rw [closure_toSubmonoid]
refine Submonoid.closure_le.mpr Set.union_subset Submonoid.subset_closure
    fun x (hx : x⁻¹ in s) => ?_
  apply Submonoid.powers_le.mpr (Submonoid.subset_closure hx)
  simp [(hs _ hx).mem_powers_iff_mem_zpowers]

Depends on / 依赖: Set.union_subset, Submonoid, Submonoid.closure_le.mpr, Submonoid.powers_le.mpr, Submonoid.subset_closure, closure_le, closure_toSubmonoid, le_antisymm, le_closure_toSubmonoid, mem_powers_iff_mem_zpowers, powers_le, subset_closure, union_subset
-/
lemma Subgroup.closure_toSubmonoid_of_isOfFinOrder {s : Set G} (hs : forall x in s, IsOfFinOrder x) :
    (closure s).toSubmonoid = Submonoid.closure s := by
  refine le_antisymm ?_ (le_closure_toSubmonoid s)
  rw [closure_toSubmonoid]
refine Submonoid.closure_le.mpr Set.union_subset Submonoid.subset_closure
    fun x (hx : x⁻¹ in s) => ?_
  apply Submonoid.powers_le.mpr (Submonoid.subset_closure hx)
  simp [(hs _ hx).mem_powers_iff_mem_zpowers]

/-- The equivalence between `Fin (orderOf x)` and `Subgroup.zpowers x`, sending `i` to `x ^ i`. -/
@[to_additive /-- The equivalence between `Fin (addOrderOf a)` and
`Subgroup.zmultiples a`, sending `i` to `i • a`. -/]
/--
Definition of `finEquivZPowers` / `finEquivZPowers` 的定义

English:
definition finEquivZPowers
  signature: (hx : IsOfFinOrder x)
  body: (finEquivPowers hx).trans Equiv.setCongr hx.powers_eq_zpowers

@[to_additive]

中文:
定义 finEquivZPowers
  签名: (hx : IsOfFinOrder x)
  定义体: (finEquivPowers hx).trans Equiv.setCongr hx.powers_eq_zpowers

@[to_additive]

Depends on / 依赖: Equiv.setCongr, finEquivPowers, hx.powers_eq_zpowers, powers_eq_zpowers, setCongr
-/
noncomputable def finEquivZPowers (hx : IsOfFinOrder x) :
    Fin (orderOf x) ≃ zpowers x :=
(finEquivPowers hx).trans Equiv.setCongr hx.powers_eq_zpowers

@[to_additive]
/--
lemma `finEquivZPowers_apply` / 引理 `finEquivZPowers_apply`

English:
lemma finEquivZPowers_apply
  given: (hx : IsOfFinOrder x) {n : Fin (orderOf x)}
  proof: rfl

@[to_additive]

中文:
引理 finEquivZPowers_apply
  条件: (hx : IsOfFinOrder x) {n : Fin (orderOf x)}
  证明: rfl

@[to_additive]
-/
lemma finEquivZPowers_apply (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
    finEquivZPowers hx n = ⟨x ^ (n : Nat), n, zpow_natCast x n⟩ := rfl

@[to_additive]
/--
lemma `finEquivZPowers_symm_apply` / 引理 `finEquivZPowers_symm_apply`

English:
lemma finEquivZPowers_symm_apply
  given: (hx : IsOfFinOrder x) (n : Nat)
  proof: by
  rw [finEquivZPowers]; rw [Equiv.symm_trans_apply]; exact finEquivPowers_symm_apply _ n

@[to_additive]

中文:
引理 finEquivZPowers_symm_apply
  条件: (hx : IsOfFinOrder x) (n : 自然数)
  证明: by
  rw [finEquivZPowers]; rw [Equiv.symm_trans_apply]; exact finEquivPowers_symm_apply _ n

@[to_additive]

Depends on / 依赖: Equiv.symm_trans_apply, finEquivPowers_symm_apply, finEquivZPowers, symm_trans_apply
-/
lemma finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (n : Nat) :
    (finEquivZPowers hx).symm ⟨x ^ n, ⟨n, by simp⟩⟩ =
    ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos⟩ := by
  rw [finEquivZPowers]; rw [Equiv.symm_trans_apply]; exact finEquivPowers_symm_apply _ n

@[to_additive]
/--
lemma `pow_finEquivZPowers_symm_apply` / 引理 `pow_finEquivZPowers_symm_apply`

English:
lemma pow_finEquivZPowers_symm_apply
  given: (hx : IsOfFinOrder x) (a : Subgroup.zpowers x)
  proof: by
  simpa only [finEquivZPowers_apply] using
    congr_arg Subtype.val ((finEquivZPowers hx).apply_symm_apply a)

中文:
引理 pow_finEquivZPowers_symm_apply
  条件: (hx : IsOfFinOrder x) (a : Subgroup.zpowers x)
  证明: by
  simpa only [finEquivZPowers_apply] using
    congr_arg Subtype.val ((finEquivZPowers hx).apply_symm_apply a)

Depends on / 依赖: Subtype, Subtype.val, apply_symm_apply, congr_arg, finEquivZPowers, finEquivZPowers_apply
-/
lemma pow_finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (a : Subgroup.zpowers x) :
    x ^ ((finEquivZPowers hx).symm a : Nat) = a := by
  simpa only [finEquivZPowers_apply] using
    congr_arg Subtype.val ((finEquivZPowers hx).apply_symm_apply a)

end Group

section CommMonoid

variable [CommMonoid G] {x y : G}

/-- Elements of finite order are closed under multiplication. -/
@[to_additive /-- Elements of finite additive order are closed under addition. -/]
/--
theorem `IsOfFinOrder.mul` / 定理 `IsOfFinOrder.mul`

English:
theorem IsOfFinOrder.mul
  given: (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
  statement: IsOfFinOrder (x * y)
  proof: (Commute.all x y).isOfFinOrder_mul hx hy

中文:
定理 IsOfFinOrder.mul
  条件: (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
  结论: IsOfFinOrder (x * y)
  证明: (Commute.all x y).isOfFinOrder_mul hx hy

Depends on / 依赖: Commute, Commute.all, isOfFinOrder_mul
-/
theorem IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) : IsOfFinOrder (x * y) :=
  (Commute.all x y).isOfFinOrder_mul hx hy

end CommMonoid

section CommGroup
variable [CommGroup G]

@[to_additive]
/--
lemma `isMulTorsionFree_iff_not_isOfFinOrder` / 引理 `isMulTorsionFree_iff_not_isOfFinOrder`

English:
lemma isMulTorsionFree_iff_not_isOfFinOrder
  proof: not_isOfFinOrder_of_isMulTorsionFree
  mpr hG := by
    refine ⟨fun n hn a b hab => ?_⟩
    rw [← div_eq_one] at hab ⊢
    simp only [← div_pow, isOfFinOrder_iff_pow_eq_one] at hab hG
    exact of_not_not fun hab' => hG hab' ⟨n, hn.bot_lt, hab⟩

@[to_additive]
alias ⟨_, IsMulTorsionFree.of_not_isOfF

中文:
引理 isMulTorsionFree_iff_not_isOfFinOrder
  证明: not_isOfFinOrder_of_isMulTorsionFree
  mpr hG := by
    refine ⟨fun n hn a b hab => ?_⟩
    rw [← div_eq_one] at hab ⊢
    simp only [← div_pow, isOfFinOrder_iff_pow_eq_one] at hab hG
    exact of_not_not fun hab' => hG hab' ⟨n, hn.bot_lt, hab⟩

@[to_additive]
alias ⟨_, IsMulTorsionFree.of_not_isOfF

Depends on / 依赖: not_isOfFinOrder_of_isMulTorsionFree
-/
lemma isMulTorsionFree_iff_not_isOfFinOrder :
    IsMulTorsionFree G ↔ forall ⦃a : G⦄, a != 1 -> ¬ IsOfFinOrder a where
  mp _ _ := not_isOfFinOrder_of_isMulTorsionFree
  mpr hG := by
    refine ⟨fun n hn a b hab => ?_⟩
    rw [← div_eq_one] at hab ⊢
    simp only [← div_pow, isOfFinOrder_iff_pow_eq_one] at hab hG
    exact of_not_not fun hab' => hG hab' ⟨n, hn.bot_lt, hab⟩

@[to_additive]
alias ⟨_, IsMulTorsionFree.of_not_isOfFinOrder⟩ := isMulTorsionFree_iff_not_isOfFinOrder

@[to_additive]
/--
lemma `not_isMulTorsionFree_iff_isOfFinOrder` / 引理 `not_isMulTorsionFree_iff_isOfFinOrder`

English:
lemma not_isMulTorsionFree_iff_isOfFinOrder
  proof: by
  simp [isMulTorsionFree_iff_not_isOfFinOrder]

@[to_additive (attr := simp)]

中文:
引理 not_isMulTorsionFree_iff_isOfFinOrder
  证明: by
  simp [isMulTorsionFree_iff_not_isOfFinOrder]

@[to_additive (attr := simp)]

Depends on / 依赖: isMulTorsionFree_iff_not_isOfFinOrder
-/
lemma not_isMulTorsionFree_iff_isOfFinOrder :
    ¬ IsMulTorsionFree G ↔ exists a != (1 : G), IsOfFinOrder a := by
  simp [isMulTorsionFree_iff_not_isOfFinOrder]

@[to_additive (attr := simp)]
/--
lemma `zpowers_mabs` / 引理 `zpowers_mabs`

English:
lemma zpowers_mabs
  given: [LinearOrder G] [IsOrderedMonoid G] (g : G)
  statement: zpowers |g|ₘ = zpowers g
  proof: by
  rcases mabs_cases g with h | h <;> simp only [h, zpowers_inv]

@[to_additive]

中文:
引理 zpowers_mabs
  条件: [LinearOrder G] [IsOrderedMonoid G] (g : G)
  结论: zpowers |g|ₘ = zpowers g
  证明: by
  rcases mabs_cases g with h | h <;> simp only [h, zpowers_inv]

@[to_additive]

Depends on / 依赖: mabs_cases, zpowers_inv
-/
lemma zpowers_mabs [LinearOrder G] [IsOrderedMonoid G] (g : G) : zpowers |g|ₘ = zpowers g := by
  rcases mabs_cases g with h | h <;> simp only [h, zpowers_inv]

@[to_additive]
/--
lemma `IsMulTorsionFree.orderOf_le_one` / 引理 `IsMulTorsionFree.orderOf_le_one`

English:
lemma IsMulTorsionFree.orderOf_le_one
  given: [IsMulTorsionFree G] (g : G)
  proof: by
  obtain rfl | ha := eq_or_ne g 1
  · simp
  · rw [ne_eq, ← isOfFinOrder_iff_eq_one, ← orderOf_eq_zero_iff] at ha
    simp [ha]

中文:
引理 IsMulTorsionFree.orderOf_le_one
  条件: [IsMulTorsionFree G] (g : G)
  证明: by
  obtain rfl | ha := eq_or_ne g 1
  · simp
  · rw [ne_eq, ← isOfFinOrder_iff_eq_one, ← orderOf_eq_zero_iff] at ha
    simp [ha]

Depends on / 依赖: eq_or_ne, isOfFinOrder_iff_eq_one, ne_eq, orderOf_eq_zero_iff
-/
lemma IsMulTorsionFree.orderOf_le_one [IsMulTorsionFree G] (g : G) :
    orderOf g <= 1 := by
  obtain rfl | ha := eq_or_ne g 1
  · simp
  · rw [ne_eq, ← isOfFinOrder_iff_eq_one, ← orderOf_eq_zero_iff] at ha
    simp [ha]

end CommGroup

section FiniteMonoid

variable [Monoid G] {x : G} {n : Nat}

@[to_additive]
/--
theorem `sum_card_orderOf_eq_card_pow_eq_one` / 定理 `sum_card_orderOf_eq_card_pow_eq_one`

English:
theorem sum_card_orderOf_eq_card_pow_eq_one
  given: [Fintype G] [DecidableEq G] (hn : n != 0)
  proof: by
  refine (Finset.card_biUnion ?_).symm.trans ?_
  · simp +contextual [Set.PairwiseDisjoint, Set.Pairwise, disjoint_iff, Finset.ext_iff]
  · congr; ext; simp [hn, orderOf_dvd_iff_pow_eq_one]

@[to_additive]

中文:
定理 sum_card_orderOf_eq_card_pow_eq_one
  条件: [Fintype G] [DecidableEq G] (hn : n != 0)
  证明: by
  refine (Finset.card_biUnion ?_).symm.trans ?_
  · simp +contextual [Set.PairwiseDisjoint, Set.Pairwise, disjoint_iff, Finset.ext_iff]
  · congr; ext; simp [hn, orderOf_dvd_iff_pow_eq_one]

@[to_additive]

Depends on / 依赖: Finset, Finset.card_biUnion, Finset.ext_iff, Pairwise, PairwiseDisjoint, Set.Pairwise, Set.PairwiseDisjoint, card_biUnion, contextual, disjoint_iff, ext_iff, orderOf_dvd_iff_pow_eq_one, symm.trans
-/
theorem sum_card_orderOf_eq_card_pow_eq_one [Fintype G] [DecidableEq G] (hn : n != 0) :
    ∑ m in divisors n, #{x : G | orderOf x = m} = #{x : G | x ^ n = 1} := by
  refine (Finset.card_biUnion ?_).symm.trans ?_
  · simp +contextual [Set.PairwiseDisjoint, Set.Pairwise, disjoint_iff, Finset.ext_iff]
  · congr; ext; simp [hn, orderOf_dvd_iff_pow_eq_one]

@[to_additive]
/--
theorem `orderOf_le_card_univ` / 定理 `orderOf_le_card_univ`

English:
theorem orderOf_le_card_univ
  given: [Fintype G]
  statement: orderOf x <= Fintype.card G
  proof: Finset.le_card_of_inj_on_range (x ^ ·) (fun _ _ => Finset.mem_univ _) pow_injOn_Iio_orderOf

@[to_additive]

中文:
定理 orderOf_le_card_univ
  条件: [Fintype G]
  结论: orderOf x <= Fintype.card G
  证明: Finset.le_card_of_inj_on_range (x ^ ·) (fun _ _ => Finset.mem_univ _) pow_injOn_Iio_orderOf

@[to_additive]

Depends on / 依赖: Finset, Finset.le_card_of_inj_on_range, Finset.mem_univ, le_card_of_inj_on_range, mem_univ, pow_injOn_Iio_orderOf
-/
theorem orderOf_le_card_univ [Fintype G] : orderOf x <= Fintype.card G :=
  Finset.le_card_of_inj_on_range (x ^ ·) (fun _ _ => Finset.mem_univ _) pow_injOn_Iio_orderOf

@[to_additive]
/--
theorem `orderOf_le_card` / 定理 `orderOf_le_card`

English:
theorem orderOf_le_card
  given: [Finite G]
  statement: orderOf x <= Nat.card G
  proof: by
  obtain ⟨⟩ := nonempty_fintype G
  simpa using orderOf_le_card_univ

中文:
定理 orderOf_le_card
  条件: [Finite G]
  结论: orderOf x <= 自然数.card G
  证明: by
  obtain ⟨⟩ := nonempty_fintype G
  simpa using orderOf_le_card_univ

Depends on / 依赖: nonempty_fintype, orderOf_le_card_univ
-/
theorem orderOf_le_card [Finite G] : orderOf x <= Nat.card G := by
  obtain ⟨⟩ := nonempty_fintype G
  simpa using orderOf_le_card_univ

end FiniteMonoid

section FiniteCancelMonoid
variable [LeftCancelMonoid G]

section Finite
variable [Finite G] {x y : G} {n : Nat}

@[to_additive]
/--
lemma `isOfFinOrder_of_finite` / 引理 `isOfFinOrder_of_finite`

English:
lemma isOfFinOrder_of_finite
  given: (x : G)
  statement: IsOfFinOrder x
  proof: by
by_contra h; exact infinite_not_isOfFinOrder h Set.toFinite _

中文:
引理 isOfFinOrder_of_finite
  条件: (x : G)
  结论: IsOfFinOrder x
  证明: by
by_contra h; exact infinite_not_isOfFinOrder h Set.toFinite _

Depends on / 依赖: Set.toFinite, infinite_not_isOfFinOrder, toFinite
-/
lemma isOfFinOrder_of_finite (x : G) : IsOfFinOrder x := by
by_contra h; exact infinite_not_isOfFinOrder h Set.toFinite _

/-- Every finite left cancellative monoid is a group. -/
@[to_additive (attr := instance_reducible)
  /-- Every finite left cancellative additive monoid is an additive group. -/]
/--
Definition of `LeftCancelMonoid.groupOfFinite` / `LeftCancelMonoid.groupOfFinite` 的定义

English:
definition LeftCancelMonoid.groupOfFinite
  signature: : Group G where
  body: x ^ (orderOf x - 1)
  inv_mul_cancel x := by
    rw [← pow_succ]; rw [tsub_add_cancel_of_le]; rw [pow_orderOf_eq_one]
    exact (isOfFinOrder_of_finite x).orderOf_pos

中文:
定义 LeftCancelMonoid.groupOfFinite
  签名: : Group G where
  定义体: x ^ (orderOf x - 1)
  inv_mul_cancel x := by
    rw [← pow_succ]; rw [tsub_add_cancel_of_le]; rw [pow_orderOf_eq_one]
    exact (isOfFinOrder_of_finite x).orderOf_pos

Depends on / 依赖: orderOf
-/
noncomputable def LeftCancelMonoid.groupOfFinite : Group G where
  inv x := x ^ (orderOf x - 1)
  inv_mul_cancel x := by
    rw [← pow_succ]; rw [tsub_add_cancel_of_le]; rw [pow_orderOf_eq_one]
    exact (isOfFinOrder_of_finite x).orderOf_pos

/-- Every finite right cancellative monoid is a group. -/
@[to_additive (attr := instance_reducible)
  /-- Every finite right cancellative additive monoid is an additive group. -/]
/--
Definition of `RightCancelMonoid.groupOfFinite` / `RightCancelMonoid.groupOfFinite` 的定义

English:
definition RightCancelMonoid.groupOfFinite
  signature: {H : Type*} [RightCancelMonoid H] [Finite H]
  body: by
  letI : Finite Hᵐᵒᵖ := Finite.of_equiv H MulOpposite.opEquiv
  letI : Group Hᵐᵒᵖ := LeftCancelMonoid.groupOfFinite (G := Hᵐᵒᵖ)
  exact (MulEquiv.opOp H).toEquiv.group

中文:
定义 RightCancelMonoid.groupOfFinite
  签名: {H : 类型} [RightCancelMonoid H] [Finite H]
  定义体: by
  letI : Finite Hᵐᵒᵖ := Finite.of_equiv H MulOpposite.opEquiv
  letI : Group Hᵐᵒᵖ := LeftCancelMonoid.groupOfFinite (G := Hᵐᵒᵖ)
  exact (MulEquiv.opOp H).toEquiv.group

Depends on / 依赖: Finite, Finite.of_equiv, LeftCancelMonoid, LeftCancelMonoid.groupOfFinite, MulEquiv, MulEquiv.opOp, MulOpposite, MulOpposite.opEquiv, groupOfFinite, of_equiv, opEquiv, toEquiv, toEquiv.group
-/
noncomputable def RightCancelMonoid.groupOfFinite {H : Type*} [RightCancelMonoid H] [Finite H] :
    Group H := by
  letI : Finite Hᵐᵒᵖ := Finite.of_equiv H MulOpposite.opEquiv
  letI : Group Hᵐᵒᵖ := LeftCancelMonoid.groupOfFinite (G := Hᵐᵒᵖ)
  exact (MulEquiv.opOp H).toEquiv.group

/-- This is the same as `IsOfFinOrder.orderOf_pos` but with one fewer explicit assumption since this
is automatic in case of a finite cancellative monoid. -/
@[to_additive /-- This is the same as `IsOfFinAddOrder.addOrderOf_pos` but with one fewer explicit
assumption since this is automatic in case of a finite cancellative additive monoid. -/]
/--
lemma `orderOf_pos` / 引理 `orderOf_pos`

English:
lemma orderOf_pos
  given: (x : G)
  statement: 0 < orderOf x
  proof: (isOfFinOrder_of_finite x).orderOf_pos

中文:
引理 orderOf_pos
  条件: (x : G)
  结论: 0 < orderOf x
  证明: (isOfFinOrder_of_finite x).orderOf_pos

Depends on / 依赖: isOfFinOrder_of_finite, orderOf_pos
-/
lemma orderOf_pos (x : G) : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos

/-- This is the same as `orderOf_pow'` and `orderOf_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid. -/
@[to_additive /-- This is the same as `addOrderOf_nsmul'` and
`addOrderOf_nsmul` but with one assumption less which is automatic in the case of a
finite cancellative additive monoid. -/]
/--
theorem `orderOf_pow` / 定理 `orderOf_pow`

English:
theorem orderOf_pow
  given: (x : G)
  statement: orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n
  proof: (isOfFinOrder_of_finite _).orderOf_pow ..

@[to_additive]

中文:
定理 orderOf_pow
  条件: (x : G)
  结论: orderOf (x ^ n) = orderOf x / 自然数.gcd (orderOf x) n
  证明: (isOfFinOrder_of_finite _).orderOf_pow ..

@[to_additive]

Depends on / 依赖: isOfFinOrder_of_finite, orderOf_pow
-/
theorem orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n :=
  (isOfFinOrder_of_finite _).orderOf_pow ..

@[to_additive]
/--
theorem `mem_powers_iff_mem_range_orderOf` / 定理 `mem_powers_iff_mem_range_orderOf`

English:
theorem mem_powers_iff_mem_range_orderOf
  given: [DecidableEq G]
  proof: Finset.mem_range_iff_mem_finset_range_of_mod_eq' (orderOf_pos x) pow_mod_orderOf _

中文:
定理 mem_powers_iff_mem_range_orderOf
  条件: [DecidableEq G]
  证明: Finset.mem_range_iff_mem_finset_range_of_mod_eq' (orderOf_pos x) pow_mod_orderOf _

Depends on / 依赖: Finset, Finset.mem_range_iff_mem_finset_range_of_mod_eq, mem_range_iff_mem_finset_range_of_mod_eq, orderOf_pos, pow_mod_orderOf
-/
theorem mem_powers_iff_mem_range_orderOf [DecidableEq G] :
    y in powers x ↔ y in (Finset.range (orderOf x)).image (x ^ ·) :=
Finset.mem_range_iff_mem_finset_range_of_mod_eq' (orderOf_pos x) pow_mod_orderOf _

/-- The equivalence between `Submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive
  /-- The equivalence between `Submonoid.multiples` of two elements `a, b` of the same additive
  order, mapping `i • a` to `i • b`. -/]
/--
Definition of `powersEquivPowers` / `powersEquivPowers` 的定义

English:
definition powersEquivPowers
  signature: (h : orderOf x = orderOf y)
  body: (finEquivPowers <| isOfFinOrder_of_finite _).symm.trans
(finCongr h).trans finEquivPowers isOfFinOrder_of_finite _

@[to_additive (attr := simp)]

中文:
定义 powersEquivPowers
  签名: (h : orderOf x = orderOf y)
  定义体: (finEquivPowers <| isOfFinOrder_of_finite _).symm.trans
(finCongr h).trans finEquivPowers isOfFinOrder_of_finite _

@[to_additive (attr := simp)]

Depends on / 依赖: finCongr, finEquivPowers, isOfFinOrder_of_finite, symm.trans
-/
noncomputable def powersEquivPowers (h : orderOf x = orderOf y) : powers x ≃ powers y :=
(finEquivPowers <| isOfFinOrder_of_finite _).symm.trans
(finCongr h).trans finEquivPowers isOfFinOrder_of_finite _

@[to_additive (attr := simp)]
/--
theorem `powersEquivPowers_apply` / 定理 `powersEquivPowers_apply`

English:
theorem powersEquivPowers_apply
  given: (h : orderOf x = orderOf y) (n : Nat)
  proof: by
  rw [powersEquivPowers]; rw [Equiv.trans_apply]; rw [Equiv.trans_apply]; rw [finEquivPowers_symm_apply]; rw [←
    Equiv.eq_symm_apply]; rw [finEquivPowers_symm_apply]
  simp [h]

中文:
定理 powersEquivPowers_apply
  条件: (h : orderOf x = orderOf y) (n : 自然数)
  证明: by
  rw [powersEquivPowers]; rw [Equiv.trans_apply]; rw [Equiv.trans_apply]; rw [finEquivPowers_symm_apply]; rw [←
    Equiv.eq_symm_apply]; rw [finEquivPowers_symm_apply]
  simp [h]

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.trans_apply, eq_symm_apply, finEquivPowers_symm_apply, powersEquivPowers, trans_apply
-/
theorem powersEquivPowers_apply (h : orderOf x = orderOf y) (n : Nat) :
    powersEquivPowers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ := by
  rw [powersEquivPowers]; rw [Equiv.trans_apply]; rw [Equiv.trans_apply]; rw [finEquivPowers_symm_apply]; rw [←
    Equiv.eq_symm_apply]; rw [finEquivPowers_symm_apply]
  simp [h]

end Finite

variable [Fintype G] {x : G}

@[to_additive]
/--
lemma `orderOf_eq_card_powers` / 引理 `orderOf_eq_card_powers`

English:
lemma orderOf_eq_card_powers
  statement: orderOf x = Fintype.card (powers x : Submonoid G)
  proof: (Fintype.card_fin (orderOf x)).symm.trans
Fintype.card_eq.2 ⟨finEquivPowers isOfFinOrder_of_finite _⟩

中文:
引理 orderOf_eq_card_powers
  结论: orderOf x = Fintype.card (powers x : Submonoid G)
  证明: (Fintype.card_fin (orderOf x)).symm.trans
Fintype.card_eq.2 ⟨finEquivPowers isOfFinOrder_of_finite _⟩

Depends on / 依赖: Fintype, Fintype.card_eq, Fintype.card_fin, card_eq, card_fin, finEquivPowers, isOfFinOrder_of_finite, orderOf, symm.trans
-/
lemma orderOf_eq_card_powers : orderOf x = Fintype.card (powers x : Submonoid G) :=
(Fintype.card_fin (orderOf x)).symm.trans
Fintype.card_eq.2 ⟨finEquivPowers isOfFinOrder_of_finite _⟩

end FiniteCancelMonoid

/--
lemma `isOfFinOrder_iff_isUnit` / 引理 `isOfFinOrder_iff_isUnit`

English:
lemma isOfFinOrder_iff_isUnit
  given: [Monoid G] [Finite Gˣ] {x : G}
  statement: IsOfFinOrder x ↔ IsUnit x
  proof: by
  use IsOfFinOrder.isUnit
  rintro ⟨u, rfl⟩
  rw [Units.isOfFinOrder_val]
  apply isOfFinOrder_of_finite

alias ⟨_, IsUnit.isOfFinOrder⟩ := isOfFinOrder_iff_isUnit

中文:
引理 isOfFinOrder_iff_isUnit
  条件: [Monoid G] [Finite Gˣ] {x : G}
  结论: IsOfFinOrder x ↔ IsUnit x
  证明: by
  use IsOfFinOrder.isUnit
  rintro ⟨u, rfl⟩
  rw [Units.isOfFinOrder_val]
  apply isOfFinOrder_of_finite

alias ⟨_, IsUnit.isOfFinOrder⟩ := isOfFinOrder_iff_isUnit

Depends on / 依赖: IsOfFinOrder, IsOfFinOrder.isUnit, Units.isOfFinOrder_val, isOfFinOrder_of_finite, isOfFinOrder_val, isUnit
-/
lemma isOfFinOrder_iff_isUnit [Monoid G] [Finite Gˣ] {x : G} : IsOfFinOrder x ↔ IsUnit x := by
  use IsOfFinOrder.isUnit
  rintro ⟨u, rfl⟩
  rw [Units.isOfFinOrder_val]
  apply isOfFinOrder_of_finite

alias ⟨_, IsUnit.isOfFinOrder⟩ := isOfFinOrder_iff_isUnit

/--
lemma `orderOf_eq_zero_iff_eq_zero` / 引理 `orderOf_eq_zero_iff_eq_zero`

English:
lemma orderOf_eq_zero_iff_eq_zero
  given: {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] {a : G₀}
  proof: by
  -- Prove an instance inline to avoid extra imports.
  -- TODO: move this instance elsewhere?
  have : Finite G₀ˣ := .of_injective _ Units.val_injective
  simp [isOfFinOrder_iff_isUnit]

中文:
引理 orderOf_eq_zero_iff_eq_zero
  条件: {G₀ : 类型} [GroupWithZero G₀] [Finite G₀] {a : G₀}
  证明: by
  -- Prove an instance inline to avoid extra imports.
  -- TODO: move this instance elsewhere?
  have : Finite G₀ˣ := .of_injective _ Units.val_injective
  simp [isOfFinOrder_iff_isUnit]
-/
lemma orderOf_eq_zero_iff_eq_zero {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] {a : G₀} :
    orderOf a = 0 ↔ a = 0 := by
  -- Prove an instance inline to avoid extra imports.
  -- TODO: move this instance elsewhere?
  have : Finite G₀ˣ := .of_injective _ Units.val_injective
  simp [isOfFinOrder_iff_isUnit]

section FiniteGroup
variable [Group G] {x y : G}

@[to_additive]
/--
theorem `zpow_eq_one_iff_modEq` / 定理 `zpow_eq_one_iff_modEq`

English:
theorem zpow_eq_one_iff_modEq
  given: {n : Int}
  statement: x ^ n = 1 ↔ n ≡ 0 [ZMOD orderOf x]
  proof: by
  rw [Int.modEq_zero_iff_dvd]; rw [orderOf_dvd_iff_zpow_eq_one]


@[to_additive]

中文:
定理 zpow_eq_one_iff_modEq
  条件: {n : 整数}
  结论: x ^ n = 1 ↔ n ≡ 0 [ZMOD orderOf x]
  证明: by
  rw [Int.modEq_zero_iff_dvd]; rw [orderOf_dvd_iff_zpow_eq_one]


@[to_additive]

Depends on / 依赖: Int.modEq_zero_iff_dvd, modEq_zero_iff_dvd, orderOf_dvd_iff_zpow_eq_one
-/
theorem zpow_eq_one_iff_modEq {n : Int} : x ^ n = 1 ↔ n ≡ 0 [ZMOD orderOf x] := by
  rw [Int.modEq_zero_iff_dvd]; rw [orderOf_dvd_iff_zpow_eq_one]


@[to_additive]
/--
theorem `zpow_eq_zpow_iff_modEq` / 定理 `zpow_eq_zpow_iff_modEq`

English:
theorem zpow_eq_zpow_iff_modEq
  given: {m n : Int}
  statement: x ^ m = x ^ n ↔ m ≡ n [ZMOD orderOf x]
  proof: by
  rw [← mul_inv_eq_one]; rw [← zpow_sub]; rw [zpow_eq_one_iff_modEq]; rw [Int.modEq_iff_dvd]; rw [Int.modEq_iff_dvd]; rw [zero_sub]; rw [neg_sub]

@[to_additive (attr := simp)]

中文:
定理 zpow_eq_zpow_iff_modEq
  条件: {m n : 整数}
  结论: x ^ m = x ^ n ↔ m ≡ n [ZMOD orderOf x]
  证明: by
  rw [← mul_inv_eq_one]; rw [← zpow_sub]; rw [zpow_eq_one_iff_modEq]; rw [Int.modEq_iff_dvd]; rw [Int.modEq_iff_dvd]; rw [zero_sub]; rw [neg_sub]

@[to_additive (attr := simp)]

Depends on / 依赖: Int.modEq_iff_dvd, modEq_iff_dvd, mul_inv_eq_one, neg_sub, zero_sub, zpow_eq_one_iff_modEq, zpow_sub
-/
theorem zpow_eq_zpow_iff_modEq {m n : Int} : x ^ m = x ^ n ↔ m ≡ n [ZMOD orderOf x] := by
  rw [← mul_inv_eq_one]; rw [← zpow_sub]; rw [zpow_eq_one_iff_modEq]; rw [Int.modEq_iff_dvd]; rw [Int.modEq_iff_dvd]; rw [zero_sub]; rw [neg_sub]

@[to_additive (attr := simp)]
/--
theorem `injective_zpow_iff_not_isOfFinOrder` / 定理 `injective_zpow_iff_not_isOfFinOrder`

English:
theorem injective_zpow_iff_not_isOfFinOrder
  statement: (Injective fun n : Int => x ^ n) ↔ ¬IsOfFinOrder x
  proof: by
  refine ⟨?_, fun h n m hnm => ?_⟩
  · simp_rw [isOfFinOrder_iff_pow_eq_one]
    rintro h ⟨n, hn, hx⟩
    exact Nat.cast_ne_zero.2 hn.ne' (h <| by simpa using hx)
  rwa [zpow_eq_zpow_iff_modEq, orderOf_eq_zero_iff.2 h, Nat.cast_zero, Int.modEq_zero_iff] at hnm

@[to_additive]

中文:
定理 injective_zpow_iff_not_isOfFinOrder
  结论: (Injective fun n : 整数 => x ^ n) ↔ ¬IsOfFinOrder x
  证明: by
  refine ⟨?_, fun h n m hnm => ?_⟩
  · simp_rw [isOfFinOrder_iff_pow_eq_one]
    rintro h ⟨n, hn, hx⟩
    exact Nat.cast_ne_zero.2 hn.ne' (h <| by simpa using hx)
  rwa [zpow_eq_zpow_iff_modEq, orderOf_eq_zero_iff.2 h, Nat.cast_zero, Int.modEq_zero_iff] at hnm

@[to_additive]

Depends on / 依赖: Int.modEq_zero_iff, Nat.cast_ne_zero, Nat.cast_zero, cast_ne_zero, cast_zero, hn.ne, isOfFinOrder_iff_pow_eq_one, modEq_zero_iff, orderOf_eq_zero_iff, simp_rw, zpow_eq_zpow_iff_modEq
-/
theorem injective_zpow_iff_not_isOfFinOrder : (Injective fun n : Int => x ^ n) ↔ ¬IsOfFinOrder x := by
  refine ⟨?_, fun h n m hnm => ?_⟩
  · simp_rw [isOfFinOrder_iff_pow_eq_one]
    rintro h ⟨n, hn, hx⟩
    exact Nat.cast_ne_zero.2 hn.ne' (h <| by simpa using hx)
  rwa [zpow_eq_zpow_iff_modEq, orderOf_eq_zero_iff.2 h, Nat.cast_zero, Int.modEq_zero_iff] at hnm

@[to_additive]
/--
lemma `Subgroup.zpowers_eq_zpowers_iff` / 引理 `Subgroup.zpowers_eq_zpowers_iff`

English:
lemma Subgroup.zpowers_eq_zpowers_iff
  given: {x y : G} (hx : ¬IsOfFinOrder x)
  proof: by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  have hx_mem : x in zpowers y := by simp [← h]
  have hy_mem : y in zpowers x := by simp [h]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy_mem
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp hx_mem
  rw [← zpow_mul] at hl
  nth_rewrite 2 [← zpow_one x] 

中文:
引理 Subgroup.zpowers_eq_zpowers_iff
  条件: {x y : G} (hx : ¬IsOfFinOrder x)
  证明: by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  have hx_mem : x in zpowers y := by simp [← h]
  have hy_mem : y in zpowers x := by simp [h]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy_mem
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp hx_mem
  rw [← zpow_mul] at hl
  nth_rewrite 2 [← zpow_one x] 

Depends on / 依赖: Int.mul_eq_one_iff_eq_one_or_neg_one, hx_mem, hy_mem, injective_zpow_iff_not_isOfFinOrder, injective_zpow_iff_not_isOfFinOrder.mpr, mem_zpowers_iff, mem_zpowers_iff.mp, mul_eq_one_iff_eq_one_or_neg_one, nth_rewrite, zpow_mul, zpow_one, zpowers
-/
lemma Subgroup.zpowers_eq_zpowers_iff {x y : G} (hx : ¬IsOfFinOrder x) :
    zpowers x = zpowers y ↔ x = y ∨ x⁻¹ = y := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  have hx_mem : x in zpowers y := by simp [← h]
  have hy_mem : y in zpowers x := by simp [h]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy_mem
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp hx_mem
  rw [← zpow_mul] at hl
  nth_rewrite 2 [← zpow_one x] at hl
  have h1 := (injective_zpow_iff_not_isOfFinOrder.mpr hx) hl
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one).mp h1 with (h | h) <;> simp [h.1]

@[to_additive]
/--
theorem `mem_zpowers_zpow_iff` / 定理 `mem_zpowers_zpow_iff`

English:
theorem mem_zpowers_zpow_iff
  given: {g : G} {k : Int}
  proof: by
  simp_rw [← Nat.dvd_one, Int.gcd_dvd_iff, Nat.cast_one, ← Int.sub_eq_iff_eq_add', ← dvd_def,
    ← Int.modEq_iff_dvd, ← zpow_eq_zpow_iff_modEq, zpow_one, zpow_mul, ← mem_zpowers_iff]

@[to_additive]

中文:
定理 mem_zpowers_zpow_iff
  条件: {g : G} {k : 整数}
  证明: by
  simp_rw [← Nat.dvd_one, Int.gcd_dvd_iff, Nat.cast_one, ← Int.sub_eq_iff_eq_add', ← dvd_def,
    ← Int.modEq_iff_dvd, ← zpow_eq_zpow_iff_modEq, zpow_one, zpow_mul, ← mem_zpowers_iff]

@[to_additive]

Depends on / 依赖: Int.gcd_dvd_iff, Int.modEq_iff_dvd, Int.sub_eq_iff_eq_add, Nat.cast_one, Nat.dvd_one, cast_one, dvd_def, dvd_one, gcd_dvd_iff, mem_zpowers_iff, modEq_iff_dvd, simp_rw, sub_eq_iff_eq_add, zpow_eq_zpow_iff_modEq, zpow_mul, zpow_one
-/
theorem mem_zpowers_zpow_iff {g : G} {k : Int} :
    g in Subgroup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1 := by
  simp_rw [← Nat.dvd_one, Int.gcd_dvd_iff, Nat.cast_one, ← Int.sub_eq_iff_eq_add', ← dvd_def,
    ← Int.modEq_iff_dvd, ← zpow_eq_zpow_iff_modEq, zpow_one, zpow_mul, ← mem_zpowers_iff]

@[to_additive]
/--
theorem `mem_zpowers_pow_iff` / 定理 `mem_zpowers_pow_iff`

English:
theorem mem_zpowers_pow_iff
  given: {g : G} {k : Nat}
  proof: by
  rw [← zpow_natCast g k]; rw [mem_zpowers_zpow_iff]; rw [Int.gcd_natCast_natCast]

中文:
定理 mem_zpowers_pow_iff
  条件: {g : G} {k : 自然数}
  证明: by
  rw [← zpow_natCast g k]; rw [mem_zpowers_zpow_iff]; rw [Int.gcd_natCast_natCast]

Depends on / 依赖: Int.gcd_natCast_natCast, gcd_natCast_natCast, mem_zpowers_zpow_iff, zpow_natCast
-/
theorem mem_zpowers_pow_iff {g : G} {k : Nat} :
    g in Subgroup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1 := by
  rw [← zpow_natCast g k]; rw [mem_zpowers_zpow_iff]; rw [Int.gcd_natCast_natCast]

section Finite
variable [Finite G]

@[to_additive]
/--
theorem `exists_zpow_eq_one` / 定理 `exists_zpow_eq_one`

English:
theorem exists_zpow_eq_one
  given: (x : G)
  statement: exists (i : Int) (_ : i != 0), x ^ (i : Int) = 1
  proof: by
  obtain ⟨w, hw1, hw2⟩ := isOfFinOrder_of_finite x
  refine ⟨w, Int.natCast_ne_zero.mpr (_root_.ne_of_gt hw1), ?_⟩
  rw [zpow_natCast]
  exact (isPeriodicPt_mul_iff_pow_eq_one _).mp hw2

@[to_additive]

中文:
定理 exists_zpow_eq_one
  条件: (x : G)
  结论: 存在 (i : 整数) (_ : i != 0), x ^ (i : 整数) = 1
  证明: by
  obtain ⟨w, hw1, hw2⟩ := isOfFinOrder_of_finite x
  refine ⟨w, Int.natCast_ne_zero.mpr (_root_.ne_of_gt hw1), ?_⟩
  rw [zpow_natCast]
  exact (isPeriodicPt_mul_iff_pow_eq_one _).mp hw2

@[to_additive]

Depends on / 依赖: Int.natCast_ne_zero.mpr, _root_, _root_.ne_of_gt, isOfFinOrder_of_finite, isPeriodicPt_mul_iff_pow_eq_one, natCast_ne_zero, ne_of_gt, zpow_natCast
-/
theorem exists_zpow_eq_one (x : G) : exists (i : Int) (_ : i != 0), x ^ (i : Int) = 1 := by
  obtain ⟨w, hw1, hw2⟩ := isOfFinOrder_of_finite x
  refine ⟨w, Int.natCast_ne_zero.mpr (_root_.ne_of_gt hw1), ?_⟩
  rw [zpow_natCast]
  exact (isPeriodicPt_mul_iff_pow_eq_one _).mp hw2

@[to_additive]
/--
lemma `mem_powers_iff_mem_zpowers` / 引理 `mem_powers_iff_mem_zpowers`

English:
lemma mem_powers_iff_mem_zpowers
  statement: y in powers x ↔ y in zpowers x
  proof: (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers

@[to_additive]

中文:
引理 mem_powers_iff_mem_zpowers
  结论: y in powers x ↔ y in zpowers x
  证明: (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers

@[to_additive]

Depends on / 依赖: isOfFinOrder_of_finite, mem_powers_iff_mem_zpowers
-/
lemma mem_powers_iff_mem_zpowers : y in powers x ↔ y in zpowers x :=
  (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers

@[to_additive]
/--
lemma `powers_eq_zpowers` / 引理 `powers_eq_zpowers`

English:
lemma powers_eq_zpowers
  given: (x : G)
  statement: (powers x : Set G) = zpowers x
  proof: (isOfFinOrder_of_finite _).powers_eq_zpowers

@[to_additive]

中文:
引理 powers_eq_zpowers
  条件: (x : G)
  结论: (powers x : Set G) = zpowers x
  证明: (isOfFinOrder_of_finite _).powers_eq_zpowers

@[to_additive]

Depends on / 依赖: isOfFinOrder_of_finite, powers_eq_zpowers
-/
lemma powers_eq_zpowers (x : G) : (powers x : Set G) = zpowers x :=
  (isOfFinOrder_of_finite _).powers_eq_zpowers

@[to_additive]
/--
lemma `mem_zpowers_iff_mem_range_orderOf` / 引理 `mem_zpowers_iff_mem_range_orderOf`

English:
lemma mem_zpowers_iff_mem_range_orderOf
  given: [DecidableEq G]
  proof: (isOfFinOrder_of_finite _).mem_zpowers_iff_mem_range_orderOf

中文:
引理 mem_zpowers_iff_mem_range_orderOf
  条件: [DecidableEq G]
  证明: (isOfFinOrder_of_finite _).mem_zpowers_iff_mem_range_orderOf

Depends on / 依赖: isOfFinOrder_of_finite, mem_zpowers_iff_mem_range_orderOf
-/
lemma mem_zpowers_iff_mem_range_orderOf [DecidableEq G] :
    y in zpowers x ↔ y in (Finset.range (orderOf x)).image (x ^ ·) :=
  (isOfFinOrder_of_finite _).mem_zpowers_iff_mem_range_orderOf

/-- The equivalence between `Subgroup.zpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive
  /-- The equivalence between `Subgroup.zmultiples` of two elements `a, b` of the same additive
  order, mapping `i • a` to `i • b`. -/]
/--
Definition of `zpowersEquivZPowers` / `zpowersEquivZPowers` 的定义

English:
definition zpowersEquivZPowers
  signature: (h : orderOf x = orderOf y)
  body: (finEquivZPowers <| isOfFinOrder_of_finite _).symm.trans (finCongr h).trans
finEquivZPowers isOfFinOrder_of_finite _

@[to_additive (attr := simp) zmultiples_equiv_zmultiples_apply]

中文:
定义 zpowersEquivZPowers
  签名: (h : orderOf x = orderOf y)
  定义体: (finEquivZPowers <| isOfFinOrder_of_finite _).symm.trans (finCongr h).trans
finEquivZPowers isOfFinOrder_of_finite _

@[to_additive (attr := simp) zmultiples_equiv_zmultiples_apply]

Depends on / 依赖: finCongr, finEquivZPowers, isOfFinOrder_of_finite, symm.trans
-/
noncomputable def zpowersEquivZPowers (h : orderOf x = orderOf y) :
    Subgroup.zpowers x ≃ Subgroup.zpowers y :=
(finEquivZPowers <| isOfFinOrder_of_finite _).symm.trans (finCongr h).trans
finEquivZPowers isOfFinOrder_of_finite _

@[to_additive (attr := simp) zmultiples_equiv_zmultiples_apply]
/--
theorem `zpowersEquivZPowers_apply` / 定理 `zpowersEquivZPowers_apply`

English:
theorem zpowersEquivZPowers_apply
  given: (h : orderOf x = orderOf y) (n : Nat)
  proof: by
  rw [zpowersEquivZPowers]; rw [Equiv.trans_apply]; rw [Equiv.trans_apply]; rw [finEquivZPowers_symm_apply]; rw [←
    Equiv.eq_symm_apply]; rw [finEquivZPowers_symm_apply]
  simp [h]

中文:
定理 zpowersEquivZPowers_apply
  条件: (h : orderOf x = orderOf y) (n : 自然数)
  证明: by
  rw [zpowersEquivZPowers]; rw [Equiv.trans_apply]; rw [Equiv.trans_apply]; rw [finEquivZPowers_symm_apply]; rw [←
    Equiv.eq_symm_apply]; rw [finEquivZPowers_symm_apply]
  simp [h]

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.trans_apply, eq_symm_apply, finEquivZPowers_symm_apply, trans_apply, zpowersEquivZPowers
-/
theorem zpowersEquivZPowers_apply (h : orderOf x = orderOf y) (n : Nat) :
    zpowersEquivZPowers h ⟨x ^ n, n, zpow_natCast x n⟩ = ⟨y ^ n, n, zpow_natCast y n⟩ := by
  rw [zpowersEquivZPowers]; rw [Equiv.trans_apply]; rw [Equiv.trans_apply]; rw [finEquivZPowers_symm_apply]; rw [←
    Equiv.eq_symm_apply]; rw [finEquivZPowers_symm_apply]
  simp [h]

/-- See `Subgroup.closure_toSubmonoid_of_isOfFinOrder` for a version with weaker assumptions. -/
@[to_additive
/-- See `AddSubgroup.closure_toAddSubmonoid_of_isOfFinOrder` for a version with weaker
assumptions. -/]
/--
lemma `Subgroup.closure_toSubmonoid_of_finite` / 引理 `Subgroup.closure_toSubmonoid_of_finite`

English:
lemma Subgroup.closure_toSubmonoid_of_finite
  given: {s : Set G}
  proof: closure_toSubmonoid_of_isOfFinOrder by simp [isOfFinOrder_of_finite]

中文:
引理 Subgroup.closure_toSubmonoid_of_finite
  条件: {s : Set G}
  证明: closure_toSubmonoid_of_isOfFinOrder by simp [isOfFinOrder_of_finite]

Depends on / 依赖: closure_toSubmonoid_of_isOfFinOrder, isOfFinOrder_of_finite
-/
lemma Subgroup.closure_toSubmonoid_of_finite {s : Set G} :
    (closure s).toSubmonoid = Submonoid.closure s :=
closure_toSubmonoid_of_isOfFinOrder by simp [isOfFinOrder_of_finite]

end Finite

variable [Fintype G] {x : G} {n : Nat}

/-- See also `Nat.card_zpowers`. -/
@[to_additive /-- See also `Nat.card_zmultiples`. -/]
/--
theorem `Fintype.card_zpowers` / 定理 `Fintype.card_zpowers`

English:
theorem Fintype.card_zpowers
  statement: Fintype.card (zpowers x) = orderOf x
  proof: (Fintype.card_eq.2 ⟨finEquivZPowers <| isOfFinOrder_of_finite _⟩).symm.trans
    Fintype.card_fin (orderOf x)

@[to_additive]

中文:
定理 Fintype.card_zpowers
  结论: Fintype.card (zpowers x) = orderOf x
  证明: (Fintype.card_eq.2 ⟨finEquivZPowers <| isOfFinOrder_of_finite _⟩).symm.trans
    Fintype.card_fin (orderOf x)

@[to_additive]

Depends on / 依赖: Fintype, Fintype.card_eq, Fintype.card_fin, card_eq, card_fin, finEquivZPowers, isOfFinOrder_of_finite, orderOf, symm.trans
-/
theorem Fintype.card_zpowers : Fintype.card (zpowers x) = orderOf x :=
(Fintype.card_eq.2 ⟨finEquivZPowers <| isOfFinOrder_of_finite _⟩).symm.trans
    Fintype.card_fin (orderOf x)

@[to_additive]
/--
theorem `card_zpowers_le` / 定理 `card_zpowers_le`

English:
theorem card_zpowers_le
  statement: (a : G) {k : Nat} (k_pos : k != 0)
  proof: by
  rw [Fintype.card_zpowers]
  apply orderOf_le_of_pow_eq_one k_pos.bot_lt ha

中文:
定理 card_zpowers_le
  结论: (a : G) {k : 自然数} (k_pos : k != 0)
  证明: by
  rw [Fintype.card_zpowers]
  apply orderOf_le_of_pow_eq_one k_pos.bot_lt ha

Depends on / 依赖: Fintype, Fintype.card_zpowers, bot_lt, card_zpowers, k_pos, k_pos.bot_lt, orderOf_le_of_pow_eq_one
-/
theorem card_zpowers_le (a : G) {k : Nat} (k_pos : k != 0)
    (ha : a ^ k = 1) : Fintype.card (Subgroup.zpowers a) <= k := by
  rw [Fintype.card_zpowers]
  apply orderOf_le_of_pow_eq_one k_pos.bot_lt ha

open QuotientGroup

@[to_additive]
/--
theorem `orderOf_dvd_card` / 定理 `orderOf_dvd_card`

English:
theorem orderOf_dvd_card
  statement: orderOf x ∣ Fintype.card G
  proof: by
  use Fintype.card (G ⧸ zpowers x)
  rw [← card_zpowers]; rw [mul_comm]; rw [← Fintype.card_prod]; rw [← Fintype.card_congr groupEquivQuotientProdSubgroup]

@[to_additive]

中文:
定理 orderOf_dvd_card
  结论: orderOf x ∣ Fintype.card G
  证明: by
  use Fintype.card (G ⧸ zpowers x)
  rw [← card_zpowers]; rw [mul_comm]; rw [← Fintype.card_prod]; rw [← Fintype.card_congr groupEquivQuotientProdSubgroup]

@[to_additive]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_congr, Fintype.card_prod, card_congr, card_prod, card_zpowers, groupEquivQuotientProdSubgroup, mul_comm, zpowers
-/
theorem orderOf_dvd_card : orderOf x ∣ Fintype.card G := by
  use Fintype.card (G ⧸ zpowers x)
  rw [← card_zpowers]; rw [mul_comm]; rw [← Fintype.card_prod]; rw [← Fintype.card_congr groupEquivQuotientProdSubgroup]

@[to_additive]
/--
theorem `orderOf_dvd_natCard` / 定理 `orderOf_dvd_natCard`

English:
theorem orderOf_dvd_natCard
  given: {G : Type*} [Group G] (x : G)
  statement: orderOf x ∣ Nat.card G
  proof: by
  obtain h | h := fintypeOrInfinite G
  · simp only [Nat.card_eq_fintype_card, orderOf_dvd_card]
  · simp only [card_eq_zero_of_infinite, dvd_zero]

@[to_additive]
nonrec lemma Subgroup.orderOf_dvd_natCard {G : Type*} [Group G] (s : Subgroup G) {x} (hx : x in s) :
    orderOf x ∣ Nat.card s := by

中文:
定理 orderOf_dvd_natCard
  条件: {G : 类型} [Group G] (x : G)
  结论: orderOf x ∣ 自然数.card G
  证明: by
  obtain h | h := fintypeOrInfinite G
  · simp only [Nat.card_eq_fintype_card, orderOf_dvd_card]
  · simp only [card_eq_zero_of_infinite, dvd_zero]

@[to_additive]
nonrec lemma Subgroup.orderOf_dvd_natCard {G : Type*} [Group G] (s : Subgroup G) {x} (hx : x in s) :
    orderOf x ∣ Nat.card s := by

Depends on / 依赖: Nat.card_eq_fintype_card, card_eq_fintype_card, card_eq_zero_of_infinite, dvd_zero, fintypeOrInfinite, orderOf_dvd_card
-/
theorem orderOf_dvd_natCard {G : Type*} [Group G] (x : G) : orderOf x ∣ Nat.card G := by
  obtain h | h := fintypeOrInfinite G
  · simp only [Nat.card_eq_fintype_card, orderOf_dvd_card]
  · simp only [card_eq_zero_of_infinite, dvd_zero]

@[to_additive]
nonrec lemma Subgroup.orderOf_dvd_natCard {G : Type*} [Group G] (s : Subgroup G) {x} (hx : x in s) :
    orderOf x ∣ Nat.card s := by
  simpa using orderOf_dvd_natCard (⟨x, hx⟩ : s)

@[to_additive]
/--
lemma `Subgroup.orderOf_le_card` / 引理 `Subgroup.orderOf_le_card`

English:
lemma Subgroup.orderOf_le_card
  statement: {G : Type*} [Group G] (s : Subgroup G) (hs : (s : Set G).Finite)
  proof: le_of_dvd (Nat.card_pos_iff.2 <| ⟨(OneMemClass.coe_nonempty s).to_subtype, hs.to_subtype⟩)
    s.orderOf_dvd_natCard hx

@[to_additive]

中文:
引理 Subgroup.orderOf_le_card
  结论: {G : 类型} [Group G] (s : Subgroup G) (hs : (s : Set G).Finite)
  证明: le_of_dvd (Nat.card_pos_iff.2 <| ⟨(OneMemClass.coe_nonempty s).to_subtype, hs.to_subtype⟩)
    s.orderOf_dvd_natCard hx

@[to_additive]

Depends on / 依赖: Nat.card_pos_iff, OneMemClass, OneMemClass.coe_nonempty, card_pos_iff, coe_nonempty, hs.to_subtype, le_of_dvd, orderOf_dvd_natCard, s.orderOf_dvd_natCard, to_subtype
-/
lemma Subgroup.orderOf_le_card {G : Type*} [Group G] (s : Subgroup G) (hs : (s : Set G).Finite)
    {x} (hx : x in s) : orderOf x <= Nat.card s :=
le_of_dvd (Nat.card_pos_iff.2 <| ⟨(OneMemClass.coe_nonempty s).to_subtype, hs.to_subtype⟩)
    s.orderOf_dvd_natCard hx

@[to_additive]
/--
lemma `Submonoid.orderOf_le_card` / 引理 `Submonoid.orderOf_le_card`

English:
lemma Submonoid.orderOf_le_card
  statement: {G : Type*} [Group G] (s : Submonoid G) (hs : (s : Set G).Finite)
  proof: by
rw [← Nat.card_submonoidPowers]; exact Nat.card_mono hs powers_le.2 hx

@[to_additive (attr := simp) card_nsmul_eq_zero']

中文:
引理 Submonoid.orderOf_le_card
  结论: {G : 类型} [Group G] (s : Submonoid G) (hs : (s : Set G).Finite)
  证明: by
rw [← Nat.card_submonoidPowers]; exact Nat.card_mono hs powers_le.2 hx

@[to_additive (attr := simp) card_nsmul_eq_zero']

Depends on / 依赖: Nat.card_mono, Nat.card_submonoidPowers, card_mono, card_submonoidPowers, powers_le
-/
lemma Submonoid.orderOf_le_card {G : Type*} [Group G] (s : Submonoid G) (hs : (s : Set G).Finite)
    {x} (hx : x in s) : orderOf x <= Nat.card s := by
rw [← Nat.card_submonoidPowers]; exact Nat.card_mono hs powers_le.2 hx

@[to_additive (attr := simp) card_nsmul_eq_zero']
/--
theorem `pow_card_eq_one'` / 定理 `pow_card_eq_one'`

English:
theorem pow_card_eq_one'
  given: {G : Type*} [Group G] {x : G}
  statement: x ^ Nat.card G = 1
  proof: orderOf_dvd_iff_pow_eq_one.mp orderOf_dvd_natCard _

中文:
定理 pow_card_eq_one'
  条件: {G : 类型} [Group G] {x : G}
  结论: x ^ 自然数.card G = 1
  证明: orderOf_dvd_iff_pow_eq_one.mp orderOf_dvd_natCard _

Depends on / 依赖: orderOf_dvd_iff_pow_eq_one, orderOf_dvd_iff_pow_eq_one.mp, orderOf_dvd_natCard
-/
theorem pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ Nat.card G = 1 :=
orderOf_dvd_iff_pow_eq_one.mp orderOf_dvd_natCard _

/- TODO: Generalise to `Finite` + `CancelMonoid`. -/
@[to_additive (attr := simp) card_nsmul_eq_zero]
/--
theorem `pow_card_eq_one` / 定理 `pow_card_eq_one`

English:
theorem pow_card_eq_one
  statement: x ^ Fintype.card G = 1
  proof: by
  rw [← Nat.card_eq_fintype_card]; rw [pow_card_eq_one']

@[to_additive]

中文:
定理 pow_card_eq_one
  结论: x ^ Fintype.card G = 1
  证明: by
  rw [← Nat.card_eq_fintype_card]; rw [pow_card_eq_one']

@[to_additive]

Depends on / 依赖: Nat.card_eq_fintype_card, card_eq_fintype_card, pow_card_eq_one
-/
theorem pow_card_eq_one : x ^ Fintype.card G = 1 := by
  rw [← Nat.card_eq_fintype_card]; rw [pow_card_eq_one']

@[to_additive]
/--
theorem `Subgroup.pow_index_mem` / 定理 `Subgroup.pow_index_mem`

English:
theorem Subgroup.pow_index_mem
  given: {G : Type*} [Group G] (H : Subgroup G) [Normal H] (g : G)
  proof: by rw [← eq_one_iff, QuotientGroup.mk_pow H, index, pow_card_eq_one']

@[to_additive]

中文:
定理 Subgroup.pow_index_mem
  条件: {G : 类型} [Group G] (H : Subgroup G) [Normal H] (g : G)
  证明: by rw [← eq_one_iff, QuotientGroup.mk_pow H, index, pow_card_eq_one']

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.mk_pow, eq_one_iff, mk_pow, pow_card_eq_one
-/
theorem Subgroup.pow_index_mem {G : Type*} [Group G] (H : Subgroup G) [Normal H] (g : G) :
    g ^ index H in H := by rw [← eq_one_iff, QuotientGroup.mk_pow H, index, pow_card_eq_one']

@[to_additive]
/--
lemma `Subgroup.pow_relIndex_mem` / 引理 `Subgroup.pow_relIndex_mem`

English:
lemma Subgroup.pow_relIndex_mem
  statement: {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {K : Subgroup G}
  proof: pow_index_mem (H.subgroupOf K) ⟨g, hg⟩

@[to_additive (attr := simp) mod_card_nsmul]

中文:
引理 Subgroup.pow_relIndex_mem
  结论: {G : 类型} [Group G] (H : Subgroup G) [H.Normal] {K : Subgroup G}
  证明: pow_index_mem (H.subgroupOf K) ⟨g, hg⟩

@[to_additive (attr := simp) mod_card_nsmul]

Depends on / 依赖: H.subgroupOf, pow_index_mem, subgroupOf
-/
lemma Subgroup.pow_relIndex_mem {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {K : Subgroup G}
    {g : G} (hg : g in K) : g ^ H.relIndex K in H :=
  pow_index_mem (H.subgroupOf K) ⟨g, hg⟩

@[to_additive (attr := simp) mod_card_nsmul]
/--
lemma `pow_mod_card` / 引理 `pow_mod_card`

English:
lemma pow_mod_card
  given: (a : G) (n : Nat)
  statement: a ^ (n % card G) = a ^ n
  proof: by
  rw [eq_comm]; rw [← pow_mod_orderOf]; rw [← Nat.mod_mod_of_dvd n orderOf_dvd_card]; rw [pow_mod_orderOf]

@[to_additive (attr := simp) mod_card_zsmul]

中文:
引理 pow_mod_card
  条件: (a : G) (n : 自然数)
  结论: a ^ (n % card G) = a ^ n
  证明: by
  rw [eq_comm]; rw [← pow_mod_orderOf]; rw [← Nat.mod_mod_of_dvd n orderOf_dvd_card]; rw [pow_mod_orderOf]

@[to_additive (attr := simp) mod_card_zsmul]

Depends on / 依赖: Nat.mod_mod_of_dvd, eq_comm, mod_mod_of_dvd, orderOf_dvd_card, pow_mod_orderOf
-/
lemma pow_mod_card (a : G) (n : Nat) : a ^ (n % card G) = a ^ n := by
  rw [eq_comm]; rw [← pow_mod_orderOf]; rw [← Nat.mod_mod_of_dvd n orderOf_dvd_card]; rw [pow_mod_orderOf]

@[to_additive (attr := simp) mod_card_zsmul]
/--
theorem `zpow_mod_card` / 定理 `zpow_mod_card`

English:
theorem zpow_mod_card
  given: (a : G) (n : Int)
  statement: a ^ (n % Fintype.card G : Int) = a ^ n
  proof: by
  rw [eq_comm]; rw [← zpow_mod_orderOf]; rw [← Int.emod_emod_of_dvd n
    (Int.natCast_dvd_natCast.2 orderOf_dvd_card)]; rw [zpow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_nsmul]

中文:
定理 zpow_mod_card
  条件: (a : G) (n : 整数)
  结论: a ^ (n % Fintype.card G : 整数) = a ^ n
  证明: by
  rw [eq_comm]; rw [← zpow_mod_orderOf]; rw [← Int.emod_emod_of_dvd n
    (Int.natCast_dvd_natCast.2 orderOf_dvd_card)]; rw [zpow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_nsmul]

Depends on / 依赖: Int.emod_emod_of_dvd, Int.natCast_dvd_natCast, emod_emod_of_dvd, eq_comm, natCast_dvd_natCast, orderOf_dvd_card, zpow_mod_orderOf
-/
theorem zpow_mod_card (a : G) (n : Int) : a ^ (n % Fintype.card G : Int) = a ^ n := by
  rw [eq_comm]; rw [← zpow_mod_orderOf]; rw [← Int.emod_emod_of_dvd n
    (Int.natCast_dvd_natCast.2 orderOf_dvd_card)]; rw [zpow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_nsmul]
/--
lemma `pow_mod_natCard` / 引理 `pow_mod_natCard`

English:
lemma pow_mod_natCard
  given: {G} [Group G] (a : G) (n : Nat)
  statement: a ^ (n % Nat.card G) = a ^ n
  proof: by
  rw [eq_comm]; rw [← pow_mod_orderOf]; rw [← Nat.mod_mod_of_dvd n <| orderOf_dvd_natCard _]; rw [pow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_zsmul]

中文:
引理 pow_mod_natCard
  条件: {G} [Group G] (a : G) (n : 自然数)
  结论: a ^ (n % 自然数.card G) = a ^ n
  证明: by
  rw [eq_comm]; rw [← pow_mod_orderOf]; rw [← Nat.mod_mod_of_dvd n <| orderOf_dvd_natCard _]; rw [pow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_zsmul]

Depends on / 依赖: Nat.mod_mod_of_dvd, eq_comm, mod_mod_of_dvd, orderOf_dvd_natCard, pow_mod_orderOf
-/
lemma pow_mod_natCard {G} [Group G] (a : G) (n : Nat) : a ^ (n % Nat.card G) = a ^ n := by
  rw [eq_comm]; rw [← pow_mod_orderOf]; rw [← Nat.mod_mod_of_dvd n <| orderOf_dvd_natCard _]; rw [pow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_zsmul]
/--
lemma `zpow_mod_natCard` / 引理 `zpow_mod_natCard`

English:
lemma zpow_mod_natCard
  given: {G} [Group G] (a : G) (n : Int)
  statement: a ^ (n % Nat.card G : Int) = a ^ n
  proof: by
  rw [eq_comm]; rw [← zpow_mod_orderOf]; rw [← Int.emod_emod_of_dvd n <|
Int.natCast_dvd_natCast.2 orderOf_dvd_natCard _]; rw [zpow_mod_orderOf]

中文:
引理 zpow_mod_natCard
  条件: {G} [Group G] (a : G) (n : 整数)
  结论: a ^ (n % 自然数.card G : 整数) = a ^ n
  证明: by
  rw [eq_comm]; rw [← zpow_mod_orderOf]; rw [← Int.emod_emod_of_dvd n <|
Int.natCast_dvd_natCast.2 orderOf_dvd_natCard _]; rw [zpow_mod_orderOf]

Depends on / 依赖: Int.emod_emod_of_dvd, Int.natCast_dvd_natCast, emod_emod_of_dvd, eq_comm, natCast_dvd_natCast, orderOf_dvd_natCard, zpow_mod_orderOf
-/
lemma zpow_mod_natCard {G} [Group G] (a : G) (n : Int) : a ^ (n % Nat.card G : Int) = a ^ n := by
  rw [eq_comm]; rw [← zpow_mod_orderOf]; rw [← Int.emod_emod_of_dvd n <|
Int.natCast_dvd_natCast.2 orderOf_dvd_natCard _]; rw [zpow_mod_orderOf]

/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[to_additive (attr := simps) /-- If `gcd(|G|,n)=1` then the smul by `n` is a bijection -/]
/--
Definition of `powCoprime` / `powCoprime` 的定义

English:
definition powCoprime
  signature: {G : Type*} [Group G] (h : (Nat.card G).Coprime n)
  body: g ^ n
  invFun g := g ^ (Nat.card G).gcdB n
  left_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
  right_i

中文:
定义 powCoprime
  签名: {G : 类型} [Group G] (h : (自然数.card G).Coprime n)
  定义体: g ^ n
  invFun g := g ^ (Nat.card G).gcdB n
  left_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
  right_i
-/
noncomputable def powCoprime {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : G ≃ G where
  toFun g := g ^ n
  invFun g := g ^ (Nat.card G).gcdB n
  left_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
  right_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key

@[to_additive]
/--
theorem `powCoprime_one` / 定理 `powCoprime_one`

English:
theorem powCoprime_one
  given: {G : Type*} [Group G] (h : (Nat.card G).Coprime n)
  statement: powCoprime h 1 = 1
  proof: one_pow n

@[to_additive]

中文:
定理 powCoprime_one
  条件: {G : 类型} [Group G] (h : (自然数.card G).Coprime n)
  结论: powCoprime h 1 = 1
  证明: one_pow n

@[to_additive]

Depends on / 依赖: one_pow
-/
theorem powCoprime_one {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : powCoprime h 1 = 1 :=
  one_pow n

@[to_additive]
/--
theorem `powCoprime_inv` / 定理 `powCoprime_inv`

English:
theorem powCoprime_inv
  given: {G : Type*} [Group G] (h : (Nat.card G).Coprime n) {g : G}
  proof: inv_pow g n

@[to_additive Nat.Coprime.nsmul_right_bijective]

中文:
定理 powCoprime_inv
  条件: {G : 类型} [Group G] (h : (自然数.card G).Coprime n) {g : G}
  证明: inv_pow g n

@[to_additive Nat.Coprime.nsmul_right_bijective]

Depends on / 依赖: inv_pow
-/
theorem powCoprime_inv {G : Type*} [Group G] (h : (Nat.card G).Coprime n) {g : G} :
    powCoprime h g⁻¹ = (powCoprime h g)⁻¹ :=
  inv_pow g n

@[to_additive Nat.Coprime.nsmul_right_bijective]
/--
lemma `Nat.Coprime.pow_left_bijective` / 引理 `Nat.Coprime.pow_left_bijective`

English:
lemma Nat.Coprime.pow_left_bijective
  given: {G} [Group G] (hn : (Nat.card G).Coprime n)
  proof: (powCoprime hn).bijective

中文:
引理 Nat.Coprime.pow_left_bijective
  条件: {G} [Group G] (hn : (自然数.card G).Coprime n)
  证明: (powCoprime hn).bijective

Depends on / 依赖: bijective, powCoprime
-/
lemma Nat.Coprime.pow_left_bijective {G} [Group G] (hn : (Nat.card G).Coprime n) :
    Bijective (· ^ n : G -> G) :=
  (powCoprime hn).bijective

/- TODO: Generalise to `Submonoid.powers`. -/
@[to_additive]
/--
theorem `image_range_orderOf` / 定理 `image_range_orderOf`

English:
theorem image_range_orderOf
  given: [DecidableEq G]
  proof: (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  let : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  ext x
  rw [Set.mem_toFinset]; rw [SetLike.mem_coe]; 

中文:
定理 image_range_orderOf
  条件: [DecidableEq G]
  证明: (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  let : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  ext x
  rw [Set.mem_toFinset]; rw [SetLike.mem_coe]; 

Depends on / 依赖: Subgroup, Subgroup.zpowers, instFintypeSubtypeMemOfDecidablePred, zpowers
-/
theorem image_range_orderOf [DecidableEq G] :
    letI : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  let : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  ext x
  rw [Set.mem_toFinset]; rw [SetLike.mem_coe]; rw [mem_zpowers_iff_mem_range_orderOf]

/--
lemma `smul_eq_of_le_smul` / 引理 `smul_eq_of_le_smul`

English:
lemma smul_eq_of_le_smul
  proof: by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul]; rw [← _root_.pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos Nat.card_pos]; rw [pow_card_eq_one']; rw [one_smul] at key
  exact le_antisymm key h

中文:
引理 smul_eq_of_le_smul
  证明: by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul]; rw [← _root_.pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos Nat.card_pos]; rw [pow_card_eq_one']; rw [one_smul] at key
  exact le_antisymm key h

Depends on / 依赖: Nat.card, Nat.card_pos, Nat.sub_one_add_one_eq_of_pos, _root_, _root_.pow_succ, card_pos, le_antisymm, le_pow_smul, one_smul, pow_card_eq_one, pow_succ, smul_mono_right, smul_smul, sub_one_add_one_eq_of_pos
-/
lemma smul_eq_of_le_smul
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : a <= g • a) : g • a = a := by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul]; rw [← _root_.pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos Nat.card_pos]; rw [pow_card_eq_one']; rw [one_smul] at key
  exact le_antisymm key h

/--
lemma `smul_eq_of_smul_le` / 引理 `smul_eq_of_smul_le`

English:
lemma smul_eq_of_smul_le
  proof: by
  have key := smul_mono_right g (pow_smul_le h (Nat.card G - 1))
  rw [smul_smul]; rw [← _root_.pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos Nat.card_pos]; rw [pow_card_eq_one']; rw [one_smul] at key
  exact le_antisymm h key

中文:
引理 smul_eq_of_smul_le
  证明: by
  have key := smul_mono_right g (pow_smul_le h (Nat.card G - 1))
  rw [smul_smul]; rw [← _root_.pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos Nat.card_pos]; rw [pow_card_eq_one']; rw [one_smul] at key
  exact le_antisymm h key

Depends on / 依赖: Nat.card, Nat.card_pos, Nat.sub_one_add_one_eq_of_pos, _root_, _root_.pow_succ, card_pos, le_antisymm, one_smul, pow_card_eq_one, pow_smul_le, pow_succ, smul_mono_right, smul_smul, sub_one_add_one_eq_of_pos
-/
lemma smul_eq_of_smul_le
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : g • a <= a) : g • a = a := by
  have key := smul_mono_right g (pow_smul_le h (Nat.card G - 1))
  rw [smul_smul]; rw [← _root_.pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos Nat.card_pos]; rw [pow_card_eq_one']; rw [one_smul] at key
  exact le_antisymm h key

end FiniteGroup

section PowIsSubgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
@[to_additive
/-- A nonempty idempotent subset of a finite cancellative additive monoid is a submonoid -/]
/--
Definition of `submonoidOfIdempotent` / `submonoidOfIdempotent` 的定义

English:
definition submonoidOfIdempotent
  signature: {M : Type*} [LeftCancelMonoid M] [Finite M] (S : Set M)
  body: have pow_mem (a : M) (ha : a in S) (n : Nat) : a ^ (n + 1) in S := by
    induction n with
    | zero => rwa [zero_add, pow_one]
    | succ n ih =>
      rw [← hS2]; rw [pow_succ]
      exact Set.mul_mem_mul ih ha
  { carrier := S
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_orderO

中文:
定义 submonoidOfIdempotent
  签名: {M : 类型} [LeftCancelMonoid M] [Finite M] (S : Set M)
  定义体: have pow_mem (a : M) (ha : a in S) (n : Nat) : a ^ (n + 1) in S := by
    induction n with
    | zero => rwa [zero_add, pow_one]
    | succ n ih =>
      rw [← hS2]; rw [pow_succ]
      exact Set.mul_mem_mul ih ha
  { carrier := S
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_orderO

Depends on / 依赖: Set.mul_mem_mul, carrier, mul_mem, mul_mem_mul, one_mem, orderOf, orderOf_pos, pow_mem, pow_one, pow_orderOf_eq_one, pow_succ, succ_le_of_lt, tsub_add_cancel_of_le, zero_add
-/
def submonoidOfIdempotent {M : Type*} [LeftCancelMonoid M] [Finite M] (S : Set M)
    (hS1 : S.Nonempty) (hS2 : S * S = S) : Submonoid M :=
  have pow_mem (a : M) (ha : a in S) (n : Nat) : a ^ (n + 1) in S := by
    induction n with
    | zero => rwa [zero_add, pow_one]
    | succ n ih =>
      rw [← hS2]; rw [pow_succ]
      exact Set.mul_mem_mul ih ha
  { carrier := S
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_orderOf_eq_one a]; rw [← tsub_add_cancel_of_le (succ_le_of_lt (orderOf_pos a))]
      exact pow_mem a ha (orderOf a - 1)
    mul_mem' := fun ha hb => (congr_arg₂ (· in ·) rfl hS2).mp (Set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
@[to_additive /-- A nonempty idempotent subset of a finite additive group is a subgroup -/]
/--
Definition of `subgroupOfIdempotent` / `subgroupOfIdempotent` 的定义

English:
definition subgroupOfIdempotent
  signature: {G : Type*} [Group G] [Finite G] (S : Set G) (hS1 : S.Nonempty)
  body: { submonoidOfIdempotent S hS1 hS2 with
    carrier := S
    inv_mem' := fun {a} ha => show a⁻¹ in submonoidOfIdempotent S hS1 hS2 by
      rw [← one_mul a⁻¹]; rw [← pow_one a]; rw [← pow_orderOf_eq_one a]; rw [← pow_sub a (orderOf_pos a)]
      exact pow_mem ha (orderOf a - 1) }

中文:
定义 subgroupOfIdempotent
  签名: {G : 类型} [Group G] [Finite G] (S : Set G) (hS1 : S.Nonempty)
  定义体: { submonoidOfIdempotent S hS1 hS2 with
    carrier := S
    inv_mem' := fun {a} ha => show a⁻¹ in submonoidOfIdempotent S hS1 hS2 by
      rw [← one_mul a⁻¹]; rw [← pow_one a]; rw [← pow_orderOf_eq_one a]; rw [← pow_sub a (orderOf_pos a)]
      exact pow_mem ha (orderOf a - 1) }

Depends on / 依赖: carrier, inv_mem, one_mul, orderOf, orderOf_pos, pow_mem, pow_one, pow_orderOf_eq_one, pow_sub, submonoidOfIdempotent
-/
def subgroupOfIdempotent {G : Type*} [Group G] [Finite G] (S : Set G) (hS1 : S.Nonempty)
    (hS2 : S * S = S) : Subgroup G :=
  { submonoidOfIdempotent S hS1 hS2 with
    carrier := S
    inv_mem' := fun {a} ha => show a⁻¹ in submonoidOfIdempotent S hS1 hS2 by
      rw [← one_mul a⁻¹]; rw [← pow_one a]; rw [← pow_orderOf_eq_one a]; rw [← pow_sub a (orderOf_pos a)]
      exact pow_mem ha (orderOf a - 1) }

/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
@[to_additive (attr := simps!) smulCardAddSubgroup
  /-- If `S` is a nonempty subset of a finite additive group `G`, then `|G| • S` is a subgroup -/]
/--
Definition of `powCardSubgroup` / `powCardSubgroup` 的定义

English:
definition powCardSubgroup
  signature: {G : Type*} [Group G] [Fintype G] (S : Set G) (hS : S.Nonempty)
  body: have one_mem : (1 : G) in S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha
subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩ by
    classical
    apply (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
    si

中文:
定义 powCardSubgroup
  签名: {G : 类型} [Group G] [Fintype G] (S : Set G) (hS : S.Nonempty)
  定义体: have one_mem : (1 : G) in S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha
subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩ by
    classical
    apply (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
    si

Depends on / 依赖: Fintype, Fintype.card, Group.card_pow_eq_card_pow_card_univ, Set.eq_of_subset_of_card_le, Set.pow_mem_pow, Set.subset_mul_left, card_pow_eq_card_pow_card_univ, classical, eq_of_subset_of_card_le, ge_of_eq, le_add_self, one_mem, pow_add, pow_card_eq_one, pow_mem_pow, simp_rw, subgroupOfIdempotent, subset_mul_left
-/
def powCardSubgroup {G : Type*} [Group G] [Fintype G] (S : Set G) (hS : S.Nonempty) : Subgroup G :=
  have one_mem : (1 : G) in S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha
subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩ by
    classical
    apply (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
    simp_rw [← pow_add,
        Group.card_pow_eq_card_pow_card_univ S (Fintype.card G + Fintype.card G) le_add_self]

end PowIsSubgroup

section LinearOrderedSemiring
variable [Semiring G] [LinearOrder G] [IsStrictOrderedRing G] {a : G}

/--
lemma `IsOfFinOrder.eq_one` / 引理 `IsOfFinOrder.eq_one`

English:
lemma IsOfFinOrder.eq_one
  given: (ha₀ : 0 <= a) (ha : IsOfFinOrder a)
  statement: a = 1
  proof: by
  obtain ⟨n, hn, ha⟩ := ha.exists_pow_eq_one
  exact (pow_eq_one_iff_of_nonneg ha₀ hn.ne').1 ha

中文:
引理 IsOfFinOrder.eq_one
  条件: (ha₀ : 0 <= a) (ha : IsOfFinOrder a)
  结论: a = 1
  证明: by
  obtain ⟨n, hn, ha⟩ := ha.exists_pow_eq_one
  exact (pow_eq_one_iff_of_nonneg ha₀ hn.ne').1 ha
-/
protected lemma IsOfFinOrder.eq_one (ha₀ : 0 <= a) (ha : IsOfFinOrder a) : a = 1 := by
  obtain ⟨n, hn, ha⟩ := ha.exists_pow_eq_one
  exact (pow_eq_one_iff_of_nonneg ha₀ hn.ne').1 ha

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring G] [LinearOrder G] [IsStrictOrderedRing G] {a x : G}

/--
lemma `IsOfFinOrder.eq_neg_one` / 引理 `IsOfFinOrder.eq_neg_one`

English:
lemma IsOfFinOrder.eq_neg_one
  given: (ha₀ : a <= 0) (ha : IsOfFinOrder a)
  statement: a = -1
  proof: (sq_eq_one_iff.1 <| ha.pow.eq_one <| sq_nonneg a).resolve_left by
    rintro rfl; exact one_pos.not_ge ha₀

中文:
引理 IsOfFinOrder.eq_neg_one
  条件: (ha₀ : a <= 0) (ha : IsOfFinOrder a)
  结论: a = -1
  证明: (sq_eq_one_iff.1 <| ha.pow.eq_one <| sq_nonneg a).resolve_left by
    rintro rfl; exact one_pos.not_ge ha₀
-/
protected lemma IsOfFinOrder.eq_neg_one (ha₀ : a <= 0) (ha : IsOfFinOrder a) : a = -1 :=
(sq_eq_one_iff.1 <| ha.pow.eq_one <| sq_nonneg a).resolve_left by
    rintro rfl; exact one_pos.not_ge ha₀

/--
theorem `orderOf_abs_ne_one` / 定理 `orderOf_abs_ne_one`

English:
theorem orderOf_abs_ne_one
  given: (h : |x| != 1)
  statement: orderOf x = 0
  proof: by
  rw [orderOf_eq_zero_iff']
  intro n hn hx
  replace hx : |x| ^ n = 1 := by simpa only [abs_one, abs_pow] using congr_arg abs hx
  rcases h.lt_or_gt with h | h
  · exact ((pow_lt_one₀ (abs_nonneg x) h hn.ne').ne hx).elim
  · exact ((one_lt_pow₀ h hn.ne').ne' hx).elim

中文:
定理 orderOf_abs_ne_one
  条件: (h : |x| != 1)
  结论: orderOf x = 0
  证明: by
  rw [orderOf_eq_zero_iff']
  intro n hn hx
  replace hx : |x| ^ n = 1 := by simpa only [abs_one, abs_pow] using congr_arg abs hx
  rcases h.lt_or_gt with h | h
  · exact ((pow_lt_one₀ (abs_nonneg x) h hn.ne').ne hx).elim
  · exact ((one_lt_pow₀ h hn.ne').ne' hx).elim

Depends on / 依赖: abs_nonneg, abs_one, abs_pow, congr_arg, h.lt_or_gt, hn.ne, lt_or_gt, orderOf_eq_zero_iff, replace
-/
theorem orderOf_abs_ne_one (h : |x| != 1) : orderOf x = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hx
  replace hx : |x| ^ n = 1 := by simpa only [abs_one, abs_pow] using congr_arg abs hx
  rcases h.lt_or_gt with h | h
  · exact ((pow_lt_one₀ (abs_nonneg x) h hn.ne').ne hx).elim
  · exact ((one_lt_pow₀ h hn.ne').ne' hx).elim

/--
theorem `LinearOrderedRing.orderOf_le_two` / 定理 `LinearOrderedRing.orderOf_le_two`

English:
theorem LinearOrderedRing.orderOf_le_two
  statement: orderOf x <= 2
  proof: by
  rcases ne_or_eq |x| 1 with h | h
  · simp [orderOf_abs_ne_one h]
  rcases eq_or_eq_neg_of_abs_eq h with (rfl | rfl)
  · simp
  exact orderOf_le_of_pow_eq_one zero_lt_two (by simp)

中文:
定理 LinearOrderedRing.orderOf_le_two
  结论: orderOf x <= 2
  证明: by
  rcases ne_or_eq |x| 1 with h | h
  · simp [orderOf_abs_ne_one h]
  rcases eq_or_eq_neg_of_abs_eq h with (rfl | rfl)
  · simp
  exact orderOf_le_of_pow_eq_one zero_lt_two (by simp)

Depends on / 依赖: eq_or_eq_neg_of_abs_eq, ne_or_eq, orderOf_abs_ne_one, orderOf_le_of_pow_eq_one, zero_lt_two
-/
theorem LinearOrderedRing.orderOf_le_two : orderOf x <= 2 := by
  rcases ne_or_eq |x| 1 with h | h
  · simp [orderOf_abs_ne_one h]
  rcases eq_or_eq_neg_of_abs_eq h with (rfl | rfl)
  · simp
  exact orderOf_le_of_pow_eq_one zero_lt_two (by simp)

end LinearOrderedRing

section Prod

variable [Monoid α] [Monoid β] {x : α × β} {a : α} {b : β}

@[to_additive]
/--
theorem `Prod.orderOf` / 定理 `Prod.orderOf`

English:
theorem Prod.orderOf
  given: (x : α × β)
  statement: orderOf x = (orderOf x.1).lcm (orderOf x.2)
  proof: minimalPeriod_prodMap _ _ _

@[to_additive]

中文:
定理 Prod.orderOf
  条件: (x : α × β)
  结论: orderOf x = (orderOf x.1).lcm (orderOf x.2)
  证明: minimalPeriod_prodMap _ _ _

@[to_additive]
-/
protected theorem Prod.orderOf (x : α × β) : orderOf x = (orderOf x.1).lcm (orderOf x.2) :=
  minimalPeriod_prodMap _ _ _

@[to_additive]
/--
theorem `orderOf_fst_dvd_orderOf` / 定理 `orderOf_fst_dvd_orderOf`

English:
theorem orderOf_fst_dvd_orderOf
  statement: orderOf x.1 ∣ orderOf x
  proof: minimalPeriod_fst_dvd

@[to_additive]

中文:
定理 orderOf_fst_dvd_orderOf
  结论: orderOf x.1 ∣ orderOf x
  证明: minimalPeriod_fst_dvd

@[to_additive]

Depends on / 依赖: minimalPeriod_fst_dvd
-/
theorem orderOf_fst_dvd_orderOf : orderOf x.1 ∣ orderOf x :=
  minimalPeriod_fst_dvd

@[to_additive]
/--
theorem `orderOf_snd_dvd_orderOf` / 定理 `orderOf_snd_dvd_orderOf`

English:
theorem orderOf_snd_dvd_orderOf
  statement: orderOf x.2 ∣ orderOf x
  proof: minimalPeriod_snd_dvd

@[to_additive]

中文:
定理 orderOf_snd_dvd_orderOf
  结论: orderOf x.2 ∣ orderOf x
  证明: minimalPeriod_snd_dvd

@[to_additive]

Depends on / 依赖: minimalPeriod_snd_dvd
-/
theorem orderOf_snd_dvd_orderOf : orderOf x.2 ∣ orderOf x :=
  minimalPeriod_snd_dvd

@[to_additive]
/--
theorem `IsOfFinOrder.fst` / 定理 `IsOfFinOrder.fst`

English:
theorem IsOfFinOrder.fst
  given: (hx : IsOfFinOrder x)
  statement: IsOfFinOrder x.1
  proof: hx.mono orderOf_fst_dvd_orderOf

@[to_additive]

中文:
定理 IsOfFinOrder.fst
  条件: (hx : IsOfFinOrder x)
  结论: IsOfFinOrder x.1
  证明: hx.mono orderOf_fst_dvd_orderOf

@[to_additive]

Depends on / 依赖: hx.mono, orderOf_fst_dvd_orderOf
-/
theorem IsOfFinOrder.fst (hx : IsOfFinOrder x) : IsOfFinOrder x.1 :=
  hx.mono orderOf_fst_dvd_orderOf

@[to_additive]
/--
theorem `IsOfFinOrder.snd` / 定理 `IsOfFinOrder.snd`

English:
theorem IsOfFinOrder.snd
  given: (hx : IsOfFinOrder x)
  statement: IsOfFinOrder x.2
  proof: hx.mono orderOf_snd_dvd_orderOf

@[to_additive IsOfFinAddOrder.prod_mk]

中文:
定理 IsOfFinOrder.snd
  条件: (hx : IsOfFinOrder x)
  结论: IsOfFinOrder x.2
  证明: hx.mono orderOf_snd_dvd_orderOf

@[to_additive IsOfFinAddOrder.prod_mk]

Depends on / 依赖: hx.mono, orderOf_snd_dvd_orderOf
-/
theorem IsOfFinOrder.snd (hx : IsOfFinOrder x) : IsOfFinOrder x.2 :=
  hx.mono orderOf_snd_dvd_orderOf

@[to_additive IsOfFinAddOrder.prod_mk]
/--
theorem `IsOfFinOrder.prod_mk` / 定理 `IsOfFinOrder.prod_mk`

English:
theorem IsOfFinOrder.prod_mk
  statement: IsOfFinOrder a -> IsOfFinOrder b -> IsOfFinOrder (a, b)
  proof: by
  simpa only [← orderOf_pos_iff, Prod.orderOf] using Nat.lcm_pos

@[to_additive IsOfFinAddOrder.prod_iff]

中文:
定理 IsOfFinOrder.prod_mk
  结论: IsOfFinOrder a -> IsOfFinOrder b -> IsOfFinOrder (a, b)
  证明: by
  simpa only [← orderOf_pos_iff, Prod.orderOf] using Nat.lcm_pos

@[to_additive IsOfFinAddOrder.prod_iff]

Depends on / 依赖: Nat.lcm_pos, Prod.orderOf, lcm_pos, orderOf, orderOf_pos_iff
-/
theorem IsOfFinOrder.prod_mk : IsOfFinOrder a -> IsOfFinOrder b -> IsOfFinOrder (a, b) := by
  simpa only [← orderOf_pos_iff, Prod.orderOf] using Nat.lcm_pos

@[to_additive IsOfFinAddOrder.prod_iff]
/--
theorem `IsOfFinOrder.prod_iff` / 定理 `IsOfFinOrder.prod_iff`

English:
theorem IsOfFinOrder.prod_iff
  statement: IsOfFinOrder x ↔ IsOfFinOrder x.1 ∧ IsOfFinOrder x.2
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => .prod_mk h.1 h.2⟩

@[to_additive]

中文:
定理 IsOfFinOrder.prod_iff
  结论: IsOfFinOrder x ↔ IsOfFinOrder x.1 ∧ IsOfFinOrder x.2
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => .prod_mk h.1 h.2⟩

@[to_additive]

Depends on / 依赖: h.fst, h.snd, prod_mk
-/
theorem IsOfFinOrder.prod_iff : IsOfFinOrder x ↔ IsOfFinOrder x.1 ∧ IsOfFinOrder x.2 :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => .prod_mk h.1 h.2⟩

@[to_additive]
/--
lemma `Prod.orderOf_mk` / 引理 `Prod.orderOf_mk`

English:
lemma Prod.orderOf_mk
  statement: orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b)
  proof: (a, b).orderOf

中文:
引理 Prod.orderOf_mk
  结论: orderOf (a, b) = 自然数.lcm (orderOf a) (orderOf b)
  证明: (a, b).orderOf

Depends on / 依赖: orderOf
-/
lemma Prod.orderOf_mk : orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b) :=
  (a, b).orderOf

end Prod

section Pi

variable {ι : Type*} {α : ι -> Type*} [forall i, Monoid (α i)] {x : forall i, α i}

@[to_additive]
/--
lemma `Pi.orderOf_eq_sInf` / 引理 `Pi.orderOf_eq_sInf`

English:
lemma Pi.orderOf_eq_sInf
  given: (x : forall i, α i)
  statement: orderOf x = sInf { n > 0 | forall i, orderOf (x i) ∣ n }
  proof: minimalPeriod_piMap

@[to_additive]

中文:
引理 Pi.orderOf_eq_sInf
  条件: (x : 对任意 i, α i)
  结论: orderOf x = sInf { n > 0 | 对任意 i, orderOf (x i) ∣ n }
  证明: minimalPeriod_piMap

@[to_additive]

Depends on / 依赖: minimalPeriod_piMap
-/
lemma Pi.orderOf_eq_sInf (x : forall i, α i) : orderOf x = sInf { n > 0 | forall i, orderOf (x i) ∣ n } :=
  minimalPeriod_piMap

@[to_additive]
/--
lemma `Pi.orderOf` / 引理 `Pi.orderOf`

English:
lemma Pi.orderOf
  given: [Fintype ι] (x : forall i, α i)
  proof: minimalPeriod_piMap_fintype

@[to_additive]

中文:
引理 Pi.orderOf
  条件: [Fintype ι] (x : 对任意 i, α i)
  证明: minimalPeriod_piMap_fintype

@[to_additive]
-/
protected lemma Pi.orderOf [Fintype ι] (x : forall i, α i) :
    orderOf x = Finset.univ.lcm (fun i => orderOf (x i)) :=
  minimalPeriod_piMap_fintype

@[to_additive]
/--
theorem `orderOf_apply_dvd_orderOf` / 定理 `orderOf_apply_dvd_orderOf`

English:
theorem orderOf_apply_dvd_orderOf
  statement: forall i, orderOf (x i) ∣ orderOf x
  proof: minimalPeriod_single_dvd_minimalPeriod_piMap

@[to_additive]

中文:
定理 orderOf_apply_dvd_orderOf
  结论: 对任意 i, orderOf (x i) ∣ orderOf x
  证明: minimalPeriod_single_dvd_minimalPeriod_piMap

@[to_additive]

Depends on / 依赖: minimalPeriod_single_dvd_minimalPeriod_piMap
-/
theorem orderOf_apply_dvd_orderOf : forall i, orderOf (x i) ∣ orderOf x :=
  minimalPeriod_single_dvd_minimalPeriod_piMap

@[to_additive]
/--
theorem `IsOfFinOrder.pi` / 定理 `IsOfFinOrder.pi`

English:
theorem IsOfFinOrder.pi
  given: [Finite ι]
  statement: (forall i, IsOfFinOrder (x i)) -> IsOfFinOrder x
  proof: by
  have := Fintype.ofFinite ι
  simp only [← orderOf_ne_zero_iff, Pi.orderOf]
  simp [Finset.lcm_eq_zero_iff]

中文:
定理 IsOfFinOrder.pi
  条件: [Finite ι]
  结论: (对任意 i, IsOfFinOrder (x i)) -> IsOfFinOrder x
  证明: by
  have := Fintype.ofFinite ι
  simp only [← orderOf_ne_zero_iff, Pi.orderOf]
  simp [Finset.lcm_eq_zero_iff]
-/
protected theorem IsOfFinOrder.pi [Finite ι] : (forall i, IsOfFinOrder (x i)) -> IsOfFinOrder x := by
  have := Fintype.ofFinite ι
  simp only [← orderOf_ne_zero_iff, Pi.orderOf]
  simp [Finset.lcm_eq_zero_iff]

end Pi

@[simp]
/--
lemma `Nat.cast_card_eq_zero` / 引理 `Nat.cast_card_eq_zero`

English:
lemma Nat.cast_card_eq_zero
  given: (R) [AddGroupWithOne R] [Fintype R]
  statement: (Fintype.card R : R) = 0
  proof: by
  rw [← nsmul_one]; rw [card_nsmul_eq_zero]

中文:
引理 Nat.cast_card_eq_zero
  条件: (R) [AddGroupWithOne R] [Fintype R]
  结论: (Fintype.card R : R) = 0
  证明: by
  rw [← nsmul_one]; rw [card_nsmul_eq_zero]

Depends on / 依赖: card_nsmul_eq_zero, nsmul_one
-/
lemma Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fintype R] : (Fintype.card R : R) = 0 := by
  rw [← nsmul_one]; rw [card_nsmul_eq_zero]

section NonAssocRing
variable (R : Type*) [NonAssocRing R] (p : Nat)

/--
lemma `CharP.addOrderOf_one` / 引理 `CharP.addOrderOf_one`

English:
lemma CharP.addOrderOf_one
  statement: CharP R (addOrderOf (1 : R)) where
  proof: by rw [← Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero]

中文:
引理 CharP.addOrderOf_one
  结论: CharP R (addOrderOf (1 : R)) where
  证明: by rw [← Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero]

Depends on / 依赖: Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero, smul_one_eq_cast
-/
lemma CharP.addOrderOf_one : CharP R (addOrderOf (1 : R)) where
  cast_eq_zero_iff n := by rw [← Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero]

variable [Fintype R]

variable {R} in
/--
lemma `charP_of_ne_zero` / 引理 `charP_of_ne_zero`

English:
lemma charP_of_ne_zero
  given: (hn : card R = p) (hR : forall i < p, (i : R) = 0 -> i = 0)
  statement: CharP R p where
  proof: by
    have H : (p : R) = 0 := by rw [← hn, Nat.cast_card_eq_zero]
    constructor
    · intro h
      rw [← Nat.mod_add_div n p]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [H]; rw [zero_mul]; rw [add_zero] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      apply hR _ (Nat.mod_lt _ _) h
      rw [← hn]; r

中文:
引理 charP_of_ne_zero
  条件: (hn : card R = p) (hR : 对任意 i < p, (i : R) = 0 -> i = 0)
  结论: CharP R p where
  证明: by
    have H : (p : R) = 0 := by rw [← hn, Nat.cast_card_eq_zero]
    constructor
    · intro h
      rw [← Nat.mod_add_div n p]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [H]; rw [zero_mul]; rw [add_zero] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      apply hR _ (Nat.mod_lt _ _) h
      rw [← hn]; r

Depends on / 依赖: Fintype, Fintype.card_pos_iff, Nat.cast_add, Nat.cast_card_eq_zero, Nat.cast_mul, Nat.dvd_iff_mod_eq_zero, Nat.mod_add_div, Nat.mod_lt, add_zero, card_pos_iff, cast_add, cast_card_eq_zero, cast_mul, dvd_iff_mod_eq_zero, mod_add_div, mod_lt, zero_mul
-/
lemma charP_of_ne_zero (hn : card R = p) (hR : forall i < p, (i : R) = 0 -> i = 0) : CharP R p where
  cast_eq_zero_iff n := by
    have H : (p : R) = 0 := by rw [← hn, Nat.cast_card_eq_zero]
    constructor
    · intro h
      rw [← Nat.mod_add_div n p]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [H]; rw [zero_mul]; rw [add_zero] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      apply hR _ (Nat.mod_lt _ _) h
      rw [← hn]; rw [Fintype.card_pos_iff]
      exact ⟨0⟩
    · rintro ⟨n, rfl⟩
      rw [Nat.cast_mul]; rw [H]; rw [zero_mul]

end NonAssocRing

/--
lemma `charP_of_prime_pow_injective` / 引理 `charP_of_prime_pow_injective`

English:
lemma charP_of_prime_pow_injective
  statement: (R) [Ring R] [Fintype R] (p n : Nat) [hp : Fact p.Prime]
  proof: by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, Nat.cast_card_eq_zero]
  obtain ⟨i, hi, rfl⟩ : exists i <= n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
obtain rfl : i = n := hR i hi by rw [← Nat.cast_pow, CharP.cast_eq_zero]
  as

中文:
引理 charP_of_prime_pow_injective
  结论: (R) [Ring R] [Fintype R] (p n : 自然数) [hp : Fact p.Prime]
  证明: by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, Nat.cast_card_eq_zero]
  obtain ⟨i, hi, rfl⟩ : exists i <= n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
obtain rfl : i = n := hR i hi by rw [← Nat.cast_pow, CharP.cast_eq_zero]
  as

Depends on / 依赖: CharP.cast_eq_zero, CharP.cast_eq_zero_iff, CharP.exists, Nat.cast_card_eq_zero, Nat.cast_pow, Nat.dvd_prime_pow, cast_card_eq_zero, cast_eq_zero, cast_eq_zero_iff, cast_pow, dvd_prime_pow
-/
lemma charP_of_prime_pow_injective (R) [Ring R] [Fintype R] (p n : Nat) [hp : Fact p.Prime]
    (hn : card R = p ^ n) (hR : forall i <= n, (p : R) ^ i = 0 -> i = n) : CharP R (p ^ n) := by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, Nat.cast_card_eq_zero]
  obtain ⟨i, hi, rfl⟩ : exists i <= n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
obtain rfl : i = n := hR i hi by rw [← Nat.cast_pow, CharP.cast_eq_zero]
  assumption

namespace SemiconjBy

@[to_additive]
/--
lemma `orderOf_eq` / 引理 `orderOf_eq`

English:
lemma orderOf_eq
  given: [Group G] (a : G) {x y : G} (h : SemiconjBy a x y)
  statement: orderOf x = orderOf y
  proof: by
  rw [orderOf_eq_orderOf_iff]
  intro n
  exact (h.pow_right n).eq_one_iff

中文:
引理 orderOf_eq
  条件: [Group G] (a : G) {x y : G} (h : SemiconjBy a x y)
  结论: orderOf x = orderOf y
  证明: by
  rw [orderOf_eq_orderOf_iff]
  intro n
  exact (h.pow_right n).eq_one_iff

Depends on / 依赖: eq_one_iff, h.pow_right, orderOf_eq_orderOf_iff, pow_right
-/
lemma orderOf_eq [Group G] (a : G) {x y : G} (h : SemiconjBy a x y) : orderOf x = orderOf y := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  exact (h.pow_right n).eq_one_iff

end SemiconjBy

section single

/--
lemma `orderOf_piMulSingle` / 引理 `orderOf_piMulSingle`

English:
lemma orderOf_piMulSingle
  statement: {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [(i : ι) -> Monoid (M i)]
  proof: orderOf_injective (MonoidHom.mulSingle M i) (Pi.mulSingle_injective i) g

中文:
引理 orderOf_piMulSingle
  结论: {ι : 类型} [DecidableEq ι] {M : ι -> 类型} [(i : ι) -> Monoid (M i)]
  证明: orderOf_injective (MonoidHom.mulSingle M i) (Pi.mulSingle_injective i) g

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, Pi.mulSingle_injective, mulSingle, mulSingle_injective, orderOf_injective
-/
lemma orderOf_piMulSingle {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [(i : ι) -> Monoid (M i)]
    (i : ι) (g : M i) :
    orderOf (Pi.mulSingle i g) = orderOf g :=
  orderOf_injective (MonoidHom.mulSingle M i) (Pi.mulSingle_injective i) g

end single
