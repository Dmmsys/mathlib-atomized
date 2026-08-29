/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodic functions

This file proves facts about periodic and antiperiodic functions from and to a field.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2 • c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

public section

assert_not_exists TwoSidedIdeal

variable {α β γ : Type*} {f g : α -> β} {c c₁ c₂ x : α}

open Set

namespace Function


/--
theorem `Periodic.const_smul₀` / 定理 `Periodic.const_smul₀`

English:
theorem Periodic.const_smul₀
  statement: [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
  proof: fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

中文:
定理 周期.const_smul₀
  结论: [加法交换幺半群 α] [除半环 γ] [模 γ α]
  证明: fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
-/
protected theorem Periodic.const_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

/--
theorem `Periodic.const_mul` / 定理 `Periodic.const_mul`

English:
theorem Periodic.const_mul
  given: [DivisionSemiring α] (h : Periodic f c) (a : α)
  proof: Periodic.const_smul₀ h a

中文:
定理 周期.const_mul
  条件: [除半环 α] (h : 周期 f c) (a : α)
  证明: Periodic.const_smul₀ h a
-/
protected theorem Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  Periodic.const_smul₀ h a

/--
theorem `Periodic.const_inv_smul₀` / 定理 `Periodic.const_inv_smul₀`

English:
theorem Periodic.const_inv_smul₀
  statement: [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
  proof: by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹

中文:
定理 周期.const_inv_smul₀
  结论: [加法交换幺半群 α] [除半环 γ] [模 γ α]
  证明: by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹

Depends on / 依赖: h.const_smul, inv_inv
-/
theorem Periodic.const_inv_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹

/--
theorem `Periodic.const_inv_mul` / 定理 `Periodic.const_inv_mul`

English:
theorem Periodic.const_inv_mul
  given: [DivisionSemiring α] (h : Periodic f c) (a : α)
  proof: h.const_inv_smul₀ a

中文:
定理 周期.const_inv_mul
  条件: [除半环 α] (h : 周期 f c) (a : α)
  证明: h.const_inv_smul₀ a

Depends on / 依赖: h.const_inv_smul
-/
theorem Periodic.const_inv_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a

/--
theorem `Periodic.mul_const` / 定理 `Periodic.mul_const`

English:
theorem Periodic.mul_const
  given: [DivisionSemiring α] (h : Periodic f c) (a : α)
  proof: h.const_smul₀ (MulOpposite.op a)

中文:
定理 周期.mul_const
  条件: [除半环 α] (h : 周期 f c) (a : α)
  证明: h.const_smul₀ (MulOpposite.op a)

Depends on / 依赖: EuclideanDomain, MulOpposite, MulOpposite.op, h.const_smul, toEuclideanDomain
-/
theorem Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ (MulOpposite.op a)

/--
theorem `Periodic.mul_const'` / 定理 `Periodic.mul_const'`

English:
theorem Periodic.mul_const'
  given: [DivisionSemiring α] (h : Periodic f c) (a : α)
  proof: by simpa only [div_eq_mul_inv] using h.mul_const a

中文:
定理 周期.mul_const'
  条件: [除半环 α] (h : 周期 f c) (a : α)
  证明: by simpa only [div_eq_mul_inv] using h.mul_const a

Depends on / 依赖: div_eq_mul_inv, h.mul_const, mul_const
-/
theorem Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c / a) := by simpa only [div_eq_mul_inv] using h.mul_const a

/--
theorem `Periodic.mul_const_inv` / 定理 `Periodic.mul_const_inv`

English:
theorem Periodic.mul_const_inv
  given: [DivisionSemiring α] (h : Periodic f c) (a : α)
  proof: h.const_inv_smul₀ (MulOpposite.op a)

中文:
定理 周期.mul_const_inv
  条件: [除半环 α] (h : 周期 f c) (a : α)
  证明: h.const_inv_smul₀ (MulOpposite.op a)

Depends on / 依赖: MulOpposite, MulOpposite.op, h.const_inv_smul
-/
theorem Periodic.mul_const_inv [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ (MulOpposite.op a)

/--
theorem `Periodic.div_const` / 定理 `Periodic.div_const`

English:
theorem Periodic.div_const
  given: [DivisionSemiring α] (h : Periodic f c) (a : α)
  proof: by simpa only [div_eq_mul_inv] using h.mul_const_inv a

中文:
定理 周期.div_const
  条件: [除半环 α] (h : 周期 f c) (a : α)
  证明: by simpa only [div_eq_mul_inv] using h.mul_const_inv a

Depends on / 依赖: div_eq_mul_inv, h.mul_const_inv, mul_const_inv
-/
theorem Periodic.div_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x / a)) (c * a) := by simpa only [div_eq_mul_inv] using h.mul_const_inv a

/--
theorem `Periodic.exists_mem_Ico₀` / 定理 `Periodic.exists_mem_Ico₀`

English:
theorem Periodic.exists_mem_Ico₀
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

中文:
定理 周期.存在_mem_Ico₀
  结论: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α]
  证明: let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

Depends on / 依赖: existsUnique_zsmul_near_of_pos, h.sub_zsmul_eq, sub_zsmul_eq
-/
theorem Periodic.exists_mem_Ico₀ [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x) : exists y in Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/--
theorem `Periodic.exists_mem_Ico` / 定理 `Periodic.exists_mem_Ico`

English:
theorem Periodic.exists_mem_Ico
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

中文:
定理 周期.存在_mem_Ico
  结论: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α]
  证明: let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

Depends on / 依赖: existsUnique_add_zsmul_mem_Ico, h.zsmul
-/
theorem Periodic.exists_mem_Ico [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : exists y in Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/--
theorem `Periodic.exists_mem_Ioc` / 定理 `Periodic.exists_mem_Ioc`

English:
theorem Periodic.exists_mem_Ioc
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

中文:
定理 周期.存在_mem_Ioc
  结论: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α]
  证明: let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

Depends on / 依赖: existsUnique_add_zsmul_mem_Ioc, h.zsmul
-/
theorem Periodic.exists_mem_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : exists y in Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/--
theorem `Periodic.image_Ioc` / 定理 `Periodic.image_Ioc`

English:
theorem Periodic.image_Ioc
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: (image_subset_range _ _).antisymm range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩

中文:
定理 周期.image_Ioc
  结论: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α]
  证明: (image_subset_range _ _).antisymm range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩

Depends on / 依赖: antisymm, exists_mem_Ioc, h.exists_mem_Ioc, hyx.symm, image_subset_range, range_subset_iff
-/
theorem Periodic.image_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Ioc a (a + c) = range f :=
(image_subset_range _ _).antisymm range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩

/--
theorem `Periodic.image_Icc` / 定理 `Periodic.image_Icc`

English:
theorem Periodic.image_Icc
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: (image_subset_range _ _).antisymm h.image_Ioc hc a ▸ image_mono Ioc_subset_Icc_self

中文:
定理 周期.image_Icc
  结论: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α]
  证明: (image_subset_range _ _).antisymm h.image_Ioc hc a ▸ image_mono Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, antisymm, h.image_Ioc, image_Ioc, image_mono, image_subset_range
-/
theorem Periodic.image_Icc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Icc a (a + c) = range f :=
(image_subset_range _ _).antisymm h.image_Ioc hc a ▸ image_mono Ioc_subset_Icc_self

/--
theorem `Periodic.image_uIcc` / 定理 `Periodic.image_uIcc`

English:
theorem Periodic.image_uIcc
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: by
  cases hc.lt_or_gt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le)]; rw [← h.neg.image_Icc (neg_pos.2 hc) (a + c)]; rw [add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

中文:
定理 周期.image_uIcc
  结论: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α]
  证明: by
  cases hc.lt_or_gt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le)]; rw [← h.neg.image_Icc (neg_pos.2 hc) (a + c)]; rw [add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

Depends on / 依赖: add_le_of_nonpos_right, add_neg_cancel_right, h.image_Icc, h.neg.image_Icc, hc.le, hc.lt_or_gt, image_Icc, le_add_of_nonneg_right, lt_or_gt, neg_pos, uIcc_of_ge, uIcc_of_le
-/
theorem Periodic.image_uIcc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : c != 0) (a : α) : f '' uIcc a (a + c) = range f := by
  cases hc.lt_or_gt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le)]; rw [← h.neg.image_Icc (neg_pos.2 hc) (a + c)]; rw [add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]


/--
theorem `Antiperiodic.add_nat_mul_eq` / 定理 `Antiperiodic.add_nat_mul_eq`

English:
theorem Antiperiodic.add_nat_mul_eq
  given: [NonAssocSemiring α] [Ring β] (h : Antiperiodic f c) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

中文:
定理 Antiperiodic.add_nat_mul_eq
  条件: [非结合半环 α] [环 β] (h : Antiperiodic f c) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

Depends on / 依赖: Int.cast_neg, Int.cast_one, Int.cast_pow, add_nsmul_eq, cast_neg, cast_one, cast_pow, h.add_nsmul_eq, nsmul_eq_mul, zsmul_eq_mul
-/
theorem Antiperiodic.add_nat_mul_eq [NonAssocSemiring α] [Ring β] (h : Antiperiodic f c) (n : Nat) :
    f (x + n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

/--
theorem `Antiperiodic.sub_nat_mul_eq` / 定理 `Antiperiodic.sub_nat_mul_eq`

English:
theorem Antiperiodic.sub_nat_mul_eq
  given: [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n

中文:
定理 Antiperiodic.sub_nat_mul_eq
  条件: [非结合环 α] [环 β] (h : Antiperiodic f c) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n

Depends on / 依赖: Int.cast_neg, Int.cast_one, Int.cast_pow, cast_neg, cast_one, cast_pow, h.sub_nsmul_eq, nsmul_eq_mul, sub_nsmul_eq, zsmul_eq_mul
-/
theorem Antiperiodic.sub_nat_mul_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : Nat) :
    f (x - n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n

/--
theorem `Antiperiodic.nat_mul_sub_eq` / 定理 `Antiperiodic.nat_mul_sub_eq`

English:
theorem Antiperiodic.nat_mul_sub_eq
  given: [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

中文:
定理 Antiperiodic.nat_mul_sub_eq
  条件: [非结合环 α] [环 β] (h : Antiperiodic f c) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

Depends on / 依赖: Int.cast_neg, Int.cast_one, Int.cast_pow, cast_neg, cast_one, cast_pow, h.nsmul_sub_eq, nsmul_eq_mul, nsmul_sub_eq, zsmul_eq_mul
-/
theorem Antiperiodic.nat_mul_sub_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : Nat) :
    f (n * c - x) = (-1) ^ n * f (-x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

/--
theorem `Antiperiodic.const_smul₀` / 定理 `Antiperiodic.const_smul₀`

English:
theorem Antiperiodic.const_smul₀
  statement: [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
  proof: fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

中文:
定理 Antiperiodic.const_smul₀
  结论: [加法幺半群 α] [取负 β] [带零群 γ] [分配乘法作用 γ α]
  证明: fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

Depends on / 依赖: smul_add
-/
theorem Antiperiodic.const_smul₀ [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a != 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

/--
theorem `Antiperiodic.const_mul` / 定理 `Antiperiodic.const_mul`

English:
theorem Antiperiodic.const_mul
  statement: [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
  proof: h.const_smul₀ ha

中文:
定理 Antiperiodic.const_mul
  结论: [除半环 α] [取负 β] (h : Antiperiodic f c) {a : α}
  证明: h.const_smul₀ ha

Depends on / 依赖: h.const_smul
-/
theorem Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a != 0) : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha

/--
theorem `Antiperiodic.const_inv_smul₀` / 定理 `Antiperiodic.const_inv_smul₀`

English:
theorem Antiperiodic.const_inv_smul₀
  statement: [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
  proof: by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)

中文:
定理 Antiperiodic.const_inv_smul₀
  结论: [加法幺半群 α] [取负 β] [带零群 γ] [分配乘法作用 γ α]
  证明: by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)

Depends on / 依赖: h.const_smul, inv_inv, inv_ne_zero
-/
theorem Antiperiodic.const_inv_smul₀ [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a != 0) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)

/--
theorem `Antiperiodic.const_inv_mul` / 定理 `Antiperiodic.const_inv_mul`

English:
theorem Antiperiodic.const_inv_mul
  statement: [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
  proof: h.const_inv_smul₀ ha

中文:
定理 Antiperiodic.const_inv_mul
  结论: [除半环 α] [取负 β] (h : Antiperiodic f c) {a : α}
  证明: h.const_inv_smul₀ ha

Depends on / 依赖: h.const_inv_smul
-/
theorem Antiperiodic.const_inv_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a != 0) : Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha

/--
theorem `Antiperiodic.mul_const` / 定理 `Antiperiodic.mul_const`

English:
theorem Antiperiodic.mul_const
  statement: [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
  proof: h.const_smul₀ (MulOpposite.op_ne_zero_iff a).mpr ha

中文:
定理 Antiperiodic.mul_const
  结论: [除半环 α] [取负 β] (h : Antiperiodic f c) {a : α}
  证明: h.const_smul₀ (MulOpposite.op_ne_zero_iff a).mpr ha

Depends on / 依赖: MulOpposite, MulOpposite.op_ne_zero_iff, h.const_smul, op_ne_zero_iff
-/
theorem Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a != 0) : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
h.const_smul₀ (MulOpposite.op_ne_zero_iff a).mpr ha

/--
theorem `Antiperiodic.mul_const'` / 定理 `Antiperiodic.mul_const'`

English:
theorem Antiperiodic.mul_const'
  statement: [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
  proof: by
  simpa only [div_eq_mul_inv] using h.mul_const ha

中文:
定理 Antiperiodic.mul_const'
  结论: [除半环 α] [取负 β] (h : Antiperiodic f c) {a : α}
  证明: by
  simpa only [div_eq_mul_inv] using h.mul_const ha

Depends on / 依赖: div_eq_mul_inv, h.mul_const, mul_const
-/
theorem Antiperiodic.mul_const' [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a != 0) : Antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const ha

/--
theorem `Antiperiodic.mul_const_inv` / 定理 `Antiperiodic.mul_const_inv`

English:
theorem Antiperiodic.mul_const_inv
  statement: [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
  proof: h.const_inv_smul₀ (MulOpposite.op_ne_zero_iff a).mpr ha

中文:
定理 Antiperiodic.mul_const_inv
  结论: [除半环 α] [取负 β] (h : Antiperiodic f c) {a : α}
  证明: h.const_inv_smul₀ (MulOpposite.op_ne_zero_iff a).mpr ha

Depends on / 依赖: MulOpposite, MulOpposite.op_ne_zero_iff, h.const_inv_smul, op_ne_zero_iff
-/
theorem Antiperiodic.mul_const_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a != 0) : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
h.const_inv_smul₀ (MulOpposite.op_ne_zero_iff a).mpr ha

/--
theorem `Antiperiodic.div_inv` / 定理 `Antiperiodic.div_inv`

English:
theorem Antiperiodic.div_inv
  statement: [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
  proof: by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

中文:
定理 Antiperiodic.div_inv
  结论: [除半环 α] [取负 β] (h : Antiperiodic f c) {a : α}
  证明: by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

Depends on / 依赖: div_eq_mul_inv, h.mul_const_inv, mul_const_inv
-/
theorem Antiperiodic.div_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a != 0) : Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

end Function

/--
theorem `Int.fract_periodic` / 定理 `Int.fract_periodic`

English:
theorem Int.fract_periodic
  given: (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  proof: fun a => mod_cast Int.fract_add_intCast a 1

中文:
定理 整数.fract_periodic
  条件: (α) [环 α] [线性序 α] [是StrictOrdered环 α] [Floor环 α]
  证明: fun a => mod_cast Int.fract_add_intCast a 1

Depends on / 依赖: Int.fract_add_intCast, fract_add_intCast, mod_cast
-/
theorem Int.fract_periodic (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => mod_cast Int.fract_add_intCast a 1
