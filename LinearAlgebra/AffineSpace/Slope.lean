/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/

@[expose] public section

open AffineMap

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

/--
Definition of `slope` / `slope` 的定义

English:
definition slope
  signature: (f : k -> PE) (a b : k)
  body: (b - a)⁻¹ • (f b -ᵥ f a)

中文:
定义 slope
  签名: (f : k -> PE) (a b : k)
  定义体: (b - a)⁻¹ • (f b -ᵥ f a)
-/
def slope (f : k -> PE) (a b : k) : E :=
  (b - a)⁻¹ • (f b -ᵥ f a)

/--
theorem `slope_fun_def` / 定理 `slope_fun_def`

English:
theorem slope_fun_def
  given: (f : k -> PE)
  statement: slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a)
  proof: rfl

中文:
定理 slope_fun_def
  条件: (f : k -> PE)
  结论: slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a)
  证明: rfl
-/
theorem slope_fun_def (f : k -> PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) :=
  rfl

/--
theorem `slope_def_field` / 定理 `slope_def_field`

English:
theorem slope_def_field
  given: (f : k -> k) (a b : k)
  statement: slope f a b = (f b - f a) / (b - a)
  proof: (div_eq_inv_mul _ _).symm

中文:
定理 slope_def_field
  条件: (f : k -> k) (a b : k)
  结论: slope f a b = (f b - f a) / (b - a)
  证明: (div_eq_inv_mul _ _).symm

Depends on / 依赖: div_eq_inv_mul
-/
theorem slope_def_field (f : k -> k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm

/--
theorem `slope_fun_def_field` / 定理 `slope_fun_def_field`

English:
theorem slope_fun_def_field
  given: (f : k -> k) (a : k)
  statement: slope f a = fun b => (f b - f a) / (b - a)
  proof: (div_eq_inv_mul _ _).symm

@[simp]

中文:
定理 slope_fun_def_field
  条件: (f : k -> k) (a : k)
  结论: slope f a = fun b => (f b - f a) / (b - a)
  证明: (div_eq_inv_mul _ _).symm

@[simp]

Depends on / 依赖: div_eq_inv_mul
-/
theorem slope_fun_def_field (f : k -> k) (a : k) : slope f a = fun b => (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm

@[simp]
/--
theorem `slope_same` / 定理 `slope_same`

English:
theorem slope_same
  given: (f : k -> PE) (a : k)
  statement: (slope f a a : E) = 0
  proof: by
  rw [slope]; rw [sub_self]; rw [inv_zero]; rw [zero_smul]

中文:
定理 slope_same
  条件: (f : k -> PE) (a : k)
  结论: (slope f a a : E) = 0
  证明: by
  rw [slope]; rw [sub_self]; rw [inv_zero]; rw [zero_smul]

Depends on / 依赖: inv_zero, sub_self, zero_smul
-/
theorem slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope]; rw [sub_self]; rw [inv_zero]; rw [zero_smul]

/--
theorem `slope_def_module` / 定理 `slope_def_module`

English:
theorem slope_def_module
  given: (f : k -> E) (a b : k)
  statement: slope f a b = (b - a)⁻¹ • (f b - f a)
  proof: rfl

@[simp]

中文:
定理 slope_def_module
  条件: (f : k -> E) (a b : k)
  结论: slope f a b = (b - a)⁻¹ • (f b - f a)
  证明: rfl

@[simp]
-/
theorem slope_def_module (f : k -> E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) :=
  rfl

@[simp]
/--
theorem `sub_smul_slope` / 定理 `sub_smul_slope`

English:
theorem sub_smul_slope
  given: (f : k -> PE) (a b : k)
  statement: (b - a) • slope f a b = f b -ᵥ f a
  proof: by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]

中文:
定理 sub_smul_slope
  条件: (f : k -> PE) (a b : k)
  结论: (b - a) • slope f a b = f b -ᵥ f a
  证明: by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]

Depends on / 依赖: eq_or_ne, hne.symm, sub_ne_zero, sub_self, vsub_self, zero_smul
-/
theorem sub_smul_slope (f : k -> PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]

/--
theorem `sub_smul_slope_vadd` / 定理 `sub_smul_slope_vadd`

English:
theorem sub_smul_slope_vadd
  given: (f : k -> PE) (a b : k)
  statement: (b - a) • slope f a b +ᵥ f a = f b
  proof: by
  rw [sub_smul_slope]; rw [vsub_vadd]

@[simp]

中文:
定理 sub_smul_slope_vadd
  条件: (f : k -> PE) (a b : k)
  结论: (b - a) • slope f a b +ᵥ f a = f b
  证明: by
  rw [sub_smul_slope]; rw [vsub_vadd]

@[simp]

Depends on / 依赖: sub_smul_slope, vsub_vadd
-/
theorem sub_smul_slope_vadd (f : k -> PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope]; rw [vsub_vadd]

@[simp]
/--
theorem `slope_vadd_const` / 定理 `slope_vadd_const`

English:
theorem slope_vadd_const
  given: (f : k -> E) (c : PE)
  statement: (slope fun x => f x +ᵥ c) = slope f
  proof: by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]

中文:
定理 slope_vadd_const
  条件: (f : k -> E) (c : PE)
  结论: (slope fun x => f x +ᵥ c) = slope f
  证明: by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]

Depends on / 依赖: vadd_vsub_vadd_cancel_right, vsub_eq_sub
-/
theorem slope_vadd_const (f : k -> E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]
/--
theorem `slope_sub_smul` / 定理 `slope_sub_smul`

English:
theorem slope_sub_smul
  given: (f : k -> E) {a b : k} (h : a != b)
  proof: by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

中文:
定理 slope_sub_smul
  条件: (f : k -> E) {a b : k} (h : a != b)
  证明: by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

Depends on / 依赖: h.symm, sub_ne_zero
-/
theorem slope_sub_smul (f : k -> E) {a b : k} (h : a != b) :
    slope (fun x => (x - a) • f x) a b = f b := by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

/--
theorem `eq_of_slope_eq_zero` / 定理 `eq_of_slope_eq_zero`

English:
theorem eq_of_slope_eq_zero
  given: {f : k -> PE} {a b : k} (h : slope f a b = (0 : E))
  statement: f a = f b
  proof: by
  rw [← sub_smul_slope_vadd f a b]; rw [h]; rw [smul_zero]; rw [zero_vadd]

中文:
定理 eq_of_slope_eq_zero
  条件: {f : k -> PE} {a b : k} (h : slope f a b = (0 : E))
  结论: f a = f b
  证明: by
  rw [← sub_smul_slope_vadd f a b]; rw [h]; rw [smul_zero]; rw [zero_vadd]

Depends on / 依赖: smul_zero, sub_smul_slope_vadd, zero_vadd
-/
theorem eq_of_slope_eq_zero {f : k -> PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b]; rw [h]; rw [smul_zero]; rw [zero_vadd]

/--
theorem `AffineMap.slope_comp` / 定理 `AffineMap.slope_comp`

English:
theorem AffineMap.slope_comp
  statement: {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
  proof: by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]

中文:
定理 仿射映射.slope_comp
  结论: {F PF : 类型} [加法交换群 F] [模 k F] [加法Torsor F PF]
  证明: by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]

Depends on / 依赖: f.linear.map_smul, f.linearMap_vsub, linear, linearMap_vsub, map_smul
-/
theorem AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
    (f : PE ->ᵃ[k] PF) (g : k -> PE) (a b : k) : slope (f ∘ g) a b = f.linear (slope g a b) := by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]

/--
theorem `LinearMap.slope_comp` / 定理 `LinearMap.slope_comp`

English:
theorem LinearMap.slope_comp
  statement: {F : Type*} [AddCommGroup F] [Module k F] (f : E ->ₗ[k] F) (g : k -> E)
  proof: f.toAffineMap.slope_comp g a b

中文:
定理 线性映射.slope_comp
  结论: {F : 类型} [加法交换群 F] [模 k F] (f : E ->ₗ[k] F) (g : k -> E)
  证明: f.toAffineMap.slope_comp g a b

Depends on / 依赖: f.toAffineMap.slope_comp, slope_comp, toAffineMap
-/
theorem LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E ->ₗ[k] F) (g : k -> E)
    (a b : k) : slope (f ∘ g) a b = f (slope g a b) :=
  f.toAffineMap.slope_comp g a b

/--
theorem `slope_comm` / 定理 `slope_comm`

English:
theorem slope_comm
  given: (f : k -> PE) (a b : k)
  statement: slope f a b = slope f b a
  proof: by
  rw [slope]; rw [slope]; rw [← neg_vsub_eq_vsub_rev]; rw [smul_neg]; rw [← neg_smul]; rw [neg_inv]; rw [neg_sub]

中文:
定理 slope_comm
  条件: (f : k -> PE) (a b : k)
  结论: slope f a b = slope f b a
  证明: by
  rw [slope]; rw [slope]; rw [← neg_vsub_eq_vsub_rev]; rw [smul_neg]; rw [← neg_smul]; rw [neg_inv]; rw [neg_sub]

Depends on / 依赖: neg_inv, neg_smul, neg_sub, neg_vsub_eq_vsub_rev, smul_neg
-/
theorem slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope]; rw [slope]; rw [← neg_vsub_eq_vsub_rev]; rw [smul_neg]; rw [← neg_smul]; rw [neg_inv]; rw [neg_sub]

/--
lemma `slope_neg` / 引理 `slope_neg`

English:
lemma slope_neg
  given: (f : k -> E) (x y : k)
  statement: slope (fun t => -f t) x y = -slope f x y
  proof: by
  simp only [slope_def_module, neg_sub_neg, ← smul_neg, neg_sub]

中文:
引理 slope_neg
  条件: (f : k -> E) (x y : k)
  结论: slope (fun t => -f t) x y = -slope f x y
  证明: by
  simp only [slope_def_module, neg_sub_neg, ← smul_neg, neg_sub]
-/
@[simp] lemma slope_neg (f : k -> E) (x y : k) : slope (fun t => -f t) x y = -slope f x y := by
  simp only [slope_def_module, neg_sub_neg, ← smul_neg, neg_sub]

/--
lemma `slope_neg_fun` / 引理 `slope_neg_fun`

English:
lemma slope_neg_fun
  given: (f : k -> E)
  statement: slope (-f) = -slope f
  proof: by
  ext x y; exact slope_neg f x y

中文:
引理 slope_neg_fun
  条件: (f : k -> E)
  结论: slope (-f) = -slope f
  证明: by
  ext x y; exact slope_neg f x y
-/
@[simp] lemma slope_neg_fun (f : k -> E) : slope (-f) = -slope f := by
  ext x y; exact slope_neg f x y

/--
lemma `slope_eq_zero_iff` / 引理 `slope_eq_zero_iff`

English:
lemma slope_eq_zero_iff
  given: {f : k -> E} {a b : k}
  statement: slope f a b = 0 ↔ f a = f b
  proof: by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

中文:
引理 slope_eq_zero_iff
  条件: {f : k -> E} {a b : k}
  结论: slope f a b = 0 ↔ f a = f b
  证明: by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

Depends on / 依赖: congr_arg, eq_comm, or_iff_right_of_imp, sub_eq_zero
-/
lemma slope_eq_zero_iff {f : k -> E} {a b : k} : slope f a b = 0 ↔ f a = f b := by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

/--
theorem `sub_div_sub_smul_slope_add_sub_div_sub_smul_slope` / 定理 `sub_div_sub_smul_slope_add_sub_div_sub_smul_slope`

English:
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope
  given: (f : k -> PE) (a b c : k)
  proof: by
  by_cases hab : a = b
  · subst hab
    rw [sub_self]; rw [zero_div]; rw [zero_smul]; rw [zero_add]
    by_cases hac : a = c
    · simp [hac]
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
  rw [add_comm]
 

中文:
定理 sub_div_sub_smul_slope_add_sub_div_sub_smul_slope
  条件: (f : k -> PE) (a b c : k)
  证明: by
  by_cases hab : a = b
  · subst hab
    rw [sub_self]; rw [zero_div]; rw [zero_smul]; rw [zero_add]
    by_cases hac : a = c
    · simp [hac]
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
  rw [add_comm]
 

Depends on / 依赖: Ne.symm, add_comm, div_eq_inv_mul, div_self, mul_smul, one_smul, simp_rw, smul_add, sub_ne_zero, sub_self, vsub_add_vsub_cancel, zero_add, zero_div, zero_smul
-/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k -> PE) (a b c : k) :
    ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := by
  by_cases hab : a = b
  · subst hab
    rw [sub_self]; rw [zero_div]; rw [zero_smul]; rw [zero_add]
    by_cases hac : a = c
    · simp [hac]
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
  rw [add_comm]
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hab), smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hbc),
    vsub_add_vsub_cancel]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_slope_slope_sub_div_sub` / 定理 `lineMap_slope_slope_sub_div_sub`

English:
theorem lineMap_slope_slope_sub_div_sub
  given: (f : k -> PE) (a b c : k) (h : a != c)
  proof: by
  simp only [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    add_left_inj]
  match_scalars
  field [sub_ne_zero.2 h.symm]

中文:
定理 lineMap_slope_slope_sub_div_sub
  条件: (f : k -> PE) (a b c : k) (h : a != c)
  证明: by
  simp only [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    add_left_inj]
  match_scalars
  field [sub_ne_zero.2 h.symm]

Depends on / 依赖: add_left_inj, h.symm, lineMap_apply_module, match_scalars, sub_div_sub_smul_slope_add_sub_div_sub_smul_slope, sub_ne_zero
-/
theorem lineMap_slope_slope_sub_div_sub (f : k -> PE) (a b c : k) (h : a != c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  simp only [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    add_left_inj]
  match_scalars
  field [sub_ne_zero.2 h.symm]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_slope_lineMap_slope_lineMap` / 定理 `lineMap_slope_lineMap_slope_lineMap`

English:
theorem lineMap_slope_lineMap_slope_lineMap
  given: (f : k -> PE) (a b r : k)
  proof: by
  obtain rfl | hab : a = b ∨ a != b := Classical.em _; · simp
  rw [slope_comm _ a]; rw [slope_comm _ a]; rw [slope_comm _ _ b]
  convert! lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring]; rw [eq_div_iff (sub_ne_zero.2 hab)]; rw [sub_mul]; rw [one_m

中文:
定理 lineMap_slope_lineMap_slope_lineMap
  条件: (f : k -> PE) (a b r : k)
  证明: by
  obtain rfl | hab : a = b ∨ a != b := Classical.em _; · simp
  rw [slope_comm _ a]; rw [slope_comm _ a]; rw [slope_comm _ _ b]
  convert! lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring]; rw [eq_div_iff (sub_ne_zero.2 hab)]; rw [sub_mul]; rw [one_m

Depends on / 依赖: Classical, Classical.em, convert, eq_div_iff, hab.symm, lineMap, lineMap_apply_ring, lineMap_slope_slope_sub_div_sub, mul_sub, one_mul, slope_comm, sub_mul, sub_ne_zero, sub_sub, sub_sub_cancel
-/
theorem lineMap_slope_lineMap_slope_lineMap (f : k -> PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a != b := Classical.em _; · simp
  rw [slope_comm _ a]; rw [slope_comm _ a]; rw [slope_comm _ _ b]
  convert! lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring]; rw [eq_div_iff (sub_ne_zero.2 hab)]; rw [sub_mul]; rw [one_mul]; rw [mul_sub]; rw [← sub_sub]; rw [sub_sub_cancel]

section Order

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k -> E} {x y : k}

/--
lemma `slope_nonneg_iff_of_le` / 引理 `slope_nonneg_iff_of_le`

English:
lemma slope_nonneg_iff_of_le
  given: (hxy : x <= y)
  statement: 0 <= slope f x y ↔ f x <= f y
  proof: by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h => ?_, fun h => smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this

中文:
引理 slope_nonneg_iff_of_le
  条件: (hxy : x <= y)
  结论: 0 <= slope f x y ↔ f x <= f y
  证明: by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h => ?_, fun h => smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this

Depends on / 依赖: Ne.symm, inv_nonneg, mul_smul, one_smul, smul_nonneg, sub_eq_zero, sub_nonneg, vsub_eq_sub
-/
lemma slope_nonneg_iff_of_le (hxy : x <= y) : 0 <= slope f x y ↔ f x <= f y := by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h => ?_, fun h => smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this
  · rwa [vsub_eq_sub, sub_nonneg]

/--
lemma `MonotoneOn.slope_nonneg` / 引理 `MonotoneOn.slope_nonneg`

English:
lemma MonotoneOn.slope_nonneg
  given: {s : Set k} (hf : MonotoneOn f s) (hx : x in s) (hy : y in s)
  proof: by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_nonneg_iff_of_le hxy).mpr (hf hy hx hxy)

中文:
引理 MonotoneOn.slope_nonneg
  条件: {s : 集合 k} (hf : MonotoneOn f s) (hx : x in s) (hy : y in s)
  证明: by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_nonneg_iff_of_le hxy).mpr (hf hy hx hxy)

Depends on / 依赖: le_total, slope_comm, slope_nonneg_iff_of_le
-/
lemma MonotoneOn.slope_nonneg {s : Set k} (hf : MonotoneOn f s) (hx : x in s) (hy : y in s) :
    0 <= slope f x y := by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_nonneg_iff_of_le hxy).mpr (hf hy hx hxy)

/--
lemma `slope_nonpos_iff_of_le` / 引理 `slope_nonpos_iff_of_le`

English:
lemma slope_nonpos_iff_of_le
  given: (hxy : x <= y)
  statement: slope f x y <= 0 ↔ f y <= f x
  proof: by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy

中文:
引理 slope_nonpos_iff_of_le
  条件: (hxy : x <= y)
  结论: slope f x y <= 0 ↔ f y <= f x
  证明: by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy

Depends on / 依赖: slope_nonneg_iff_of_le
-/
lemma slope_nonpos_iff_of_le (hxy : x <= y) : slope f x y <= 0 ↔ f y <= f x := by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy

/--
lemma `AntitoneOn.slope_nonpos` / 引理 `AntitoneOn.slope_nonpos`

English:
lemma AntitoneOn.slope_nonpos
  given: {s : Set k} (hf : AntitoneOn f s) (hx : x in s) (hy : y in s)
  proof: by
  simpa using hf.neg.slope_nonneg hx hy

中文:
引理 AntitoneOn.slope_nonpos
  条件: {s : 集合 k} (hf : AntitoneOn f s) (hx : x in s) (hy : y in s)
  证明: by
  simpa using hf.neg.slope_nonneg hx hy

Depends on / 依赖: hf.neg.slope_nonneg, slope_nonneg
-/
lemma AntitoneOn.slope_nonpos {s : Set k} (hf : AntitoneOn f s) (hx : x in s) (hy : y in s) :
    slope f x y <= 0 := by
  simpa using hf.neg.slope_nonneg hx hy

/--
lemma `slope_pos_iff_of_le` / 引理 `slope_pos_iff_of_le`

English:
lemma slope_pos_iff_of_le
  given: (hxy : x <= y)
  statement: 0 < slope f x y ↔ f x < f y
  proof: by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]

中文:
引理 slope_pos_iff_of_le
  条件: (hxy : x <= y)
  结论: 0 < slope f x y ↔ f x < f y
  证明: by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]

Depends on / 依赖: eq_comm, lt_iff_le_and_ne, simp_rw, slope_eq_zero_iff, slope_nonneg_iff_of_le
-/
lemma slope_pos_iff_of_le (hxy : x <= y) : 0 < slope f x y ↔ f x < f y := by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]

/--
lemma `StrictMonoOn.slope_pos` / 引理 `StrictMonoOn.slope_pos`

English:
lemma StrictMonoOn.slope_pos
  statement: {s : Set k} (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s)
  proof: by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_pos_iff_of_le hxy.le).mpr (hf hy hx hxy)

中文:
引理 StrictMonoOn.slope_pos
  结论: {s : 集合 k} (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s)
  证明: by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_pos_iff_of_le hxy.le).mpr (hf hy hx hxy)

Depends on / 依赖: hxy.le, lt_or_gt_of_ne, slope_comm, slope_pos_iff_of_le
-/
lemma StrictMonoOn.slope_pos {s : Set k} (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s)
    (hxy : x != y) : 0 < slope f x y := by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_pos_iff_of_le hxy.le).mpr (hf hy hx hxy)

/--
lemma `slope_neg_iff_of_le` / 引理 `slope_neg_iff_of_le`

English:
lemma slope_neg_iff_of_le
  given: (hxy : x <= y)
  statement: slope f x y < 0 ↔ f y < f x
  proof: by
  simpa using slope_pos_iff_of_le (f := -f) hxy

中文:
引理 slope_neg_iff_of_le
  条件: (hxy : x <= y)
  结论: slope f x y < 0 ↔ f y < f x
  证明: by
  simpa using slope_pos_iff_of_le (f := -f) hxy

Depends on / 依赖: slope_pos_iff_of_le
-/
lemma slope_neg_iff_of_le (hxy : x <= y) : slope f x y < 0 ↔ f y < f x := by
  simpa using slope_pos_iff_of_le (f := -f) hxy

/--
lemma `StrictAntiOn.slope_neg` / 引理 `StrictAntiOn.slope_neg`

English:
lemma StrictAntiOn.slope_neg
  statement: {s : Set k} (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s)
  proof: by
  simpa using hf.neg.slope_pos hx hy hxy

中文:
引理 StrictAntiOn.slope_neg
  结论: {s : 集合 k} (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s)
  证明: by
  simpa using hf.neg.slope_pos hx hy hxy

Depends on / 依赖: hf.neg.slope_pos, slope_pos
-/
lemma StrictAntiOn.slope_neg {s : Set k} (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s)
    (hxy : x != y) : slope f x y < 0 := by
  simpa using hf.neg.slope_pos hx hy hxy

end Order
