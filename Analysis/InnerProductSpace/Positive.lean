/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Trace

/-!
# Positive operators

In this file we define when an operator in a Hilbert space is positive. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `LinearMap.IsPositive` : a linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.
* `ContinuousLinearMap.IsPositive` : a continuous linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.

## Main statements

* `ContinuousLinearMap.IsPositive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `ContinuousLinearMap.isPositive_iff_complex` : in a ***complex*** Hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/

@[expose] public section

open InnerProductSpace RCLike LinearMap ContinuousLinearMap

open scoped InnerProduct ComplexConjugate ComplexOrder

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/--
Definition of `IsPositive` / `IsPositive` 的定义

English:
definition IsPositive
  signature: (T : E ->ₗ[𝕜] E)
  body: IsSymmetric T ∧ forall x, 0 <= re ⟪T x, x⟫

中文:
定义 IsPositive
  签名: (T : E ->ₗ[𝕜] E)
  定义体: IsSymmetric T ∧ forall x, 0 <= re ⟪T x, x⟫

Depends on / 依赖: IsSymmetric
-/
def IsPositive (T : E ->ₗ[𝕜] E) : Prop :=
  IsSymmetric T ∧ forall x, 0 <= re ⟪T x, x⟫

/--
theorem `IsPositive.isSymmetric` / 定理 `IsPositive.isSymmetric`

English:
theorem IsPositive.isSymmetric
  given: {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  proof: hT.1

中文:
定理 IsPositive.isSymmetric
  条件: {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  证明: hT.1
-/
theorem IsPositive.isSymmetric {T : E ->ₗ[𝕜] E} (hT : IsPositive T) :
    IsSymmetric T := hT.1

/--
theorem `IsPositive.re_inner_nonneg_left` / 定理 `IsPositive.re_inner_nonneg_left`

English:
theorem IsPositive.re_inner_nonneg_left
  statement: {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  proof: hT.2 x

中文:
定理 IsPositive.re_inner_nonneg_left
  结论: {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  证明: hT.2 x
-/
theorem IsPositive.re_inner_nonneg_left {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 <= re ⟪T x, x⟫ :=
  hT.2 x

/--
theorem `IsPositive.re_inner_nonneg_right` / 定理 `IsPositive.re_inner_nonneg_right`

English:
theorem IsPositive.re_inner_nonneg_right
  statement: {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  proof: inner_re_symm (𝕜 := 𝕜) _ x ▸ hT.re_inner_nonneg_left x

中文:
定理 IsPositive.re_inner_nonneg_right
  结论: {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  证明: inner_re_symm (𝕜 := 𝕜) _ x ▸ hT.re_inner_nonneg_left x

Depends on / 依赖: hT.re_inner_nonneg_left, inner_re_symm, re_inner_nonneg_left
-/
theorem IsPositive.re_inner_nonneg_right {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 <= re ⟪x, T x⟫ :=
  inner_re_symm (𝕜 := 𝕜) _ x ▸ hT.re_inner_nonneg_left x

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace Complex E']

/--
theorem `isPositive_iff_complex` / 定理 `isPositive_iff_complex`

English:
theorem isPositive_iff_complex
  given: (T : E' ->ₗ[Complex] E')
  proof: by
  simp_rw [IsPositive, forall_and, isSymmetric_iff_inner_map_self_real,
    conj_eq_iff_re, re_to_complex, Complex.coe_algebraMap]

中文:
定理 isPositive_iff_complex
  条件: (T : E' ->ₗ[复形] E')
  证明: by
  simp_rw [IsPositive, forall_and, isSymmetric_iff_inner_map_self_real,
    conj_eq_iff_re, re_to_complex, Complex.coe_algebraMap]

Depends on / 依赖: Complex.coe_algebraMap, IsPositive, coe_algebraMap, conj_eq_iff_re, forall_and, isSymmetric_iff_inner_map_self_real, re_to_complex, simp_rw
-/
theorem isPositive_iff_complex (T : E' ->ₗ[Complex] E') :
    IsPositive T ↔ forall x, (re ⟪T x, x⟫_Complex : Complex) = ⟪T x, x⟫_Complex ∧ 0 <= re ⟪T x, x⟫_Complex := by
  simp_rw [IsPositive, forall_and, isSymmetric_iff_inner_map_self_real,
    conj_eq_iff_re, re_to_complex, Complex.coe_algebraMap]

end Complex

/--
theorem `IsPositive.isSelfAdjoint` / 定理 `IsPositive.isSelfAdjoint`

English:
theorem IsPositive.isSelfAdjoint
  given: [FiniteDimensional 𝕜 E] {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  proof: (isSymmetric_iff_isSelfAdjoint _).mp hT.isSymmetric

中文:
定理 IsPositive.isSelfAdjoint
  条件: [有限维 𝕜 E] {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  证明: (isSymmetric_iff_isSelfAdjoint _).mp hT.isSymmetric

Depends on / 依赖: hT.isSymmetric, isSymmetric, isSymmetric_iff_isSelfAdjoint
-/
theorem IsPositive.isSelfAdjoint [FiniteDimensional 𝕜 E] {T : E ->ₗ[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := (isSymmetric_iff_isSelfAdjoint _).mp hT.isSymmetric

/--
theorem `IsPositive.adjoint_eq` / 定理 `IsPositive.adjoint_eq`

English:
theorem IsPositive.adjoint_eq
  given: [FiniteDimensional 𝕜 E] {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  proof: hT.isSelfAdjoint

中文:
定理 IsPositive.adjoint_eq
  条件: [有限维 𝕜 E] {T : E ->ₗ[𝕜] E} (hT : IsPositive T)
  证明: hT.isSelfAdjoint

Depends on / 依赖: hT.isSelfAdjoint, isSelfAdjoint
-/
theorem IsPositive.adjoint_eq [FiniteDimensional 𝕜 E] {T : E ->ₗ[𝕜] E} (hT : IsPositive T) :
    T.adjoint = T := hT.isSelfAdjoint

/--
theorem `isPositive_iff` / 定理 `isPositive_iff`

English:
theorem isPositive_iff
  given: (T : E ->ₗ[𝕜] E)
  proof: by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [hT]

中文:
定理 isPositive_iff
  条件: (T : E ->ₗ[𝕜] E)
  证明: by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [hT]

Depends on / 依赖: IsPositive, RCLike, RCLike.ofReal_nonneg, and_congr_right_iff, ofReal_nonneg, simp_rw
-/
theorem isPositive_iff (T : E ->ₗ[𝕜] E) :
    IsPositive T ↔ IsSymmetric T ∧ forall x, 0 <= ⟪T x, x⟫ := by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [hT]

/--
theorem `IsPositive.inner_nonneg_left` / 定理 `IsPositive.inner_nonneg_left`

English:
theorem IsPositive.inner_nonneg_left
  given: {T : E ->ₗ[𝕜] E} (hT : IsPositive T) (x : E)
  statement: 0 <= ⟪T x, x⟫
  proof: (T.isPositive_iff.mp hT).right x

中文:
定理 IsPositive.inner_nonneg_left
  条件: {T : E ->ₗ[𝕜] E} (hT : IsPositive T) (x : E)
  结论: 0 <= ⟪T x, x⟫
  证明: (T.isPositive_iff.mp hT).right x

Depends on / 依赖: T.isPositive_iff.mp, isPositive_iff
-/
theorem IsPositive.inner_nonneg_left {T : E ->ₗ[𝕜] E} (hT : IsPositive T) (x : E) : 0 <= ⟪T x, x⟫ :=
  (T.isPositive_iff.mp hT).right x

/--
theorem `IsPositive.inner_nonneg_right` / 定理 `IsPositive.inner_nonneg_right`

English:
theorem IsPositive.inner_nonneg_right
  given: {T : E ->ₗ[𝕜] E} (hT : IsPositive T) (x : E)
  proof: hT.isSymmetric _ _ ▸ hT.inner_nonneg_left x

@[simp]

中文:
定理 IsPositive.inner_nonneg_right
  条件: {T : E ->ₗ[𝕜] E} (hT : IsPositive T) (x : E)
  证明: hT.isSymmetric _ _ ▸ hT.inner_nonneg_left x

@[simp]

Depends on / 依赖: hT.inner_nonneg_left, hT.isSymmetric, inner_nonneg_left, isSymmetric
-/
theorem IsPositive.inner_nonneg_right {T : E ->ₗ[𝕜] E} (hT : IsPositive T) (x : E) :
    0 <= ⟪x, T x⟫ :=
  hT.isSymmetric _ _ ▸ hT.inner_nonneg_left x

@[simp]
/--
theorem `isPositive_zero` / 定理 `isPositive_zero`

English:
theorem isPositive_zero
  statement: IsPositive (0 : E ->ₗ[𝕜] E)
  proof: ⟨.zero, by simp⟩

@[simp]

中文:
定理 isPositive_zero
  结论: IsPositive (0 : E ->ₗ[𝕜] E)
  证明: ⟨.zero, by simp⟩

@[simp]
-/
theorem isPositive_zero : IsPositive (0 : E ->ₗ[𝕜] E) := ⟨.zero, by simp⟩

@[simp]
/--
theorem `isPositive_one` / 定理 `isPositive_one`

English:
theorem isPositive_one
  statement: IsPositive (1 : E ->ₗ[𝕜] E)
  proof: ⟨.id, fun _ => inner_self_nonneg⟩

@[simp]

中文:
定理 isPositive_one
  结论: IsPositive (1 : E ->ₗ[𝕜] E)
  证明: ⟨.id, fun _ => inner_self_nonneg⟩

@[simp]

Depends on / 依赖: inner_self_nonneg
-/
theorem isPositive_one : IsPositive (1 : E ->ₗ[𝕜] E) := ⟨.id, fun _ => inner_self_nonneg⟩

@[simp]
/--
theorem `isPositive_id` / 定理 `isPositive_id`

English:
theorem isPositive_id
  statement: IsPositive (id : E ->ₗ[𝕜] E)
  proof: isPositive_one

@[simp]

中文:
定理 isPositive_id
  结论: IsPositive (id : E ->ₗ[𝕜] E)
  证明: isPositive_one

@[simp]

Depends on / 依赖: isPositive_one
-/
theorem isPositive_id : IsPositive (id : E ->ₗ[𝕜] E) := isPositive_one

@[simp]
/--
theorem `isPositive_natCast` / 定理 `isPositive_natCast`

English:
theorem isPositive_natCast
  given: {n : Nat}
  statement: IsPositive (n : E ->ₗ[𝕜] E)
  proof: by
  refine ⟨IsSymmetric.natCast n, fun x => ?_⟩
  simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, map_natCast,
    mul_re, natCast_re, inner_self_im, mul_zero, sub_zero]
  positivity [inner_self_nonneg (x := x) (𝕜 := 𝕜)]

@[simp]

中文:
定理 isPositive_natCast
  条件: {n : 自然数}
  结论: IsPositive (n : E ->ₗ[𝕜] E)
  证明: by
  refine ⟨IsSymmetric.natCast n, fun x => ?_⟩
  simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, map_natCast,
    mul_re, natCast_re, inner_self_im, mul_zero, sub_zero]
  positivity [inner_self_nonneg (x := x) (𝕜 := 𝕜)]

@[simp]

Depends on / 依赖: IsSymmetric, IsSymmetric.natCast, Module, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, inner_self_im, inner_self_nonneg, inner_smul_left, map_natCast, mul_re, mul_zero, natCast, natCast_apply, natCast_re, sub_zero
-/
theorem isPositive_natCast {n : Nat} : IsPositive (n : E ->ₗ[𝕜] E) := by
  refine ⟨IsSymmetric.natCast n, fun x => ?_⟩
  simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, map_natCast,
    mul_re, natCast_re, inner_self_im, mul_zero, sub_zero]
  positivity [inner_self_nonneg (x := x) (𝕜 := 𝕜)]

@[simp]
/--
theorem `isPositive_ofNat` / 定理 `isPositive_ofNat`

English:
theorem isPositive_ofNat
  given: {n : Nat} [n.AtLeastTwo]
  statement: IsPositive (ofNat(n) : E ->ₗ[𝕜] E)
  proof: isPositive_natCast

@[aesop safe apply]

中文:
定理 isPositive_of自然数
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: IsPositive (of自然数(n) : E ->ₗ[𝕜] E)
  证明: isPositive_natCast

@[aesop safe apply]

Depends on / 依赖: isPositive_natCast
-/
theorem isPositive_ofNat {n : Nat} [n.AtLeastTwo] : IsPositive (ofNat(n) : E ->ₗ[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
/--
theorem `IsPositive.add` / 定理 `IsPositive.add`

English:
theorem IsPositive.add
  given: {T S : E ->ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
  proof: by
  refine ⟨hT.isSymmetric.add hS.isSymmetric, fun x => ?_⟩
  rw [add_apply]; rw [inner_add_left]; rw [map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)

中文:
定理 IsPositive.add
  条件: {T S : E ->ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
  证明: by
  refine ⟨hT.isSymmetric.add hS.isSymmetric, fun x => ?_⟩
  rw [add_apply]; rw [inner_add_left]; rw [map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)

Depends on / 依赖: add_apply, add_nonneg, hS.isSymmetric, hS.re_inner_nonneg_left, hT.isSymmetric.add, hT.re_inner_nonneg_left, inner_add_left, isSymmetric, map_add, re_inner_nonneg_left
-/
theorem IsPositive.add {T S : E ->ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive := by
  refine ⟨hT.isSymmetric.add hS.isSymmetric, fun x => ?_⟩
  rw [add_apply]; rw [inner_add_left]; rw [map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)

/--
theorem `isPositive_sum` / 定理 `isPositive_sum`

English:
theorem isPositive_sum
  statement: {ι : Type*} {T : ι -> (E ->ₗ[𝕜] E)} (s : Finset ι)
  proof: by
  refine ⟨isSymmetric_sum s fun _ hi => (hT _ hi).isSymmetric, fun _ => ?_⟩
  simpa [sum_inner] using Finset.sum_nonneg fun _ hi => (hT _ hi).re_inner_nonneg_left _

中文:
定理 isPositive_sum
  结论: {ι : 类型} {T : ι -> (E ->ₗ[𝕜] E)} (s : 有限集 ι)
  证明: by
  refine ⟨isSymmetric_sum s fun _ hi => (hT _ hi).isSymmetric, fun _ => ?_⟩
  simpa [sum_inner] using Finset.sum_nonneg fun _ hi => (hT _ hi).re_inner_nonneg_left _

Depends on / 依赖: Finset, Finset.sum_nonneg, isSymmetric, isSymmetric_sum, re_inner_nonneg_left, sum_inner, sum_nonneg
-/
theorem isPositive_sum {ι : Type*} {T : ι -> (E ->ₗ[𝕜] E)} (s : Finset ι)
    (hT : forall i in s, (T i).IsPositive) : (∑ i in s, T i).IsPositive := by
  refine ⟨isSymmetric_sum s fun _ hi => (hT _ hi).isSymmetric, fun _ => ?_⟩
  simpa [sum_inner] using Finset.sum_nonneg fun _ hi => (hT _ hi).re_inner_nonneg_left _

/--
theorem `IsPositive.ne_zero_iff` / 定理 `IsPositive.ne_zero_iff`

English:
theorem IsPositive.ne_zero_iff
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsPositive)
  proof: by
  simp [← hT.isSymmetric.inner_map_self_eq_zero, lt_iff_le_and_ne', hT.inner_nonneg_left]

@[aesop safe apply]

中文:
定理 IsPositive.ne_zero_iff
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsPositive)
  证明: by
  simp [← hT.isSymmetric.inner_map_self_eq_zero, lt_iff_le_and_ne', hT.inner_nonneg_left]

@[aesop safe apply]

Depends on / 依赖: hT.inner_nonneg_left, hT.isSymmetric.inner_map_self_eq_zero, inner_map_self_eq_zero, inner_nonneg_left, isSymmetric, lt_iff_le_and_ne
-/
theorem IsPositive.ne_zero_iff {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) :
    T != 0 ↔ exists x, 0 < inner 𝕜 (T x) x := by
  simp [← hT.isSymmetric.inner_map_self_eq_zero, lt_iff_le_and_ne', hT.inner_nonneg_left]

@[aesop safe apply]
/--
theorem `IsPositive.smul_of_nonneg` / 定理 `IsPositive.smul_of_nonneg`

English:
theorem IsPositive.smul_of_nonneg
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 <= c)
  proof: by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  refine ⟨hT.left.smul hc', fun x => ?_⟩
  rw [smul_apply]; rw [inner_smul_left]; rw [hc']; rw [mul_re]; rw [conj_eq_iff_im.mp hc']; rw [zero_mul]; rw [sub_zero]
  exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)

中文:
定理 IsPositive.smul_of_nonneg
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 <= c)
  证明: by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  refine ⟨hT.left.smul hc', fun x => ?_⟩
  rw [smul_apply]; rw [inner_smul_left]; rw [hc']; rw [mul_re]; rw [conj_eq_iff_im.mp hc']; rw [zero_mul]; rw [sub_zero]
  exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)

Depends on / 依赖: conj_eq_iff_im, conj_eq_iff_im.mp, hT.left.smul, inner_smul_left, le_iff_re_im, le_iff_re_im.mp, mul_nonneg, mul_re, re_inner_nonneg_left, re_nonneg_of_nonneg, smul_apply, starRingEnd, sub_zero, zero_mul
-/
theorem IsPositive.smul_of_nonneg {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 <= c) :
    (c • T).IsPositive := by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  refine ⟨hT.left.smul hc', fun x => ?_⟩
  rw [smul_apply]; rw [inner_smul_left]; rw [hc']; rw [mul_re]; rw [conj_eq_iff_im.mp hc']; rw [zero_mul]; rw [sub_zero]
  exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)

/--
theorem `IsPositive.isPositive_smul_iff` / 定理 `IsPositive.isPositive_smul_iff`

English:
theorem IsPositive.isPositive_smul_iff
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) (hT' : T != 0) {α : 𝕜}
  proof: by
  refine ⟨fun h => ?_, hT.smul_of_nonneg⟩
  obtain ⟨x, hx⟩ := by simpa only [hT.1 _] using hT.ne_zero_iff.mp hT'
  have := by simpa [inner_smul_right] using h.inner_nonneg_right x
  exact le_of_smul_le_smul_of_pos_right (by simpa) hx

中文:
定理 IsPositive.isPositive_smul_iff
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) (hT' : T != 0) {α : 𝕜}
  证明: by
  refine ⟨fun h => ?_, hT.smul_of_nonneg⟩
  obtain ⟨x, hx⟩ := by simpa only [hT.1 _] using hT.ne_zero_iff.mp hT'
  have := by simpa [inner_smul_right] using h.inner_nonneg_right x
  exact le_of_smul_le_smul_of_pos_right (by simpa) hx

Depends on / 依赖: h.inner_nonneg_right, hT.ne_zero_iff.mp, hT.smul_of_nonneg, inner_nonneg_right, inner_smul_right, le_of_smul_le_smul_of_pos_right, ne_zero_iff, smul_of_nonneg
-/
theorem IsPositive.isPositive_smul_iff {T : E ->ₗ[𝕜] E} (hT : T.IsPositive) (hT' : T != 0) {α : 𝕜} :
    (α • T).IsPositive ↔ 0 <= α := by
  refine ⟨fun h => ?_, hT.smul_of_nonneg⟩
  obtain ⟨x, hx⟩ := by simpa only [hT.1 _] using hT.ne_zero_iff.mp hT'
  have := by simpa [inner_smul_right] using h.inner_nonneg_right x
  exact le_of_smul_le_smul_of_pos_right (by simpa) hx

/--
theorem `IsPositive.nonneg_eigenvalues` / 定理 `IsPositive.nonneg_eigenvalues`

English:
theorem IsPositive.nonneg_eigenvalues
  statement: [FiniteDimensional 𝕜 E]
  proof: by
  simpa only [hT.isSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
      using hT.right (hT.isSymmetric.eigenvectorBasis hn i)

中文:
定理 IsPositive.nonneg_eigenvalues
  结论: [有限维 𝕜 E]
  证明: by
  simpa only [hT.isSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
      using hT.right (hT.isSymmetric.eigenvectorBasis hn i)

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.norm_eq_one, RCLike, RCLike.smul_re, apply_eigenvectorBasis, eigenvectorBasis, hT.isSymmetric.apply_eigenvectorBasis, hT.isSymmetric.eigenvectorBasis, hT.right, inner_self_eq_norm_sq, inner_smul_real_left, isSymmetric, mul_one, norm_eq_one, one_pow, smul_re
-/
theorem IsPositive.nonneg_eigenvalues [FiniteDimensional 𝕜 E]
    {T : E ->ₗ[𝕜] E} {n : Nat} (hT : T.IsPositive)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 <= hT.isSymmetric.eigenvalues hn i := by
  simpa only [hT.isSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
      using hT.right (hT.isSymmetric.eigenvectorBasis hn i)

section PartialOrder

/--
Instance `instLoewnerPartialOrder` / 实例 `instLoewnerPartialOrder`

English:
instance instLoewnerPartialOrder
  signature: : PartialOrder (E ->ₗ[𝕜] E) where
  body: (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]; rw [← h₂.isSymmetric.inner_map_self_eq_zero]
    intro x
    have hba2 := h₁.2 x
    rw [← neg_le_neg_iff]; rw [← map_neg]; rw [← inner_neg_left]; rw [← neg_apply]; rw [neg_sub]; rw [neg_zero] at hba2
    rw [← h₂.isSymmetric.coe_re_inner_apply_self]; rw [RCLike.ofReal_eq_zero]
    exact le_antisymm hba2 (h₂.2 _)

中文:
实例 instLoewnerPartialOrder
  签名: : 偏序 (E ->ₗ[𝕜] E) where
  定义体: (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]; rw [← h₂.isSymmetric.inner_map_self_eq_zero]
    intro x
    have hba2 := h₁.2 x
    rw [← neg_le_neg_iff]; rw [← map_neg]; rw [← inner_neg_left]; rw [← neg_apply]; rw [neg_sub]; rw [neg_zero] at hba2
    rw [← h₂.isSymmetric.coe_re_inner_apply_self]; rw [RCLike.ofReal_eq_zero]
    exact le_antisymm hba2 (h₂.2 _)

Depends on / 依赖: IsPositive
-/
instance instLoewnerPartialOrder : PartialOrder (E ->ₗ[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]; rw [← h₂.isSymmetric.inner_map_self_eq_zero]
    intro x
    have hba2 := h₁.2 x
    rw [← neg_le_neg_iff]; rw [← map_neg]; rw [← inner_neg_left]; rw [← neg_apply]; rw [neg_sub]; rw [neg_zero] at hba2
    rw [← h₂.isSymmetric.coe_re_inner_apply_self]; rw [RCLike.ofReal_eq_zero]
    exact le_antisymm hba2 (h₂.2 _)

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: (f g : E ->ₗ[𝕜] E)
  statement: f <= g ↔ (g - f).IsPositive
  proof: Iff.rfl

中文:
引理 le_def
  条件: (f g : E ->ₗ[𝕜] E)
  结论: f <= g ↔ (g - f).IsPositive
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def (f g : E ->ₗ[𝕜] E) : f <= g ↔ (g - f).IsPositive := Iff.rfl

/--
lemma `nonneg_iff_isPositive` / 引理 `nonneg_iff_isPositive`

English:
lemma nonneg_iff_isPositive
  given: (f : E ->ₗ[𝕜] E)
  statement: 0 <= f ↔ f.IsPositive
  proof: by
  simpa using le_def 0 f

中文:
引理 nonneg_iff_isPositive
  条件: (f : E ->ₗ[𝕜] E)
  结论: 0 <= f ↔ f.IsPositive
  证明: by
  simpa using le_def 0 f

Depends on / 依赖: le_def
-/
lemma nonneg_iff_isPositive (f : E ->ₗ[𝕜] E) : 0 <= f ↔ f.IsPositive := by
  simpa using le_def 0 f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (E ->ₗ[𝕜] E)
  body: by simpa [le_def]

中文:
实例 :
  签名: 是OrderedAdd幺半群 (E ->ₗ[𝕜] E)
  定义体: by simpa [le_def]

Depends on / 依赖: le_def
-/
instance : IsOrderedAddMonoid (E ->ₗ[𝕜] E) where add_le_add_left a b hab c := by simpa [le_def]

end PartialOrder

/--
theorem `IsIdempotentElem.isPositive_iff_isSymmetric` / 定理 `IsIdempotentElem.isPositive_iff_isSymmetric`

English:
theorem IsIdempotentElem.isPositive_iff_isSymmetric
  given: {T : E ->ₗ[𝕜] E} (hT : IsIdempotentElem T)
  proof: by
  refine ⟨fun h => h.isSymmetric, fun h => ⟨h, fun x => ?_⟩⟩
  rw [← hT.eq]; rw [Module.End.mul_apply]; rw [h]
  exact inner_self_nonneg

中文:
定理 IsIdempotentElem.isPositive_iff_isSymmetric
  条件: {T : E ->ₗ[𝕜] E} (hT : IsIdempotentElem T)
  证明: by
  refine ⟨fun h => h.isSymmetric, fun h => ⟨h, fun x => ?_⟩⟩
  rw [← hT.eq]; rw [Module.End.mul_apply]; rw [h]
  exact inner_self_nonneg

Depends on / 依赖: Module, Module.End.mul_apply, h.isSymmetric, hT.eq, inner_self_nonneg, isSymmetric, mul_apply
-/
theorem IsIdempotentElem.isPositive_iff_isSymmetric {T : E ->ₗ[𝕜] E} (hT : IsIdempotentElem T) :
    T.IsPositive ↔ T.IsSymmetric := by
  refine ⟨fun h => h.isSymmetric, fun h => ⟨h, fun x => ?_⟩⟩
  rw [← hT.eq]; rw [Module.End.mul_apply]; rw [h]
  exact inner_self_nonneg

/--
theorem `isPositive_linearIsometryEquiv_conj_iff` / 定理 `isPositive_linearIsometryEquiv_conj_iff`

English:
theorem isPositive_linearIsometryEquiv_conj_iff
  given: {T : E ->ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F)
  proof: by
  simp_rw [IsPositive, isSymmetric_linearIsometryEquiv_conj_iff, and_congr_right_iff,
    LinearIsometryEquiv.toLinearEquiv_symm, coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    Function.comp_apply, LinearIsometryEquiv.inner_map_eq_flip]
  exact fun _ => ⟨fun h x => by simpa using h (f x), fun h x => h _⟩

中文:
定理 isPositive_linearIsometryEquiv_conj_iff
  条件: {T : E ->ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F)
  证明: by
  simp_rw [IsPositive, isSymmetric_linearIsometryEquiv_conj_iff, and_congr_right_iff,
    LinearIsometryEquiv.toLinearEquiv_symm, coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    Function.comp_apply, LinearIsometryEquiv.inner_map_eq_flip]
  exact fun _ => ⟨fun h x => by simpa using h (f x), fun h x => h _⟩

Depends on / 依赖: Function, Function.comp_apply, IsPositive, LinearEquiv, LinearEquiv.coe_coe, LinearIsometryEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.toLinearEquiv_symm, and_congr_right_iff, coe_coe, coe_comp, coe_symm_toLinearEquiv, coe_toLinearEquiv, comp_apply, inner_map_eq_flip, isSymmetric_linearIsometryEquiv_conj_iff, simp_rw, toLinearEquiv_symm
-/
theorem isPositive_linearIsometryEquiv_conj_iff {T : E ->ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F) :
    IsPositive (f.toLinearMap ∘ₗ T ∘ₗ f.symm.toLinearMap) ↔ IsPositive T := by
  simp_rw [IsPositive, isSymmetric_linearIsometryEquiv_conj_iff, and_congr_right_iff,
    LinearIsometryEquiv.toLinearEquiv_symm, coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    Function.comp_apply, LinearIsometryEquiv.inner_map_eq_flip]
  exact fun _ => ⟨fun h x => by simpa using h (f x), fun h x => h _⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `_root_.Matrix.isPositive_toEuclideanLin_iff` / 定理 `_root_.Matrix.isPositive_toEuclideanLin_iff`

English:
theorem _root_.Matrix.isPositive_toEuclideanLin_iff
  statement: {n : Type*} [Fintype n] [DecidableEq n]
  proof: by
  simp_rw [LinearMap.IsPositive, Matrix.isSymmetric_toEuclideanLin_iff, inner_re_symm,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    dotProduct_comm (A.mulVec _), Matrix.posSemidef_iff_dotProduct_mulVec, and_congr_right_iff,
    RCLike.nonneg_iff (K := 𝕜)]
  refine fun hA => (EuclideanSpace.equiv n 𝕜).forall_congr' fun x => ?_
  simp [hA.im_star_dotProduct_mulVec_self]

中文:
定理 _root_.矩阵.isPositive_toEuclideanLin_iff
  结论: {n : 类型} [有限类型 n] [DecidableEq n]
  证明: by
  simp_rw [LinearMap.IsPositive, Matrix.isSymmetric_toEuclideanLin_iff, inner_re_symm,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    dotProduct_comm (A.mulVec _), Matrix.posSemidef_iff_dotProduct_mulVec, and_congr_right_iff,
    RCLike.nonneg_iff (K := 𝕜)]
  refine fun hA => (EuclideanSpace.equiv n 𝕜).forall_congr' fun x => ?_
  simp [hA.im_star_dotProduct_mulVec_self]
-/
@[simp] theorem _root_.Matrix.isPositive_toEuclideanLin_iff {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} : A.toEuclideanLin.IsPositive ↔ A.PosSemidef := by
  simp_rw [LinearMap.IsPositive, Matrix.isSymmetric_toEuclideanLin_iff, inner_re_symm,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    dotProduct_comm (A.mulVec _), Matrix.posSemidef_iff_dotProduct_mulVec, and_congr_right_iff,
    RCLike.nonneg_iff (K := 𝕜)]
  refine fun hA => (EuclideanSpace.equiv n 𝕜).forall_congr' fun x => ?_
  simp [hA.im_star_dotProduct_mulVec_self]

/--
theorem `posSemidef_toMatrix_iff` / 定理 `posSemidef_toMatrix_iff`

English:
theorem posSemidef_toMatrix_iff
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι]
  proof: by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  convert! isPositive_linearIsometryEquiv_conj_iff b.repr
  ext
  simp [LinearMap.toMatrix]

中文:
定理 posSemidef_toMatrix_iff
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι]
  证明: by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  convert! isPositive_linearIsometryEquiv_conj_iff b.repr
  ext
  simp [LinearMap.toMatrix]
-/
@[simp] theorem posSemidef_toMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : E ->ₗ[𝕜] E} (b : OrthonormalBasis ι 𝕜 E) :
    (A.toMatrix b.toBasis b.toBasis).PosSemidef ↔ A.IsPositive := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  convert! isPositive_linearIsometryEquiv_conj_iff b.repr
  ext
  simp [LinearMap.toMatrix]

/-- A symmetric projection is positive. -/
@[aesop 10% apply, grind ->]
/--
theorem `IsSymmetricProjection.isPositive` / 定理 `IsSymmetricProjection.isPositive`

English:
theorem IsSymmetricProjection.isPositive
  given: {p : E ->ₗ[𝕜] E} (hp : p.IsSymmetricProjection)
  proof: hp.isIdempotentElem.isPositive_iff_isSymmetric.mpr hp.isSymmetric

中文:
定理 是SymmetricProjection.isPositive
  条件: {p : E ->ₗ[𝕜] E} (hp : p.是SymmetricProjection)
  证明: hp.isIdempotentElem.isPositive_iff_isSymmetric.mpr hp.isSymmetric

Depends on / 依赖: hp.isIdempotentElem.isPositive_iff_isSymmetric.mpr, hp.isSymmetric, isIdempotentElem, isPositive_iff_isSymmetric, isSymmetric
-/
theorem IsSymmetricProjection.isPositive {p : E ->ₗ[𝕜] E} (hp : p.IsSymmetricProjection) :
    p.IsPositive :=
  hp.isIdempotentElem.isPositive_iff_isSymmetric.mpr hp.isSymmetric

/--
theorem `IsSymmetricProjection.le_iff_range_le_range` / 定理 `IsSymmetricProjection.le_iff_range_le_range`

English:
theorem IsSymmetricProjection.le_iff_range_le_range
  statement: {p q : E ->ₗ[𝕜] E}
  proof: by
  refine ⟨fun ⟨h1, h2⟩ a ha => ?_, fun hpq => (hp.sub_of_range_le_range hq hpq).isPositive⟩
  specialize h2 a
  have hh {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetricProjection) : RCLike.re ⟪T a, a⟫_𝕜 = ‖T a‖ ^ 2 := by
    conv_lhs => rw [← hT.isIdempotentElem]
    rw [Module.End.mul_apply]; rw [hT.isSymmetric]
    exact inner_self_eq_norm_sq _
  simp_rw [sub_apply, inner_sub_left, map_sub, hh hq, hh hp,
    hp.isIdempotentElem.mem_range_iff.mp ha, sub_nonneg, sq_le_sq, abs_norm] at h2
  obtain ⟨U, _, rfl⟩ := isSymmetricProjection_iff_eq_coe_starProjection.mp hq
  simpa [Submodule.toLinearMap_starProjection_eq_isComplProjection] using
.mpr le_antisymm (U.norm_starProjection_apply_le a) h2 U.mem_iff_norm_starProjection _

中文:
定理 是SymmetricProjection.le_iff_range_le_range
  结论: {p q : E ->ₗ[𝕜] E}
  证明: by
  refine ⟨fun ⟨h1, h2⟩ a ha => ?_, fun hpq => (hp.sub_of_range_le_range hq hpq).isPositive⟩
  specialize h2 a
  have hh {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetricProjection) : RCLike.re ⟪T a, a⟫_𝕜 = ‖T a‖ ^ 2 := by
    conv_lhs => rw [← hT.isIdempotentElem]
    rw [Module.End.mul_apply]; rw [hT.isSymmetric]
    exact inner_self_eq_norm_sq _
  simp_rw [sub_apply, inner_sub_left, map_sub, hh hq, hh hp,
    hp.isIdempotentElem.mem_range_iff.mp ha, sub_nonneg, sq_le_sq, abs_norm] at h2
  obtain ⟨U, _, rfl⟩ := isSymmetricProjection_iff_eq_coe_starProjection.mp hq
  simpa [Submodule.toLinearMap_starProjection_eq_isComplProjection] using
.mpr le_antisymm (U.norm_starProjection_apply_le a) h2 U.mem_iff_norm_starProjection _

Depends on / 依赖: IsSymmetricProjection, Module, Module.End.mul_apply, RCLike, RCLike.re, T.IsSymmetricProjection, abs_norm, conv_lhs, hT.isIdempotentElem, hT.isSymmetric, hp.isIdempotentElem.mem_range_iff.mp, hp.sub_of_range_le_range, inner_self_eq_norm_sq, inner_sub_left, isIdempotentElem, isPositive, isSymmetric, isSymmetricProject, map_sub, mem_range_iff
-/
theorem IsSymmetricProjection.le_iff_range_le_range {p q : E ->ₗ[𝕜] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) : p <= q ↔ range p <= range q := by
  refine ⟨fun ⟨h1, h2⟩ a ha => ?_, fun hpq => (hp.sub_of_range_le_range hq hpq).isPositive⟩
  specialize h2 a
  have hh {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetricProjection) : RCLike.re ⟪T a, a⟫_𝕜 = ‖T a‖ ^ 2 := by
    conv_lhs => rw [← hT.isIdempotentElem]
    rw [Module.End.mul_apply]; rw [hT.isSymmetric]
    exact inner_self_eq_norm_sq _
  simp_rw [sub_apply, inner_sub_left, map_sub, hh hq, hh hp,
    hp.isIdempotentElem.mem_range_iff.mp ha, sub_nonneg, sq_le_sq, abs_norm] at h2
  obtain ⟨U, _, rfl⟩ := isSymmetricProjection_iff_eq_coe_starProjection.mp hq
  simpa [Submodule.toLinearMap_starProjection_eq_isComplProjection] using
.mpr le_antisymm (U.norm_starProjection_apply_le a) h2 U.mem_iff_norm_starProjection _

/--
theorem `IsPositive.trace_nonneg` / 定理 `IsPositive.trace_nonneg`

English:
theorem IsPositive.trace_nonneg
  given: {f : E ->ₗ[𝕜] E} (hf : f.IsPositive)
  statement: 0 <= f.trace 𝕜 E
  proof: by
  unfold trace
  split_ifs with h
  · have : FiniteDimensional 𝕜 E := Module.Finite.of_basis h.choose_spec.some
    simp_rw [traceAux_eq 𝕜 _ (stdOrthonormalBasis 𝕜 E).toBasis]
.trace_nonneg .mpr hf exact posSemidef_toMatrix_iff (stdOrthonormalBasis 𝕜 E)
  · simp

中文:
定理 IsPositive.trace_nonneg
  条件: {f : E ->ₗ[𝕜] E} (hf : f.IsPositive)
  结论: 0 <= f.trace 𝕜 E
  证明: by
  unfold trace
  split_ifs with h
  · have : FiniteDimensional 𝕜 E := Module.Finite.of_basis h.choose_spec.some
    simp_rw [traceAux_eq 𝕜 _ (stdOrthonormalBasis 𝕜 E).toBasis]
.trace_nonneg .mpr hf exact posSemidef_toMatrix_iff (stdOrthonormalBasis 𝕜 E)
  · simp

Depends on / 依赖: Finite, FiniteDimensional, Module, Module.Finite.of_basis, choose_spec, h.choose_spec.some, of_basis, posSemidef_toMatrix_iff, simp_rw, split_ifs, stdOrthonormalBasis, toBasis, traceAux_eq, trace_nonneg
-/
theorem IsPositive.trace_nonneg {f : E ->ₗ[𝕜] E} (hf : f.IsPositive) : 0 <= f.trace 𝕜 E := by
  unfold trace
  split_ifs with h
  · have : FiniteDimensional 𝕜 E := Module.Finite.of_basis h.choose_spec.some
    simp_rw [traceAux_eq 𝕜 _ (stdOrthonormalBasis 𝕜 E).toBasis]
.trace_nonneg .mpr hf exact posSemidef_toMatrix_iff (stdOrthonormalBasis 𝕜 E)
  · simp

variable (𝕜 E) in
/--
Definition of `tracePositiveLinearMap` / `tracePositiveLinearMap` 的定义

English:
definition tracePositiveLinearMap
  signature: : (E ->ₗ[𝕜] E) ->ₚ[𝕜] 𝕜
  body: .mk₀ (LinearMap.trace 𝕜 E) fun x h => sub_zero x ▸ h.trace_nonneg

中文:
定义 tracePositiveLinearMap
  签名: : (E ->ₗ[𝕜] E) ->ₚ[𝕜] 𝕜
  定义体: .mk₀ (LinearMap.trace 𝕜 E) fun x h => sub_zero x ▸ h.trace_nonneg

Depends on / 依赖: LinearMap, LinearMap.trace, h.trace_nonneg, sub_zero, trace_nonneg
-/
noncomputable def tracePositiveLinearMap : (E ->ₗ[𝕜] E) ->ₚ[𝕜] 𝕜 :=
  .mk₀ (LinearMap.trace 𝕜 E) fun x h => sub_zero x ▸ h.trace_nonneg

/--
lemma `toLinearMap_tracePositiveLinearMap` / 引理 `toLinearMap_tracePositiveLinearMap`

English:
lemma toLinearMap_tracePositiveLinearMap
  proof: rfl

中文:
引理 toLinearMap_tracePositiveLinearMap
  证明: rfl
-/
@[simp] lemma toLinearMap_tracePositiveLinearMap :
    (tracePositiveLinearMap 𝕜 E).toLinearMap = trace 𝕜 E := rfl

/--
lemma `tracePositiveLinearMap_apply` / 引理 `tracePositiveLinearMap_apply`

English:
lemma tracePositiveLinearMap_apply
  given: (x)
  statement: tracePositiveLinearMap 𝕜 E x = x.trace 𝕜 E
  proof: rfl

中文:
引理 tracePositiveLinearMap_apply
  条件: (x)
  结论: tracePositiveLinearMap 𝕜 E x = x.trace 𝕜 E
  证明: rfl
-/
@[simp] lemma tracePositiveLinearMap_apply (x) : tracePositiveLinearMap 𝕜 E x = x.trace 𝕜 E := rfl

end LinearMap

namespace ContinuousLinearMap

/--
Definition of `IsPositive` / `IsPositive` 的定义

English:
definition IsPositive
  signature: (T : E ->L[𝕜] E)
  body: T.IsSymmetric ∧ forall x, 0 <= T.reApplyInnerSelf x

中文:
定义 IsPositive
  签名: (T : E ->L[𝕜] E)
  定义体: T.IsSymmetric ∧ forall x, 0 <= T.reApplyInnerSelf x

Depends on / 依赖: IsSymmetric, T.IsSymmetric, T.reApplyInnerSelf, reApplyInnerSelf
-/
def IsPositive (T : E ->L[𝕜] E) : Prop :=
  T.IsSymmetric ∧ forall x, 0 <= T.reApplyInnerSelf x

/--
theorem `isPositive_def` / 定理 `isPositive_def`

English:
theorem isPositive_def
  given: {T : E ->L[𝕜] E}
  proof: Iff.rfl

中文:
定理 isPositive_def
  条件: {T : E ->L[𝕜] E}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isPositive_def {T : E ->L[𝕜] E} :
    T.IsPositive ↔ T.IsSymmetric ∧ forall x, 0 <= T.reApplyInnerSelf x := Iff.rfl

/--
theorem `isPositive_def'` / 定理 `isPositive_def'`

English:
theorem isPositive_def'
  given: [CompleteSpace E] {T : E ->L[𝕜] E}
  proof: by
  simp [IsPositive, isSelfAdjoint_iff_isSymmetric, LinearMap.IsSymmetric]

中文:
定理 isPositive_def'
  条件: [完备空间 E] {T : E ->L[𝕜] E}
  证明: by
  simp [IsPositive, isSelfAdjoint_iff_isSymmetric, LinearMap.IsSymmetric]

Depends on / 依赖: IsPositive, IsSymmetric, LinearMap, LinearMap.IsSymmetric, isSelfAdjoint_iff_isSymmetric
-/
theorem isPositive_def' [CompleteSpace E] {T : E ->L[𝕜] E} :
    T.IsPositive ↔ IsSelfAdjoint T ∧ forall x, 0 <= T.reApplyInnerSelf x := by
  simp [IsPositive, isSelfAdjoint_iff_isSymmetric, LinearMap.IsSymmetric]

/--
theorem `IsPositive.isSymmetric` / 定理 `IsPositive.isSymmetric`

English:
theorem IsPositive.isSymmetric
  given: {T : E ->L[𝕜] E} (hT : T.IsPositive)
  proof: hT.1

中文:
定理 IsPositive.isSymmetric
  条件: {T : E ->L[𝕜] E} (hT : T.IsPositive)
  证明: hT.1
-/
theorem IsPositive.isSymmetric {T : E ->L[𝕜] E} (hT : T.IsPositive) :
    T.IsSymmetric := hT.1

/--
theorem `IsPositive.isSelfAdjoint` / 定理 `IsPositive.isSelfAdjoint`

English:
theorem IsPositive.isSelfAdjoint
  given: [CompleteSpace E] {T : E ->L[𝕜] E} (hT : IsPositive T)
  proof: hT.isSymmetric.isSelfAdjoint

中文:
定理 IsPositive.isSelfAdjoint
  条件: [完备空间 E] {T : E ->L[𝕜] E} (hT : IsPositive T)
  证明: hT.isSymmetric.isSelfAdjoint
-/
theorem IsPositive.isSelfAdjoint [CompleteSpace E] {T : E ->L[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := hT.isSymmetric.isSelfAdjoint

/--
theorem `IsPositive.inner_left_eq_inner_right` / 定理 `IsPositive.inner_left_eq_inner_right`

English:
theorem IsPositive.inner_left_eq_inner_right
  given: {T : E ->L[𝕜] E} (hT : IsPositive T) (x y : E)
  proof: hT.isSymmetric _ _

中文:
定理 IsPositive.inner_left_eq_inner_right
  条件: {T : E ->L[𝕜] E} (hT : IsPositive T) (x y : E)
  证明: hT.isSymmetric _ _

Depends on / 依赖: hT.isSymmetric, isSymmetric
-/
theorem IsPositive.inner_left_eq_inner_right {T : E ->L[𝕜] E} (hT : IsPositive T) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ := hT.isSymmetric _ _

/--
theorem `IsPositive.re_inner_nonneg_left` / 定理 `IsPositive.re_inner_nonneg_left`

English:
theorem IsPositive.re_inner_nonneg_left
  given: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  proof: hT.2 x

中文:
定理 IsPositive.re_inner_nonneg_left
  条件: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  证明: hT.2 x
-/
theorem IsPositive.re_inner_nonneg_left {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 <= re ⟪T x, x⟫ := hT.2 x

/--
lemma `_root_.LinearMap.isPositive_toContinuousLinearMap_iff` / 引理 `_root_.LinearMap.isPositive_toContinuousLinearMap_iff`

English:
lemma _root_.LinearMap.isPositive_toContinuousLinearMap_iff
  proof: Iff.rfl

中文:
引理 _root_.线性映射.isPositive_toContinuousLinearMap_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma _root_.LinearMap.isPositive_toContinuousLinearMap_iff
    [FiniteDimensional 𝕜 E] (T : E ->ₗ[𝕜] E) :
    T.toContinuousLinearMap.IsPositive ↔ T.IsPositive := Iff.rfl

/--
lemma `isPositive_toLinearMap_iff` / 引理 `isPositive_toLinearMap_iff`

English:
lemma isPositive_toLinearMap_iff
  given: (T : E ->L[𝕜] E)
  proof: Iff.rfl

alias ⟨_, IsPositive.toLinearMap⟩ := isPositive_toLinearMap_iff

中文:
引理 isPositive_toLinearMap_iff
  条件: (T : E ->L[𝕜] E)
  证明: Iff.rfl

alias ⟨_, IsPositive.toLinearMap⟩ := isPositive_toLinearMap_iff

Depends on / 依赖: Iff.rfl
-/
lemma isPositive_toLinearMap_iff (T : E ->L[𝕜] E) :
    (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive := Iff.rfl

alias ⟨_, IsPositive.toLinearMap⟩ := isPositive_toLinearMap_iff

/--
theorem `IsPositive.re_inner_nonneg_right` / 定理 `IsPositive.re_inner_nonneg_right`

English:
theorem IsPositive.re_inner_nonneg_right
  given: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  proof: hT.toLinearMap.re_inner_nonneg_right x

中文:
定理 IsPositive.re_inner_nonneg_right
  条件: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  证明: hT.toLinearMap.re_inner_nonneg_right x
-/
theorem IsPositive.re_inner_nonneg_right {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 <= re ⟪x, T x⟫ := hT.toLinearMap.re_inner_nonneg_right x

/--
theorem `isPositive_iff` / 定理 `isPositive_iff`

English:
theorem isPositive_iff
  given: (T : E ->L[𝕜] E)
  proof: LinearMap.isPositive_iff _

中文:
定理 isPositive_iff
  条件: (T : E ->L[𝕜] E)
  证明: LinearMap.isPositive_iff _

Depends on / 依赖: LinearMap, LinearMap.isPositive_iff, isPositive_iff
-/
theorem isPositive_iff (T : E ->L[𝕜] E) :
    IsPositive T ↔ T.IsSymmetric ∧ forall x, 0 <= ⟪T x, x⟫ := LinearMap.isPositive_iff _

/--
theorem `isPositive_iff'` / 定理 `isPositive_iff'`

English:
theorem isPositive_iff'
  given: [CompleteSpace E] (T : E ->L[𝕜] E)
  proof: by
  simp [isSelfAdjoint_iff_isSymmetric, isPositive_iff]

中文:
定理 isPositive_iff'
  条件: [完备空间 E] (T : E ->L[𝕜] E)
  证明: by
  simp [isSelfAdjoint_iff_isSymmetric, isPositive_iff]

Depends on / 依赖: isPositive_iff, isSelfAdjoint_iff_isSymmetric
-/
theorem isPositive_iff' [CompleteSpace E] (T : E ->L[𝕜] E) :
    IsPositive T ↔ IsSelfAdjoint T ∧ forall x, 0 <= ⟪T x, x⟫ := by
  simp [isSelfAdjoint_iff_isSymmetric, isPositive_iff]

/--
theorem `IsPositive.inner_nonneg_left` / 定理 `IsPositive.inner_nonneg_left`

English:
theorem IsPositive.inner_nonneg_left
  given: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  proof: hT.toLinearMap.inner_nonneg_left x

中文:
定理 IsPositive.inner_nonneg_left
  条件: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  证明: hT.toLinearMap.inner_nonneg_left x
-/
theorem IsPositive.inner_nonneg_left {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 <= ⟪T x, x⟫ := hT.toLinearMap.inner_nonneg_left x

/--
theorem `IsPositive.inner_nonneg_right` / 定理 `IsPositive.inner_nonneg_right`

English:
theorem IsPositive.inner_nonneg_right
  given: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  proof: hT.toLinearMap.inner_nonneg_right x

@[simp]

中文:
定理 IsPositive.inner_nonneg_right
  条件: {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E)
  证明: hT.toLinearMap.inner_nonneg_right x

@[simp]
-/
theorem IsPositive.inner_nonneg_right {T : E ->L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 <= ⟪x, T x⟫ := hT.toLinearMap.inner_nonneg_right x

@[simp]
/--
theorem `isPositive_zero` / 定理 `isPositive_zero`

English:
theorem isPositive_zero
  statement: IsPositive (0 : E ->L[𝕜] E)
  proof: LinearMap.isPositive_zero

@[simp]

中文:
定理 isPositive_zero
  结论: IsPositive (0 : E ->L[𝕜] E)
  证明: LinearMap.isPositive_zero

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isPositive_zero, isPositive_zero
-/
theorem isPositive_zero : IsPositive (0 : E ->L[𝕜] E) := LinearMap.isPositive_zero

@[simp]
/--
theorem `isPositive_id` / 定理 `isPositive_id`

English:
theorem isPositive_id
  statement: IsPositive (.id 𝕜 E : E ->L[𝕜] E)
  proof: LinearMap.isPositive_id

@[simp]

中文:
定理 isPositive_id
  结论: IsPositive (.id 𝕜 E : E ->L[𝕜] E)
  证明: LinearMap.isPositive_id

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isPositive_id, isPositive_id
-/
theorem isPositive_id : IsPositive (.id 𝕜 E : E ->L[𝕜] E) := LinearMap.isPositive_id

@[simp]
/--
theorem `isPositive_one` / 定理 `isPositive_one`

English:
theorem isPositive_one
  statement: IsPositive (1 : E ->L[𝕜] E)
  proof: LinearMap.isPositive_one

@[simp]

中文:
定理 isPositive_one
  结论: IsPositive (1 : E ->L[𝕜] E)
  证明: LinearMap.isPositive_one

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isPositive_one, isPositive_one
-/
theorem isPositive_one : IsPositive (1 : E ->L[𝕜] E) := LinearMap.isPositive_one

@[simp]
/--
theorem `isPositive_natCast` / 定理 `isPositive_natCast`

English:
theorem isPositive_natCast
  given: {n : Nat}
  statement: IsPositive (n : E ->L[𝕜] E)
  proof: (isPositive_toLinearMap_iff _).mp LinearMap.isPositive_natCast

@[simp]

中文:
定理 isPositive_natCast
  条件: {n : 自然数}
  结论: IsPositive (n : E ->L[𝕜] E)
  证明: (isPositive_toLinearMap_iff _).mp LinearMap.isPositive_natCast

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isPositive_natCast, isPositive_natCast, isPositive_toLinearMap_iff
-/
theorem isPositive_natCast {n : Nat} : IsPositive (n : E ->L[𝕜] E) :=
  (isPositive_toLinearMap_iff _).mp LinearMap.isPositive_natCast

@[simp]
/--
theorem `isPositive_ofNat` / 定理 `isPositive_ofNat`

English:
theorem isPositive_ofNat
  given: {n : Nat} [n.AtLeastTwo]
  statement: IsPositive (ofNat(n) : E ->L[𝕜] E)
  proof: isPositive_natCast

@[aesop safe apply]

中文:
定理 isPositive_of自然数
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: IsPositive (of自然数(n) : E ->L[𝕜] E)
  证明: isPositive_natCast

@[aesop safe apply]

Depends on / 依赖: isPositive_natCast
-/
theorem isPositive_ofNat {n : Nat} [n.AtLeastTwo] : IsPositive (ofNat(n) : E ->L[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
/--
theorem `IsPositive.add` / 定理 `IsPositive.add`

English:
theorem IsPositive.add
  given: {T S : E ->L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
  proof: (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.add hS.toLinearMap)

中文:
定理 IsPositive.add
  条件: {T S : E ->L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
  证明: (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.add hS.toLinearMap)
-/
theorem IsPositive.add {T S : E ->L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive :=
  (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.add hS.toLinearMap)

/--
theorem `isPositive_sum` / 定理 `isPositive_sum`

English:
theorem isPositive_sum
  statement: {ι : Type*} {T : ι -> (E ->L[𝕜] E)} (s : Finset ι)
  proof: (isPositive_toLinearMap_iff _).mp by simp [LinearMap.isPositive_sum s hT]

@[aesop safe apply]

中文:
定理 isPositive_sum
  结论: {ι : 类型} {T : ι -> (E ->L[𝕜] E)} (s : 有限集 ι)
  证明: (isPositive_toLinearMap_iff _).mp by simp [LinearMap.isPositive_sum s hT]

@[aesop safe apply]

Depends on / 依赖: LinearMap, LinearMap.isPositive_sum, isPositive_sum, isPositive_toLinearMap_iff
-/
theorem isPositive_sum {ι : Type*} {T : ι -> (E ->L[𝕜] E)} (s : Finset ι)
    (hT : forall i in s, (T i).IsPositive) : (∑ i in s, T i).IsPositive :=
(isPositive_toLinearMap_iff _).mp by simp [LinearMap.isPositive_sum s hT]

@[aesop safe apply]
/--
theorem `IsPositive.smul_of_nonneg` / 定理 `IsPositive.smul_of_nonneg`

English:
theorem IsPositive.smul_of_nonneg
  given: {T : E ->L[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 <= c)
  proof: (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.smul_of_nonneg hc)

@[aesop safe apply]

中文:
定理 IsPositive.smul_of_nonneg
  条件: {T : E ->L[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 <= c)
  证明: (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.smul_of_nonneg hc)

@[aesop safe apply]
-/
theorem IsPositive.smul_of_nonneg {T : E ->L[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 <= c) :
    (c • T).IsPositive :=
  (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.smul_of_nonneg hc)

@[aesop safe apply]
/--
theorem `IsPositive.conj_adjoint` / 定理 `IsPositive.conj_adjoint`

English:
theorem IsPositive.conj_adjoint
  statement: [CompleteSpace E] [CompleteSpace F] {T : E ->L[𝕜] E}
  proof: by
  refine isPositive_def'.mpr ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf]; rw [comp_apply]; rw [← adjoint_inner_right]
  exact hT.re_inner_nonneg_left _

中文:
定理 IsPositive.conj_adjoint
  结论: [完备空间 E] [完备空间 F] {T : E ->L[𝕜] E}
  证明: by
  refine isPositive_def'.mpr ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf]; rw [comp_apply]; rw [← adjoint_inner_right]
  exact hT.re_inner_nonneg_left _

Depends on / 依赖: adjoint_inner_right, comp_apply, conj_adjoint, hT.isSelfAdjoint.conj_adjoint, hT.re_inner_nonneg_left, isPositive_def, isSelfAdjoint, reApplyInnerSelf, re_inner_nonneg_left
-/
theorem IsPositive.conj_adjoint [CompleteSpace E] [CompleteSpace F] {T : E ->L[𝕜] E}
    (hT : T.IsPositive) (S : E ->L[𝕜] F) : (S ∘L T ∘L S†).IsPositive := by
  refine isPositive_def'.mpr ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf]; rw [comp_apply]; rw [← adjoint_inner_right]
  exact hT.re_inner_nonneg_left _

/--
theorem `isPositive_self_comp_adjoint` / 定理 `isPositive_self_comp_adjoint`

English:
theorem isPositive_self_comp_adjoint
  given: [CompleteSpace E] [CompleteSpace F] (S : E ->L[𝕜] F)
  proof: by
  simpa using! isPositive_one.conj_adjoint S

@[aesop safe apply]

中文:
定理 isPositive_self_comp_adjoint
  条件: [完备空间 E] [完备空间 F] (S : E ->L[𝕜] F)
  证明: by
  simpa using! isPositive_one.conj_adjoint S

@[aesop safe apply]

Depends on / 依赖: conj_adjoint, isPositive_one, isPositive_one.conj_adjoint
-/
theorem isPositive_self_comp_adjoint [CompleteSpace E] [CompleteSpace F] (S : E ->L[𝕜] F) :
    (S ∘L S†).IsPositive := by
  simpa using! isPositive_one.conj_adjoint S

@[aesop safe apply]
/--
theorem `IsPositive.adjoint_conj` / 定理 `IsPositive.adjoint_conj`

English:
theorem IsPositive.adjoint_conj
  statement: [CompleteSpace E] [CompleteSpace F] {T : E ->L[𝕜] E}
  proof: by
  convert! hT.conj_adjoint (S†)
  rw [adjoint_adjoint]

中文:
定理 IsPositive.adjoint_conj
  结论: [完备空间 E] [完备空间 F] {T : E ->L[𝕜] E}
  证明: by
  convert! hT.conj_adjoint (S†)
  rw [adjoint_adjoint]

Depends on / 依赖: adjoint_adjoint, conj_adjoint, convert, hT.conj_adjoint
-/
theorem IsPositive.adjoint_conj [CompleteSpace E] [CompleteSpace F] {T : E ->L[𝕜] E}
    (hT : T.IsPositive) (S : F ->L[𝕜] E) : (S† ∘L T ∘L S).IsPositive := by
  convert! hT.conj_adjoint (S†)
  rw [adjoint_adjoint]

/--
theorem `isPositive_adjoint_comp_self` / 定理 `isPositive_adjoint_comp_self`

English:
theorem isPositive_adjoint_comp_self
  given: [CompleteSpace E] [CompleteSpace F] (S : E ->L[𝕜] F)
  proof: by
  simpa using! isPositive_one.adjoint_conj S

中文:
定理 isPositive_adjoint_comp_self
  条件: [完备空间 E] [完备空间 F] (S : E ->L[𝕜] F)
  证明: by
  simpa using! isPositive_one.adjoint_conj S

Depends on / 依赖: adjoint_conj, isPositive_one, isPositive_one.adjoint_conj
-/
theorem isPositive_adjoint_comp_self [CompleteSpace E] [CompleteSpace F] (S : E ->L[𝕜] F) :
    (S† ∘L S).IsPositive := by
  simpa using! isPositive_one.adjoint_conj S

section LinearMap
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

@[aesop safe apply]
/--
theorem `_root_.LinearMap.IsPositive.conj_adjoint` / 定理 `_root_.LinearMap.IsPositive.conj_adjoint`

English:
theorem _root_.LinearMap.IsPositive.conj_adjoint
  statement: {T : E ->ₗ[𝕜] E}
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa [← isPositive_toContinuousLinearMap_iff] using!
    ((T.isPositive_toContinuousLinearMap_iff.mpr hT).conj_adjoint S.toContinuousLinearMap)

中文:
定理 _root_.线性映射.IsPositive.conj_adjoint
  结论: {T : E ->ₗ[𝕜] E}
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa [← isPositive_toContinuousLinearMap_iff] using!
    ((T.isPositive_toContinuousLinearMap_iff.mpr hT).conj_adjoint S.toContinuousLinearMap)

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, S.toContinuousLinearMap, T.isPositive_toContinuousLinearMap_iff.mpr, complete, conj_adjoint, isPositive_toContinuousLinearMap_iff, toContinuousLinearMap
-/
theorem _root_.LinearMap.IsPositive.conj_adjoint {T : E ->ₗ[𝕜] E}
    (hT : T.IsPositive) (S : E ->ₗ[𝕜] F) : (S ∘ₗ T ∘ₗ S.adjoint).IsPositive := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa [← isPositive_toContinuousLinearMap_iff] using!
    ((T.isPositive_toContinuousLinearMap_iff.mpr hT).conj_adjoint S.toContinuousLinearMap)

/--
theorem `_root_.LinearMap.isPositive_self_comp_adjoint` / 定理 `_root_.LinearMap.isPositive_self_comp_adjoint`

English:
theorem _root_.LinearMap.isPositive_self_comp_adjoint
  given: (S : E ->ₗ[𝕜] F)
  proof: by
  simpa using! LinearMap.isPositive_one.conj_adjoint S

@[aesop safe apply]

中文:
定理 _root_.线性映射.isPositive_self_comp_adjoint
  条件: (S : E ->ₗ[𝕜] F)
  证明: by
  simpa using! LinearMap.isPositive_one.conj_adjoint S

@[aesop safe apply]

Depends on / 依赖: LinearMap, LinearMap.isPositive_one.conj_adjoint, conj_adjoint, isPositive_one
-/
theorem _root_.LinearMap.isPositive_self_comp_adjoint (S : E ->ₗ[𝕜] F) :
    (S ∘ₗ S.adjoint).IsPositive := by
  simpa using! LinearMap.isPositive_one.conj_adjoint S

@[aesop safe apply]
/--
theorem `_root_.LinearMap.IsPositive.adjoint_conj` / 定理 `_root_.LinearMap.IsPositive.adjoint_conj`

English:
theorem _root_.LinearMap.IsPositive.adjoint_conj
  statement: {T : E ->ₗ[𝕜] E}
  proof: by
  convert! hT.conj_adjoint S.adjoint
  rw [LinearMap.adjoint_adjoint]

中文:
定理 _root_.线性映射.IsPositive.adjoint_conj
  结论: {T : E ->ₗ[𝕜] E}
  证明: by
  convert! hT.conj_adjoint S.adjoint
  rw [LinearMap.adjoint_adjoint]

Depends on / 依赖: LinearMap, LinearMap.adjoint_adjoint, S.adjoint, adjoint, adjoint_adjoint, conj_adjoint, convert, hT.conj_adjoint
-/
theorem _root_.LinearMap.IsPositive.adjoint_conj {T : E ->ₗ[𝕜] E}
    (hT : T.IsPositive) (S : F ->ₗ[𝕜] E) : (S.adjoint ∘ₗ T ∘ₗ S).IsPositive := by
  convert! hT.conj_adjoint S.adjoint
  rw [LinearMap.adjoint_adjoint]

/--
theorem `_root_.LinearMap.isPositive_adjoint_comp_self` / 定理 `_root_.LinearMap.isPositive_adjoint_comp_self`

English:
theorem _root_.LinearMap.isPositive_adjoint_comp_self
  given: (S : E ->ₗ[𝕜] F)
  proof: by
  simpa using! LinearMap.isPositive_one.adjoint_conj S

中文:
定理 _root_.线性映射.isPositive_adjoint_comp_self
  条件: (S : E ->ₗ[𝕜] F)
  证明: by
  simpa using! LinearMap.isPositive_one.adjoint_conj S

Depends on / 依赖: LinearMap, LinearMap.isPositive_one.adjoint_conj, adjoint_conj, isPositive_one
-/
theorem _root_.LinearMap.isPositive_adjoint_comp_self (S : E ->ₗ[𝕜] F) :
    (S.adjoint ∘ₗ S).IsPositive := by
  simpa using! LinearMap.isPositive_one.adjoint_conj S

end LinearMap

/--
theorem `IsPositive.conj_starProjection` / 定理 `IsPositive.conj_starProjection`

English:
theorem IsPositive.conj_starProjection
  statement: (U : Submodule 𝕜 E) {T : E ->L[𝕜] E} (hT : T.IsPositive)
  proof: by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [← coe_coe, U.starProjection_isSymmetric _, hT.isSymmetric _,
    U.starProjection_isSymmetric _, ← U.starProjection_isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

中文:
定理 IsPositive.conj_starProjection
  结论: (U : 子模 𝕜 E) {T : E ->L[𝕜] E} (hT : T.IsPositive)
  证明: by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [← coe_coe, U.starProjection_isSymmetric _, hT.isSymmetric _,
    U.starProjection_isSymmetric _, ← U.starProjection_isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

Depends on / 依赖: Function, Function.comp_apply, IsSymmetric, LinearMap, LinearMap.coe_comp, U.starProjection_isSymmetric, and_self, coe_coe, coe_comp, comp_apply, hT.inner_nonneg_right, hT.isSymmetric, implies_true, inner_nonneg_right, isPositive_iff, isSymmetric, simp_rw, starProjection_isSymmetric, toLinearMap_comp
-/
theorem IsPositive.conj_starProjection (U : Submodule 𝕜 E) {T : E ->L[𝕜] E} (hT : T.IsPositive)
    [U.HasOrthogonalProjection] :
    (U.starProjection ∘L T ∘L U.starProjection).IsPositive := by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [← coe_coe, U.starProjection_isSymmetric _, hT.isSymmetric _,
    U.starProjection_isSymmetric _, ← U.starProjection_isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

/--
theorem `IsPositive.orthogonalProjectionOnto_comp` / 定理 `IsPositive.orthogonalProjectionOnto_comp`

English:
theorem IsPositive.orthogonalProjectionOnto_comp
  statement: {T : E ->L[𝕜] E} (hT : T.IsPositive)
  proof: by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [U.inner_orthogonalProjectionOnto_eq_of_mem_right, Submodule.subtypeL_apply,
    U.inner_orthogonalProjectionOnto_eq_of_mem_left, ← coe_coe, hT.isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

@[deprecated (since := "2026-05-05")] alias IsPositive.orthogonalProjection_comp :=
  IsPositive.orthogonalProjectionOnto_comp

中文:
定理 IsPositive.orthogonalProjectionOnto_comp
  结论: {T : E ->L[𝕜] E} (hT : T.IsPositive)
  证明: by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [U.inner_orthogonalProjectionOnto_eq_of_mem_right, Submodule.subtypeL_apply,
    U.inner_orthogonalProjectionOnto_eq_of_mem_left, ← coe_coe, hT.isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

@[deprecated (since := "2026-05-05")] alias IsPositive.orthogonalProjection_comp :=
  IsPositive.orthogonalProjectionOnto_comp

Depends on / 依赖: Function, Function.comp_apply, IsSymmetric, LinearMap, LinearMap.coe_comp, Submodule, Submodule.subtypeL_apply, U.inner_orthogonalProjectionOnto_eq_of_mem_left, U.inner_orthogonalProjectionOnto_eq_of_mem_right, and_self, coe_coe, coe_comp, comp_apply, hT.inner_nonneg_right, hT.isSymmetric, implies_true, inner_nonneg_right, inner_orthogonalProjectionOnto_eq_of_mem_left, inner_orthogonalProjectionOnto_eq_of_mem_right, isPositive_iff
-/
theorem IsPositive.orthogonalProjectionOnto_comp {T : E ->L[𝕜] E} (hT : T.IsPositive)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL).IsPositive := by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [U.inner_orthogonalProjectionOnto_eq_of_mem_right, Submodule.subtypeL_apply,
    U.inner_orthogonalProjectionOnto_eq_of_mem_left, ← coe_coe, hT.isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

@[deprecated (since := "2026-05-05")] alias IsPositive.orthogonalProjection_comp :=
  IsPositive.orthogonalProjectionOnto_comp

open scoped NNReal

/--
lemma `antilipschitz_of_forall_le_inner_map` / 引理 `antilipschitz_of_forall_le_inner_map`

English:
lemma antilipschitz_of_forall_le_inner_map
  statement: {H : Type*} [NormedAddCommGroup H]
  proof: by
  refine f.antilipschitz_of_bound (K := c⁻¹) fun x => ?_
  rw [NNReal.coe_inv]; rw [inv_mul_eq_div]; rw [le_div_iff₀ (by exact_mod_cast hc)]
  simp_rw [sq, mul_assoc] at h
  by_cases hx0 : x = 0
  · simp [hx0]
  · apply (map_le_map_iff <| OrderIso.mulLeft₀ ‖x‖ (norm_pos_iff.mpr hx0)).mp
exact (h x).trans (norm_inner_le_norm _ _).trans (mul_comm _ _).le

中文:
引理 antilipschitz_of_对任意_le_inner_map
  结论: {H : 类型} [赋范交换加群 H]
  证明: by
  refine f.antilipschitz_of_bound (K := c⁻¹) fun x => ?_
  rw [NNReal.coe_inv]; rw [inv_mul_eq_div]; rw [le_div_iff₀ (by exact_mod_cast hc)]
  simp_rw [sq, mul_assoc] at h
  by_cases hx0 : x = 0
  · simp [hx0]
  · apply (map_le_map_iff <| OrderIso.mulLeft₀ ‖x‖ (norm_pos_iff.mpr hx0)).mp
exact (h x).trans (norm_inner_le_norm _ _).trans (mul_comm _ _).le

Depends on / 依赖: NNReal, NNReal.coe_inv, OrderIso, OrderIso.mulLeft, antilipschitz_of_bound, coe_inv, f.antilipschitz_of_bound, inv_mul_eq_div, map_le_map_iff, mul_assoc, mul_comm, norm_inner_le_norm, norm_pos_iff, norm_pos_iff.mpr, simp_rw
-/
lemma antilipschitz_of_forall_le_inner_map {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (f : H ->L[𝕜] H) {c : Real>=0} (hc : 0 < c)
    (h : forall x, ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖) : AntilipschitzWith c⁻¹ f := by
  refine f.antilipschitz_of_bound (K := c⁻¹) fun x => ?_
  rw [NNReal.coe_inv]; rw [inv_mul_eq_div]; rw [le_div_iff₀ (by exact_mod_cast hc)]
  simp_rw [sq, mul_assoc] at h
  by_cases hx0 : x = 0
  · simp [hx0]
  · apply (map_le_map_iff <| OrderIso.mulLeft₀ ‖x‖ (norm_pos_iff.mpr hx0)).mp
exact (h x).trans (norm_inner_le_norm _ _).trans (mul_comm _ _).le

/--
lemma `isUnit_of_forall_le_norm_inner_map` / 引理 `isUnit_of_forall_le_norm_inner_map`

English:
lemma isUnit_of_forall_le_norm_inner_map
  statement: [CompleteSpace E] (f : E ->L[𝕜] E) {c : Real>=0} (hc : 0 < c)
  proof: by
  rw [isUnit_iff_bijective]; rw [bijective_iff_dense_range_and_antilipschitz]
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff]; rw [Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

中文:
引理 isUnit_of_对任意_le_norm_inner_map
  结论: [完备空间 E] (f : E ->L[𝕜] E) {c : 实数>=0} (hc : 0 < c)
  证明: by
  rw [isUnit_iff_bijective]; rw [bijective_iff_dense_range_and_antilipschitz]
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff]; rw [Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

Depends on / 依赖: AntilipschitzWith, Submodule, Submodule.eq_bot_iff, Submodule.topologicalClosure_eq_top_iff, antilipschitz_of_forall_le_inner_map, bijective_iff_dense_range_and_antilipschitz, eq_bot_iff, h_anti, isUnit_iff_bijective, le_antisymm, norm_zero, topologicalClosure_eq_top_iff
-/
lemma isUnit_of_forall_le_norm_inner_map [CompleteSpace E] (f : E ->L[𝕜] E) {c : Real>=0} (hc : 0 < c)
    (h : forall x, ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖) : IsUnit f := by
  rw [isUnit_iff_bijective]; rw [bijective_iff_dense_range_and_antilipschitz]
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff]; rw [Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

section Complex
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace Complex E']

/--
theorem `isPositive_iff_complex` / 定理 `isPositive_iff_complex`

English:
theorem isPositive_iff_complex
  given: (T : E' ->L[Complex] E')
  proof: by
  simp [← isPositive_toLinearMap_iff, LinearMap.isPositive_iff_complex]

中文:
定理 isPositive_iff_complex
  条件: (T : E' ->L[复形] E')
  证明: by
  simp [← isPositive_toLinearMap_iff, LinearMap.isPositive_iff_complex]

Depends on / 依赖: LinearMap, LinearMap.isPositive_iff_complex, isPositive_iff_complex, isPositive_toLinearMap_iff
-/
theorem isPositive_iff_complex (T : E' ->L[Complex] E') :
    IsPositive T ↔ forall x, (re ⟪T x, x⟫_Complex : Complex) = ⟪T x, x⟫_Complex ∧ 0 <= re ⟪T x, x⟫_Complex := by
  simp [← isPositive_toLinearMap_iff, LinearMap.isPositive_iff_complex]

end Complex

section PartialOrder

/--
Instance `instLoewnerPartialOrder` / 实例 `instLoewnerPartialOrder`

English:
instance instLoewnerPartialOrder
  signature: : PartialOrder (E ->L[𝕜] E) where
  body: (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm _ _ h₁ h₂ := coe_inj.mp (le_antisymm h₁.toLinearMap h₂.toLinearMap)

中文:
实例 instLoewnerPartialOrder
  签名: : 偏序 (E ->L[𝕜] E) where
  定义体: (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm _ _ h₁ h₂ := coe_inj.mp (le_antisymm h₁.toLinearMap h₂.toLinearMap)

Depends on / 依赖: IsPositive
-/
instance instLoewnerPartialOrder : PartialOrder (E ->L[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm _ _ h₁ h₂ := coe_inj.mp (le_antisymm h₁.toLinearMap h₂.toLinearMap)

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: (f g : E ->L[𝕜] E)
  statement: f <= g ↔ (g - f).IsPositive
  proof: Iff.rfl

中文:
引理 le_def
  条件: (f g : E ->L[𝕜] E)
  结论: f <= g ↔ (g - f).IsPositive
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def (f g : E ->L[𝕜] E) : f <= g ↔ (g - f).IsPositive := Iff.rfl

/--
lemma `coe_le_coe_iff` / 引理 `coe_le_coe_iff`

English:
lemma coe_le_coe_iff
  given: (f g : E ->L[𝕜] E)
  proof: isPositive_toLinearMap_iff (g - f)

中文:
引理 coe_le_coe_iff
  条件: (f g : E ->L[𝕜] E)
  证明: isPositive_toLinearMap_iff (g - f)

Depends on / 依赖: isPositive_toLinearMap_iff
-/
lemma coe_le_coe_iff (f g : E ->L[𝕜] E) :
    (f : E ->ₗ[𝕜] E) <= g ↔ f <= g :=
  isPositive_toLinearMap_iff (g - f)

/--
lemma `nonneg_iff_isPositive` / 引理 `nonneg_iff_isPositive`

English:
lemma nonneg_iff_isPositive
  given: (f : E ->L[𝕜] E)
  statement: 0 <= f ↔ f.IsPositive
  proof: by
  simpa using le_def 0 f

中文:
引理 nonneg_iff_isPositive
  条件: (f : E ->L[𝕜] E)
  结论: 0 <= f ↔ f.IsPositive
  证明: by
  simpa using le_def 0 f

Depends on / 依赖: le_def
-/
lemma nonneg_iff_isPositive (f : E ->L[𝕜] E) : 0 <= f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

/-- An idempotent operator is positive if and only if it is self-adjoint. -/
@[grind ->]
/--
theorem `IsIdempotentElem.isPositive_iff_isSelfAdjoint` / 定理 `IsIdempotentElem.isPositive_iff_isSelfAdjoint`

English:
theorem IsIdempotentElem.isPositive_iff_isSelfAdjoint
  statement: [CompleteSpace E]
  proof: by
  rw [← isPositive_toLinearMap_iff]; rw [IsIdempotentElem.isPositive_iff_isSymmetric hp.toLinearMap]
  exact isSelfAdjoint_iff_isSymmetric.symm

中文:
定理 IsIdempotentElem.isPositive_iff_isSelfAdjoint
  结论: [完备空间 E]
  证明: by
  rw [← isPositive_toLinearMap_iff]; rw [IsIdempotentElem.isPositive_iff_isSymmetric hp.toLinearMap]
  exact isSelfAdjoint_iff_isSymmetric.symm

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.isPositive_iff_isSymmetric, hp.toLinearMap, isPositive_iff_isSymmetric, isPositive_toLinearMap_iff, isSelfAdjoint_iff_isSymmetric, isSelfAdjoint_iff_isSymmetric.symm, toLinearMap
-/
theorem IsIdempotentElem.isPositive_iff_isSelfAdjoint [CompleteSpace E]
    {p : E ->L[𝕜] E} (hp : IsIdempotentElem p) : p.IsPositive ↔ IsSelfAdjoint p := by
  rw [← isPositive_toLinearMap_iff]; rw [IsIdempotentElem.isPositive_iff_isSymmetric hp.toLinearMap]
  exact isSelfAdjoint_iff_isSymmetric.symm

/-- A star projection operator is positive.

The proof of this will soon be simplified to `IsStarProjection.nonneg` when we
have `StarOrderedRing (E →L[𝕜] E)`. -/
@[aesop 10% apply, grind ->]
/--
theorem `IsPositive.of_isStarProjection` / 定理 `IsPositive.of_isStarProjection`

English:
theorem IsPositive.of_isStarProjection
  statement: [CompleteSpace E] {p : E ->L[𝕜] E}
  proof: hp.isIdempotentElem.isPositive_iff_isSelfAdjoint.mpr hp.isSelfAdjoint

中文:
定理 IsPositive.of_isStarProjection
  结论: [完备空间 E] {p : E ->L[𝕜] E}
  证明: hp.isIdempotentElem.isPositive_iff_isSelfAdjoint.mpr hp.isSelfAdjoint

Depends on / 依赖: hp.isIdempotentElem.isPositive_iff_isSelfAdjoint.mpr, hp.isSelfAdjoint, isIdempotentElem, isPositive_iff_isSelfAdjoint, isSelfAdjoint
-/
theorem IsPositive.of_isStarProjection [CompleteSpace E] {p : E ->L[𝕜] E}
    (hp : IsStarProjection p) : p.IsPositive :=
  hp.isIdempotentElem.isPositive_iff_isSelfAdjoint.mpr hp.isSelfAdjoint

/--
theorem `IsIdempotentElem.TFAE` / 定理 `IsIdempotentElem.TFAE`

English:
theorem IsIdempotentElem.TFAE
  given: [CompleteSpace E] {p : E ->L[𝕜] E} (hp : IsIdempotentElem p)
  proof: by
  tfae_have 2 ↔ 3 := hp.isSelfAdjoint_iff_isStarNormal.symm
  tfae_have 3 ↔ 4 := hp.isPositive_iff_isSelfAdjoint.symm
  tfae_have 3 ↔ 1 := p.isSelfAdjoint_iff_isSymmetric.eq ▸
    (LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hp.toLinearMap)
  tfae_finish

中文:
定理 IsIdempotentElem.TFAE
  条件: [完备空间 E] {p : E ->L[𝕜] E} (hp : IsIdempotentElem p)
  证明: by
  tfae_have 2 ↔ 3 := hp.isSelfAdjoint_iff_isStarNormal.symm
  tfae_have 3 ↔ 4 := hp.isPositive_iff_isSelfAdjoint.symm
  tfae_have 3 ↔ 1 := p.isSelfAdjoint_iff_isSymmetric.eq ▸
    (LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hp.toLinearMap)
  tfae_finish

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range, hp.isPositive_iff_isSelfAdjoint.symm, hp.isSelfAdjoint_iff_isStarNormal.symm, hp.toLinearMap, isPositive_iff_isSelfAdjoint, isSelfAdjoint_iff_isStarNormal, isSelfAdjoint_iff_isSymmetric, isSymmetric_iff_orthogonal_range, p.isSelfAdjoint_iff_isSymmetric.eq, tfae_finish, tfae_have, toLinearMap
-/
theorem IsIdempotentElem.TFAE [CompleteSpace E] {p : E ->L[𝕜] E} (hp : IsIdempotentElem p) :
    [p.rangeᗮ = p.ker,
      IsStarNormal p,
      IsSelfAdjoint p,
      p.IsPositive].TFAE := by
  tfae_have 2 ↔ 3 := hp.isSelfAdjoint_iff_isStarNormal.symm
  tfae_have 3 ↔ 4 := hp.isPositive_iff_isSelfAdjoint.symm
  tfae_have 3 ↔ 1 := p.isSelfAdjoint_iff_isSymmetric.eq ▸
    (LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hp.toLinearMap)
  tfae_finish

end ContinuousLinearMap

/--
theorem `Submodule.starProjection_le_starProjection_iff` / 定理 `Submodule.starProjection_le_starProjection_iff`

English:
theorem Submodule.starProjection_le_starProjection_iff
  statement: {U V : Submodule 𝕜 E}
  proof: by
  simp_rw [← coe_le_coe_iff, isSymmetricProjection_starProjection _
.le_iff_range_le_range isSymmetricProjection_starProjection _,
    toLinearMap_starProjection_eq_isComplProjection, range_projection]

中文:
定理 子模.starProjection_le_starProjection_iff
  结论: {U V : 子模 𝕜 E}
  证明: by
  simp_rw [← coe_le_coe_iff, isSymmetricProjection_starProjection _
.le_iff_range_le_range isSymmetricProjection_starProjection _,
    toLinearMap_starProjection_eq_isComplProjection, range_projection]

Depends on / 依赖: coe_le_coe_iff, isSymmetricProjection_starProjection, le_iff_range_le_range, range_projection, simp_rw, toLinearMap_starProjection_eq_isComplProjection
-/
theorem Submodule.starProjection_le_starProjection_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection <= V.starProjection ↔ U <= V := by
  simp_rw [← coe_le_coe_iff, isSymmetricProjection_starProjection _
.le_iff_range_le_range isSymmetricProjection_starProjection _,
    toLinearMap_starProjection_eq_isComplProjection, range_projection]

/--
theorem `Submodule.starProjection_inj` / 定理 `Submodule.starProjection_inj`

English:
theorem Submodule.starProjection_inj
  statement: {U V : Submodule 𝕜 E}
  proof: by
  simp only [le_antisymm_iff, ← starProjection_le_starProjection_iff]

中文:
定理 子模.starProjection_inj
  结论: {U V : 子模 𝕜 E}
  证明: by
  simp only [le_antisymm_iff, ← starProjection_le_starProjection_iff]

Depends on / 依赖: le_antisymm_iff, starProjection_le_starProjection_iff
-/
theorem Submodule.starProjection_inj {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection = V.starProjection ↔ U = V := by
  simp only [le_antisymm_iff, ← starProjection_le_starProjection_iff]

/--
theorem `LinearMap.IsPositive.toLinearMap_symm` / 定理 `LinearMap.IsPositive.toLinearMap_symm`

English:
theorem LinearMap.IsPositive.toLinearMap_symm
  given: {T : E ≃ₗ[𝕜] E} (hT : T.IsPositive)
  proof: by
  refine ⟨hT.isSymmetric.toLinearMap_symm, fun x => ?_⟩
  have := by simpa using hT.2 (T.symm.toLinearMap x)
  rwa [← T.symm.coe_toLinearMap, ← hT.isSymmetric.toLinearMap_symm] at this

中文:
定理 线性映射.IsPositive.toLinearMap_symm
  条件: {T : E ≃ₗ[𝕜] E} (hT : T.IsPositive)
  证明: by
  refine ⟨hT.isSymmetric.toLinearMap_symm, fun x => ?_⟩
  have := by simpa using hT.2 (T.symm.toLinearMap x)
  rwa [← T.symm.coe_toLinearMap, ← hT.isSymmetric.toLinearMap_symm] at this

Depends on / 依赖: T.symm.coe_toLinearMap, T.symm.toLinearMap, coe_toLinearMap, hT.isSymmetric.toLinearMap_symm, isSymmetric, toLinearMap, toLinearMap_symm
-/
theorem LinearMap.IsPositive.toLinearMap_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsPositive) :
    T.symm.IsPositive := by
  refine ⟨hT.isSymmetric.toLinearMap_symm, fun x => ?_⟩
  have := by simpa using hT.2 (T.symm.toLinearMap x)
  rwa [← T.symm.coe_toLinearMap, ← hT.isSymmetric.toLinearMap_symm] at this

/--
theorem `LinearEquiv.isPositive_symm_iff` / 定理 `LinearEquiv.isPositive_symm_iff`

English:
theorem LinearEquiv.isPositive_symm_iff
  given: {T : E ≃ₗ[𝕜] E}
  proof: ⟨.toLinearMap_symm, .toLinearMap_symm⟩

中文:
定理 线性等价.isPositive_symm_iff
  条件: {T : E ≃ₗ[𝕜] E}
  证明: ⟨.toLinearMap_symm, .toLinearMap_symm⟩
-/
@[simp] theorem LinearEquiv.isPositive_symm_iff {T : E ≃ₗ[𝕜] E} :
    T.symm.IsPositive ↔ T.IsPositive := ⟨.toLinearMap_symm, .toLinearMap_symm⟩

/--
lemma `InnerProductSpace.isPositive_rankOne_self` / 引理 `InnerProductSpace.isPositive_rankOne_self`

English:
lemma InnerProductSpace.isPositive_rankOne_self
  given: (x : E)
  proof: by
  simp_rw [ContinuousLinearMap.isPositive_iff, isSymmetric_rankOne_self, rankOne_apply,
    inner_smul_left, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_nonneg]
  simp

中文:
引理 内积空间.isPositive_rankOne_self
  条件: (x : E)
  证明: by
  simp_rw [ContinuousLinearMap.isPositive_iff, isSymmetric_rankOne_self, rankOne_apply,
    inner_smul_left, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_nonneg]
  simp
-/
@[simp] lemma InnerProductSpace.isPositive_rankOne_self (x : E) :
    (rankOne 𝕜 x x).IsPositive := by
  simp_rw [ContinuousLinearMap.isPositive_iff, isSymmetric_rankOne_self, rankOne_apply,
    inner_smul_left, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_nonneg]
  simp

/--
theorem `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne` / 定理 `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`

English:
theorem ContinuousLinearMap.isPositive_iff_eq_sum_rankOne
  given: [FiniteDimensional 𝕜 E] {T : E ->L[𝕜] E}
  proof: by
  refine ⟨fun hT => ?_, fun ⟨m, u, hT⟩ => hT ▸ isPositive_sum _ fun _ _ => isPositive_rankOne_self _⟩
  let a (i : Fin (Module.finrank 𝕜 E)) : E :=
    ((hT.isSymmetric.eigenvalues rfl i).sqrt : 𝕜) • hT.isSymmetric.eigenvectorBasis rfl i
  refine ⟨Module.finrank 𝕜 E, a, ext fun _ => ?_⟩
  simp_rw [_root_.sum_apply, rankOne_apply, a, inner_smul_left, smul_smul, mul_assoc, conj_ofReal,
    mul_comm (⟪_, _⟫_𝕜), ← mul_assoc, ← ofReal_mul,
    ← Real.sqrt_mul (hT.toLinearMap.nonneg_eigenvalues rfl _),
    Real.sqrt_mul_self (hT.toLinearMap.nonneg_eigenvalues rfl _), mul_comm _ (⟪_, _⟫_𝕜),
    ← smul_eq_mul, smul_assoc, ← hT.isSymmetric.apply_eigenvectorBasis, ← map_smul, ← map_sum,
    ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr, coe_coe]

中文:
定理 连续线性映射.isPositive_iff_eq_sum_rankOne
  条件: [有限维 𝕜 E] {T : E ->L[𝕜] E}
  证明: by
  refine ⟨fun hT => ?_, fun ⟨m, u, hT⟩ => hT ▸ isPositive_sum _ fun _ _ => isPositive_rankOne_self _⟩
  let a (i : Fin (Module.finrank 𝕜 E)) : E :=
    ((hT.isSymmetric.eigenvalues rfl i).sqrt : 𝕜) • hT.isSymmetric.eigenvectorBasis rfl i
  refine ⟨Module.finrank 𝕜 E, a, ext fun _ => ?_⟩
  simp_rw [_root_.sum_apply, rankOne_apply, a, inner_smul_left, smul_smul, mul_assoc, conj_ofReal,
    mul_comm (⟪_, _⟫_𝕜), ← mul_assoc, ← ofReal_mul,
    ← Real.sqrt_mul (hT.toLinearMap.nonneg_eigenvalues rfl _),
    Real.sqrt_mul_self (hT.toLinearMap.nonneg_eigenvalues rfl _), mul_comm _ (⟪_, _⟫_𝕜),
    ← smul_eq_mul, smul_assoc, ← hT.isSymmetric.apply_eigenvectorBasis, ← map_smul, ← map_sum,
    ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr, coe_coe]

Depends on / 依赖: Module, Module.finrank, Real.sqrt_mul, Real.sqrt_mul_s, _root_, _root_.sum_apply, conj_ofReal, eigenvalues, eigenvectorBasis, finrank, hT.isSymmetric.eigenvalues, hT.isSymmetric.eigenvectorBasis, hT.toLinearMap.nonneg_eigenvalues, inner_smul_left, isPositive_rankOne_self, isPositive_sum, isSymmetric, mul_assoc, mul_comm, nonneg_eigenvalues
-/
theorem ContinuousLinearMap.isPositive_iff_eq_sum_rankOne [FiniteDimensional 𝕜 E] {T : E ->L[𝕜] E} :
    T.IsPositive ↔ exists (m : Nat) (u : Fin m -> E), T = ∑ i : Fin m, rankOne 𝕜 (u i) (u i) := by
  refine ⟨fun hT => ?_, fun ⟨m, u, hT⟩ => hT ▸ isPositive_sum _ fun _ _ => isPositive_rankOne_self _⟩
  let a (i : Fin (Module.finrank 𝕜 E)) : E :=
    ((hT.isSymmetric.eigenvalues rfl i).sqrt : 𝕜) • hT.isSymmetric.eigenvectorBasis rfl i
  refine ⟨Module.finrank 𝕜 E, a, ext fun _ => ?_⟩
  simp_rw [_root_.sum_apply, rankOne_apply, a, inner_smul_left, smul_smul, mul_assoc, conj_ofReal,
    mul_comm (⟪_, _⟫_𝕜), ← mul_assoc, ← ofReal_mul,
    ← Real.sqrt_mul (hT.toLinearMap.nonneg_eigenvalues rfl _),
    Real.sqrt_mul_self (hT.toLinearMap.nonneg_eigenvalues rfl _), mul_comm _ (⟪_, _⟫_𝕜),
    ← smul_eq_mul, smul_assoc, ← hT.isSymmetric.apply_eigenvectorBasis, ← map_smul, ← map_sum,
    ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr, coe_coe]

/--
theorem `Matrix.posSemidef_iff_eq_sum_vecMulVec` / 定理 `Matrix.posSemidef_iff_eq_sum_vecMulVec`

English:
theorem Matrix.posSemidef_iff_eq_sum_vecMulVec
  given: {n : Type*} [Finite n] {M : Matrix n n 𝕜}
  proof: by
  classical
  have := Fintype.ofFinite n
  rw [← isPositive_toEuclideanLin_iff]; rw [← isPositive_toContinuousLinearMap_iff]; rw [isPositive_iff_eq_sum_rankOne]
  simp_rw [eq_comm, ← LinearEquiv.symm_apply_eq, coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_sum, map_sum, symm_toEuclideanLin_rankOne, eq_comm]
  exact ⟨fun ⟨m, u, hu⟩ => ⟨m, fun i => (u i).ofLp, hu⟩,
    fun ⟨m, u, hu⟩ => ⟨m, fun i => WithLp.toLp 2 (u i), hu⟩⟩

中文:
定理 矩阵.posSemidef_iff_eq_sum_vecMulVec
  条件: {n : 类型} [有限 n] {M : 矩阵 n n 𝕜}
  证明: by
  classical
  have := Fintype.ofFinite n
  rw [← isPositive_toEuclideanLin_iff]; rw [← isPositive_toContinuousLinearMap_iff]; rw [isPositive_iff_eq_sum_rankOne]
  simp_rw [eq_comm, ← LinearEquiv.symm_apply_eq, coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_sum, map_sum, symm_toEuclideanLin_rankOne, eq_comm]
  exact ⟨fun ⟨m, u, hu⟩ => ⟨m, fun i => (u i).ofLp, hu⟩,
    fun ⟨m, u, hu⟩ => ⟨m, fun i => WithLp.toLp 2 (u i), hu⟩⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toLinearMap_sum, Fintype, Fintype.ofFinite, LinearEquiv, LinearEquiv.symm_apply_eq, WithLp, WithLp.toLp, classical, coe_toContinuousLinearMap_symm, eq_comm, isPositive_iff_eq_sum_rankOne, isPositive_toContinuousLinearMap_iff, isPositive_toEuclideanLin_iff, map_sum, ofFinite, simp_rw, symm_apply_eq, symm_toEuclideanLin_rankOne, toLinearMap_sum
-/
theorem Matrix.posSemidef_iff_eq_sum_vecMulVec {n : Type*} [Finite n] {M : Matrix n n 𝕜} :
    M.PosSemidef ↔ exists (m : Nat) (v : Fin m -> (n -> 𝕜)), M = ∑ i, vecMulVec (v i) (star (v i)) := by
  classical
  have := Fintype.ofFinite n
  rw [← isPositive_toEuclideanLin_iff]; rw [← isPositive_toContinuousLinearMap_iff]; rw [isPositive_iff_eq_sum_rankOne]
  simp_rw [eq_comm, ← LinearEquiv.symm_apply_eq, coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_sum, map_sum, symm_toEuclideanLin_rankOne, eq_comm]
  exact ⟨fun ⟨m, u, hu⟩ => ⟨m, fun i => (u i).ofLp, hu⟩,
    fun ⟨m, u, hu⟩ => ⟨m, fun i => WithLp.toLp 2 (u i), hu⟩⟩
