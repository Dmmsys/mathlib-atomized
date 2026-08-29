/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Classification of elements of `GL (Fin 2) R`

Here we classify `2 × 2` matrices over the reals (or more generally over `R` where `R` is a
suitable ring, but `ℝ` is the motivating case), into the following classes:

* scalars
* parabolic elements (`Matrix.IsParabolic`) - one eigenvalue with non-semisimple generalized
  eigenspace
* hyperbolic elements (`Matrix.IsHyperbolic`) - two distinct real eigenvalues
* elliptic elements (`Matrix.IsElliptic`) - two distinct non-real complex eigenvalues

This classification is used (among other places) in classifying the fixed points of elements of
`GL(2, ℝ)⁺` acting on the upper half-plane. See [Wikipedia:SL2(R)#Classification_of_elements]
(https://en.wikipedia.org/wiki/SL2(R)#Classification_of_elements).
-/

@[expose] public section

open Polynomial

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/--
Definition of `IsParabolic` / `IsParabolic` 的定义

English:
definition IsParabolic
  signature: : Prop
  body: m ∉ Set.range (scalar _) ∧ m.discr = 0

中文:
定义 IsParabolic
  签名: : 命题
  定义体: m ∉ Set.range (scalar _) ∧ m.discr = 0

Depends on / 依赖: Set.range, m.discr, scalar
-/
def IsParabolic : Prop := m ∉ Set.range (scalar _) ∧ m.discr = 0

variable {m}

section conjugation

/--
lemma `isParabolic_conj_iff` / 引理 `isParabolic_conj_iff`

English:
lemma isParabolic_conj_iff
  statement: (g.val * m * g.val⁻¹).IsParabolic ↔ IsParabolic m
  proof: by
  simp_rw [IsParabolic, discr_conj, Set.mem_range, ← Matrix.coe_units_inv,
    Units.eq_mul_inv_iff_mul_eq, scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal,
    Units.mul_right_inj]

中文:
引理 isParabolic_conj_iff
  结论: (g.val * m * g.val⁻¹).IsParabolic ↔ IsParabolic m
  证明: by
  simp_rw [IsParabolic, discr_conj, Set.mem_range, ← Matrix.coe_units_inv,
    Units.eq_mul_inv_iff_mul_eq, scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal,
    Units.mul_right_inj]
-/
@[simp] lemma isParabolic_conj_iff : (g.val * m * g.val⁻¹).IsParabolic ↔ IsParabolic m := by
  simp_rw [IsParabolic, discr_conj, Set.mem_range, ← Matrix.coe_units_inv,
    Units.eq_mul_inv_iff_mul_eq, scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal,
    Units.mul_right_inj]

/--
lemma `isParabolic_conj'_iff` / 引理 `isParabolic_conj'_iff`

English:
lemma isParabolic_conj'_iff
  statement: (g.val⁻¹ * m * g.val).IsParabolic ↔ m.IsParabolic
  proof: by
  simpa using isParabolic_conj_iff g⁻¹

中文:
引理 isParabolic_conj'_iff
  结论: (g.val⁻¹ * m * g.val).IsParabolic ↔ m.IsParabolic
  证明: by
  simpa using isParabolic_conj_iff g⁻¹
-/
@[simp] lemma isParabolic_conj'_iff : (g.val⁻¹ * m * g.val).IsParabolic ↔ m.IsParabolic := by
  simpa using isParabolic_conj_iff g⁻¹

/--
lemma `IsParabolic.neg` / 引理 `IsParabolic.neg`

English:
lemma IsParabolic.neg
  given: (h : IsParabolic m)
  statement: IsParabolic (-m)
  proof: by
  constructor
  · rw [← RingHom.coe_range, SetLike.mem_coe, neg_mem_iff]
    exact h.1
  · -- TODO: prove `discr_neg` for a matrix of any size, use it here
    simpa [discr_fin_two, det_neg] using h.2

中文:
引理 IsParabolic.neg
  条件: (h : IsParabolic m)
  结论: IsParabolic (-m)
  证明: by
  constructor
  · rw [← RingHom.coe_range, SetLike.mem_coe, neg_mem_iff]
    exact h.1
  · -- TODO: prove `discr_neg` for a matrix of any size, use it here
    simpa [discr_fin_two, det_neg] using h.2

Depends on / 依赖: RingHom, RingHom.coe_range, SetLike, SetLike.mem_coe, coe_range, det_neg, discr_fin_two, discr_neg, matrix, mem_coe, neg_mem_iff
-/
lemma IsParabolic.neg (h : IsParabolic m) : IsParabolic (-m) := by
  constructor
  · rw [← RingHom.coe_range, SetLike.mem_coe, neg_mem_iff]
    exact h.1
  · -- TODO: prove `discr_neg` for a matrix of any size, use it here
    simpa [discr_fin_two, det_neg] using h.2

/--
lemma `IsParabolic.of_neg` / 引理 `IsParabolic.of_neg`

English:
lemma IsParabolic.of_neg
  given: (h : IsParabolic (-m))
  statement: IsParabolic m
  proof: by
  simpa using h.neg

中文:
引理 IsParabolic.of_neg
  条件: (h : IsParabolic (-m))
  结论: IsParabolic m
  证明: by
  simpa using h.neg

Depends on / 依赖: h.neg
-/
lemma IsParabolic.of_neg (h : IsParabolic (-m)) : IsParabolic m := by
  simpa using h.neg

/--
lemma `isParabolic_neg_iff` / 引理 `isParabolic_neg_iff`

English:
lemma isParabolic_neg_iff
  statement: IsParabolic (-m) ↔ IsParabolic m
  proof: ⟨.of_neg, .neg⟩

中文:
引理 isParabolic_neg_iff
  结论: IsParabolic (-m) ↔ IsParabolic m
  证明: ⟨.of_neg, .neg⟩
-/
@[simp] lemma isParabolic_neg_iff : IsParabolic (-m) ↔ IsParabolic m := ⟨.of_neg, .neg⟩

end conjugation

/--
lemma `isParabolic_iff_of_upperTriangular` / 引理 `isParabolic_iff_of_upperTriangular`

English:
lemma isParabolic_iff_of_upperTriangular
  given: [IsReduced R] (hm : m 1 0 = 0)
  proof: by
  rw [IsParabolic]
  have aux : m.discr = 0 ↔ m 0 0 = m 1 1 := by
    suffices m.discr = (m 0 0 - m 1 1) ^ 2 by
      rw [this]; rw [pow_eq_zero_iff two_ne_zero]; rw [sub_eq_zero]
    grind [discr_fin_two, trace_fin_two, det_fin_two]
  have (h : m 0 0 = m 1 1) : m in Set.range (scalar _) ↔ m 0 1 

中文:
引理 isParabolic_iff_of_upperTriangular
  条件: [IsReduced R] (hm : m 1 0 = 0)
  证明: by
  rw [IsParabolic]
  have aux : m.discr = 0 ↔ m 0 0 = m 1 1 := by
    suffices m.discr = (m 0 0 - m 1 1) ^ 2 by
      rw [this]; rw [pow_eq_zero_iff two_ne_zero]; rw [sub_eq_zero]
    grind [discr_fin_two, trace_fin_two, det_fin_two]
  have (h : m 0 0 = m 1 1) : m in Set.range (scalar _) ↔ m 0 1 

Depends on / 依赖: IsParabolic, Set.range, det_fin_two, discr_fin_two, fin_cases, m.discr, pow_eq_zero_iff, scalar, sub_eq_zero, trace_fin_two, two_ne_zero
-/
lemma isParabolic_iff_of_upperTriangular [IsReduced R] (hm : m 1 0 = 0) :
    m.IsParabolic ↔ m 0 0 = m 1 1 ∧ m 0 1 != 0 := by
  rw [IsParabolic]
  have aux : m.discr = 0 ↔ m 0 0 = m 1 1 := by
    suffices m.discr = (m 0 0 - m 1 1) ^ 2 by
      rw [this]; rw [pow_eq_zero_iff two_ne_zero]; rw [sub_eq_zero]
    grind [discr_fin_two, trace_fin_two, det_fin_two]
  have (h : m 0 0 = m 1 1) : m in Set.range (scalar _) ↔ m 0 1 = 0 := by
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro h'
      use m 1 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h', hm]
  tauto

end CommRing

section Field

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

/--
lemma `sub_scalar_sq_eq_discr` / 引理 `sub_scalar_sq_eq_discr`

English:
lemma sub_scalar_sq_eq_discr
  given: [NeZero (2 : K)]
  proof: by
  simp only [scalar_apply, trace_fin_two, discr_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field

中文:
引理 sub_scalar_sq_eq_discr
  条件: [NeZero (2 : K)]
  证明: by
  simp only [scalar_apply, trace_fin_two, discr_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field

Depends on / 依赖: Matrix, Matrix.mul_apply, det_fin_two, discr_fin_two, fin_cases, mul_apply, scalar_apply, trace_fin_two
-/
lemma sub_scalar_sq_eq_discr [NeZero (2 : K)] :
    (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.discr / 4) := by
  simp only [scalar_apply, trace_fin_two, discr_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field

variable (m) in
/--
Definition of `parabolicEigenvalue` / `parabolicEigenvalue` 的定义

English:
definition parabolicEigenvalue
  signature: : K
  body: m.trace / 2

中文:
定义 parabolicEigenvalue
  签名: : K
  定义体: m.trace / 2

Depends on / 依赖: m.trace
-/
def parabolicEigenvalue : K := m.trace / 2

/--
lemma `IsParabolic.sub_eigenvalue_sq_eq_zero` / 引理 `IsParabolic.sub_eigenvalue_sq_eq_zero`

English:
lemma IsParabolic.sub_eigenvalue_sq_eq_zero
  given: [NeZero (2 : K)] (hm : m.IsParabolic)
  proof: by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_discr, hm.2]

中文:
引理 IsParabolic.sub_eigenvalue_sq_eq_zero
  条件: [NeZero (2 : K)] (hm : m.IsParabolic)
  证明: by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_discr, hm.2]

Depends on / 依赖: parabolicEigenvalue, scalar_apply, sub_scalar_sq_eq_discr
-/
lemma IsParabolic.sub_eigenvalue_sq_eq_zero [NeZero (2 : K)] (hm : m.IsParabolic) :
    (m - scalar _ m.parabolicEigenvalue) ^ 2 = 0 := by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_discr, hm.2]

/--
lemma `isParabolic_iff_exists` / 引理 `isParabolic_iff_exists`

English:
lemma isParabolic_iff_exists
  given: [NeZero (2 : K)]
  proof: by
  constructor
  · exact fun hm => ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h => hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ => hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb,

中文:
引理 isParabolic_iff_exists
  条件: [NeZero (2 : K)]
  证明: by
  constructor
  · exact fun hm => ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h => hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ => hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb,

Depends on / 依赖: add_sub_cancel, div_eq_zero_iff, h.symm, hm.sub_eigenvalue_sq_eq_zero, m.discr, map_pow, map_sub, map_zero, scalar, scalar_inj, sq_eq_zero_iff, sub_eigenvalue_sq_eq_zero, sub_eq_iff_eq_add, sub_ne_zero, sub_ne_zero.mpr
-/
lemma isParabolic_iff_exists [NeZero (2 : K)] :
    m.IsParabolic ↔ exists a n, m = scalar _ a + n ∧ n != 0 ∧ n ^ 2 = 0 := by
  constructor
  · exact fun hm => ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h => hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ => hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb, ← map_sub, ← map_pow, ← map_zero (scalar (Fin 2)), scalar_inj,
        sq_eq_zero_iff] using hnsq
    · suffices scalar (Fin 2) (m.discr / 4) = 0 by
        rw [← map_zero (scalar (Fin 2))]; rw [scalar_inj]; rw [div_eq_zero_iff] at this
        have : (4 : K) != 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using NeZero.ne _
        tauto
      rw [← sub_scalar_sq_eq_discr]; rw [hm]; rw [trace_add]; rw [scalar_apply]; rw [trace_diagonal]
      simp [mul_div_cancel_left₀ _ (NeZero.ne (2 : K)),
        (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hnsq⟩).eq_zero, hnsq]

end Field

section Preorder

variable {R : Type*} [CommRing R] [Preorder R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/--
Definition of `IsHyperbolic` / `IsHyperbolic` 的定义

English:
definition IsHyperbolic
  signature: : Prop
  body: 0 < m.discr

中文:
定义 IsHyperbolic
  签名: : 命题
  定义体: 0 < m.discr

Depends on / 依赖: m.discr
-/
def IsHyperbolic : Prop := 0 < m.discr

/--
Definition of `IsElliptic` / `IsElliptic` 的定义

English:
definition IsElliptic
  signature: : Prop
  body: m.discr < 0

中文:
定义 IsElliptic
  签名: : 命题
  定义体: m.discr < 0

Depends on / 依赖: m.discr
-/
def IsElliptic : Prop := m.discr < 0

variable {m}

/--
lemma `isHyperbolic_conj_iff` / 引理 `isHyperbolic_conj_iff`

English:
lemma isHyperbolic_conj_iff
  statement: (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperbolic
  proof: by
  simp [IsHyperbolic]

中文:
引理 isHyperbolic_conj_iff
  结论: (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperbolic
  证明: by
  simp [IsHyperbolic]

Depends on / 依赖: IsHyperbolic
-/
lemma isHyperbolic_conj_iff : (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperbolic := by
  simp [IsHyperbolic]

/--
lemma `isHyperbolic_conj'_iff` / 引理 `isHyperbolic_conj'_iff`

English:
lemma isHyperbolic_conj'_iff
  statement: (g.val⁻¹ * m * g.val).IsHyperbolic ↔ m.IsHyperbolic
  proof: by
  simpa using isHyperbolic_conj_iff g⁻¹

中文:
引理 isHyperbolic_conj'_iff
  结论: (g.val⁻¹ * m * g.val).IsHyperbolic ↔ m.IsHyperbolic
  证明: by
  simpa using isHyperbolic_conj_iff g⁻¹

Depends on / 依赖: isHyperbolic_conj_iff
-/
lemma isHyperbolic_conj'_iff : (g.val⁻¹ * m * g.val).IsHyperbolic ↔ m.IsHyperbolic := by
  simpa using isHyperbolic_conj_iff g⁻¹

/--
lemma `isElliptic_conj_iff` / 引理 `isElliptic_conj_iff`

English:
lemma isElliptic_conj_iff
  statement: (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic
  proof: by
  simp [IsElliptic]

中文:
引理 isElliptic_conj_iff
  结论: (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic
  证明: by
  simp [IsElliptic]

Depends on / 依赖: IsElliptic
-/
lemma isElliptic_conj_iff : (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic := by
  simp [IsElliptic]

/--
lemma `isElliptic_conj'_iff` / 引理 `isElliptic_conj'_iff`

English:
lemma isElliptic_conj'_iff
  statement: (g.val⁻¹ * m * g.val).IsElliptic ↔ m.IsElliptic
  proof: by
  simpa using isElliptic_conj_iff g⁻¹

@[simp]

中文:
引理 isElliptic_conj'_iff
  结论: (g.val⁻¹ * m * g.val).IsElliptic ↔ m.IsElliptic
  证明: by
  simpa using isElliptic_conj_iff g⁻¹

@[simp]

Depends on / 依赖: isElliptic_conj_iff
-/
lemma isElliptic_conj'_iff : (g.val⁻¹ * m * g.val).IsElliptic ↔ m.IsElliptic := by
  simpa using isElliptic_conj_iff g⁻¹

@[simp]
/--
theorem `isHyperbolic_neg_iff` / 定理 `isHyperbolic_neg_iff`

English:
theorem isHyperbolic_neg_iff
  statement: (-m).IsHyperbolic ↔ m.IsHyperbolic
  proof: by
  simp [IsHyperbolic, discr_fin_two, det_neg]

protected alias ⟨IsHyperbolic.of_neg, IsHyperbolic.neg⟩ := isHyperbolic_neg_iff

@[simp]

中文:
定理 isHyperbolic_neg_iff
  结论: (-m).IsHyperbolic ↔ m.IsHyperbolic
  证明: by
  simp [IsHyperbolic, discr_fin_two, det_neg]

protected alias ⟨IsHyperbolic.of_neg, IsHyperbolic.neg⟩ := isHyperbolic_neg_iff

@[simp]

Depends on / 依赖: IsHyperbolic, det_neg, discr_fin_two
-/
theorem isHyperbolic_neg_iff : (-m).IsHyperbolic ↔ m.IsHyperbolic := by
  simp [IsHyperbolic, discr_fin_two, det_neg]

protected alias ⟨IsHyperbolic.of_neg, IsHyperbolic.neg⟩ := isHyperbolic_neg_iff

@[simp]
/--
theorem `isElliptic_neg_iff` / 定理 `isElliptic_neg_iff`

English:
theorem isElliptic_neg_iff
  statement: (-m).IsElliptic ↔ m.IsElliptic
  proof: by
  simp [IsElliptic, discr_fin_two, det_neg]

protected alias ⟨IsElliptic.of_neg, IsElliptic.neg⟩ := isElliptic_neg_iff

中文:
定理 isElliptic_neg_iff
  结论: (-m).IsElliptic ↔ m.IsElliptic
  证明: by
  simp [IsElliptic, discr_fin_two, det_neg]

protected alias ⟨IsElliptic.of_neg, IsElliptic.neg⟩ := isElliptic_neg_iff

Depends on / 依赖: IsElliptic, det_neg, discr_fin_two
-/
theorem isElliptic_neg_iff : (-m).IsElliptic ↔ m.IsElliptic := by
  simp [IsElliptic, discr_fin_two, det_neg]

protected alias ⟨IsElliptic.of_neg, IsElliptic.neg⟩ := isElliptic_neg_iff

end Preorder

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] {m : Matrix (Fin 2) (Fin 2) R}

/--
theorem `IsElliptic.bc_ne_zero` / 定理 `IsElliptic.bc_ne_zero`

English:
theorem IsElliptic.bc_ne_zero
  given: (hm : m.IsElliptic)
  statement: m 0 1 * m 1 0 != 0
  proof: by
  intro hc
  rw [IsElliptic]; rw [discr_fin_two]; rw [trace_fin_two]; rw [det_fin_two]; rw [hc] at hm
  refine hm.not_ge ?_
  linear_combination sq_nonneg (m 0 0 - m 1 1)

中文:
定理 IsElliptic.bc_ne_zero
  条件: (hm : m.IsElliptic)
  结论: m 0 1 * m 1 0 != 0
  证明: by
  intro hc
  rw [IsElliptic]; rw [discr_fin_two]; rw [trace_fin_two]; rw [det_fin_two]; rw [hc] at hm
  refine hm.not_ge ?_
  linear_combination sq_nonneg (m 0 0 - m 1 1)

Depends on / 依赖: IsElliptic, det_fin_two, discr_fin_two, hm.not_ge, linear_combination, not_ge, sq_nonneg, trace_fin_two
-/
theorem IsElliptic.bc_ne_zero (hm : m.IsElliptic) : m 0 1 * m 1 0 != 0 := by
  intro hc
  rw [IsElliptic]; rw [discr_fin_two]; rw [trace_fin_two]; rw [det_fin_two]; rw [hc] at hm
  refine hm.not_ge ?_
  linear_combination sq_nonneg (m 0 0 - m 1 1)

/--
theorem `IsElliptic.b_ne_zero` / 定理 `IsElliptic.b_ne_zero`

English:
theorem IsElliptic.b_ne_zero
  given: (hm : m.IsElliptic)
  statement: m 0 1 != 0
  proof: left_ne_zero_of_mul hm.bc_ne_zero

中文:
定理 IsElliptic.b_ne_zero
  条件: (hm : m.IsElliptic)
  结论: m 0 1 != 0
  证明: left_ne_zero_of_mul hm.bc_ne_zero

Depends on / 依赖: bc_ne_zero, hm.bc_ne_zero, left_ne_zero_of_mul
-/
theorem IsElliptic.b_ne_zero (hm : m.IsElliptic) : m 0 1 != 0 :=
  left_ne_zero_of_mul hm.bc_ne_zero

/--
theorem `IsElliptic.c_ne_zero` / 定理 `IsElliptic.c_ne_zero`

English:
theorem IsElliptic.c_ne_zero
  given: (hm : m.IsElliptic)
  statement: m 1 0 != 0
  proof: right_ne_zero_of_mul hm.bc_ne_zero

中文:
定理 IsElliptic.c_ne_zero
  条件: (hm : m.IsElliptic)
  结论: m 1 0 != 0
  证明: right_ne_zero_of_mul hm.bc_ne_zero

Depends on / 依赖: bc_ne_zero, hm.bc_ne_zero, right_ne_zero_of_mul
-/
theorem IsElliptic.c_ne_zero (hm : m.IsElliptic) : m 1 0 != 0 :=
  right_ne_zero_of_mul hm.bc_ne_zero

end LinearOrder

namespace GeneralLinearGroup

section Ring

variable {R : Type*} [Ring R]

/-- The map sending `x` to `[1, x; 0, 1]` (bundled as an `AddChar`). -/
@[simps apply]
/--
Definition of `upperRightHom` / `upperRightHom` 的定义

English:
definition upperRightHom
  signature: : AddChar R (GL (Fin 2) R) where
  body: ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  map_zero_eq_one' := by simp [Units.ext_iff, one_fin_two]
  map_add_eq_mul' a b := by simp [Units.ext_iff, add_comm]

中文:
定义 upperRightHom
  签名: : AddChar R (GL (Fin 2) R) where
  定义体: ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  map_zero_eq_one' := by simp [Units.ext_iff, one_fin_two]
  map_add_eq_mul' a b := by simp [Units.ext_iff, add_comm]

Depends on / 依赖: one_fin_two
-/
def upperRightHom : AddChar R (GL (Fin 2) R) where
  toFun x := ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  map_zero_eq_one' := by simp [Units.ext_iff, one_fin_two]
  map_add_eq_mul' a b := by simp [Units.ext_iff, add_comm]

/--
lemma `injective_upperRightHom` / 引理 `injective_upperRightHom`

English:
lemma injective_upperRightHom
  statement: Function.Injective (upperRightHom (R := R))
  proof: by
  refine (injective_iff_map_eq_zero (upperRightHom (R := R)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]

中文:
引理 injective_upperRightHom
  结论: Function.Injective (upperRightHom (R := R))
  证明: by
  refine (injective_iff_map_eq_zero (upperRightHom (R := R)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]

Depends on / 依赖: Units.ext_iff, ext_iff, injective_iff_map_eq_zero, one_fin_two, toAddMonoidHom, upperRightHom
-/
lemma injective_upperRightHom : Function.Injective (upperRightHom (R := R)) := by
  refine (injective_iff_map_eq_zero (upperRightHom (R := R)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]

end Ring

variable {R K : Type*} [CommRing R] [Field K]

/--
Definition of `IsParabolic` / `IsParabolic` 的定义

English:
abbreviation IsParabolic
  signature: (g : GL (Fin 2) R)
  body: g.val.IsParabolic

中文:
缩写 IsParabolic
  签名: (g : GL (Fin 2) R)
  定义体: g.val.IsParabolic

Depends on / 依赖: IsParabolic, g.val.IsParabolic
-/
abbrev IsParabolic (g : GL (Fin 2) R) : Prop := g.val.IsParabolic

/--
lemma `isParabolic_conj_iff` / 引理 `isParabolic_conj_iff`

English:
lemma isParabolic_conj_iff
  given: (g h : GL (Fin 2) R)
  proof: by
  simp [IsParabolic]

中文:
引理 isParabolic_conj_iff
  条件: (g h : GL (Fin 2) R)
  证明: by
  simp [IsParabolic]
-/
@[simp] lemma isParabolic_conj_iff (g h : GL (Fin 2) R) :
    IsParabolic (g * h * g⁻¹) ↔ IsParabolic h := by
  simp [IsParabolic]

/--
lemma `isParabolic_conj_iff'` / 引理 `isParabolic_conj_iff'`

English:
lemma isParabolic_conj_iff'
  given: (g h : GL (Fin 2) R)
  proof: by
  simp [IsParabolic]

中文:
引理 isParabolic_conj_iff'
  条件: (g h : GL (Fin 2) R)
  证明: by
  simp [IsParabolic]
-/
@[simp] lemma isParabolic_conj_iff' (g h : GL (Fin 2) R) :
    IsParabolic (g⁻¹ * h * g) ↔ IsParabolic h := by
  simp [IsParabolic]

/--
Definition of `IsElliptic` / `IsElliptic` 的定义

English:
abbreviation IsElliptic
  signature: [Preorder R] (g : GL (Fin 2) R)
  body: g.val.IsElliptic

中文:
缩写 IsElliptic
  签名: [Preorder R] (g : GL (Fin 2) R)
  定义体: g.val.IsElliptic

Depends on / 依赖: IsElliptic, g.val.IsElliptic
-/
abbrev IsElliptic [Preorder R] (g : GL (Fin 2) R) : Prop := g.val.IsElliptic

/--
Definition of `IsHyperbolic` / `IsHyperbolic` 的定义

English:
abbreviation IsHyperbolic
  signature: [Preorder R] (g : GL (Fin 2) R)
  body: g.val.IsHyperbolic

中文:
缩写 IsHyperbolic
  签名: [Preorder R] (g : GL (Fin 2) R)
  定义体: g.val.IsHyperbolic

Depends on / 依赖: IsHyperbolic, g.val.IsHyperbolic
-/
abbrev IsHyperbolic [Preorder R] (g : GL (Fin 2) R) : Prop := g.val.IsHyperbolic

/--
Definition of `fixpointPolynomial` / `fixpointPolynomial` 的定义

English:
definition fixpointPolynomial
  signature: (g : GL (Fin 2) R)
  body: C (g 1 0) * X ^ 2 + C (g 1 1 - g 0 0) * X - C (g 0 1)

中文:
定义 fixpointPolynomial
  签名: (g : GL (Fin 2) R)
  定义体: C (g 1 0) * X ^ 2 + C (g 1 1 - g 0 0) * X - C (g 0 1)
-/
noncomputable def fixpointPolynomial (g : GL (Fin 2) R) : R[X] :=
  C (g 1 0) * X ^ 2 + C (g 1 1 - g 0 0) * X - C (g 0 1)

/--
lemma `fixpointPolynomial_eq_zero_iff` / 引理 `fixpointPolynomial_eq_zero_iff`

English:
lemma fixpointPolynomial_eq_zero_iff
  given: {g : GL (Fin 2) R}
  proof: by
  rw [fixpointPolynomial]
  constructor
  · refine fun hP => ⟨g 0 0, ?_⟩
    have hb : g 0 1 = 0 := by simpa using congr_arg (coeff · 0) hP
    have hc : g 1 0 = 0 := by simpa using congr_arg (coeff · 2) hP
    have hd : g 1 1 = g 0 0 := by simpa [sub_eq_zero] using congr_arg (coeff · 1) hP
    e

中文:
引理 fixpointPolynomial_eq_zero_iff
  条件: {g : GL (Fin 2) R}
  证明: by
  rw [fixpointPolynomial]
  constructor
  · refine fun hP => ⟨g 0 0, ?_⟩
    have hb : g 0 1 = 0 := by simpa using congr_arg (coeff · 0) hP
    have hc : g 1 0 = 0 := by simpa using congr_arg (coeff · 2) hP
    have hd : g 1 1 = g 0 0 := by simpa [sub_eq_zero] using congr_arg (coeff · 1) hP
    e

Depends on / 依赖: congr_arg, fin_cases, fixpointPolynomial, sub_eq_zero
-/
lemma fixpointPolynomial_eq_zero_iff {g : GL (Fin 2) R} :
    g.fixpointPolynomial = 0 ↔ g.val in Set.range (Matrix.scalar _) := by
  rw [fixpointPolynomial]
  constructor
  · refine fun hP => ⟨g 0 0, ?_⟩
    have hb : g 0 1 = 0 := by simpa using congr_arg (coeff · 0) hP
    have hc : g 1 0 = 0 := by simpa using congr_arg (coeff · 2) hP
    have hd : g 1 1 = g 0 0 := by simpa [sub_eq_zero] using congr_arg (coeff · 1) hP
    ext i j
    fin_cases i <;>
    fin_cases j <;>
    simp [hb, hc, hd]
  · rintro ⟨a, ha⟩
    simp [← ha]

/--
lemma `parabolicEigenvalue_ne_zero` / 引理 `parabolicEigenvalue_ne_zero`

English:
lemma parabolicEigenvalue_ne_zero
  given: {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsParabolic g)
  proof: by
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, discr_fin_two] using hg.2
  rw [parabolicEigenvalue]; rw [div_ne_zero_iff]; rw [eq_true_intro (two_ne_zero' K)]; rw [and_true]; rw [Ne]; rw [← sq_eq_zero_iff]; rw [this]; rw [show (4 : K) = 2 ^ 2 by norm_num]; rw [mul_eq_zero]; rw

中文:
引理 parabolicEigenvalue_ne_zero
  条件: {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsParabolic g)
  证明: by
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, discr_fin_two] using hg.2
  rw [parabolicEigenvalue]; rw [div_ne_zero_iff]; rw [eq_true_intro (two_ne_zero' K)]; rw [and_true]; rw [Ne]; rw [← sq_eq_zero_iff]; rw [this]; rw [show (4 : K) = 2 ^ 2 by norm_num]; rw [mul_eq_zero]; rw

Depends on / 依赖: NeZero, NeZero.ne, and_true, det_ne_zero, discr_fin_two, div_ne_zero_iff, eq_true_intro, g.det_ne_zero, g.val.det, g.val.trace, mul_eq_zero, not_or, parabolicEigenvalue, sq_eq_zero_iff, sub_eq_zero, two_ne_zero
-/
lemma parabolicEigenvalue_ne_zero {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsParabolic g) :
    g.val.parabolicEigenvalue != 0 := by
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, discr_fin_two] using hg.2
  rw [parabolicEigenvalue]; rw [div_ne_zero_iff]; rw [eq_true_intro (two_ne_zero' K)]; rw [and_true]; rw [Ne]; rw [← sq_eq_zero_iff]; rw [this]; rw [show (4 : K) = 2 ^ 2 by norm_num]; rw [mul_eq_zero]; rw [sq_eq_zero_iff]; rw [not_or]
  exact ⟨NeZero.ne _, g.det_ne_zero⟩

/--
lemma `IsParabolic.pow` / 引理 `IsParabolic.pow`

English:
lemma IsParabolic.pow
  statement: {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
  proof: by
  rw [IsParabolic]; rw [isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    

中文:
引理 IsParabolic.pow
  结论: {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
  证明: by
  rw [IsParabolic]; rw [isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    

Depends on / 依赖: IsParabolic, Nat.add_sub_cancel, Nat.le_induction, Nat.one_le_iff_ne_zero, Units.val_pow_eq_pow_val, add_assoc, add_mul, add_sub_cancel, isParabolic_iff_exists, le_induction, map_mul, mul_add, mul_smul, one_le_iff_ne_zero, pow_succ, scalar_apply, smul_eq_diagonal_mul, smul_eq_mul_diagonal, smul_mul, smul_pow
-/
lemma IsParabolic.pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
    {n : Nat} (hn : n != 0) : IsParabolic (g ^ n) := by
  rw [IsParabolic]; rw [isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn IH =>
      simp only [pow_succ, IH, add_mul, Nat.add_sub_cancel, mul_add, ← map_mul, add_assoc]
      simp only [scalar_apply, ← smul_eq_mul_diagonal, ← mul_smul,
        ← smul_eq_diagonal_mul, smul_mul, ← sq, hmsq, smul_zero, add_zero, ← add_smul,
        Nat.cast_add_one, add_mul, one_mul]
      rw [(by lia : n = n - 1 + 1)]; rw [pow_succ]; rw [(by lia : n - 1 + 1 = n)]
      ring_nf
  · suffices a != 0 by simp [this, hm0, hn]
    refine fun ha => (g ^ 2).det_ne_zero ?_
    rw [ha]; rw [map_zero]; rw [zero_add] at hg
    rw [← hg] at hmsq
    rw [Units.val_pow_eq_pow_val]; rw [hmsq]; rw [det_zero]

/--
lemma `isParabolic_iff_of_upperTriangular` / 引理 `isParabolic_iff_of_upperTriangular`

English:
lemma isParabolic_iff_of_upperTriangular
  given: {g : GL (Fin 2) K} (hg : g 1 0 = 0)
  proof: Matrix.isParabolic_iff_of_upperTriangular hg

中文:
引理 isParabolic_iff_of_upperTriangular
  条件: {g : GL (Fin 2) K} (hg : g 1 0 = 0)
  证明: Matrix.isParabolic_iff_of_upperTriangular hg

Depends on / 依赖: Matrix, Matrix.isParabolic_iff_of_upperTriangular, isParabolic_iff_of_upperTriangular
-/
lemma isParabolic_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) :
    g.IsParabolic ↔ g 0 0 = g 1 1 ∧ g 0 1 != 0 :=
  Matrix.isParabolic_iff_of_upperTriangular hg

/--
lemma `isParabolic_iff_of_upperTriangular_of_det` / 引理 `isParabolic_iff_of_upperTriangular_of_det`

English:
lemma isParabolic_iff_of_upperTriangular_of_det
  statement: [LinearOrder K] [IsStrictOrderedRing K]
  proof: by
  rw [isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det

中文:
引理 isParabolic_iff_of_upperTriangular_of_det
  结论: [LinearOrder K] [IsStrictOrderedRing K]
  证明: by
  rw [isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det

Depends on / 依赖: Units.ext_iff, Units.val_neg, Units.val_one, det_fin_two, eta_fin_two, ext_iff, g.det, g.val.eta_fin_two, h_det, h_det.resolve_right, isParabolic_iff_of_upperTriangular, neg_eq_zero, neg_one_lt_zero, neg_one_lt_zero.trans_le, resolve_right, sq_eq_one_iff, sq_eq_one_iff.mp, sq_nonneg, trans_le, val_det_apply
-/
lemma isParabolic_iff_of_upperTriangular_of_det [LinearOrder K] [IsStrictOrderedRing K]
    {g : GL (Fin 2) K} (h_det : g.det = 1 ∨ g.det = -1) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (exists x != 0, g = upperRightHom x) ∨ (exists x != (0 : K), g = -upperRightHom x) := by
  rw [isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det.resolve_right (neg_one_lt_zero.trans_le <| sq_nonneg _).ne'
    apply (sq_eq_one_iff.mp this).imp <;> intro hg11 <;> simp only [Units.ext_iff]
    · refine ⟨g 0 1, hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
    · refine ⟨-g 0 1, neg_eq_zero.not.mpr hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;>
    simpa using hx

end GeneralLinearGroup

end Matrix
