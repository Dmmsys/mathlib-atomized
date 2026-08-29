/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Orthonormal sets

This file defines orthonormal sets in inner product spaces.

## Main results

- We define `Orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.
- Bessel's inequality, `Orthonormal.tsum_inner_products_le`, states that given an orthonormal set
  `v` and a vector `x`, the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more
  than the norm-square of `x`.

For the existence of orthonormal bases, Hilbert bases, etc., see the file
`Analysis.InnerProductSpace.projection`.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter Module Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section OrthonormalSets_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

/--
Definition of `Orthonormal` / `Orthonormal` 的定义

English:
definition Orthonormal
  signature: (v : ι -> E)
  body: (forall i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0

中文:
定义 Orthonormal
  签名: (v : ι -> E)
  定义体: (forall i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0

Depends on / 依赖: Pairwise
-/
def Orthonormal (v : ι -> E) : Prop :=
  (forall i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0

variable {𝕜}

@[simp]
/--
lemma `Orthonormal.of_isEmpty` / 引理 `Orthonormal.of_isEmpty`

English:
lemma Orthonormal.of_isEmpty
  given: [IsEmpty ι] (v : ι -> E)
  statement: Orthonormal 𝕜 v
  proof: ⟨IsEmpty.elim ‹_›, Subsingleton.pairwise⟩

@[simp]

中文:
引理 Orthonormal.of_isEmpty
  条件: [IsEmpty ι] (v : ι -> E)
  结论: Orthonormal 𝕜 v
  证明: ⟨IsEmpty.elim ‹_›, Subsingleton.pairwise⟩

@[simp]

Depends on / 依赖: IsEmpty, IsEmpty.elim, Subsingleton, Subsingleton.pairwise, pairwise
-/
lemma Orthonormal.of_isEmpty [IsEmpty ι] (v : ι -> E) : Orthonormal 𝕜 v :=
  ⟨IsEmpty.elim ‹_›, Subsingleton.pairwise⟩

@[simp]
/--
lemma `orthonormal_vecCons_iff` / 引理 `orthonormal_vecCons_iff`

English:
lemma orthonormal_vecCons_iff
  given: {n : Nat} {v : E} {vs : Fin n -> E}
  proof: by
  simp_rw [Orthonormal, pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]
  tauto

中文:
引理 orthonormal_vecCons_iff
  条件: {n : 自然数} {v : E} {vs : Fin n -> E}
  证明: by
  simp_rw [Orthonormal, pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]
  tauto

Depends on / 依赖: Fin.forall_fin_succ, Orthonormal, forall_fin_succ, pairwise_fin_succ_iff_of_isSymm, simp_rw
-/
lemma orthonormal_vecCons_iff {n : Nat} {v : E} {vs : Fin n -> E} :
    Orthonormal 𝕜 (Matrix.vecCons v vs) ↔ ‖v‖ = 1 ∧ (forall i, ⟪v, vs i⟫ = 0) ∧ Orthonormal 𝕜 vs := by
  simp_rw [Orthonormal, pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]
  tauto

/--
lemma `Orthonormal.norm_eq_one` / 引理 `Orthonormal.norm_eq_one`

English:
lemma Orthonormal.norm_eq_one
  given: {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι)
  proof: h.1 i

中文:
引理 Orthonormal.norm_eq_one
  条件: {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι)
  证明: h.1 i
-/
lemma Orthonormal.norm_eq_one {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι) :
    ‖v i‖ = 1 := h.1 i

/--
lemma `Orthonormal.nnnorm_eq_one` / 引理 `Orthonormal.nnnorm_eq_one`

English:
lemma Orthonormal.nnnorm_eq_one
  given: {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι)
  proof: by
  suffices (‖v i‖₊ : Real) = 1 by norm_cast at this
  simp [h.norm_eq_one]

中文:
引理 Orthonormal.nnnorm_eq_one
  条件: {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι)
  证明: by
  suffices (‖v i‖₊ : Real) = 1 by norm_cast at this
  simp [h.norm_eq_one]

Depends on / 依赖: h.norm_eq_one, norm_eq_one
-/
lemma Orthonormal.nnnorm_eq_one {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι) :
    ‖v i‖₊ = 1 := by
  suffices (‖v i‖₊ : Real) = 1 by norm_cast at this
  simp [h.norm_eq_one]

/--
lemma `Orthonormal.enorm_eq_one` / 引理 `Orthonormal.enorm_eq_one`

English:
lemma Orthonormal.enorm_eq_one
  given: {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι)
  proof: by rw [← ofReal_norm]; simp [h.norm_eq_one]

中文:
引理 Orthonormal.enorm_eq_one
  条件: {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι)
  证明: by rw [← ofReal_norm]; simp [h.norm_eq_one]

Depends on / 依赖: h.norm_eq_one, norm_eq_one, ofReal_norm
-/
lemma Orthonormal.enorm_eq_one {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι) :
    ‖v i‖ₑ = 1 := by rw [← ofReal_norm]; simp [h.norm_eq_one]

/--
lemma `Orthonormal.inner_eq_zero` / 引理 `Orthonormal.inner_eq_zero`

English:
lemma Orthonormal.inner_eq_zero
  given: {v : ι -> E} {i j : ι} (h : Orthonormal 𝕜 v) (hij : i != j)
  proof: h.2 hij

中文:
引理 Orthonormal.inner_eq_zero
  条件: {v : ι -> E} {i j : ι} (h : Orthonormal 𝕜 v) (hij : i != j)
  证明: h.2 hij
-/
lemma Orthonormal.inner_eq_zero {v : ι -> E} {i j : ι} (h : Orthonormal 𝕜 v) (hij : i != j) :
    ⟪v i, v j⟫ = 0 := h.2 hij

/--
theorem `orthonormal_iff_ite` / 定理 `orthonormal_iff_ite`

English:
theorem orthonormal_iff_ite
  given: [DecidableEq ι] {v : ι -> E}
  proof: by
  constructor
  · intro hv i j
    split_ifs with h
    · simp [h, inner_self_eq_norm_sq_to_K, hv.norm_eq_one]
    · exact hv.inner_eq_zero h
  · intro h
    constructor
    · intro i
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by
        rw [@norm_sq_eq_re_inner 𝕜]; rw [h i i]; simp
      have h₁ : 0 <

中文:
定理 orthonormal_iff_ite
  条件: [DecidableEq ι] {v : ι -> E}
  证明: by
  constructor
  · intro hv i j
    split_ifs with h
    · simp [h, inner_self_eq_norm_sq_to_K, hv.norm_eq_one]
    · exact hv.inner_eq_zero h
  · intro h
    constructor
    · intro i
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by
        rw [@norm_sq_eq_re_inner 𝕜]; rw [h i i]; simp
      have h₁ : 0 <

Depends on / 依赖: hv.inner_eq_zero, hv.norm_eq_one, inner_eq_zero, inner_self_eq_norm_sq_to_K, norm_eq_one, norm_nonneg, norm_sq_eq_re_inner, split_ifs, zero_le_one
-/
theorem orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} :
    Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜) := by
  constructor
  · intro hv i j
    split_ifs with h
    · simp [h, inner_self_eq_norm_sq_to_K, hv.norm_eq_one]
    · exact hv.inner_eq_zero h
  · intro h
    constructor
    · intro i
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by
        rw [@norm_sq_eq_re_inner 𝕜]; rw [h i i]; simp
      have h₁ : 0 <= ‖v i‖ := norm_nonneg _
      have h₂ : (0 : Real) <= 1 := zero_le_one
      rwa [sq_eq_sq₀ h₁ h₂] at h'
    · intro i j hij
      simpa [hij] using h i j

@[simp]
/--
theorem `orthonormal_subsingleton_iff` / 定理 `orthonormal_subsingleton_iff`

English:
theorem orthonormal_subsingleton_iff
  given: [Subsingleton ι] {v : ι -> E}
  proof: by
  simp [orthonormal_iff_ite, ← map_pow, pow_eq_one_iff_of_nonneg]

中文:
定理 orthonormal_subsingleton_iff
  条件: [Subsingleton ι] {v : ι -> E}
  证明: by
  simp [orthonormal_iff_ite, ← map_pow, pow_eq_one_iff_of_nonneg]

Depends on / 依赖: map_pow, orthonormal_iff_ite, pow_eq_one_iff_of_nonneg
-/
theorem orthonormal_subsingleton_iff [Subsingleton ι] {v : ι -> E} :
    Orthonormal 𝕜 v ↔ forall i, ‖v i‖ = 1 := by
  simp [orthonormal_iff_ite, ← map_pow, pow_eq_one_iff_of_nonneg]

/--
theorem `orthonormal_subtype_iff_ite` / 定理 `orthonormal_subtype_iff_ite`

English:
theorem orthonormal_subtype_iff_ite
  given: [DecidableEq E] {s : Set E}
  proof: by
  rw [orthonormal_iff_ite]
  simp

中文:
定理 orthonormal_subtype_iff_ite
  条件: [DecidableEq E] {s : Set E}
  证明: by
  rw [orthonormal_iff_ite]
  simp

Depends on / 依赖: orthonormal_iff_ite
-/
theorem orthonormal_subtype_iff_ite [DecidableEq E] {s : Set E} :
    Orthonormal 𝕜 (Subtype.val : s -> E) ↔ forall v in s, forall w in s, ⟪v, w⟫ = if v = w then 1 else 0 := by
  rw [orthonormal_iff_ite]
  simp

/--
theorem `Orthonormal.inner_right_finsupp` / 定理 `Orthonormal.inner_right_finsupp`

English:
theorem Orthonormal.inner_right_finsupp
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι)
  proof: by
  classical
  simp [linearCombination_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv, inner_smul_right,
    eq_comm]

中文:
定理 Orthonormal.inner_right_finsupp
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι)
  证明: by
  classical
  simp [linearCombination_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv, inner_smul_right,
    eq_comm]

Depends on / 依赖: Finsupp, Finsupp.inner_sum, classical, eq_comm, inner_smul_right, inner_sum, linearCombination_apply, orthonormal_iff_ite, orthonormal_iff_ite.mp
-/
theorem Orthonormal.inner_right_finsupp {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) :
    ⟪v i, linearCombination 𝕜 v l⟫ = l i := by
  classical
  simp [linearCombination_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv, inner_smul_right,
    eq_comm]

/--
theorem `Orthonormal.inner_right_sum` / 定理 `Orthonormal.inner_right_sum`

English:
theorem Orthonormal.inner_right_sum
  statement: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι}
  proof: by
  classical
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]

中文:
定理 Orthonormal.inner_right_sum
  结论: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι}
  证明: by
  classical
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]

Depends on / 依赖: classical, inner_smul_right, inner_sum, orthonormal_iff_ite, orthonormal_iff_ite.mp
-/
theorem Orthonormal.inner_right_sum {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι}
    {i : ι} (hi : i in s) : ⟪v i, ∑ i in s, l i • v i⟫ = l i := by
  classical
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]

/--
theorem `Orthonormal.inner_right_fintype` / 定理 `Orthonormal.inner_right_fintype`

English:
theorem Orthonormal.inner_right_fintype
  statement: [Fintype ι] {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜)
  proof: hv.inner_right_sum l (Finset.mem_univ _)

中文:
定理 Orthonormal.inner_right_fintype
  结论: [Fintype ι] {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜)
  证明: hv.inner_right_sum l (Finset.mem_univ _)

Depends on / 依赖: Finset, Finset.mem_univ, hv.inner_right_sum, inner_right_sum, mem_univ
-/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜)
    (i : ι) : ⟪v i, ∑ i : ι, l i • v i⟫ = l i :=
  hv.inner_right_sum l (Finset.mem_univ _)

/--
theorem `Orthonormal.inner_left_finsupp` / 定理 `Orthonormal.inner_left_finsupp`

English:
theorem Orthonormal.inner_left_finsupp
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι)
  proof: by rw [← inner_conj_symm, hv.inner_right_finsupp]

中文:
定理 Orthonormal.inner_left_finsupp
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι)
  证明: by rw [← inner_conj_symm, hv.inner_right_finsupp]

Depends on / 依赖: hv.inner_right_finsupp, inner_conj_symm, inner_right_finsupp
-/
theorem Orthonormal.inner_left_finsupp {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) :
    ⟪linearCombination 𝕜 v l, v i⟫ = conj (l i) := by rw [← inner_conj_symm, hv.inner_right_finsupp]

/--
theorem `Orthonormal.inner_left_sum` / 定理 `Orthonormal.inner_left_sum`

English:
theorem Orthonormal.inner_left_sum
  statement: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι}
  proof: by
  classical
  simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
    Finset.sum_ite_eq', if_true]

中文:
定理 Orthonormal.inner_left_sum
  结论: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι}
  证明: by
  classical
  simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
    Finset.sum_ite_eq', if_true]

Depends on / 依赖: Finset, Finset.sum_ite_eq, classical, if_true, inner_smul_left, mul_boole, orthonormal_iff_ite, orthonormal_iff_ite.mp, sum_inner, sum_ite_eq
-/
theorem Orthonormal.inner_left_sum {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι}
    {i : ι} (hi : i in s) : ⟪∑ i in s, l i • v i, v i⟫ = conj (l i) := by
  classical
  simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
    Finset.sum_ite_eq', if_true]

/--
theorem `Orthonormal.inner_left_fintype` / 定理 `Orthonormal.inner_left_fintype`

English:
theorem Orthonormal.inner_left_fintype
  statement: [Fintype ι] {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜)
  proof: hv.inner_left_sum l (Finset.mem_univ _)

中文:
定理 Orthonormal.inner_left_fintype
  结论: [Fintype ι] {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜)
  证明: hv.inner_left_sum l (Finset.mem_univ _)

Depends on / 依赖: Finset, Finset.mem_univ, hv.inner_left_sum, inner_left_sum, mem_univ
-/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜)
    (i : ι) : ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i) :=
  hv.inner_left_sum l (Finset.mem_univ _)

/--
theorem `Orthonormal.inner_finsupp_eq_sum_left` / 定理 `Orthonormal.inner_finsupp_eq_sum_left`

English:
theorem Orthonormal.inner_finsupp_eq_sum_left
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι ->₀ 𝕜)
  proof: by
  simp [l₁.linearCombination_apply, Finsupp.sum_inner, hv.inner_right_finsupp, inner_smul_left]

中文:
定理 Orthonormal.inner_finsupp_eq_sum_left
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι ->₀ 𝕜)
  证明: by
  simp [l₁.linearCombination_apply, Finsupp.sum_inner, hv.inner_right_finsupp, inner_smul_left]

Depends on / 依赖: Finsupp, Finsupp.sum_inner, hv.inner_right_finsupp, inner_right_finsupp, inner_smul_left, linearCombination_apply, sum_inner
-/
theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι ->₀ 𝕜) :
    ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₁.sum fun i y => conj y * l₂ i := by
  simp [l₁.linearCombination_apply, Finsupp.sum_inner, hv.inner_right_finsupp, inner_smul_left]

/--
theorem `Orthonormal.inner_finsupp_eq_sum_right` / 定理 `Orthonormal.inner_finsupp_eq_sum_right`

English:
theorem Orthonormal.inner_finsupp_eq_sum_right
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι ->₀ 𝕜)
  proof: by
  simp [l₂.linearCombination_apply, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm,
    inner_smul_right]

中文:
定理 Orthonormal.inner_finsupp_eq_sum_right
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι ->₀ 𝕜)
  证明: by
  simp [l₂.linearCombination_apply, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm,
    inner_smul_right]

Depends on / 依赖: Finsupp, Finsupp.inner_sum, hv.inner_left_finsupp, inner_left_finsupp, inner_smul_right, inner_sum, linearCombination_apply, mul_comm
-/
theorem Orthonormal.inner_finsupp_eq_sum_right {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι ->₀ 𝕜) :
    ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₂.sum fun i y => conj (l₁ i) * y := by
  simp [l₂.linearCombination_apply, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm,
    inner_smul_right]

/--
theorem `Orthonormal.inner_sum` / 定理 `Orthonormal.inner_sum`

English:
theorem Orthonormal.inner_sum
  statement: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι -> 𝕜)
  proof: by
  simp_rw [sum_inner, inner_smul_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hv.inner_right_sum l₂ hi]

中文:
定理 Orthonormal.inner_sum
  结论: {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι -> 𝕜)
  证明: by
  simp_rw [sum_inner, inner_smul_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hv.inner_right_sum l₂ hi]
-/
protected theorem Orthonormal.inner_sum {v : ι -> E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι -> 𝕜)
    (s : Finset ι) : ⟪∑ i in s, l₁ i • v i, ∑ i in s, l₂ i • v i⟫ = ∑ i in s, conj (l₁ i) * l₂ i := by
  simp_rw [sum_inner, inner_smul_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hv.inner_right_sum l₂ hi]

/--
theorem `Orthonormal.inner_left_right_finset` / 定理 `Orthonormal.inner_left_right_finset`

English:
theorem Orthonormal.inner_left_right_finset
  statement: {s : Finset ι} {v : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: by
  classical
  simp [orthonormal_iff_ite.mp hv]

中文:
定理 Orthonormal.inner_left_right_finset
  结论: {s : Finset ι} {v : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: by
  classical
  simp [orthonormal_iff_ite.mp hv]

Depends on / 依赖: classical, orthonormal_iff_ite, orthonormal_iff_ite.mp
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι -> E} (hv : Orthonormal 𝕜 v)
    {a : ι -> ι -> 𝕜} : (∑ i in s, ∑ j in s, a i j • ⟪v j, v i⟫) = ∑ k in s, a k k := by
  classical
  simp [orthonormal_iff_ite.mp hv]

/--
theorem `Orthonormal.linearIndependent` / 定理 `Orthonormal.linearIndependent`

English:
theorem Orthonormal.linearIndependent
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.linearCombination 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using! key

中文:
定理 Orthonormal.linearIndependent
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.linearCombination 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using! key

Depends on / 依赖: Finsupp, Finsupp.linearCombination, hv.inner_right_finsupp, inner_right_finsupp, inner_zero_right, linearCombination, linearIndependent_iff
-/
theorem Orthonormal.linearIndependent {v : ι -> E} (hv : Orthonormal 𝕜 v) :
    LinearIndependent 𝕜 v := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.linearCombination 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using! key

/--
theorem `Orthonormal.comp` / 定理 `Orthonormal.comp`

English:
theorem Orthonormal.comp
  statement: {ι' : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : ι' -> ι)
  proof: by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  convert! hv (f i) (f j) using 1
  simp [hf.eq_iff]

中文:
定理 Orthonormal.comp
  结论: {ι' : 类型} {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : ι' -> ι)
  证明: by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  convert! hv (f i) (f j) using 1
  simp [hf.eq_iff]

Depends on / 依赖: classical, convert, eq_iff, hf.eq_iff, orthonormal_iff_ite
-/
theorem Orthonormal.comp {ι' : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : ι' -> ι)
    (hf : Function.Injective f) : Orthonormal 𝕜 (v ∘ f) := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  convert! hv (f i) (f j) using 1
  simp [hf.eq_iff]

/--
theorem `orthonormal_subtype_range` / 定理 `orthonormal_subtype_range`

English:
theorem orthonormal_subtype_range
  given: {v : ι -> E} (hv : Function.Injective v)
  proof: by
  let f : ι ≃ Set.range v := Equiv.ofInjective v hv
  refine ⟨fun h => h.comp f f.injective, fun h => ?_⟩
  rw [← Equiv.self_comp_ofInjective_symm hv]
  exact h.comp f.symm f.symm.injective

中文:
定理 orthonormal_subtype_range
  条件: {v : ι -> E} (hv : Function.Injective v)
  证明: by
  let f : ι ≃ Set.range v := Equiv.ofInjective v hv
  refine ⟨fun h => h.comp f f.injective, fun h => ?_⟩
  rw [← Equiv.self_comp_ofInjective_symm hv]
  exact h.comp f.symm f.symm.injective

Depends on / 依赖: Equiv.ofInjective, Equiv.self_comp_ofInjective_symm, Set.range, f.injective, f.symm, f.symm.injective, h.comp, injective, ofInjective, self_comp_ofInjective_symm
-/
theorem orthonormal_subtype_range {v : ι -> E} (hv : Function.Injective v) :
    Orthonormal 𝕜 (Subtype.val : Set.range v -> E) ↔ Orthonormal 𝕜 v := by
  let f : ι ≃ Set.range v := Equiv.ofInjective v hv
  refine ⟨fun h => h.comp f f.injective, fun h => ?_⟩
  rw [← Equiv.self_comp_ofInjective_symm hv]
  exact h.comp f.symm f.symm.injective

/--
theorem `Orthonormal.toSubtypeRange` / 定理 `Orthonormal.toSubtypeRange`

English:
theorem Orthonormal.toSubtypeRange
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: (orthonormal_subtype_range hv.linearIndependent.injective).2 hv

中文:
定理 Orthonormal.toSubtypeRange
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: (orthonormal_subtype_range hv.linearIndependent.injective).2 hv

Depends on / 依赖: hv.linearIndependent.injective, injective, linearIndependent, orthonormal_subtype_range
-/
theorem Orthonormal.toSubtypeRange {v : ι -> E} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (Subtype.val : Set.range v -> E) :=
  (orthonormal_subtype_range hv.linearIndependent.injective).2 hv

/--
theorem `Orthonormal.inner_finsupp_eq_zero` / 定理 `Orthonormal.inner_finsupp_eq_zero`

English:
theorem Orthonormal.inner_finsupp_eq_zero
  statement: {v : ι -> E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι}
  proof: by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]

中文:
定理 Orthonormal.inner_finsupp_eq_zero
  结论: {v : ι -> E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι}
  证明: by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]

Depends on / 依赖: Finsupp, Finsupp.mem_supported, hv.inner_left_finsupp, inner_left_finsupp, map_zero, mem_supported
-/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι -> E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι}
    (hi : i ∉ s) {l : ι ->₀ 𝕜} (hl : l in Finsupp.supported 𝕜 𝕜 s) :
    ⟪Finsupp.linearCombination 𝕜 v l, v i⟫ = 0 := by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]

/--
theorem `Orthonormal.orthonormal_of_forall_eq_or_eq_neg` / 定理 `Orthonormal.orthonormal_of_forall_eq_or_eq_neg`

English:
theorem Orthonormal.orthonormal_of_forall_eq_or_eq_neg
  statement: {v w : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: by
  classical
  rw [orthonormal_iff_ite] at *
  intro i j
  rcases hw i with hi | hi <;> rcases hw j with hj | hj <;>
    replace hv := hv i j <;> split_ifs at hv ⊢ with h <;>
    simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
      neg_eq_zero] using hv

中文:
定理 Orthonormal.orthonormal_of_forall_eq_or_eq_neg
  结论: {v w : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: by
  classical
  rw [orthonormal_iff_ite] at *
  intro i j
  rcases hw i with hi | hi <;> rcases hw j with hj | hj <;>
    replace hv := hv i j <;> split_ifs at hv ⊢ with h <;>
    simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
      neg_eq_zero] using hv

Depends on / 依赖: classical, eq_self_iff_true, inner_neg_left, inner_neg_right, neg_eq_zero, neg_neg, orthonormal_iff_ite, replace, split_ifs
-/
theorem Orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι -> E} (hv : Orthonormal 𝕜 v)
    (hw : forall i, w i = v i ∨ w i = -v i) : Orthonormal 𝕜 w := by
  classical
  rw [orthonormal_iff_ite] at *
  intro i j
  rcases hw i with hi | hi <;> rcases hw j with hj | hj <;>
    replace hv := hv i j <;> split_ifs at hv ⊢ with h <;>
    simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
      neg_eq_zero] using hv

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independent sets. See
`exists_linearIndependent` in particular. -/
variable (𝕜 E)

/--
theorem `orthonormal_empty` / 定理 `orthonormal_empty`

English:
theorem orthonormal_empty
  statement: Orthonormal 𝕜 (fun x => x : (∅ : Set E) -> E)
  proof: by
  simp

中文:
定理 orthonormal_empty
  结论: Orthonormal 𝕜 (fun x => x : (∅ : Set E) -> E)
  证明: by
  simp
-/
theorem orthonormal_empty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) -> E) := by
  simp

variable {𝕜 E}

/--
theorem `orthonormal_iUnion_of_directed` / 定理 `orthonormal_iUnion_of_directed`

English:
theorem orthonormal_iUnion_of_directed
  statement: {η : Type*} {s : η -> Set E} (hs : Directed (· subseteq ·) s)
  proof: by
  classical
  rw [orthonormal_subtype_iff_ite]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
  obtain ⟨k, hik, hjk⟩ := hs i j
  have h_orth : Orthonormal 𝕜 (fun x => x : s k -> E) := h k
  rw [orthonormal_subtype_iff_ite] at h_orth
  exact h_orth x (hik hxi) y (hjk hyj)

中文:
定理 orthonormal_iUnion_of_directed
  结论: {η : 类型} {s : η -> Set E} (hs : Directed (· subseteq ·) s)
  证明: by
  classical
  rw [orthonormal_subtype_iff_ite]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
  obtain ⟨k, hik, hjk⟩ := hs i j
  have h_orth : Orthonormal 𝕜 (fun x => x : s k -> E) := h k
  rw [orthonormal_subtype_iff_ite] at h_orth
  exact h_orth x (hik hxi) y (hjk hyj)

Depends on / 依赖: Orthonormal, classical, h_orth, orthonormal_subtype_iff_ite
-/
theorem orthonormal_iUnion_of_directed {η : Type*} {s : η -> Set E} (hs : Directed (· subseteq ·) s)
    (h : forall i, Orthonormal 𝕜 (fun x => x : s i -> E)) :
    Orthonormal 𝕜 (fun x => x : (⋃ i, s i) -> E) := by
  classical
  rw [orthonormal_subtype_iff_ite]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
  obtain ⟨k, hik, hjk⟩ := hs i j
  have h_orth : Orthonormal 𝕜 (fun x => x : s k -> E) := h k
  rw [orthonormal_subtype_iff_ite] at h_orth
  exact h_orth x (hik hxi) y (hjk hyj)

/--
theorem `orthonormal_sUnion_of_directed` / 定理 `orthonormal_sUnion_of_directed`

English:
theorem orthonormal_sUnion_of_directed
  statement: {s : Set (Set E)} (hs : DirectedOn (· subseteq ·) s)
  proof: by
  rw [Set.sUnion_eq_iUnion]; exact orthonormal_iUnion_of_directed hs.directed_val (by simpa using h)

中文:
定理 orthonormal_sUnion_of_directed
  结论: {s : Set (Set E)} (hs : DirectedOn (· subseteq ·) s)
  证明: by
  rw [Set.sUnion_eq_iUnion]; exact orthonormal_iUnion_of_directed hs.directed_val (by simpa using h)

Depends on / 依赖: Set.sUnion_eq_iUnion, directed_val, hs.directed_val, orthonormal_iUnion_of_directed, sUnion_eq_iUnion
-/
theorem orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· subseteq ·) s)
    (h : forall a in s, Orthonormal 𝕜 (fun x => ((x : a) : E))) :
    Orthonormal 𝕜 (fun x => x : ⋃₀ s -> E) := by
  rw [Set.sUnion_eq_iUnion]; exact orthonormal_iUnion_of_directed hs.directed_val (by simpa using h)

/--
theorem `exists_maximal_orthonormal` / 定理 `exists_maximal_orthonormal`

English:
theorem exists_maximal_orthonormal
  given: {s : Set E} (hs : Orthonormal 𝕜 (Subtype.val : s -> E))
  proof: by
  have := zorn_subset_nonempty { b | Orthonormal 𝕜 (Subtype.val : b -> E) } ?_ _ hs
  · obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.1, hb.2.1, fun u hus hu => hb.2.eq_of_ge hu hus⟩
  · refine fun c hc cc _c0 => ⟨⋃₀ c, ?_, ?_⟩
    · exact orthonormal_sUnion_of_directed cc.directedOn fun x xc => hc xc


中文:
定理 exists_maximal_orthonormal
  条件: {s : Set E} (hs : Orthonormal 𝕜 (Subtype.val : s -> E))
  证明: by
  have := zorn_subset_nonempty { b | Orthonormal 𝕜 (Subtype.val : b -> E) } ?_ _ hs
  · obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.1, hb.2.1, fun u hus hu => hb.2.eq_of_ge hu hus⟩
  · refine fun c hc cc _c0 => ⟨⋃₀ c, ?_, ?_⟩
    · exact orthonormal_sUnion_of_directed cc.directedOn fun x xc => hc xc


Depends on / 依赖: Orthonormal, Set.subset_sUnion_of_mem, Subtype, Subtype.val, cc.directedOn, directedOn, eq_of_ge, orthonormal_sUnion_of_directed, subset_sUnion_of_mem, zorn_subset_nonempty
-/
theorem exists_maximal_orthonormal {s : Set E} (hs : Orthonormal 𝕜 (Subtype.val : s -> E)) :
    exists w ⊇ s, Orthonormal 𝕜 (Subtype.val : w -> E) ∧
      forall u ⊇ w, Orthonormal 𝕜 (Subtype.val : u -> E) -> u = w := by
  have := zorn_subset_nonempty { b | Orthonormal 𝕜 (Subtype.val : b -> E) } ?_ _ hs
  · obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.1, hb.2.1, fun u hus hu => hb.2.eq_of_ge hu hus⟩
  · refine fun c hc cc _c0 => ⟨⋃₀ c, ?_, ?_⟩
    · exact orthonormal_sUnion_of_directed cc.directedOn fun x xc => hc xc
    · exact fun _ => Set.subset_sUnion_of_mem

open Module

/--
Definition of `basisOfOrthonormalOfCardEqFinrank` / `basisOfOrthonormalOfCardEqFinrank` 的定义

English:
definition basisOfOrthonormalOfCardEqFinrank
  signature: [Fintype ι] [Nonempty ι] {v : ι -> E} (hv : Orthonormal 𝕜 v)
  body: basisOfLinearIndependentOfCardEqFinrank hv.linearIndependent card_eq

@[simp]

中文:
定义 basisOfOrthonormalOfCardEqFinrank
  签名: [Fintype ι] [Nonempty ι] {v : ι -> E} (hv : Orthonormal 𝕜 v)
  定义体: basisOfLinearIndependentOfCardEqFinrank hv.linearIndependent card_eq

@[simp]

Depends on / 依赖: basisOfLinearIndependentOfCardEqFinrank, card_eq, hv.linearIndependent, linearIndependent
-/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι -> E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.linearIndependent card_eq

@[simp]
/--
theorem `coe_basisOfOrthonormalOfCardEqFinrank` / 定理 `coe_basisOfOrthonormalOfCardEqFinrank`

English:
theorem coe_basisOfOrthonormalOfCardEqFinrank
  statement: [Fintype ι] [Nonempty ι] {v : ι -> E}
  proof: coe_basisOfLinearIndependentOfCardEqFinrank _ _

中文:
定理 coe_basisOfOrthonormalOfCardEqFinrank
  结论: [Fintype ι] [Nonempty ι] {v : ι -> E}
  证明: coe_basisOfLinearIndependentOfCardEqFinrank _ _

Depends on / 依赖: coe_basisOfLinearIndependentOfCardEqFinrank
-/
theorem coe_basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι -> E}
    (hv : Orthonormal 𝕜 v) (card_eq : Fintype.card ι = finrank 𝕜 E) :
    (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι -> E) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/--
theorem `Orthonormal.ne_zero` / 定理 `Orthonormal.ne_zero`

English:
theorem Orthonormal.ne_zero
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (i : ι)
  statement: v i != 0
  proof: by
  refine ne_of_apply_ne norm ?_
  rw [hv.1 i]; rw [norm_zero]
  simp

中文:
定理 Orthonormal.ne_zero
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (i : ι)
  结论: v i != 0
  证明: by
  refine ne_of_apply_ne norm ?_
  rw [hv.1 i]; rw [norm_zero]
  simp

Depends on / 依赖: ne_of_apply_ne, norm_zero
-/
theorem Orthonormal.ne_zero {v : ι -> E} (hv : Orthonormal 𝕜 v) (i : ι) : v i != 0 := by
  refine ne_of_apply_ne norm ?_
  rw [hv.1 i]; rw [norm_zero]
  simp

end OrthonormalSets_Seminormed

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']

/--
theorem `LinearIsometry.orthonormal_comp_iff` / 定理 `LinearIsometry.orthonormal_comp_iff`

English:
theorem LinearIsometry.orthonormal_comp_iff
  given: {v : ι -> E} (f : E ->ₗᵢ[𝕜] E')
  proof: by
  classical simp_rw [orthonormal_iff_ite, Function.comp_apply, LinearIsometry.inner_map_map]

中文:
定理 LinearIsometry.orthonormal_comp_iff
  条件: {v : ι -> E} (f : E ->ₗᵢ[𝕜] E')
  证明: by
  classical simp_rw [orthonormal_iff_ite, Function.comp_apply, LinearIsometry.inner_map_map]

Depends on / 依赖: Function, Function.comp_apply, LinearIsometry, LinearIsometry.inner_map_map, classical, comp_apply, inner_map_map, orthonormal_iff_ite, simp_rw
-/
theorem LinearIsometry.orthonormal_comp_iff {v : ι -> E} (f : E ->ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v := by
  classical simp_rw [orthonormal_iff_ite, Function.comp_apply, LinearIsometry.inner_map_map]

/--
theorem `Orthonormal.comp_linearIsometry` / 定理 `Orthonormal.comp_linearIsometry`

English:
theorem Orthonormal.comp_linearIsometry
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ->ₗᵢ[𝕜] E')
  proof: by rwa [f.orthonormal_comp_iff]

中文:
定理 Orthonormal.comp_linearIsometry
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ->ₗᵢ[𝕜] E')
  证明: by rwa [f.orthonormal_comp_iff]

Depends on / 依赖: f.orthonormal_comp_iff, orthonormal_comp_iff
-/
theorem Orthonormal.comp_linearIsometry {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ->ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) := by rwa [f.orthonormal_comp_iff]

/--
theorem `Orthonormal.comp_linearIsometryEquiv` / 定理 `Orthonormal.comp_linearIsometryEquiv`

English:
theorem Orthonormal.comp_linearIsometryEquiv
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E')
  proof: hv.comp_linearIsometry f.toLinearIsometry

中文:
定理 Orthonormal.comp_linearIsometryEquiv
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E')
  证明: hv.comp_linearIsometry f.toLinearIsometry

Depends on / 依赖: comp_linearIsometry, f.toLinearIsometry, hv.comp_linearIsometry, toLinearIsometry
-/
theorem Orthonormal.comp_linearIsometryEquiv {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) :=
  hv.comp_linearIsometry f.toLinearIsometry

/--
theorem `Orthonormal.mapLinearIsometryEquiv` / 定理 `Orthonormal.mapLinearIsometryEquiv`

English:
theorem Orthonormal.mapLinearIsometryEquiv
  statement: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  proof: hv.comp_linearIsometryEquiv f

中文:
定理 Orthonormal.mapLinearIsometryEquiv
  结论: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  证明: hv.comp_linearIsometryEquiv f

Depends on / 依赖: comp_linearIsometryEquiv, hv.comp_linearIsometryEquiv
-/
theorem Orthonormal.mapLinearIsometryEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (v.map f.toLinearEquiv) :=
  hv.comp_linearIsometryEquiv f

/--
Definition of `LinearMap.isometryOfOrthonormal` / `LinearMap.isometryOfOrthonormal` 的定义

English:
definition LinearMap.isometryOfOrthonormal
  signature: (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  body: f.isometryOfInner fun x y => by
    rw [← v.linearCombination_repr x]; rw [← v.linearCombination_repr y]; rw [Finsupp.apply_linearCombination]; rw [Finsupp.apply_linearCombination]; rw [hv.inner_finsupp_eq_sum_left]; rw [hf.inner_finsupp_eq_sum_left]

@[simp]

中文:
定义 LinearMap.isometryOfOrthonormal
  签名: (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  定义体: f.isometryOfInner fun x y => by
    rw [← v.linearCombination_repr x]; rw [← v.linearCombination_repr y]; rw [Finsupp.apply_linearCombination]; rw [Finsupp.apply_linearCombination]; rw [hv.inner_finsupp_eq_sum_left]; rw [hf.inner_finsupp_eq_sum_left]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.apply_linearCombination, apply_linearCombination, f.isometryOfInner, hf.inner_finsupp_eq_sum_left, hv.inner_finsupp_eq_sum_left, inner_finsupp_eq_sum_left, isometryOfInner, linearCombination_repr, v.linearCombination_repr
-/
def LinearMap.isometryOfOrthonormal (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ->ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← v.linearCombination_repr x]; rw [← v.linearCombination_repr y]; rw [Finsupp.apply_linearCombination]; rw [Finsupp.apply_linearCombination]; rw [hv.inner_finsupp_eq_sum_left]; rw [hf.inner_finsupp_eq_sum_left]

@[simp]
/--
theorem `LinearMap.coe_isometryOfOrthonormal` / 定理 `LinearMap.coe_isometryOfOrthonormal`

English:
theorem LinearMap.coe_isometryOfOrthonormal
  statement: (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  proof: rfl

@[simp]

中文:
定理 LinearMap.coe_isometryOfOrthonormal
  结论: (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  证明: rfl

@[simp]
-/
theorem LinearMap.coe_isometryOfOrthonormal (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
/--
theorem `LinearMap.isometryOfOrthonormal_toLinearMap` / 定理 `LinearMap.isometryOfOrthonormal_toLinearMap`

English:
theorem LinearMap.isometryOfOrthonormal_toLinearMap
  statement: (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  proof: rfl

中文:
定理 LinearMap.isometryOfOrthonormal_toLinearMap
  结论: (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  证明: rfl
-/
theorem LinearMap.isometryOfOrthonormal_toLinearMap (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearMap = f :=
  rfl

/--
Definition of `LinearEquiv.isometryOfOrthonormal` / `LinearEquiv.isometryOfOrthonormal` 的定义

English:
definition LinearEquiv.isometryOfOrthonormal
  signature: (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  body: f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.linearCombination_repr x]; rw [← v.linearCombination_repr y]; rw [← LinearEquiv.coe_coe f]; rw [Finsupp.apply_linearCombination]; rw [Finsupp.apply_linearCombination]; rw [hv.inner_finsupp_eq_sum_left]; rw [hf.inner_fin

中文:
定义 LinearEquiv.isometryOfOrthonormal
  签名: (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  定义体: f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.linearCombination_repr x]; rw [← v.linearCombination_repr y]; rw [← LinearEquiv.coe_coe f]; rw [Finsupp.apply_linearCombination]; rw [Finsupp.apply_linearCombination]; rw [hv.inner_finsupp_eq_sum_left]; rw [hf.inner_fin

Depends on / 依赖: Finsupp, Finsupp.apply_linearCombination, LinearEquiv, LinearEquiv.coe_coe, apply_linearCombination, coe_coe, f.isometryOfInner, hf.inner_finsupp_eq_sum_left, hv.inner_finsupp_eq_sum_left, inner_finsupp_eq_sum_left, isometryOfInner, linearCombination_repr, v.linearCombination_repr
-/
def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.linearCombination_repr x]; rw [← v.linearCombination_repr y]; rw [← LinearEquiv.coe_coe f]; rw [Finsupp.apply_linearCombination]; rw [Finsupp.apply_linearCombination]; rw [hv.inner_finsupp_eq_sum_left]; rw [hf.inner_finsupp_eq_sum_left]

@[simp]
/--
theorem `LinearEquiv.coe_isometryOfOrthonormal` / 定理 `LinearEquiv.coe_isometryOfOrthonormal`

English:
theorem LinearEquiv.coe_isometryOfOrthonormal
  statement: (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  proof: rfl

@[simp]

中文:
定理 LinearEquiv.coe_isometryOfOrthonormal
  结论: (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  证明: rfl

@[simp]
-/
theorem LinearEquiv.coe_isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
/--
theorem `LinearEquiv.isometryOfOrthonormal_toLinearEquiv` / 定理 `LinearEquiv.isometryOfOrthonormal_toLinearEquiv`

English:
theorem LinearEquiv.isometryOfOrthonormal_toLinearEquiv
  statement: (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  proof: rfl

中文:
定理 LinearEquiv.isometryOfOrthonormal_toLinearEquiv
  结论: (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
  证明: rfl
-/
theorem LinearEquiv.isometryOfOrthonormal_toLinearEquiv (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearEquiv = f :=
  rfl

/--
Definition of `Orthonormal.equiv` / `Orthonormal.equiv` 的定义

English:
definition Orthonormal.equiv
  signature: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  body: (v.equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      exact hv'.comp _ e.injective)

@[simp]

中文:
定义 Orthonormal.equiv
  签名: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  定义体: (v.equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      exact hv'.comp _ e.injective)

@[simp]

Depends on / 依赖: e.injective, injective, isometryOfOrthonormal, v.equiv
-/
def Orthonormal.equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E' :=
  (v.equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      exact hv'.comp _ e.injective)

@[simp]
/--
theorem `Orthonormal.equiv_toLinearEquiv` / 定理 `Orthonormal.equiv_toLinearEquiv`

English:
theorem Orthonormal.equiv_toLinearEquiv
  statement: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  proof: rfl

@[simp]

中文:
定理 Orthonormal.equiv_toLinearEquiv
  结论: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  证明: rfl

@[simp]
-/
theorem Orthonormal.equiv_toLinearEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    (hv.equiv hv' e).toLinearEquiv = v.equiv v' e :=
  rfl

@[simp]
/--
theorem `Orthonormal.equiv_apply` / 定理 `Orthonormal.equiv_apply`

English:
theorem Orthonormal.equiv_apply
  statement: {ι' : Type*} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  proof: Basis.equiv_apply _ _ _ _

@[simp]

中文:
定理 Orthonormal.equiv_apply
  结论: {ι' : 类型} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  证明: Basis.equiv_apply _ _ _ _

@[simp]

Depends on / 依赖: Basis.equiv_apply, equiv_apply
-/
theorem Orthonormal.equiv_apply {ι' : Type*} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) :
    hv.equiv hv' e (v i) = v' (e i) :=
  Basis.equiv_apply _ _ _ _

@[simp]
/--
theorem `Orthonormal.equiv_trans` / 定理 `Orthonormal.equiv_trans`

English:
theorem Orthonormal.equiv_trans
  statement: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  proof: v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans,
      Function.comp_apply]

中文:
定理 Orthonormal.equiv_trans
  结论: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  证明: v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans,
      Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearIsometryEquiv, LinearIsometryEquiv.trans_apply, Orthonormal, Orthonormal.equiv_apply, coe_trans, comp_apply, e.coe_trans, equiv_apply, ext_linearIsometryEquiv, trans_apply, v.ext_linearIsometryEquiv
-/
theorem Orthonormal.equiv_trans {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') {v'' : Basis ι'' 𝕜 E''} (hv'' : Orthonormal 𝕜 v'')
    (e' : ι' ≃ ι'') : (hv.equiv hv' e).trans (hv'.equiv hv'' e') = hv.equiv hv'' (e.trans e') :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans,
      Function.comp_apply]

/--
theorem `Orthonormal.map_equiv` / 定理 `Orthonormal.map_equiv`

English:
theorem Orthonormal.map_equiv
  statement: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  proof: v.map_equiv _ _

中文:
定理 Orthonormal.map_equiv
  结论: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  证明: v.map_equiv _ _

Depends on / 依赖: map_equiv, v.map_equiv
-/
theorem Orthonormal.map_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    v.map (hv.equiv hv' e).toLinearEquiv = v'.reindex e.symm :=
  v.map_equiv _ _

end

section

variable {ι : Type*} {ι' : Type*} {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

@[simp]
/--
theorem `Orthonormal.equiv_refl` / 定理 `Orthonormal.equiv_refl`

English:
theorem Orthonormal.equiv_refl
  given: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  proof: v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id, LinearIsometryEquiv.coe_refl]

@[simp]

中文:
定理 Orthonormal.equiv_refl
  条件: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
  证明: v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id, LinearIsometryEquiv.coe_refl]

@[simp]

Depends on / 依赖: Equiv.coe_refl, LinearIsometryEquiv, LinearIsometryEquiv.coe_refl, Orthonormal, Orthonormal.equiv_apply, coe_refl, equiv_apply, ext_linearIsometryEquiv, v.ext_linearIsometryEquiv
-/
theorem Orthonormal.equiv_refl {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) :
    hv.equiv hv (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id, LinearIsometryEquiv.coe_refl]

@[simp]
/--
theorem `Orthonormal.equiv_symm` / 定理 `Orthonormal.equiv_symm`

English:
theorem Orthonormal.equiv_symm
  statement: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  proof: v'.ext_linearIsometryEquiv fun i =>
(hv.equiv hv' e).injective by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]

中文:
定理 Orthonormal.equiv_symm
  结论: {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
  证明: v'.ext_linearIsometryEquiv fun i =>
(hv.equiv hv' e).injective by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.apply_symm_apply, Orthonormal, Orthonormal.equiv_apply, apply_symm_apply, e.apply_symm_apply, equiv_apply, ext_linearIsometryEquiv, hv.equiv, injective
-/
theorem Orthonormal.equiv_symm {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.equiv hv' e).symm = hv'.equiv hv e.symm :=
  v'.ext_linearIsometryEquiv fun i =>
(hv.equiv hv' e).injective by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]

end

end Norm_Seminormed

section BesselsInequality

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {ι : Type*} (x : E) {v : ι -> E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `Orthonormal.sum_inner_products_le` / 定理 `Orthonormal.sum_inner_products_le`

English:
theorem Orthonormal.sum_inner_products_le
  given: {s : Finset ι} (hv : Orthonormal 𝕜 v)
  proof: by
  have h₂ :
    (∑ i in s, ∑ j in s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k in s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) := by
    exact hv.inner_left_right_finset
  have h₃ : forall z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj]
    norm_cast
  suffices hbf : ‖x - ∑ i in s, ⟪v i

中文:
定理 Orthonormal.sum_inner_products_le
  条件: {s : Finset ι} (hv : Orthonormal 𝕜 v)
  证明: by
  have h₂ :
    (∑ i in s, ∑ j in s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k in s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) := by
    exact hv.inner_left_right_finset
  have h₃ : forall z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj]
    norm_cast
  suffices hbf : ‖x - ∑ i in s, ⟪v i

Depends on / 依赖: InnerProductSpace, InnerProductSpace.norm_sq_eq_re_inner, hv.inner_left_right_finset, inner_left_right_finset, inner_sum, mul_conj, norm_nonneg, norm_sq_eq_re_inner, norm_sub_sq, pow_nonneg, sub_add, sub_nonneg, sum_
-/
theorem Orthonormal.sum_inner_products_le {s : Finset ι} (hv : Orthonormal 𝕜 v) :
    ∑ i in s, ‖⟪v i, x⟫‖ ^ 2 <= ‖x‖ ^ 2 := by
  have h₂ :
    (∑ i in s, ∑ j in s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k in s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) := by
    exact hv.inner_left_right_finset
  have h₃ : forall z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj]
    norm_cast
  suffices hbf : ‖x - ∑ i in s, ⟪v i, x⟫ • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i in s, ‖⟪v i, x⟫‖ ^ 2 by
    rw [← sub_nonneg]; rw [← hbf]
    simp only [norm_nonneg, pow_nonneg]
  rw [@norm_sub_sq 𝕜]; rw [sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

/--
theorem `Orthonormal.tsum_inner_products_le` / 定理 `Orthonormal.tsum_inner_products_le`

English:
theorem Orthonormal.tsum_inner_products_le
  given: (hv : Orthonormal 𝕜 v)
  proof: by
  refine tsum_le_of_sum_le' ?_ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]

中文:
定理 Orthonormal.tsum_inner_products_le
  条件: (hv : Orthonormal 𝕜 v)
  证明: by
  refine tsum_le_of_sum_le' ?_ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]

Depends on / 依赖: hv.sum_inner_products_le, norm_nonneg, pow_nonneg, sum_inner_products_le, tsum_le_of_sum_le
-/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) :
    ∑' i, ‖⟪v i, x⟫‖ ^ 2 <= ‖x‖ ^ 2 := by
  refine tsum_le_of_sum_le' ?_ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]

/--
theorem `Orthonormal.inner_products_summable` / 定理 `Orthonormal.inner_products_summable`

English:
theorem Orthonormal.inner_products_summable
  given: (hv : Orthonormal 𝕜 v)
  proof: by
  use ⨆ s : Finset ι, ∑ i in s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine isLUB_ciSup ?_
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x

中文:
定理 Orthonormal.inner_products_summable
  条件: (hv : Orthonormal 𝕜 v)
  证明: by
  use ⨆ s : Finset ι, ∑ i in s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine isLUB_ciSup ?_
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x

Depends on / 依赖: Finset, hasSum_of_isLUB_of_nonneg, hv.sum_inner_products_le, isLUB_ciSup, norm_nonneg, pow_nonneg, sum_inner_products_le
-/
theorem Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) :
    Summable fun i => ‖⟪v i, x⟫‖ ^ 2 := by
  use ⨆ s : Finset ι, ∑ i in s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine isLUB_ciSup ?_
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x

end BesselsInequality
