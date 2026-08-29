/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Doubly stochastic matrices

## Main definitions

* `doublyStochastic`: a square matrix is doubly stochastic if all entries are nonnegative, and left
  or right multiplication by the vector of all 1s gives the vector of all 1s. Equivalently, all
  row and column sums are equal to 1.

## Main statements

* `convex_doublyStochastic`: The set of doubly stochastic matrices is convex.
* `permMatrix_mem_doublyStochastic`: Any permutation matrix is doubly stochastic.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

@[expose] public section

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

/--
Definition of `doublyStochastic` / `doublyStochastic` 的定义

English:
definition doublyStochastic
  signature: (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
  body: {M | (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]

中文:
定义 doublyStochastic
  签名: (R n : 类型) [有限类型 n] [DecidableEq n] [半环 R] [偏序 R]
  定义体: {M | (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]
-/
def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]

/--
lemma `mem_doublyStochastic` / 引理 `mem_doublyStochastic`

English:
lemma mem_doublyStochastic
  proof: Iff.rfl

中文:
引理 mem_doublyStochastic
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_doublyStochastic :
    M in doublyStochastic R n ↔ (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 :=
  Iff.rfl

/--
lemma `mem_doublyStochastic_iff_sum` / 引理 `mem_doublyStochastic_iff_sum`

English:
lemma mem_doublyStochastic_iff_sum
  proof: by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]

中文:
引理 mem_doublyStochastic_iff_sum
  证明: by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]

Depends on / 依赖: dotProduct, doublyStochastic, funext_iff, mulVec, vecMul
-/
lemma mem_doublyStochastic_iff_sum :
    M in doublyStochastic R n ↔
      (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1) ∧ forall j, ∑ i, M i j = 1 := by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]

/-- A matrix is doubly stochastic if and only if it is both row and
column stochastic. -/
@[local grind =]
/--
lemma `doublyStochastic_eq_rowStochastic_inf_colStochastic` / 引理 `doublyStochastic_eq_rowStochastic_inf_colStochastic`

English:
lemma doublyStochastic_eq_rowStochastic_inf_colStochastic
  proof: by
  ext M
  simp only [rowStochastic, colStochastic, Submonoid.mem_inf, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, doublyStochastic]
  grind

中文:
引理 doublyStochastic_eq_rowStochastic_inf_colStochastic
  证明: by
  ext M
  simp only [rowStochastic, colStochastic, Submonoid.mem_inf, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, doublyStochastic]
  grind

Depends on / 依赖: Set.mem_ofPred_eq, Submonoid, Submonoid.mem_inf, Submonoid.mem_mk, Subsemigroup, Subsemigroup.mem_mk, colStochastic, doublyStochastic, mem_inf, mem_mk, mem_ofPred_eq, rowStochastic
-/
lemma doublyStochastic_eq_rowStochastic_inf_colStochastic :
    doublyStochastic R n = rowStochastic R n ⊓ colStochastic R n := by
  ext M
  simp only [rowStochastic, colStochastic, Submonoid.mem_inf, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, doublyStochastic]
  grind

/--
lemma `mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic` / 引理 `mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic`

English:
lemma mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic
  given: {M : Matrix n n R}
  proof: by
  rw [doublyStochastic_eq_rowStochastic_inf_colStochastic]; rw [Submonoid.mem_inf]

中文:
引理 mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic
  条件: {M : 矩阵 n n R}
  证明: by
  rw [doublyStochastic_eq_rowStochastic_inf_colStochastic]; rw [Submonoid.mem_inf]

Depends on / 依赖: Submonoid, Submonoid.mem_inf, doublyStochastic_eq_rowStochastic_inf_colStochastic, mem_inf
-/
lemma mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic {M : Matrix n n R} :
    M in doublyStochastic R n ↔ M in rowStochastic R n ∧ M in colStochastic R n := by
  rw [doublyStochastic_eq_rowStochastic_inf_colStochastic]; rw [Submonoid.mem_inf]

/--
lemma `nonneg_of_mem_doublyStochastic` / 引理 `nonneg_of_mem_doublyStochastic`

English:
lemma nonneg_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n) {i j : n}
  statement: 0 <= M i j
  proof: hM.1 _ _

中文:
引理 nonneg_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n) {i j : n}
  结论: 0 <= M i j
  证明: hM.1 _ _
-/
lemma nonneg_of_mem_doublyStochastic (hM : M in doublyStochastic R n) {i j : n} : 0 <= M i j :=
  hM.1 _ _

/--
lemma `sum_row_of_mem_doublyStochastic` / 引理 `sum_row_of_mem_doublyStochastic`

English:
lemma sum_row_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n) (i : n)
  statement: ∑ j, M i j = 1
  proof: (mem_doublyStochastic_iff_sum.1 hM).2.1 _

中文:
引理 sum_row_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n) (i : n)
  结论: ∑ j, M i j = 1
  证明: (mem_doublyStochastic_iff_sum.1 hM).2.1 _

Depends on / 依赖: mem_doublyStochastic_iff_sum
-/
lemma sum_row_of_mem_doublyStochastic (hM : M in doublyStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.1 _

/--
lemma `sum_col_of_mem_doublyStochastic` / 引理 `sum_col_of_mem_doublyStochastic`

English:
lemma sum_col_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n) (j : n)
  statement: ∑ i, M i j = 1
  proof: (mem_doublyStochastic_iff_sum.1 hM).2.2 _

中文:
引理 sum_col_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n) (j : n)
  结论: ∑ i, M i j = 1
  证明: (mem_doublyStochastic_iff_sum.1 hM).2.2 _

Depends on / 依赖: mem_doublyStochastic_iff_sum
-/
lemma sum_col_of_mem_doublyStochastic (hM : M in doublyStochastic R n) (j : n) : ∑ i, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.2 _

/--
lemma `mulVec_one_of_mem_doublyStochastic` / 引理 `mulVec_one_of_mem_doublyStochastic`

English:
lemma mulVec_one_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n)
  statement: M *ᵥ 1 = 1
  proof: (mem_doublyStochastic.1 hM).2.1

中文:
引理 mulVec_one_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n)
  结论: M *ᵥ 1 = 1
  证明: (mem_doublyStochastic.1 hM).2.1

Depends on / 依赖: mem_doublyStochastic
-/
lemma mulVec_one_of_mem_doublyStochastic (hM : M in doublyStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_doublyStochastic.1 hM).2.1

/--
lemma `one_vecMul_of_mem_doublyStochastic` / 引理 `one_vecMul_of_mem_doublyStochastic`

English:
lemma one_vecMul_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n)
  statement: 1 ᵥ* M = 1
  proof: (mem_doublyStochastic.1 hM).2.2

中文:
引理 one_vecMul_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n)
  结论: 1 ᵥ* M = 1
  证明: (mem_doublyStochastic.1 hM).2.2

Depends on / 依赖: mem_doublyStochastic
-/
lemma one_vecMul_of_mem_doublyStochastic (hM : M in doublyStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_doublyStochastic.1 hM).2.2

/--
lemma `le_one_of_mem_doublyStochastic` / 引理 `le_one_of_mem_doublyStochastic`

English:
lemma le_one_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n) {i j : n}
  proof: by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

中文:
引理 le_one_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n) {i j : n}
  证明: by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

Depends on / 依赖: mem_univ, single_le_sum, sum_row_of_mem_doublyStochastic
-/
lemma le_one_of_mem_doublyStochastic (hM : M in doublyStochastic R n) {i j : n} :
    M i j <= 1 := by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

/--
lemma `convex_doublyStochastic` / 引理 `convex_doublyStochastic`

English:
lemma convex_doublyStochastic
  statement: Convex R (doublyStochastic R n : Set (Matrix n n R))
  proof: by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

中文:
引理 convex_doublyStochastic
  结论: 凸 R (doublyStochastic R n : 集合 (矩阵 n n R))
  证明: by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

Depends on / 依赖: SetLike, SetLike.mem_coe, add_nonneg, mem_coe, mem_doublyStochastic_iff_sum, mul_nonneg, mul_sum, sum_add_distrib
-/
lemma convex_doublyStochastic : Convex R (doublyStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is doubly stochastic. -/
@[simp, grind ←]
/--
lemma `permMatrix_mem_doublyStochastic` / 引理 `permMatrix_mem_doublyStochastic`

English:
lemma permMatrix_mem_doublyStochastic
  given: {σ : Equiv.Perm n}
  proof: by grind

中文:
引理 permMatrix_mem_doublyStochastic
  条件: {σ : 等价.置换 n}
  证明: by grind
-/
lemma permMatrix_mem_doublyStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R in doublyStochastic R n := by grind

/-- A matrix is doubly stochastic iff its transpose is doubly stochastic -/
@[grind =]
/--
lemma `transpose_mem_doublyStochastic_iff` / 引理 `transpose_mem_doublyStochastic_iff`

English:
lemma transpose_mem_doublyStochastic_iff
  proof: by grind

中文:
引理 transpose_mem_doublyStochastic_iff
  证明: by grind
-/
lemma transpose_mem_doublyStochastic_iff :
    Mᵀ in doublyStochastic R n ↔ M in doublyStochastic R n := by grind

/-- Reindexing a matrix preserves double stochasticity. -/
@[aesop safe apply]
/--
lemma `reindex_mem_doublyStochastic` / 引理 `reindex_mem_doublyStochastic`

English:
lemma reindex_mem_doublyStochastic
  statement: {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
  proof: by
  grind

中文:
引理 reindex_mem_doublyStochastic
  结论: {m : 类型} [有限类型 m] [DecidableEq m] {M : 矩阵 n n R}
  证明: by
  grind
-/
lemma reindex_mem_doublyStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M in doublyStochastic R n) : M.reindex e₁ e₂ in doublyStochastic R m := by
  grind

/-- Reindexing a matrix preserves double stochasticity. -/
@[grind =]
/--
lemma `reindex_mem_doublyStochastic_iff` / 引理 `reindex_mem_doublyStochastic_iff`

English:
lemma reindex_mem_doublyStochastic_iff
  statement: {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
  proof: by
  grind

中文:
引理 reindex_mem_doublyStochastic_iff
  结论: {m : 类型} [有限类型 m] [DecidableEq m] {M : 矩阵 n n R}
  证明: by
  grind
-/
lemma reindex_mem_doublyStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ in doublyStochastic R m ↔ M in doublyStochastic R n := by
  grind

/--
lemma `sum_mulVec_of_mem_doublyStochastic` / 引理 `sum_mulVec_of_mem_doublyStochastic`

English:
lemma sum_mulVec_of_mem_doublyStochastic
  statement: {M : Matrix n n R} {x : n -> R}
  proof: by
  apply sum_mulVec_of_mem_colStochastic
  grind

中文:
引理 sum_mulVec_of_mem_doublyStochastic
  结论: {M : 矩阵 n n R} {x : n -> R}
  证明: by
  apply sum_mulVec_of_mem_colStochastic
  grind

Depends on / 依赖: sum_mulVec_of_mem_colStochastic
-/
lemma sum_mulVec_of_mem_doublyStochastic {M : Matrix n n R} {x : n -> R}
    (hA : M in doublyStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  apply sum_mulVec_of_mem_colStochastic
  grind

end OrderedSemiring

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]

/--
lemma `exists_mem_doublyStochastic_eq_smul_iff` / 引理 `exists_mem_doublyStochastic_eq_smul_iff`

English:
lemma exists_mem_doublyStochastic_eq_smul_iff
  given: {M : Matrix n n R} {s : R} (hs : 0 <= s)
  proof: by
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', *]⟩

中文:
引理 存在_mem_doublyStochastic_eq_smul_iff
  条件: {M : 矩阵 n n R} {s : R} (hs : 0 <= s)
  证明: by
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', *]⟩

Depends on / 依赖: Matrix, Matrix.smul_apply, Submonoid, Submonoid.one_mem, and_imp, eq_or_lt_of_le, exists_and_right, mem_doublyStochastic_iff_sum, mul_nonneg, mul_sum, one_mem, smul_apply, smul_eq_mul, specialize, sum_eq_zero_iff_of_nonneg, zero_smul
-/
lemma exists_mem_doublyStochastic_eq_smul_iff {M : Matrix n n R} {s : R} (hs : 0 <= s) :
    (exists M' in doublyStochastic R n, M = s • M') ↔
      (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = s) ∧ (forall j, ∑ i, M i j = s) := by
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', *]⟩

end LinearOrderedSemifield
