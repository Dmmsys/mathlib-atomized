/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Row- and Column-stochastic matrices

A square matrix `M` is *row-stochastic* if all its entries are non-negative and `M *ᵥ 1 = 1`.
Likewise, `M` is *column-stochastic* if all its entries are non-negative and `1 ᵥ* M = 1`. This
file defines these concepts and provides basic API for them.

Note that *doubly stochastic* matrices (i.e. matrices that are both row- and column-stochastic)
are defined in `Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`.

## Main definitions

* `rowStochastic`: row-stochastic matrices indexed by `n` with entries in `R`, as a submonoid
  of `Matrix n n R`.
* `colStochastic R n`: column-stochastic matrices indexed by `n` with entries in `R`, as a
  submonoid of `Matrix n n R`.

-/

@[expose] public section

open Finset

namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}
variable {x : n -> R}

/- ## Row-stochastic matrices -/

/--
Definition of `rowStochastic` / `rowStochastic` 的定义

English:
definition rowStochastic
  signature: (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
  body: {M | (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    rw [← mulVec_mulVec]; rw [hN.2]; rw [hM.2]
  one_mem' := by
    simp [zero_le_one_elem]

中文:
定义 rowStochastic
  签名: (R n : 类型) [有限类型 n] [DecidableEq n] [半环 R] [偏序 R]
  定义体: {M | (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    rw [← mulVec_mulVec]; rw [hN.2]; rw [hM.2]
  one_mem' := by
    simp [zero_le_one_elem]
-/
def rowStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    rw [← mulVec_mulVec]; rw [hN.2]; rw [hM.2]
  one_mem' := by
    simp [zero_le_one_elem]

/--
lemma `mem_rowStochastic` / 引理 `mem_rowStochastic`

English:
lemma mem_rowStochastic
  proof: Iff.rfl

中文:
引理 mem_rowStochastic
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_rowStochastic :
    M in rowStochastic R n ↔ (forall i j, 0 <= M i j) ∧ M *ᵥ 1 = 1 :=
  Iff.rfl

/--
lemma `mem_rowStochastic_iff_sum` / 引理 `mem_rowStochastic_iff_sum`

English:
lemma mem_rowStochastic_iff_sum
  proof: by
  simp [funext_iff, rowStochastic, mulVec, dotProduct]

中文:
引理 mem_rowStochastic_iff_sum
  证明: by
  simp [funext_iff, rowStochastic, mulVec, dotProduct]

Depends on / 依赖: dotProduct, funext_iff, mulVec, rowStochastic
-/
lemma mem_rowStochastic_iff_sum :
    M in rowStochastic R n ↔ (forall i j, 0 <= M i j) ∧ (forall i, ∑ j, M i j = 1) := by
  simp [funext_iff, rowStochastic, mulVec, dotProduct]

/--
lemma `nonneg_of_mem_rowStochastic` / 引理 `nonneg_of_mem_rowStochastic`

English:
lemma nonneg_of_mem_rowStochastic
  given: (hM : M in rowStochastic R n) {i j : n}
  statement: 0 <= M i j
  proof: hM.1 _ _

中文:
引理 nonneg_of_mem_rowStochastic
  条件: (hM : M in rowStochastic R n) {i j : n}
  结论: 0 <= M i j
  证明: hM.1 _ _
-/
lemma nonneg_of_mem_rowStochastic (hM : M in rowStochastic R n) {i j : n} : 0 <= M i j :=
  hM.1 _ _

/--
lemma `sum_row_of_mem_rowStochastic` / 引理 `sum_row_of_mem_rowStochastic`

English:
lemma sum_row_of_mem_rowStochastic
  given: (hM : M in rowStochastic R n) (i : n)
  statement: ∑ j, M i j = 1
  proof: (mem_rowStochastic_iff_sum.1 hM).2 _

中文:
引理 sum_row_of_mem_rowStochastic
  条件: (hM : M in rowStochastic R n) (i : n)
  结论: ∑ j, M i j = 1
  证明: (mem_rowStochastic_iff_sum.1 hM).2 _

Depends on / 依赖: mem_rowStochastic_iff_sum
-/
lemma sum_row_of_mem_rowStochastic (hM : M in rowStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_rowStochastic_iff_sum.1 hM).2 _

/--
lemma `one_vecMul_of_mem_rowStochastic` / 引理 `one_vecMul_of_mem_rowStochastic`

English:
lemma one_vecMul_of_mem_rowStochastic
  given: (hM : M in rowStochastic R n)
  statement: M *ᵥ 1 = 1
  proof: (mem_rowStochastic.1 hM).2

中文:
引理 one_vecMul_of_mem_rowStochastic
  条件: (hM : M in rowStochastic R n)
  结论: M *ᵥ 1 = 1
  证明: (mem_rowStochastic.1 hM).2

Depends on / 依赖: mem_rowStochastic
-/
lemma one_vecMul_of_mem_rowStochastic (hM : M in rowStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_rowStochastic.1 hM).2

/--
lemma `le_one_of_mem_rowStochastic` / 引理 `le_one_of_mem_rowStochastic`

English:
lemma le_one_of_mem_rowStochastic
  given: (hM : M in rowStochastic R n) {i j : n}
  proof: by
  rw [← sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

中文:
引理 le_one_of_mem_rowStochastic
  条件: (hM : M in rowStochastic R n) {i j : n}
  证明: by
  rw [← sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

Depends on / 依赖: mem_univ, single_le_sum, sum_row_of_mem_rowStochastic
-/
lemma le_one_of_mem_rowStochastic (hM : M in rowStochastic R n) {i j : n} :
    M i j <= 1 := by
  rw [← sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

/--
lemma `nonneg_vecMul_of_mem_rowStochastic` / 引理 `nonneg_vecMul_of_mem_rowStochastic`

English:
lemma nonneg_vecMul_of_mem_rowStochastic
  statement: (hM : M in rowStochastic R n)
  proof: by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

中文:
引理 nonneg_vecMul_of_mem_rowStochastic
  结论: (hM : M in rowStochastic R n)
  证明: by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

Depends on / 依赖: Finset, Finset.sum_nonneg, Matrix, Matrix.vecMul, dotProduct, mul_nonneg, nonneg_of_mem_rowStochastic, sum_nonneg, vecMul
-/
lemma nonneg_vecMul_of_mem_rowStochastic (hM : M in rowStochastic R n)
    (hx : forall i : n, 0 <= x i) : forall j : n, 0 <= (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

/--
lemma `nonneg_mulVec_of_mem_rowStochastic` / 引理 `nonneg_mulVec_of_mem_rowStochastic`

English:
lemma nonneg_mulVec_of_mem_rowStochastic
  statement: (hM : M in rowStochastic R n)
  proof: by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

中文:
引理 nonneg_mulVec_of_mem_rowStochastic
  结论: (hM : M in rowStochastic R n)
  证明: by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

Depends on / 依赖: Finset, Finset.sum_nonneg, Left.mul_nonneg, Matrix, Matrix.mulVec, dotProduct, mulVec, mul_nonneg, nonneg_of_mem_rowStochastic, sum_nonneg
-/
lemma nonneg_mulVec_of_mem_rowStochastic (hM : M in rowStochastic R n)
    (hx : forall i : n, 0 <= x i) : forall j : n, 0 <= (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

/--
lemma `vecMul_dotProduct_one_eq_one_rowStochastic` / 引理 `vecMul_dotProduct_one_eq_one_rowStochastic`

English:
lemma vecMul_dotProduct_one_eq_one_rowStochastic
  statement: (hM : M in rowStochastic R n)
  proof: by
  rw [← dotProduct_mulVec]; rw [hM.2]; rw [hx]

中文:
引理 vecMul_dotProduct_one_eq_one_rowStochastic
  结论: (hM : M in rowStochastic R n)
  证明: by
  rw [← dotProduct_mulVec]; rw [hM.2]; rw [hx]

Depends on / 依赖: dotProduct_mulVec
-/
lemma vecMul_dotProduct_one_eq_one_rowStochastic (hM : M in rowStochastic R n)
    (hx : x ⬝ᵥ 1 = 1) : (x ᵥ* M) ⬝ᵥ 1 = 1 := by
  rw [← dotProduct_mulVec]; rw [hM.2]; rw [hx]

/--
lemma `convex_rowStochastic` / 引理 `convex_rowStochastic`

English:
lemma convex_rowStochastic
  statement: Convex R (rowStochastic R n : Set (Matrix n n R))
  proof: by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_rowStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

中文:
引理 convex_rowStochastic
  结论: 凸 R (rowStochastic R n : 集合 (矩阵 n n R))
  证明: by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_rowStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

Depends on / 依赖: SetLike, SetLike.mem_coe, add_nonneg, mem_coe, mem_rowStochastic_iff_sum, mul_nonneg, mul_sum, sum_add_distrib
-/
lemma convex_rowStochastic : Convex R (rowStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_rowStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is row stochastic. -/
@[simp, grind ←]
/--
lemma `permMatrix_mem_rowStochastic` / 引理 `permMatrix_mem_rowStochastic`

English:
lemma permMatrix_mem_rowStochastic
  given: {σ : Equiv.Perm n}
  proof: by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]

中文:
引理 permMatrix_mem_rowStochastic
  条件: {σ : 等价.置换 n}
  证明: by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]

Depends on / 依赖: Equiv.toPEquiv_apply, mem_rowStochastic_iff_sum, toPEquiv_apply
-/
lemma permMatrix_mem_rowStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R in rowStochastic R n := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]


/- ## Column-stochastic matrices -/

/--
Definition of `colStochastic` / `colStochastic` 的定义

English:
definition colStochastic
  signature: (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
  body: {M | (forall i j, 0 <= M i j) ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine Set.mem_sep ?_ ?_
    · intro i j
      apply Finset.sum_nonneg
      grind [mul_nonneg]
    · rw [← vecMul_vecMul, hM.2, hN.2]
  one_mem' := by
    simp [zero_le_one_elem]

中文:
定义 colStochastic
  签名: (R n : 类型) [有限类型 n] [DecidableEq n] [半环 R] [偏序 R]
  定义体: {M | (forall i j, 0 <= M i j) ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine Set.mem_sep ?_ ?_
    · intro i j
      apply Finset.sum_nonneg
      grind [mul_nonneg]
    · rw [← vecMul_vecMul, hM.2, hN.2]
  one_mem' := by
    simp [zero_le_one_elem]
-/
def colStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (forall i j, 0 <= M i j) ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine Set.mem_sep ?_ ?_
    · intro i j
      apply Finset.sum_nonneg
      grind [mul_nonneg]
    · rw [← vecMul_vecMul, hM.2, hN.2]
  one_mem' := by
    simp [zero_le_one_elem]

/--
lemma `mem_colStochastic` / 引理 `mem_colStochastic`

English:
lemma mem_colStochastic
  proof: Iff.rfl

中文:
引理 mem_colStochastic
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_colStochastic :
    M in colStochastic R n ↔ (forall i j, 0 <= M i j) ∧ 1 ᵥ* M = 1 :=
  Iff.rfl

/--
lemma `mem_colStochastic_iff_sum` / 引理 `mem_colStochastic_iff_sum`

English:
lemma mem_colStochastic_iff_sum
  proof: by
  simp [funext_iff, colStochastic, vecMul, dotProduct]

中文:
引理 mem_colStochastic_iff_sum
  证明: by
  simp [funext_iff, colStochastic, vecMul, dotProduct]

Depends on / 依赖: colStochastic, dotProduct, funext_iff, vecMul
-/
lemma mem_colStochastic_iff_sum :
    M in colStochastic R n ↔
      (forall i j, 0 <= M i j) ∧ (forall j, ∑ i, M i j = 1) := by
  simp [funext_iff, colStochastic, vecMul, dotProduct]

/--
lemma `nonneg_of_mem_colStochastic` / 引理 `nonneg_of_mem_colStochastic`

English:
lemma nonneg_of_mem_colStochastic
  given: (hM : M in colStochastic R n) {i j : n}
  statement: 0 <= M i j
  proof: hM.1 _ _

中文:
引理 nonneg_of_mem_colStochastic
  条件: (hM : M in colStochastic R n) {i j : n}
  结论: 0 <= M i j
  证明: hM.1 _ _
-/
lemma nonneg_of_mem_colStochastic (hM : M in colStochastic R n) {i j : n} : 0 <= M i j :=
  hM.1 _ _

/--
lemma `sum_col_of_mem_colStochastic` / 引理 `sum_col_of_mem_colStochastic`

English:
lemma sum_col_of_mem_colStochastic
  given: (hM : M in colStochastic R n) (i : n)
  statement: ∑ j, M j i = 1
  proof: (mem_colStochastic_iff_sum.1 hM).2 _

中文:
引理 sum_col_of_mem_colStochastic
  条件: (hM : M in colStochastic R n) (i : n)
  结论: ∑ j, M j i = 1
  证明: (mem_colStochastic_iff_sum.1 hM).2 _

Depends on / 依赖: mem_colStochastic_iff_sum
-/
lemma sum_col_of_mem_colStochastic (hM : M in colStochastic R n) (i : n) : ∑ j, M j i = 1 :=
  (mem_colStochastic_iff_sum.1 hM).2 _

/--
lemma `one_vecMul_of_mem_colStochastic` / 引理 `one_vecMul_of_mem_colStochastic`

English:
lemma one_vecMul_of_mem_colStochastic
  given: (hM : M in colStochastic R n)
  statement: 1 ᵥ* M = 1
  proof: (mem_colStochastic.1 hM).2

中文:
引理 one_vecMul_of_mem_colStochastic
  条件: (hM : M in colStochastic R n)
  结论: 1 ᵥ* M = 1
  证明: (mem_colStochastic.1 hM).2

Depends on / 依赖: mem_colStochastic
-/
lemma one_vecMul_of_mem_colStochastic (hM : M in colStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_colStochastic.1 hM).2

/--
lemma `le_one_of_mem_colStochastic` / 引理 `le_one_of_mem_colStochastic`

English:
lemma le_one_of_mem_colStochastic
  given: (hM : M in colStochastic R n) {i j : n}
  proof: by
  rw [← sum_col_of_mem_colStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 k _) (mem_univ j)

中文:
引理 le_one_of_mem_colStochastic
  条件: (hM : M in colStochastic R n) {i j : n}
  证明: by
  rw [← sum_col_of_mem_colStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 k _) (mem_univ j)

Depends on / 依赖: mem_univ, single_le_sum, sum_col_of_mem_colStochastic
-/
lemma le_one_of_mem_colStochastic (hM : M in colStochastic R n) {i j : n} :
    M j i <= 1 := by
  rw [← sum_col_of_mem_colStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 k _) (mem_univ j)

/--
lemma `nonneg_mulVec_of_mem_colStochastic` / 引理 `nonneg_mulVec_of_mem_colStochastic`

English:
lemma nonneg_mulVec_of_mem_colStochastic
  statement: (hM : M in colStochastic R n)
  proof: by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_colStochastic hM

中文:
引理 nonneg_mulVec_of_mem_colStochastic
  结论: (hM : M in colStochastic R n)
  证明: by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_colStochastic hM

Depends on / 依赖: Finset, Finset.sum_nonneg, Left.mul_nonneg, Matrix, Matrix.mulVec, dotProduct, mulVec, mul_nonneg, nonneg_of_mem_colStochastic, sum_nonneg
-/
lemma nonneg_mulVec_of_mem_colStochastic (hM : M in colStochastic R n)
    (hx : forall i : n, 0 <= x i) : forall j : n, 0 <= (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_colStochastic hM

/--
lemma `nonneg_vecMul_of_mem_colStochastic` / 引理 `nonneg_vecMul_of_mem_colStochastic`

English:
lemma nonneg_vecMul_of_mem_colStochastic
  statement: (hM : M in colStochastic R n)
  proof: by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg (hx k) ?_
  exact nonneg_of_mem_colStochastic hM

中文:
引理 nonneg_vecMul_of_mem_colStochastic
  结论: (hM : M in colStochastic R n)
  证明: by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg (hx k) ?_
  exact nonneg_of_mem_colStochastic hM

Depends on / 依赖: Finset, Finset.sum_nonneg, Left.mul_nonneg, Matrix, Matrix.vecMul, dotProduct, mul_nonneg, nonneg_of_mem_colStochastic, sum_nonneg, vecMul
-/
lemma nonneg_vecMul_of_mem_colStochastic (hM : M in colStochastic R n)
    (hx : forall i : n, 0 <= x i) : forall j : n, 0 <= (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg (hx k) ?_
  exact nonneg_of_mem_colStochastic hM

/--
lemma `mulVec_dotProduct_one_eq_one_colStochastic` / 引理 `mulVec_dotProduct_one_eq_one_colStochastic`

English:
lemma mulVec_dotProduct_one_eq_one_colStochastic
  statement: (hM : M in colStochastic R n)
  proof: by
  rw [dotProduct_mulVec]; rw [hM.2]; rw [hx]

中文:
引理 mulVec_dotProduct_one_eq_one_colStochastic
  结论: (hM : M in colStochastic R n)
  证明: by
  rw [dotProduct_mulVec]; rw [hM.2]; rw [hx]

Depends on / 依赖: dotProduct_mulVec
-/
lemma mulVec_dotProduct_one_eq_one_colStochastic (hM : M in colStochastic R n)
    (hx : 1 ⬝ᵥ x = 1) : 1 ⬝ᵥ (M *ᵥ x) = 1 := by
  rw [dotProduct_mulVec]; rw [hM.2]; rw [hx]

/--
lemma `sum_mulVec_of_mem_colStochastic` / 引理 `sum_mulVec_of_mem_colStochastic`

English:
lemma sum_mulVec_of_mem_colStochastic
  statement: {M : Matrix n n R} {x : n -> R}
  proof: by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [sum_col_of_mem_colStochastic hA, ← Finset.sum_mul]

中文:
引理 sum_mulVec_of_mem_colStochastic
  结论: {M : 矩阵 n n R} {x : n -> R}
  证明: by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [sum_col_of_mem_colStochastic hA, ← Finset.sum_mul]

Depends on / 依赖: Finset, Finset.sum_comm, Finset.sum_mul, Matrix, Matrix.mulVec, dotProduct, mulVec, sum_col_of_mem_colStochastic, sum_comm, sum_mul
-/
lemma sum_mulVec_of_mem_colStochastic {M : Matrix n n R} {x : n -> R}
    (hA : M in colStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [sum_col_of_mem_colStochastic hA, ← Finset.sum_mul]

/--
lemma `convex_colStochastic` / 引理 `convex_colStochastic`

English:
lemma convex_colStochastic
  statement: Convex R (colStochastic R n : Set (Matrix n n R))
  proof: by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_colStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

中文:
引理 convex_colStochastic
  结论: 凸 R (colStochastic R n : 集合 (矩阵 n n R))
  证明: by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_colStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

Depends on / 依赖: SetLike, SetLike.mem_coe, add_nonneg, mem_coe, mem_colStochastic_iff_sum, mul_nonneg, mul_sum, sum_add_distrib
-/
lemma convex_colStochastic : Convex R (colStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_colStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is column stochastic. -/
@[simp, grind ←]
/--
lemma `permMatrix_mem_colStochastic` / 引理 `permMatrix_mem_colStochastic`

English:
lemma permMatrix_mem_colStochastic
  given: {σ : Equiv.Perm n}
  proof: by
  rw [mem_colStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply σ]

中文:
引理 permMatrix_mem_colStochastic
  条件: {σ : 等价.置换 n}
  证明: by
  rw [mem_colStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply σ]

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.toPEquiv_apply, eq_symm_apply, mem_colStochastic_iff_sum, toPEquiv_apply
-/
lemma permMatrix_mem_colStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R in colStochastic R n := by
  rw [mem_colStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply σ]

/-- The transpose of a matrix is row stochastic matrix if it is column stochastic. -/
@[grind =]
/--
lemma `transpose_mem_rowStochastic_iff_mem_colStochastic` / 引理 `transpose_mem_rowStochastic_iff_mem_colStochastic`

English:
lemma transpose_mem_rowStochastic_iff_mem_colStochastic
  proof: by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ => forall_comm

中文:
引理 transpose_mem_rowStochastic_iff_mem_colStochastic
  证明: by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ => forall_comm

Depends on / 依赖: and_congr_left_iff, forall_comm, mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply
-/
lemma transpose_mem_rowStochastic_iff_mem_colStochastic :
    Mᵀ in rowStochastic R n ↔ M in colStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ => forall_comm

/-- The transpose of a matrix is column stochastic matrix if it is row stochastic. -/
@[grind =]
/--
lemma `transpose_mem_colStochastic_iff_mem_rowStochastic` / 引理 `transpose_mem_colStochastic_iff_mem_rowStochastic`

English:
lemma transpose_mem_colStochastic_iff_mem_rowStochastic
  proof: by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ => forall_comm

中文:
引理 transpose_mem_colStochastic_iff_mem_rowStochastic
  证明: by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ => forall_comm

Depends on / 依赖: and_congr_left_iff, forall_comm, mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply
-/
lemma transpose_mem_colStochastic_iff_mem_rowStochastic :
    Mᵀ in colStochastic R n ↔ M in rowStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ => forall_comm

/-- Reindexing a matrix preserves row-stochasticity. -/
@[aesop safe apply]
/--
lemma `reindex_mem_rowStochastic` / 引理 `reindex_mem_rowStochastic`

English:
lemma reindex_mem_rowStochastic
  statement: {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
  proof: ⟨fun _ _ => by simpa using nonneg_of_mem_rowStochastic hM, by simp [submatrix_mulVec_equiv, hM.2]⟩

中文:
引理 reindex_mem_rowStochastic
  结论: {m : 类型} [有限类型 m] [DecidableEq m] {M : 矩阵 n n R}
  证明: ⟨fun _ _ => by simpa using nonneg_of_mem_rowStochastic hM, by simp [submatrix_mulVec_equiv, hM.2]⟩

Depends on / 依赖: nonneg_of_mem_rowStochastic, submatrix_mulVec_equiv
-/
lemma reindex_mem_rowStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M in rowStochastic R n) : M.reindex e₁ e₂ in rowStochastic R m :=
  ⟨fun _ _ => by simpa using nonneg_of_mem_rowStochastic hM, by simp [submatrix_mulVec_equiv, hM.2]⟩

/-- Reindexing a matrix preserves row-stochasticity. -/
@[grind =]
/--
lemma `reindex_mem_rowStochastic_iff` / 引理 `reindex_mem_rowStochastic_iff`

English:
lemma reindex_mem_rowStochastic_iff
  statement: {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
  proof: by
  refine ⟨fun h => ?_, reindex_mem_rowStochastic⟩
  have : M = (M.reindex e₁ e₂).reindex e₁.symm e₂.symm := by simp
  rw [this]
  exact reindex_mem_rowStochastic h

中文:
引理 reindex_mem_rowStochastic_iff
  结论: {m : 类型} [有限类型 m] [DecidableEq m] {M : 矩阵 n n R}
  证明: by
  refine ⟨fun h => ?_, reindex_mem_rowStochastic⟩
  have : M = (M.reindex e₁ e₂).reindex e₁.symm e₂.symm := by simp
  rw [this]
  exact reindex_mem_rowStochastic h

Depends on / 依赖: M.reindex, reindex, reindex_mem_rowStochastic
-/
lemma reindex_mem_rowStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ in rowStochastic R m ↔ M in rowStochastic R n := by
  refine ⟨fun h => ?_, reindex_mem_rowStochastic⟩
  have : M = (M.reindex e₁ e₂).reindex e₁.symm e₂.symm := by simp
  rw [this]
  exact reindex_mem_rowStochastic h

/-- Reindexing a matrix preserves column-stochasticity. -/
@[grind =]
/--
lemma `reindex_mem_colStochastic_iff` / 引理 `reindex_mem_colStochastic_iff`

English:
lemma reindex_mem_colStochastic_iff
  statement: {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
  proof: by
  rw [← transpose_transpose (reindex e₁ e₂ M)]; rw [transpose_reindex]; rw [transpose_mem_colStochastic_iff_mem_rowStochastic]; rw [reindex_mem_rowStochastic_iff]; rw [← transpose_mem_colStochastic_iff_mem_rowStochastic]; rw [transpose_transpose]

中文:
引理 reindex_mem_colStochastic_iff
  结论: {m : 类型} [有限类型 m] [DecidableEq m] {M : 矩阵 n n R}
  证明: by
  rw [← transpose_transpose (reindex e₁ e₂ M)]; rw [transpose_reindex]; rw [transpose_mem_colStochastic_iff_mem_rowStochastic]; rw [reindex_mem_rowStochastic_iff]; rw [← transpose_mem_colStochastic_iff_mem_rowStochastic]; rw [transpose_transpose]

Depends on / 依赖: reindex, reindex_mem_rowStochastic_iff, transpose_mem_colStochastic_iff_mem_rowStochastic, transpose_reindex, transpose_transpose
-/
lemma reindex_mem_colStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ in colStochastic R m ↔ M in colStochastic R n := by
  rw [← transpose_transpose (reindex e₁ e₂ M)]; rw [transpose_reindex]; rw [transpose_mem_colStochastic_iff_mem_rowStochastic]; rw [reindex_mem_rowStochastic_iff]; rw [← transpose_mem_colStochastic_iff_mem_rowStochastic]; rw [transpose_transpose]

/-- Reindexing a matrix preserves column-stochasticity. -/
@[aesop safe apply]
alias ⟨_, reindex_mem_colStochastic⟩ := reindex_mem_colStochastic_iff

end Matrix
