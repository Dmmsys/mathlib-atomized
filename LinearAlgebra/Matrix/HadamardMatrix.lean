/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Star.Unitary

/-!
# Hadamard matrices

This file defines `Matrix.IsHadamard`, a unified notion that specializes to the classical real
Hadamard matrices over `ℝ`/`ℤ` (where `star` is trivial and entries are `±1`) and to the complex
Hadamard matrices over `ℂ` (where entries have unit norm). Basic results: conjugate-transpose
closure, the order identity `n = s * star s` from constant row or column sums, the Sylvester
(Kronecker) construction, and the divisibility obstruction `4 ∣ n`.

## References

* [W. de Launey and D. L. Flannery, *Algebraic Design Theory*][deLauneyFlannery2011]
-/

@[expose] public section


variable {m n R : Type*}

namespace Matrix

open scoped Kronecker

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Semiring
variable [Semiring R] [StarRing R]

/--
Definition of `IsHadamard` / `IsHadamard` 的定义

English:
structure IsHadamard
  parameters: (A : Matrix n n R)
  axioms and operations (3):
    - apply_mem((i j : n)) : A i j in unitary R
    - mul_conjTranspose : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R)
    - conjTranspose_mul : Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R)

中文:
结构 是Hadamard
  参数: (A : 矩阵 n n R)
  公理与运算 (3 个):
    - apply_mem((i j : n)) : A i j in unitary R
    - mul_conjTranspose : A * Aᴴ = (有限类型.card n : R) • (1 : 矩阵 n n R)
    - conjTranspose_mul : Aᴴ * A = (有限类型.card n : R) • (1 : 矩阵 n n R)
-/
@[mk_iff] structure IsHadamard (A : Matrix n n R) : Prop where
  apply_mem (i j : n) : A i j in unitary R
  mul_conjTranspose : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R)
  conjTranspose_mul : Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R)

variable {A : Matrix n n R}

/--
theorem `IsHadamard.isStarNormal` / 定理 `IsHadamard.isStarNormal`

English:
theorem IsHadamard.isStarNormal
  given: (hA : A.IsHadamard)
  statement: IsStarNormal A where
  proof: by
    rw [commute_iff_eq]; rw [star_eq_conjTranspose]; rw [hA.conjTranspose_mul]; rw [hA.mul_conjTranspose]

中文:
定理 是Hadamard.isStarNormal
  条件: (hA : A.是Hadamard)
  结论: 是StarNormal A where
  证明: by
    rw [commute_iff_eq]; rw [star_eq_conjTranspose]; rw [hA.conjTranspose_mul]; rw [hA.mul_conjTranspose]

Depends on / 依赖: commute_iff_eq, conjTranspose_mul, hA.conjTranspose_mul, hA.mul_conjTranspose, mul_conjTranspose, star_eq_conjTranspose
-/
theorem IsHadamard.isStarNormal (hA : A.IsHadamard) : IsStarNormal A where
  star_comm_self := by
    rw [commute_iff_eq]; rw [star_eq_conjTranspose]; rw [hA.conjTranspose_mul]; rw [hA.mul_conjTranspose]

/--
theorem `IsHadamard.conjTranspose` / 定理 `IsHadamard.conjTranspose`

English:
theorem IsHadamard.conjTranspose
  given: (hA : A.IsHadamard)
  statement: Aᴴ.IsHadamard
  proof: by
  exact ⟨fun i j => Unitary.star_mem (hA.apply_mem j i),
    by simpa using hA.conjTranspose_mul,
    by simpa using hA.mul_conjTranspose⟩

@[simp]

中文:
定理 是Hadamard.conjTranspose
  条件: (hA : A.是Hadamard)
  结论: Aᴴ.是Hadamard
  证明: by
  exact ⟨fun i j => Unitary.star_mem (hA.apply_mem j i),
    by simpa using hA.conjTranspose_mul,
    by simpa using hA.mul_conjTranspose⟩

@[simp]

Depends on / 依赖: Unitary, Unitary.star_mem, apply_mem, conjTranspose_mul, hA.apply_mem, hA.conjTranspose_mul, hA.mul_conjTranspose, mul_conjTranspose, star_mem
-/
theorem IsHadamard.conjTranspose (hA : A.IsHadamard) : Aᴴ.IsHadamard := by
  exact ⟨fun i j => Unitary.star_mem (hA.apply_mem j i),
    by simpa using hA.conjTranspose_mul,
    by simpa using hA.mul_conjTranspose⟩

@[simp]
/--
theorem `isHadamard_conjTranspose_iff` / 定理 `isHadamard_conjTranspose_iff`

English:
theorem isHadamard_conjTranspose_iff
  statement: Aᴴ.IsHadamard ↔ A.IsHadamard
  proof: ⟨fun hA => by simpa using hA.conjTranspose, (·.conjTranspose)⟩

中文:
定理 isHadamard_conjTranspose_iff
  结论: Aᴴ.是Hadamard ↔ A.是Hadamard
  证明: ⟨fun hA => by simpa using hA.conjTranspose, (·.conjTranspose)⟩

Depends on / 依赖: conjTranspose, hA.conjTranspose
-/
theorem isHadamard_conjTranspose_iff : Aᴴ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.conjTranspose, (·.conjTranspose)⟩

/--
theorem `IsHadamard.reindex` / 定理 `IsHadamard.reindex`

English:
theorem IsHadamard.reindex
  given: (e₁ e₂ : n ≃ m) (hA : A.IsHadamard)
  proof: by
  refine ⟨fun i j => hA.apply_mem _ _, ?_, ?_⟩ <;>
    simp [reindex_apply, submatrix_mul_equiv, hA.mul_conjTranspose, hA.conjTranspose_mul,
      Fintype.card_congr e₁, submatrix_smul, Pi.smul_apply]

@[simp]

中文:
定理 是Hadamard.reindex
  条件: (e₁ e₂ : n ≃ m) (hA : A.是Hadamard)
  证明: by
  refine ⟨fun i j => hA.apply_mem _ _, ?_, ?_⟩ <;>
    simp [reindex_apply, submatrix_mul_equiv, hA.mul_conjTranspose, hA.conjTranspose_mul,
      Fintype.card_congr e₁, submatrix_smul, Pi.smul_apply]

@[simp]

Depends on / 依赖: Fintype, Fintype.card_congr, Pi.smul_apply, apply_mem, card_congr, conjTranspose_mul, hA.apply_mem, hA.conjTranspose_mul, hA.mul_conjTranspose, mul_conjTranspose, reindex_apply, smul_apply, submatrix_mul_equiv, submatrix_smul
-/
theorem IsHadamard.reindex (e₁ e₂ : n ≃ m) (hA : A.IsHadamard) :
    (reindex e₁ e₂ A).IsHadamard := by
  refine ⟨fun i j => hA.apply_mem _ _, ?_, ?_⟩ <;>
    simp [reindex_apply, submatrix_mul_equiv, hA.mul_conjTranspose, hA.conjTranspose_mul,
      Fintype.card_congr e₁, submatrix_smul, Pi.smul_apply]

@[simp]
/--
theorem `isHadamard_submatrix_equiv_iff` / 定理 `isHadamard_submatrix_equiv_iff`

English:
theorem isHadamard_submatrix_equiv_iff
  given: (e₁ e₂ : m ≃ n)
  proof: ⟨fun h => by simpa using h.reindex e₁ e₂,
    fun h => by simpa [reindex_apply] using h.reindex e₁.symm e₂.symm⟩

中文:
定理 isHadamard_submatrix_equiv_iff
  条件: (e₁ e₂ : m ≃ n)
  证明: ⟨fun h => by simpa using h.reindex e₁ e₂,
    fun h => by simpa [reindex_apply] using h.reindex e₁.symm e₂.symm⟩

Depends on / 依赖: h.reindex, reindex, reindex_apply
-/
theorem isHadamard_submatrix_equiv_iff (e₁ e₂ : m ≃ n) :
    (A.submatrix e₁ e₂).IsHadamard ↔ A.IsHadamard :=
  ⟨fun h => by simpa using h.reindex e₁ e₂,
    fun h => by simpa [reindex_apply] using h.reindex e₁.symm e₂.symm⟩

/--
theorem `IsHadamard.kronecker` / 定理 `IsHadamard.kronecker`

English:
theorem IsHadamard.kronecker
  statement: {A : Matrix m m R} {B : Matrix n n R}
  proof: by
  refine ⟨fun _ _ => mul_mem (hA.apply_mem _ _) (hB.apply_mem _ _), ?_, ?_⟩ <;> ext ⟨i, i'⟩ ⟨j, j'⟩
  · calc
      _ = ∑ x₁, ∑ x₂, A i x₁ * (B i' x₂ * Bᴴ x₂ j') * Aᴴ x₁ j := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i' = j' then ∑ x, A i x * (Fintype.card n • Aᴴ) x j else 0 := by
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hB.mul_conjTranspose,
          one_apply, mul_assoc _ (Fintype.card n : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hA.mul_conjTranspose]
        simp [one_apply, ← Nat.cast_mul, mul_comm, ← ite_and, and_comm]
  · calc
      _ = ∑ x₁, ∑ x₂, Bᴴ i' x₂ * (Aᴴ i x₁ * A x₁ j) * B x₂ j' := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i = j then ∑ x, Bᴴ i' x * (Fintype.card m • B) x j' else 0 := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hA.conjTranspose_mul,
          one_apply, mul_assoc _ (Fintype.card m : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hB.conjTranspose_mul]
        simp [one_apply, ← Nat.cast_mul, ← ite_and]

中文:
定理 是Hadamard.kronecker
  结论: {A : 矩阵 m m R} {B : 矩阵 n n R}
  证明: by
  refine ⟨fun _ _ => mul_mem (hA.apply_mem _ _) (hB.apply_mem _ _), ?_, ?_⟩ <;> ext ⟨i, i'⟩ ⟨j, j'⟩
  · calc
      _ = ∑ x₁, ∑ x₂, A i x₁ * (B i' x₂ * Bᴴ x₂ j') * Aᴴ x₁ j := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i' = j' then ∑ x, A i x * (Fintype.card n • Aᴴ) x j else 0 := by
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hB.mul_conjTranspose,
          one_apply, mul_assoc _ (Fintype.card n : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hA.mul_conjTranspose]
        simp [one_apply, ← Nat.cast_mul, mul_comm, ← ite_and, and_comm]
  · calc
      _ = ∑ x₁, ∑ x₂, Bᴴ i' x₂ * (Aᴴ i x₁ * A x₁ j) * B x₂ j' := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i = j then ∑ x, Bᴴ i' x * (Fintype.card m • B) x j' else 0 := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hA.conjTranspose_mul,
          one_apply, mul_assoc _ (Fintype.card m : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hB.conjTranspose_mul]
        simp [one_apply, ← Nat.cast_mul, ← ite_and]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_mul, Finset.sum_product, Fintype, Fintype.card, apply_mem, conjTranspose_apply, conjTranspose_kronecker, hA.apply_mem, hB.apply_mem, hB.mul_conjTranspose, mul_apply, mul_assoc, mul_conjTranspose, mul_mem, mul_sum, one_apply, sum_mul, sum_product
-/
theorem IsHadamard.kronecker {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHadamard) (hB : B.IsHadamard) : (A otimesₖ B).IsHadamard := by
  refine ⟨fun _ _ => mul_mem (hA.apply_mem _ _) (hB.apply_mem _ _), ?_, ?_⟩ <;> ext ⟨i, i'⟩ ⟨j, j'⟩
  · calc
      _ = ∑ x₁, ∑ x₂, A i x₁ * (B i' x₂ * Bᴴ x₂ j') * Aᴴ x₁ j := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i' = j' then ∑ x, A i x * (Fintype.card n • Aᴴ) x j else 0 := by
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hB.mul_conjTranspose,
          one_apply, mul_assoc _ (Fintype.card n : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hA.mul_conjTranspose]
        simp [one_apply, ← Nat.cast_mul, mul_comm, ← ite_and, and_comm]
  · calc
      _ = ∑ x₁, ∑ x₂, Bᴴ i' x₂ * (Aᴴ i x₁ * A x₁ j) * B x₂ j' := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i = j then ∑ x, Bᴴ i' x * (Fintype.card m • B) x j' else 0 := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hA.conjTranspose_mul,
          one_apply, mul_assoc _ (Fintype.card m : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hB.conjTranspose_mul]
        simp [one_apply, ← Nat.cast_mul, ← ite_and]

/--
theorem `IsHadamard.card_eq_mul_star_of_const_col_sum` / 定理 `IsHadamard.card_eq_mul_star_of_const_col_sum`

English:
theorem IsHadamard.card_eq_mul_star_of_const_col_sum
  statement: {s : R}
  proof: by
  have hvcol : (1 : n -> R) ᵥ* A = s • 1 := by
    ext j
    simpa [Matrix.vecMul, dotProduct] using hcol j
  have hconjcol : Aᴴ *ᵥ (1 : n -> R) = star s • 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← star_sum, hcol i]
  have hleft : (1 : n -> R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) ^ 2 := by
    rw [hA.mul_conjTranspose]; rw [Nat.cast_smul_eq_nsmul]; rw [vecMul_smul]; rw [smul_dotProduct]
    simp [dotProduct, pow_two]
  have hright : (1 : n -> R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) * (s * star s) := by
    rw [← vecMul_vecMul]; rw [← dotProduct_mulVec]; rw [hvcol]; rw [hconjcol]
    simp [dotProduct]
exact hcard.left show (Fintype.card n : R) * (Fintype.card n : R) =
      (Fintype.card n : R) * (s * star s) by
    simpa [pow_two] using hleft.symm.trans hright

中文:
定理 是Hadamard.card_eq_mul_star_of_const_col_sum
  结论: {s : R}
  证明: by
  have hvcol : (1 : n -> R) ᵥ* A = s • 1 := by
    ext j
    simpa [Matrix.vecMul, dotProduct] using hcol j
  have hconjcol : Aᴴ *ᵥ (1 : n -> R) = star s • 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← star_sum, hcol i]
  have hleft : (1 : n -> R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) ^ 2 := by
    rw [hA.mul_conjTranspose]; rw [Nat.cast_smul_eq_nsmul]; rw [vecMul_smul]; rw [smul_dotProduct]
    simp [dotProduct, pow_two]
  have hright : (1 : n -> R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) * (s * star s) := by
    rw [← vecMul_vecMul]; rw [← dotProduct_mulVec]; rw [hvcol]; rw [hconjcol]
    simp [dotProduct]
exact hcard.left show (Fintype.card n : R) * (Fintype.card n : R) =
      (Fintype.card n : R) * (s * star s) by
    simpa [pow_two] using hleft.symm.trans hright

Depends on / 依赖: Fintype, Fintype.card, Matrix, Matrix.mulVec, Matrix.vecMul, Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, dotProduct, hA.mul_conjTranspose, hconjcol, hright, mulVec, mul_conjTranspose, pow_two, smul_dotProduct, star_sum, vecMul, vecMul_smul
-/
theorem IsHadamard.card_eq_mul_star_of_const_col_sum {s : R}
    (hA : A.IsHadamard) (hcard : IsRegular (Fintype.card n : R))
    (hcol : forall j, ∑ i, A i j = s) : (Fintype.card n : R) = s * star s := by
  have hvcol : (1 : n -> R) ᵥ* A = s • 1 := by
    ext j
    simpa [Matrix.vecMul, dotProduct] using hcol j
  have hconjcol : Aᴴ *ᵥ (1 : n -> R) = star s • 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← star_sum, hcol i]
  have hleft : (1 : n -> R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) ^ 2 := by
    rw [hA.mul_conjTranspose]; rw [Nat.cast_smul_eq_nsmul]; rw [vecMul_smul]; rw [smul_dotProduct]
    simp [dotProduct, pow_two]
  have hright : (1 : n -> R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) * (s * star s) := by
    rw [← vecMul_vecMul]; rw [← dotProduct_mulVec]; rw [hvcol]; rw [hconjcol]
    simp [dotProduct]
exact hcard.left show (Fintype.card n : R) * (Fintype.card n : R) =
      (Fintype.card n : R) * (s * star s) by
    simpa [pow_two] using hleft.symm.trans hright

/--
theorem `IsHadamard.card_eq_star_mul_of_const_row_sum` / 定理 `IsHadamard.card_eq_star_mul_of_const_row_sum`

English:
theorem IsHadamard.card_eq_star_mul_of_const_row_sum
  statement: {s : R}
  proof: by
  have hcol : forall j, ∑ i, Aᴴ i j = star s := fun j => by
    simp [conjTranspose_apply, ← star_sum, hrow j]
  simpa using hA.conjTranspose.card_eq_mul_star_of_const_col_sum hcard hcol

中文:
定理 是Hadamard.card_eq_star_mul_of_const_row_sum
  结论: {s : R}
  证明: by
  have hcol : forall j, ∑ i, Aᴴ i j = star s := fun j => by
    simp [conjTranspose_apply, ← star_sum, hrow j]
  simpa using hA.conjTranspose.card_eq_mul_star_of_const_col_sum hcard hcol

Depends on / 依赖: card_eq_mul_star_of_const_col_sum, conjTranspose, conjTranspose_apply, hA.conjTranspose.card_eq_mul_star_of_const_col_sum, star_sum
-/
theorem IsHadamard.card_eq_star_mul_of_const_row_sum {s : R}
    (hA : A.IsHadamard) (hcard : IsRegular (Fintype.card n : R))
    (hrow : forall i, ∑ j, A i j = s) : (Fintype.card n : R) = star s * s := by
  have hcol : forall j, ∑ i, Aᴴ i j = star s := fun j => by
    simp [conjTranspose_apply, ← star_sum, hrow j]
  simpa using hA.conjTranspose.card_eq_mul_star_of_const_col_sum hcard hcol

end Semiring

section CommSemiring
variable [CommSemiring R] [StarRing R] {A : Matrix n n R}

/--
theorem `IsHadamard.transpose` / 定理 `IsHadamard.transpose`

English:
theorem IsHadamard.transpose
  given: (hA : A.IsHadamard)
  statement: Aᵀ.IsHadamard where
  proof: hA.apply_mem j i
  mul_conjTranspose := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose]; rw [← transpose_mul]; rw [hA.conjTranspose_mul]; rw [transpose_smul]; rw [transpose_one]
  conjTranspose_mul := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose]; rw [← transpose_mul]; rw [hA.mul_conjTranspose]; rw [transpose_smul]; rw [transpose_one]

@[simp]

中文:
定理 是Hadamard.transpose
  条件: (hA : A.是Hadamard)
  结论: Aᵀ.是Hadamard where
  证明: hA.apply_mem j i
  mul_conjTranspose := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose]; rw [← transpose_mul]; rw [hA.conjTranspose_mul]; rw [transpose_smul]; rw [transpose_one]
  conjTranspose_mul := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose]; rw [← transpose_mul]; rw [hA.mul_conjTranspose]; rw [transpose_smul]; rw [transpose_one]

@[simp]

Depends on / 依赖: apply_mem, hA.apply_mem
-/
theorem IsHadamard.transpose (hA : A.IsHadamard) : Aᵀ.IsHadamard where
  apply_mem i j := hA.apply_mem j i
  mul_conjTranspose := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose]; rw [← transpose_mul]; rw [hA.conjTranspose_mul]; rw [transpose_smul]; rw [transpose_one]
  conjTranspose_mul := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose]; rw [← transpose_mul]; rw [hA.mul_conjTranspose]; rw [transpose_smul]; rw [transpose_one]

@[simp]
/--
theorem `isHadamard_transpose_iff` / 定理 `isHadamard_transpose_iff`

English:
theorem isHadamard_transpose_iff
  statement: Aᵀ.IsHadamard ↔ A.IsHadamard
  proof: ⟨fun hA => by simpa using hA.transpose, (·.transpose)⟩

中文:
定理 isHadamard_transpose_iff
  结论: Aᵀ.是Hadamard ↔ A.是Hadamard
  证明: ⟨fun hA => by simpa using hA.transpose, (·.transpose)⟩

Depends on / 依赖: hA.transpose, transpose
-/
theorem isHadamard_transpose_iff : Aᵀ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.transpose, (·.transpose)⟩

end CommSemiring

section Ring
variable [Ring R] [StarRing R] {A : Matrix n n R}

/--
theorem `IsHadamard.neg` / 定理 `IsHadamard.neg`

English:
theorem IsHadamard.neg
  given: (hA : A.IsHadamard)
  statement: (-A).IsHadamard
  proof: by
  simpa [isHadamard_iff, Unitary.mem_iff] using hA

中文:
定理 是Hadamard.neg
  条件: (hA : A.是Hadamard)
  结论: (-A).是Hadamard
  证明: by
  simpa [isHadamard_iff, Unitary.mem_iff] using hA

Depends on / 依赖: Unitary, Unitary.mem_iff, isHadamard_iff, mem_iff
-/
theorem IsHadamard.neg (hA : A.IsHadamard) : (-A).IsHadamard := by
  simpa [isHadamard_iff, Unitary.mem_iff] using hA

/-- A matrix is Hadamard iff its negation is. -/
@[simp]
/--
theorem `IsHadamard.neg_iff` / 定理 `IsHadamard.neg_iff`

English:
theorem IsHadamard.neg_iff
  statement: (-A).IsHadamard ↔ A.IsHadamard
  proof: ⟨fun hA => by simpa using hA.neg, (·.neg)⟩

中文:
定理 是Hadamard.neg_iff
  结论: (-A).是Hadamard ↔ A.是Hadamard
  证明: ⟨fun hA => by simpa using hA.neg, (·.neg)⟩

Depends on / 依赖: hA.neg
-/
theorem IsHadamard.neg_iff : (-A).IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.neg, (·.neg)⟩

end Ring

section CommRing
variable [CommRing R] [StarRing R] {A : Matrix n n R}

/--
theorem `IsHadamard.det_mul_star_det` / 定理 `IsHadamard.det_mul_star_det`

English:
theorem IsHadamard.det_mul_star_det
  given: (hA : A.IsHadamard)
  proof: by
  have := congr_arg det hA.mul_conjTranspose
  rwa [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this

中文:
定理 是Hadamard.det_mul_star_det
  条件: (hA : A.是Hadamard)
  证明: by
  have := congr_arg det hA.mul_conjTranspose
  rwa [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this

Depends on / 依赖: congr_arg, det_conjTranspose, det_mul, det_one, det_smul, hA.mul_conjTranspose, mul_conjTranspose, mul_one
-/
theorem IsHadamard.det_mul_star_det (hA : A.IsHadamard) :
    A.det * star A.det = (Fintype.card n : R) ^ Fintype.card n := by
  have := congr_arg det hA.mul_conjTranspose
  rwa [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this

/--
theorem `IsHadamard.star_det_mul_det` / 定理 `IsHadamard.star_det_mul_det`

English:
theorem IsHadamard.star_det_mul_det
  given: (hA : A.IsHadamard)
  proof: by
  rw [mul_comm]; rw [hA.det_mul_star_det]

中文:
定理 是Hadamard.star_det_mul_det
  条件: (hA : A.是Hadamard)
  证明: by
  rw [mul_comm]; rw [hA.det_mul_star_det]

Depends on / 依赖: det_mul_star_det, hA.det_mul_star_det, mul_comm
-/
theorem IsHadamard.star_det_mul_det (hA : A.IsHadamard) :
    star A.det * A.det = (Fintype.card n : R) ^ Fintype.card n := by
  rw [mul_comm]; rw [hA.det_mul_star_det]

/--
theorem `IsHadamard.det_ne_zero` / 定理 `IsHadamard.det_ne_zero`

English:
theorem IsHadamard.det_ne_zero
  statement: [IsReduced R] (hA : A.IsHadamard)
  proof: fun h =>
pow_ne_zero _ hcard by rw [← hA.det_mul_star_det, h, star_zero, zero_mul]

中文:
定理 是Hadamard.det_ne_zero
  结论: [是既约 R] (hA : A.是Hadamard)
  证明: fun h =>
pow_ne_zero _ hcard by rw [← hA.det_mul_star_det, h, star_zero, zero_mul]
-/
theorem IsHadamard.det_ne_zero [IsReduced R] (hA : A.IsHadamard)
    (hcard : (Fintype.card n : R) != 0) : A.det != 0 := fun h =>
pow_ne_zero _ hcard by rw [← hA.det_mul_star_det, h, star_zero, zero_mul]

/--
theorem `IsHadamard.isRegular_det` / 定理 `IsHadamard.isRegular_det`

English:
theorem IsHadamard.isRegular_det
  statement: (hA : A.IsHadamard)
  proof: by
  have : IsRegular (A.det * star A.det) := by
    rw [hA.det_mul_star_det]
    exact hcard.pow _
  exact this.of_mul_left

中文:
定理 是Hadamard.isRegular_det
  结论: (hA : A.是Hadamard)
  证明: by
  have : IsRegular (A.det * star A.det) := by
    rw [hA.det_mul_star_det]
    exact hcard.pow _
  exact this.of_mul_left

Depends on / 依赖: A.det, IsRegular, det_mul_star_det, hA.det_mul_star_det, hcard.pow, of_mul_left, this.of_mul_left
-/
theorem IsHadamard.isRegular_det (hA : A.IsHadamard)
    (hcard : IsRegular (Fintype.card n : R)) : IsRegular A.det := by
  have : IsRegular (A.det * star A.det) := by
    rw [hA.det_mul_star_det]
    exact hcard.pow _
  exact this.of_mul_left

/--
theorem `IsHadamard.of_mul_conjTranspose` / 定理 `IsHadamard.of_mul_conjTranspose`

English:
theorem IsHadamard.of_mul_conjTranspose
  proof: by
  refine ⟨hentry, hmul, ?_⟩
  have hdet : IsRegular (A.det * star A.det) := by
    have := congr_arg det hmul
    rw [det_mul]; rw [det_conjTranspose]; rw [det_smul]; rw [det_one]; rw [mul_one] at this
    rw [this]
    exact hcard.pow _
  have hreg : IsLeftRegular A :=
    (isRegular_of_isLeftRegular_det hdet.of_mul_left.left).left
exact hreg show A * (Aᴴ * A) = A * ((Fintype.card n : R) • 1) by
    rw [← mul_assoc]; rw [hmul]; rw [smul_mul_assoc]; rw [one_mul]; rw [mul_smul_comm]; rw [mul_one]

中文:
定理 是Hadamard.of_mul_conjTranspose
  证明: by
  refine ⟨hentry, hmul, ?_⟩
  have hdet : IsRegular (A.det * star A.det) := by
    have := congr_arg det hmul
    rw [det_mul]; rw [det_conjTranspose]; rw [det_smul]; rw [det_one]; rw [mul_one] at this
    rw [this]
    exact hcard.pow _
  have hreg : IsLeftRegular A :=
    (isRegular_of_isLeftRegular_det hdet.of_mul_left.left).left
exact hreg show A * (Aᴴ * A) = A * ((Fintype.card n : R) • 1) by
    rw [← mul_assoc]; rw [hmul]; rw [smul_mul_assoc]; rw [one_mul]; rw [mul_smul_comm]; rw [mul_one]

Depends on / 依赖: A.det, Fintype, Fintype.card, IsLeftRegular, IsRegular, congr_arg, det_conjTranspose, det_mul, det_one, det_smul, hcard.pow, hdet.of_mul_left.left, hentry, isRegular_of_isLeftRegular_det, mul_assoc, mul_one, mul_smul_comm, of_mul_left, one_mul, smul_mul_assoc
-/
theorem IsHadamard.of_mul_conjTranspose
    (hentry : forall i j, A i j in unitary R)
    (hmul : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R))
    (hcard : IsRegular (Fintype.card n : R)) : A.IsHadamard := by
  refine ⟨hentry, hmul, ?_⟩
  have hdet : IsRegular (A.det * star A.det) := by
    have := congr_arg det hmul
    rw [det_mul]; rw [det_conjTranspose]; rw [det_smul]; rw [det_one]; rw [mul_one] at this
    rw [this]
    exact hcard.pow _
  have hreg : IsLeftRegular A :=
    (isRegular_of_isLeftRegular_det hdet.of_mul_left.left).left
exact hreg show A * (Aᴴ * A) = A * ((Fintype.card n : R) • 1) by
    rw [← mul_assoc]; rw [hmul]; rw [smul_mul_assoc]; rw [one_mul]; rw [mul_smul_comm]; rw [mul_one]

/--
theorem `isHadamard_iff_mul_conjTranspose` / 定理 `isHadamard_iff_mul_conjTranspose`

English:
theorem isHadamard_iff_mul_conjTranspose
  proof: ⟨fun hA => ⟨hA.apply_mem, hA.mul_conjTranspose⟩,
   fun hA => IsHadamard.of_mul_conjTranspose hA.1 hA.2 hcard⟩

中文:
定理 isHadamard_iff_mul_conjTranspose
  证明: ⟨fun hA => ⟨hA.apply_mem, hA.mul_conjTranspose⟩,
   fun hA => IsHadamard.of_mul_conjTranspose hA.1 hA.2 hcard⟩

Depends on / 依赖: IsHadamard, IsHadamard.of_mul_conjTranspose, apply_mem, hA.apply_mem, hA.mul_conjTranspose, mul_conjTranspose, of_mul_conjTranspose
-/
theorem isHadamard_iff_mul_conjTranspose
    (hcard : IsRegular (Fintype.card n : R)) :
    A.IsHadamard ↔
      (forall i j, A i j in unitary R) ∧
        A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) :=
  ⟨fun hA => ⟨hA.apply_mem, hA.mul_conjTranspose⟩,
   fun hA => IsHadamard.of_mul_conjTranspose hA.1 hA.2 hcard⟩

end CommRing

/--
theorem `IsHadamard.four_dvd_card` / 定理 `IsHadamard.four_dvd_card`

English:
theorem IsHadamard.four_dvd_card
  statement: {A : Matrix n n Int}
  proof: by
  have hpm : forall i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth ⦃i k : n⦄ (hik : i != k) : ∑ j, A i j * A k j = 0 := by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.mul_conjTranspose i) k
  have hexpand : forall j, (1 + A s j * A r j) * (1 + A t j * A r j) =
      1 + A s j * A r j + A t j * A r j + A s j * A t j := fun j => by
    obtain hr | hr := hpm r j <;> simp [hr] <;> ring
  have hdvd : forall j, (4 : Int) ∣ (1 + A s j * A r j) * (1 + A t j * A r j) := fun j => by
    obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
      obtain ht | ht := hpm t j <;> simp [hs, hr, ht]
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : Int) := by
    simp_rw [hexpand]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  rw [← Int.ofNat_dvd]; rw [← hsum]
  exact Finset.dvd_sum fun j _ => hdvd j

中文:
定理 是Hadamard.four_dvd_card
  结论: {A : 矩阵 n n 整数}
  证明: by
  have hpm : forall i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth ⦃i k : n⦄ (hik : i != k) : ∑ j, A i j * A k j = 0 := by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.mul_conjTranspose i) k
  have hexpand : forall j, (1 + A s j * A r j) * (1 + A t j * A r j) =
      1 + A s j * A r j + A t j * A r j + A s j * A t j := fun j => by
    obtain hr | hr := hpm r j <;> simp [hr] <;> ring
  have hdvd : forall j, (4 : Int) ∣ (1 + A s j * A r j) * (1 + A t j * A r j) := fun j => by
    obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
      obtain ht | ht := hpm t j <;> simp [hs, hr, ht]
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : Int) := by
    simp_rw [hexpand]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  rw [← Int.ofNat_dvd]; rw [← hsum]
  exact Finset.dvd_sum fun j _ => hdvd j

Depends on / 依赖: Fintype, Fintype.two_lt_card_iff.mp, Matrix, Matrix.mul_apply, Unitary, Unitary.mem_iff_eq_one_or_eq_neg_one.mp, apply_mem, congr_fun, hA.apply_mem, hA.mul_conjTranspose, hexpand, mem_iff_eq_one_or_eq_neg_one, mul_apply, mul_conjTranspose, two_lt_card_iff
-/
theorem IsHadamard.four_dvd_card {A : Matrix n n Int}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  have hpm : forall i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth ⦃i k : n⦄ (hik : i != k) : ∑ j, A i j * A k j = 0 := by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.mul_conjTranspose i) k
  have hexpand : forall j, (1 + A s j * A r j) * (1 + A t j * A r j) =
      1 + A s j * A r j + A t j * A r j + A s j * A t j := fun j => by
    obtain hr | hr := hpm r j <;> simp [hr] <;> ring
  have hdvd : forall j, (4 : Int) ∣ (1 + A s j * A r j) * (1 + A t j * A r j) := fun j => by
    obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
      obtain ht | ht := hpm t j <;> simp [hs, hr, ht]
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : Int) := by
    simp_rw [hexpand]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  rw [← Int.ofNat_dvd]; rw [← hsum]
  exact Finset.dvd_sum fun j _ => hdvd j

end Matrix
