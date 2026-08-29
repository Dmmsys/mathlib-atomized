/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Aristotle AI
-/
module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence and nonsingularity of matrices

In this file we formalize several theorems proved by Yi-Jia Tan in his paper [Tan2016]
*Free sets and free subsemimodules in a semimodule*. As consequences, we show that
commutative semirings satisfy the strong rank condition, and that the columns of a square matrix
are linearly independent if and only if the matrix is nonsingular (over a commutative ring,
a matrix is nonsingular if and only if its determinant is not a zero divisor).

## Main theorems

* `Matrix.Nonsingular.of_linearIndependent_col`: if the columns of a square matrix are linearly
  independent, then the matrix is nonsingular. Corollary 3.2(1) of [Tan2016].

* `Matrix.Nonsingular.linearIndependent_col`: if a matrix over a commutative semiring with
  cancellative addition is nonsingular, then its columns are linearly independent.
  Corollary 3.2(2) of [Tan2016].

* `CommSemiring.strongRankCondition_of_nontrivial`: a commutative semiring satisfies the strong
  rank condition.
-/

public section

variable {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {A : Matrix n n R}

namespace Matrix

/--
lemma `isDetpBalanced_iff_sub_mul_det_eq_zero` / 引理 `isDetpBalanced_iff_sub_mul_det_eq_zero`

English:
lemma isDetpBalanced_iff_sub_mul_det_eq_zero
  given: {R : Type*} [CommRing R] {A : Matrix n n R} {a b : R}
  proof: by
  grind [IsDetpBalanced, det_eq_detp_sub_detp]

中文:
引理 isDetpBalanced_iff_sub_mul_det_eq_zero
  条件: {R : 类型} [交换环 R] {A : 矩阵 n n R} {a b : R}
  证明: by
  grind [IsDetpBalanced, det_eq_detp_sub_detp]

Depends on / 依赖: IsDetpBalanced, det_eq_detp_sub_detp
-/
lemma isDetpBalanced_iff_sub_mul_det_eq_zero {R : Type*} [CommRing R] {A : Matrix n n R} {a b : R} :
    A.IsDetpBalanced a b ↔ (a - b) * A.det = 0 := by
  grind [IsDetpBalanced, det_eq_detp_sub_detp]

/--
lemma `nonsingular_iff_det_mem_nonZeroDivisors` / 引理 `nonsingular_iff_det_mem_nonZeroDivisors`

English:
lemma nonsingular_iff_det_mem_nonZeroDivisors
  statement: {R : Type*} [CommRing R]
  proof: by
  simp_rw [Nonsingular, isDetpBalanced_iff_sub_mul_det_eq_zero, mem_nonZeroDivisors_iff_right]
exact ⟨fun h x eq => h x 0 (by simpa), fun h a b eq => sub_eq_zero.mp h _ (by simpa)⟩

中文:
引理 nonsingular_iff_det_mem_nonZeroDivisors
  结论: {R : 类型} [交换环 R]
  证明: by
  simp_rw [Nonsingular, isDetpBalanced_iff_sub_mul_det_eq_zero, mem_nonZeroDivisors_iff_right]
exact ⟨fun h x eq => h x 0 (by simpa), fun h a b eq => sub_eq_zero.mp h _ (by simpa)⟩

Depends on / 依赖: Nonsingular, isDetpBalanced_iff_sub_mul_det_eq_zero, mem_nonZeroDivisors_iff_right, simp_rw, sub_eq_zero, sub_eq_zero.mp
-/
lemma nonsingular_iff_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {A : Matrix n n R} : A.Nonsingular ↔ A.det in nonZeroDivisors R := by
  simp_rw [Nonsingular, isDetpBalanced_iff_sub_mul_det_eq_zero, mem_nonZeroDivisors_iff_right]
exact ⟨fun h x eq => h x 0 (by simpa), fun h a b eq => sub_eq_zero.mp h _ (by simpa)⟩

/--
lemma `nonsingular_iff_det_ne_zero` / 引理 `nonsingular_iff_det_ne_zero`

English:
lemma nonsingular_iff_det_ne_zero
  statement: {R : Type*} [CommRing R] [IsDomain R]
  proof: by
  rw [nonsingular_iff_det_mem_nonZeroDivisors]; rw [mem_nonZeroDivisors_iff_ne_zero]

中文:
引理 nonsingular_iff_det_ne_zero
  结论: {R : 类型} [交换环 R] [是整环 R]
  证明: by
  rw [nonsingular_iff_det_mem_nonZeroDivisors]; rw [mem_nonZeroDivisors_iff_ne_zero]

Depends on / 依赖: mem_nonZeroDivisors_iff_ne_zero, nonsingular_iff_det_mem_nonZeroDivisors
-/
lemma nonsingular_iff_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {A : Matrix n n R} : A.Nonsingular ↔ A.det != 0 := by
  rw [nonsingular_iff_det_mem_nonZeroDivisors]; rw [mem_nonZeroDivisors_iff_ne_zero]

/--
theorem `Nonsingular.of_linearIndependent_col` / 定理 `Nonsingular.of_linearIndependent_col`

English:
theorem Nonsingular.of_linearIndependent_col
  given: (ind : LinearIndependent R A.col)
  statement: A.Nonsingular
  proof: by
  intro a b bal
  let P (r : Nat) : Prop := forall f g : Fin r -> n, (A.submatrix f g).IsDetpBalanced a b
  suffices h : P 0 by simpa [IsDetpBalanced] using h Fin.elim0 Fin.elim0
refine Nat.decreasingInduction' (n := Fintype.card n) (fun r _ _ ih f g => ?_) (Nat.zero_le _)
    bal.submatrix_of_card_le (Fintype.card_fin _).ge
  by_cases hg : g.Surjective
  · exact bal.submatrix_of_card_le (Fintype.card_le_of_surjective g hg) f g
  obtain ⟨j₀, h₀⟩ := by simpa [Function.Surjective] using hg
  let D := A.submatrix f g
  let Aj (j : Fin r) := A.submatrix f (Function.update g j j₀)
  let v (a b : R) : n ->₀ R := ∑ j, .single (g j) (a * (Aj j).detp (-1) + b * (Aj j).detp 1) +
    .single j₀ (a * D.detp 1 + b * D.detp (-1))
  suffices h : v a b = v b a by simpa [IsDetpBalanced, v, h₀] using congr($h j₀)
  refine ind (funext fun i => ?_)
  let Ai := A.submatrix (Option.rec i f) (Option.rec j₀ g)
  have (s : Intˣ) : Ai.detp s = ∑ j, (Aj j).detp (-s) * A.col (g j) i + D.detp s * A.col j₀ i := by
    simp_rw [mul_comm]; rw [detp_option_expand_row_none, add_comm]
    congr!; aesop (add simp Function.update)
  have (a b : R) : (v a b).linearCombination R A.col i = a * Ai.detp 1 + b * Ai.detp (-1) := by
    simp [v, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, add_add_add_comm, mul_add, this]
  simpa [this, IsDetpBalanced, ← submatrix_submatrix] using
    ih (Option.rec i f ∘ finSuccEquiv r) (Option.rec j₀ g ∘ finSuccEquiv r)

中文:
定理 非奇异.of_linearIndependent_col
  条件: (ind : LinearIndependent R A.col)
  结论: A.非奇异
  证明: by
  intro a b bal
  let P (r : Nat) : Prop := forall f g : Fin r -> n, (A.submatrix f g).IsDetpBalanced a b
  suffices h : P 0 by simpa [IsDetpBalanced] using h Fin.elim0 Fin.elim0
refine Nat.decreasingInduction' (n := Fintype.card n) (fun r _ _ ih f g => ?_) (Nat.zero_le _)
    bal.submatrix_of_card_le (Fintype.card_fin _).ge
  by_cases hg : g.Surjective
  · exact bal.submatrix_of_card_le (Fintype.card_le_of_surjective g hg) f g
  obtain ⟨j₀, h₀⟩ := by simpa [Function.Surjective] using hg
  let D := A.submatrix f g
  let Aj (j : Fin r) := A.submatrix f (Function.update g j j₀)
  let v (a b : R) : n ->₀ R := ∑ j, .single (g j) (a * (Aj j).detp (-1) + b * (Aj j).detp 1) +
    .single j₀ (a * D.detp 1 + b * D.detp (-1))
  suffices h : v a b = v b a by simpa [IsDetpBalanced, v, h₀] using congr($h j₀)
  refine ind (funext fun i => ?_)
  let Ai := A.submatrix (Option.rec i f) (Option.rec j₀ g)
  have (s : Intˣ) : Ai.detp s = ∑ j, (Aj j).detp (-s) * A.col (g j) i + D.detp s * A.col j₀ i := by
    simp_rw [mul_comm]; rw [detp_option_expand_row_none, add_comm]
    congr!; aesop (add simp Function.update)
  have (a b : R) : (v a b).linearCombination R A.col i = a * Ai.detp 1 + b * Ai.detp (-1) := by
    simp [v, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, add_add_add_comm, mul_add, this]
  simpa [this, IsDetpBalanced, ← submatrix_submatrix] using
    ih (Option.rec i f ∘ finSuccEquiv r) (Option.rec j₀ g ∘ finSuccEquiv r)

Depends on / 依赖: A.submatrix, Fin.elim0, Fintype, Fintype.card, Fintype.card_fin, Fintype.card_le_of_surjective, Function, Function.Surjective, IsDetpBalanced, Nat.decreasingInduction, Nat.zero_le, Surjective, bal.submatrix_of_card_le, card_fin, card_le_of_surjective, decreasingInduction, g.Surjective, submatrix, submatrix_of_card_le, zero_le
-/
theorem Nonsingular.of_linearIndependent_col (ind : LinearIndependent R A.col) : A.Nonsingular := by
  intro a b bal
  let P (r : Nat) : Prop := forall f g : Fin r -> n, (A.submatrix f g).IsDetpBalanced a b
  suffices h : P 0 by simpa [IsDetpBalanced] using h Fin.elim0 Fin.elim0
refine Nat.decreasingInduction' (n := Fintype.card n) (fun r _ _ ih f g => ?_) (Nat.zero_le _)
    bal.submatrix_of_card_le (Fintype.card_fin _).ge
  by_cases hg : g.Surjective
  · exact bal.submatrix_of_card_le (Fintype.card_le_of_surjective g hg) f g
  obtain ⟨j₀, h₀⟩ := by simpa [Function.Surjective] using hg
  let D := A.submatrix f g
  let Aj (j : Fin r) := A.submatrix f (Function.update g j j₀)
  let v (a b : R) : n ->₀ R := ∑ j, .single (g j) (a * (Aj j).detp (-1) + b * (Aj j).detp 1) +
    .single j₀ (a * D.detp 1 + b * D.detp (-1))
  suffices h : v a b = v b a by simpa [IsDetpBalanced, v, h₀] using congr($h j₀)
  refine ind (funext fun i => ?_)
  let Ai := A.submatrix (Option.rec i f) (Option.rec j₀ g)
  have (s : Intˣ) : Ai.detp s = ∑ j, (Aj j).detp (-s) * A.col (g j) i + D.detp s * A.col j₀ i := by
    simp_rw [mul_comm]; rw [detp_option_expand_row_none, add_comm]
    congr!; aesop (add simp Function.update)
  have (a b : R) : (v a b).linearCombination R A.col i = a * Ai.detp 1 + b * Ai.detp (-1) := by
    simp [v, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, add_add_add_comm, mul_add, this]
  simpa [this, IsDetpBalanced, ← submatrix_submatrix] using
    ih (Option.rec i f ∘ finSuccEquiv r) (Option.rec j₀ g ∘ finSuccEquiv r)

/--
theorem `Nonsingular.of_linearIndependent_row` / 定理 `Nonsingular.of_linearIndependent_row`

English:
theorem Nonsingular.of_linearIndependent_row
  given: (ind : LinearIndependent R A.row)
  statement: A.Nonsingular
  proof: by
  simpa using Nonsingular.of_linearIndependent_col (A := Aᵀ) ind

中文:
定理 非奇异.of_linearIndependent_row
  条件: (ind : LinearIndependent R A.row)
  结论: A.非奇异
  证明: by
  simpa using Nonsingular.of_linearIndependent_col (A := Aᵀ) ind

Depends on / 依赖: Nonsingular, Nonsingular.of_linearIndependent_col, of_linearIndependent_col
-/
theorem Nonsingular.of_linearIndependent_row (ind : LinearIndependent R A.row) : A.Nonsingular := by
  simpa using Nonsingular.of_linearIndependent_col (A := Aᵀ) ind

/--
theorem `Nonsingular.of_leftRegular` / 定理 `Nonsingular.of_leftRegular`

English:
theorem Nonsingular.of_leftRegular
  given: (h : IsLeftRegular A)
  statement: A.Nonsingular
  proof: .of_linearIndependent_col (by rwa [← mulVec_injective_iff, ← isLeftRegular_iff_mulVec_injective])

中文:
定理 非奇异.of_leftRegular
  条件: (h : IsLeftRegular A)
  结论: A.非奇异
  证明: .of_linearIndependent_col (by rwa [← mulVec_injective_iff, ← isLeftRegular_iff_mulVec_injective])

Depends on / 依赖: isLeftRegular_iff_mulVec_injective, mulVec_injective_iff, of_linearIndependent_col
-/
theorem Nonsingular.of_leftRegular (h : IsLeftRegular A) : A.Nonsingular :=
  .of_linearIndependent_col (by rwa [← mulVec_injective_iff, ← isLeftRegular_iff_mulVec_injective])

/--
theorem `Nonsingular.of_rightRegular` / 定理 `Nonsingular.of_rightRegular`

English:
theorem Nonsingular.of_rightRegular
  given: (h : IsRightRegular A)
  statement: A.Nonsingular
  proof: .of_linearIndependent_row (by rwa [← vecMul_injective_iff, ← isRightRegular_iff_vecMul_injective])

中文:
定理 非奇异.of_rightRegular
  条件: (h : IsRightRegular A)
  结论: A.非奇异
  证明: .of_linearIndependent_row (by rwa [← vecMul_injective_iff, ← isRightRegular_iff_vecMul_injective])

Depends on / 依赖: isRightRegular_iff_vecMul_injective, of_linearIndependent_row, vecMul_injective_iff
-/
theorem Nonsingular.of_rightRegular (h : IsRightRegular A) : A.Nonsingular :=
  .of_linearIndependent_row (by rwa [← vecMul_injective_iff, ← isRightRegular_iff_vecMul_injective])

variable [IsCancelAdd R]

/--
theorem `Nonsingular.linearIndependent_col` / 定理 `Nonsingular.linearIndependent_col`

English:
theorem Nonsingular.linearIndependent_col
  given: (hA : A.Nonsingular)
  statement: LinearIndependent R A.col
  proof: mulVec_injective_iff.mp fun x y eq => funext fun k => hA _ _ show _ = _ by
    have h v : ((A.adjp 1 * A + A.detp (-1) • 1) *ᵥ v) k =
        ((A.adjp (-1) * A + A.detp 1 • 1) *ᵥ v) k := by
      congr 1; ext k i
      obtain (h | h) := eq_or_ne k i <;> simp [adjp_mul_apply_eq, add_comm, adjp_mul_apply_ne, h]
    simp [add_mulVec, smul_mulVec, ← mulVec_mulVec] at h; grind

中文:
定理 非奇异.linearIndependent_col
  条件: (hA : A.非奇异)
  结论: LinearIndependent R A.col
  证明: mulVec_injective_iff.mp fun x y eq => funext fun k => hA _ _ show _ = _ by
    have h v : ((A.adjp 1 * A + A.detp (-1) • 1) *ᵥ v) k =
        ((A.adjp (-1) * A + A.detp 1 • 1) *ᵥ v) k := by
      congr 1; ext k i
      obtain (h | h) := eq_or_ne k i <;> simp [adjp_mul_apply_eq, add_comm, adjp_mul_apply_ne, h]
    simp [add_mulVec, smul_mulVec, ← mulVec_mulVec] at h; grind

Depends on / 依赖: A.adjp, A.detp, add_comm, add_mulVec, adjp_mul_apply_eq, adjp_mul_apply_ne, eq_or_ne, mulVec_injective_iff, mulVec_injective_iff.mp, mulVec_mulVec, smul_mulVec
-/
theorem Nonsingular.linearIndependent_col (hA : A.Nonsingular) : LinearIndependent R A.col :=
mulVec_injective_iff.mp fun x y eq => funext fun k => hA _ _ show _ = _ by
    have h v : ((A.adjp 1 * A + A.detp (-1) • 1) *ᵥ v) k =
        ((A.adjp (-1) * A + A.detp 1 • 1) *ᵥ v) k := by
      congr 1; ext k i
      obtain (h | h) := eq_or_ne k i <;> simp [adjp_mul_apply_eq, add_comm, adjp_mul_apply_ne, h]
    simp [add_mulVec, smul_mulVec, ← mulVec_mulVec] at h; grind

/--
theorem `Nonsingular.linearIndependent_row` / 定理 `Nonsingular.linearIndependent_row`

English:
theorem Nonsingular.linearIndependent_row
  given: (hA : A.Nonsingular)
  statement: LinearIndependent R A.row
  proof: hA.transpose.linearIndependent_col

中文:
定理 非奇异.linearIndependent_row
  条件: (hA : A.非奇异)
  结论: LinearIndependent R A.row
  证明: hA.transpose.linearIndependent_col

Depends on / 依赖: hA.transpose.linearIndependent_col, linearIndependent_col, transpose
-/
theorem Nonsingular.linearIndependent_row (hA : A.Nonsingular) : LinearIndependent R A.row :=
  hA.transpose.linearIndependent_col

/--
theorem `linearIndependent_col_iff` / 定理 `linearIndependent_col_iff`

English:
theorem linearIndependent_col_iff
  statement: LinearIndependent R A.col ↔ A.Nonsingular
  proof: ⟨.of_linearIndependent_col, (·.linearIndependent_col)⟩

中文:
定理 linearIndependent_col_iff
  结论: LinearIndependent R A.col ↔ A.非奇异
  证明: ⟨.of_linearIndependent_col, (·.linearIndependent_col)⟩

Depends on / 依赖: linearIndependent_col, of_linearIndependent_col
-/
theorem linearIndependent_col_iff : LinearIndependent R A.col ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_col, (·.linearIndependent_col)⟩

/--
theorem `linearIndependent_row_iff` / 定理 `linearIndependent_row_iff`

English:
theorem linearIndependent_row_iff
  statement: LinearIndependent R A.row ↔ A.Nonsingular
  proof: ⟨.of_linearIndependent_row, (·.linearIndependent_row)⟩

中文:
定理 linearIndependent_row_iff
  结论: LinearIndependent R A.row ↔ A.非奇异
  证明: ⟨.of_linearIndependent_row, (·.linearIndependent_row)⟩

Depends on / 依赖: linearIndependent_row, of_linearIndependent_row
-/
theorem linearIndependent_row_iff : LinearIndependent R A.row ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_row, (·.linearIndependent_row)⟩

/--
theorem `isLeftRegular_iff_nonsingular` / 定理 `isLeftRegular_iff_nonsingular`

English:
theorem isLeftRegular_iff_nonsingular
  statement: IsLeftRegular A ↔ A.Nonsingular
  proof: by
  rw [isLeftRegular_iff_mulVec_injective]; rw [mulVec_injective_iff]; rw [linearIndependent_col_iff]

中文:
定理 isLeftRegular_iff_nonsingular
  结论: IsLeftRegular A ↔ A.非奇异
  证明: by
  rw [isLeftRegular_iff_mulVec_injective]; rw [mulVec_injective_iff]; rw [linearIndependent_col_iff]

Depends on / 依赖: isLeftRegular_iff_mulVec_injective, linearIndependent_col_iff, mulVec_injective_iff
-/
theorem isLeftRegular_iff_nonsingular : IsLeftRegular A ↔ A.Nonsingular := by
  rw [isLeftRegular_iff_mulVec_injective]; rw [mulVec_injective_iff]; rw [linearIndependent_col_iff]

/--
theorem `isRightRegular_iff_nonsingular` / 定理 `isRightRegular_iff_nonsingular`

English:
theorem isRightRegular_iff_nonsingular
  statement: IsRightRegular A ↔ A.Nonsingular
  proof: by
  rw [isRightRegular_iff_vecMul_injective]; rw [vecMul_injective_iff]; rw [linearIndependent_row_iff]

中文:
定理 isRightRegular_iff_nonsingular
  结论: IsRightRegular A ↔ A.非奇异
  证明: by
  rw [isRightRegular_iff_vecMul_injective]; rw [vecMul_injective_iff]; rw [linearIndependent_row_iff]

Depends on / 依赖: isRightRegular_iff_vecMul_injective, linearIndependent_row_iff, vecMul_injective_iff
-/
theorem isRightRegular_iff_nonsingular : IsRightRegular A ↔ A.Nonsingular := by
  rw [isRightRegular_iff_vecMul_injective]; rw [vecMul_injective_iff]; rw [linearIndependent_row_iff]

/--
lemma `Nonsingular.mul` / 引理 `Nonsingular.mul`

English:
lemma Nonsingular.mul
  given: {B : Matrix n n R} (hA : A.Nonsingular) (hB : B.Nonsingular)
  proof: by
  rw [← isLeftRegular_iff_nonsingular] at *
  exact hA.mul hB

中文:
引理 非奇异.mul
  条件: {B : 矩阵 n n R} (hA : A.非奇异) (hB : B.非奇异)
  证明: by
  rw [← isLeftRegular_iff_nonsingular] at *
  exact hA.mul hB

Depends on / 依赖: hA.mul, isLeftRegular_iff_nonsingular
-/
lemma Nonsingular.mul {B : Matrix n n R} (hA : A.Nonsingular) (hB : B.Nonsingular) :
    (A * B).Nonsingular := by
  rw [← isLeftRegular_iff_nonsingular] at *
  exact hA.mul hB

/--
lemma `nonsingular_mul_iff` / 引理 `nonsingular_mul_iff`

English:
lemma nonsingular_mul_iff
  given: {A B : Matrix n n R}
  proof: ⟨isRightRegular_iff_nonsingular.mp .of_mul isRightRegular_iff_nonsingular.mpr h,
isLeftRegular_iff_nonsingular.mp .of_mul isLeftRegular_iff_nonsingular.mpr h⟩
  mpr h := h.1.mul h.2

中文:
引理 nonsingular_mul_iff
  条件: {A B : 矩阵 n n R}
  证明: ⟨isRightRegular_iff_nonsingular.mp .of_mul isRightRegular_iff_nonsingular.mpr h,
isLeftRegular_iff_nonsingular.mp .of_mul isLeftRegular_iff_nonsingular.mpr h⟩
  mpr h := h.1.mul h.2

Depends on / 依赖: isRightRegular_iff_nonsingular, isRightRegular_iff_nonsingular.mp, isRightRegular_iff_nonsingular.mpr, of_mul
-/
lemma nonsingular_mul_iff {A B : Matrix n n R} :
    (A * B).Nonsingular ↔ A.Nonsingular ∧ B.Nonsingular where
mp h := ⟨isRightRegular_iff_nonsingular.mp .of_mul isRightRegular_iff_nonsingular.mpr h,
isLeftRegular_iff_nonsingular.mp .of_mul isLeftRegular_iff_nonsingular.mpr h⟩
  mpr h := h.1.mul h.2

/--
lemma `Nonsingular.pow` / 引理 `Nonsingular.pow`

English:
lemma Nonsingular.pow
  given: (hA : A.Nonsingular)
  statement: forall k, (A ^ k).Nonsingular

中文:
引理 非奇异.pow
  条件: (hA : A.非奇异)
  结论: 对任意 k, (A ^ k).非奇异
-/
lemma Nonsingular.pow (hA : A.Nonsingular) : forall k, (A ^ k).Nonsingular
  | 0 => by simp
  | k + 1 => by simp [pow_succ, (hA.pow k).mul hA]

omit [DecidableEq n] in
/--
theorem `isLeftRegular_iff_isRightRegular` / 定理 `isLeftRegular_iff_isRightRegular`

English:
theorem isLeftRegular_iff_isRightRegular
  statement: IsLeftRegular A ↔ IsRightRegular A
  proof: by
  classical rw [isLeftRegular_iff_nonsingular, isRightRegular_iff_nonsingular]

omit [DecidableEq n] [Fintype n] in

中文:
定理 isLeftRegular_iff_isRightRegular
  结论: IsLeftRegular A ↔ IsRightRegular A
  证明: by
  classical rw [isLeftRegular_iff_nonsingular, isRightRegular_iff_nonsingular]

omit [DecidableEq n] [Fintype n] in

Depends on / 依赖: classical, isLeftRegular_iff_nonsingular, isRightRegular_iff_nonsingular
-/
theorem isLeftRegular_iff_isRightRegular : IsLeftRegular A ↔ IsRightRegular A := by
  classical rw [isLeftRegular_iff_nonsingular, isRightRegular_iff_nonsingular]

omit [DecidableEq n] [Fintype n] in
/--
theorem `linearIndependent_col_iff_row` / 定理 `linearIndependent_col_iff_row`

English:
theorem linearIndependent_col_iff_row
  given: [Finite n]
  proof: by
  have := Fintype.ofFinite
  classical rw [linearIndependent_col_iff, linearIndependent_row_iff]

中文:
定理 linearIndependent_col_iff_row
  条件: [有限 n]
  证明: by
  have := Fintype.ofFinite
  classical rw [linearIndependent_col_iff, linearIndependent_row_iff]

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, linearIndependent_col_iff, linearIndependent_row_iff, ofFinite
-/
theorem linearIndependent_col_iff_row [Finite n] :
    LinearIndependent R A.col ↔ LinearIndependent R A.row := by
  have := Fintype.ofFinite
  classical rw [linearIndependent_col_iff, linearIndependent_row_iff]

end Matrix

open Matrix

/-- A nontrivial commutative semiring satisfies the strong rank condition. -/
instance (priority := 100) CommSemiring.strongRankCondition_of_nontrivial [Nontrivial R] :
    StrongRankCondition R where
  le_of_fin_injective {n m} f hf := by
    let g : (Fin m -> R) ->ₗ[R] (Fin n -> R) := .pi fun i => if h : i < m then .proj ⟨i, h⟩ else 0
    by_contra! hnm
    have hg : Function.Injective g := fun x y eq => funext fun i => by
      simpa [g] using congr($eq ⟨i, i.prop.trans hnm⟩)
    let A := (g ∘ₗ f).toMatrix'
have hA : A.Nonsingular := .of_linearIndependent_col mulVec_injective_iff.mp by
      convert hg.comp hf; ext; simp [A, g]
    have : A.row ⟨m, hnm⟩ = 0 := by ext; simp [A, g]
    exact not_subsingleton R
      ⟨by simpa [Nonsingular, IsDetpBalanced, detp_eq_of_row_eq_zero _ this] using hA⟩
