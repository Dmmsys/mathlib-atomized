/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery, Seed Prover, Huanyu Zheng
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

* `Matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
* `symplecticGroup`: the group of symplectic matrices

## Implementation Notes

* `SymplecticGroup.det_eq_one`: Symplectic matrices have determinant 1. The proof strategy
comes in two steps:

1. Consider a symplectic matrix `M` over a local ring, we can construct a matrix of the
form `fromBlocks 1 X 0 1` s.t. the upper-left block of `(fromBlocks 1 X 0 1) * M` is invertible.
From this we can calculate the determinant.

2. For a symplectic matrix `M` over general commutative ring `R`, we note that by step 1,
`M.det - 1 = 0` in any localization at a maximal ideal in `R`. Therefore `M.det = 1` in `R`.

Developing the proof in two steps is helpful, since the local ring hypothesis allows us to
construct the desired `X` in step 1 at the residue field level, and lift back to the ring while
keeping the upper-left block invertible.

## TODO
* For `n = 1` the symplectic group coincides with the special linear group.
-/

@[expose] public section


open Matrix

variable {l R : Type*}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

section JMatrixLemmas

/--
Definition of `J` / `J` 的定义

English:
definition J
  signature: : Matrix (l oplus l) (l oplus l) R
  body: Matrix.fromBlocks 0 (-1) 1 0

中文:
定义 J
  签名: : 矩阵 (l oplus l) (l oplus l) R
  定义体: Matrix.fromBlocks 0 (-1) 1 0

Depends on / 依赖: Matrix, Matrix.fromBlocks, fromBlocks
-/
def J : Matrix (l oplus l) (l oplus l) R :=
  Matrix.fromBlocks 0 (-1) 1 0

variable {R} in
@[simp]
/--
theorem `map_J` / 定理 `map_J`

English:
theorem map_J
  statement: {F S : Type*} [CommRing S] [FunLike F R S]
  proof: by
  simp [J, fromBlocks_map, Matrix.map_neg]

@[simp]

中文:
定理 map_J
  结论: {F S : 类型} [交换环 S] [函数状 F R S]
  证明: by
  simp [J, fromBlocks_map, Matrix.map_neg]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_neg, fromBlocks_map, map_neg
-/
theorem map_J {F S : Type*} [CommRing S] [FunLike F R S]
    [AddMonoidHomClass F R S] [OneHomClass F R S] (f : F) :
    (J l R).map f = J l S := by
  simp [J, fromBlocks_map, Matrix.map_neg]

@[simp]
/--
theorem `J_transpose` / 定理 `J_transpose`

English:
theorem J_transpose
  statement: (J l R)ᵀ = -J l R
  proof: by
  rw [J]; rw [fromBlocks_transpose]; rw [← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l oplus l) (l oplus l) R)]; rw [fromBlocks_smul]; rw [Matrix.transpose_zero]; rw [Matrix.transpose_one]; rw [transpose_neg]
  simp [fromBlocks]

中文:
定理 J_transpose
  结论: (J l R)ᵀ = -J l R
  证明: by
  rw [J]; rw [fromBlocks_transpose]; rw [← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l oplus l) (l oplus l) R)]; rw [fromBlocks_smul]; rw [Matrix.transpose_zero]; rw [Matrix.transpose_one]; rw [transpose_neg]
  simp [fromBlocks]

Depends on / 依赖: Matrix, Matrix.transpose_one, Matrix.transpose_zero, fromBlocks, fromBlocks_smul, fromBlocks_transpose, neg_one_smul, transpose_neg, transpose_one, transpose_zero
-/
theorem J_transpose : (J l R)ᵀ = -J l R := by
  rw [J]; rw [fromBlocks_transpose]; rw [← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l oplus l) (l oplus l) R)]; rw [fromBlocks_smul]; rw [Matrix.transpose_zero]; rw [Matrix.transpose_one]; rw [transpose_neg]
  simp [fromBlocks]

variable [Fintype l]

/--
theorem `J_squared` / 定理 `J_squared`

English:
theorem J_squared
  statement: J l R * J l R = -1
  proof: by
  rw [J]; rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero]; rw [← Matrix.fromBlocks_neg]; rw [← fromBlocks_one]

中文:
定理 J_squared
  结论: J l R * J l R = -1
  证明: by
  rw [J]; rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero]; rw [← Matrix.fromBlocks_neg]; rw [← fromBlocks_one]

Depends on / 依赖: Matrix, Matrix.fromBlocks_neg, Matrix.neg_mul, Matrix.one_mul, Matrix.zero_mul, add_zero, fromBlocks_multiply, fromBlocks_neg, fromBlocks_one, neg_mul, neg_zero, one_mul, zero_add, zero_mul
-/
theorem J_squared : J l R * J l R = -1 := by
  rw [J]; rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero]; rw [← Matrix.fromBlocks_neg]; rw [← fromBlocks_one]

/--
theorem `J_inv` / 定理 `J_inv`

English:
theorem J_inv
  statement: (J l R)⁻¹ = -J l R
  proof: by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg]; rw [J_squared]
  exact neg_neg 1

中文:
定理 J_inv
  结论: (J l R)⁻¹ = -J l R
  证明: by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg]; rw [J_squared]
  exact neg_neg 1

Depends on / 依赖: J_squared, Matrix, Matrix.inv_eq_right_inv, Matrix.mul_neg, inv_eq_right_inv, mul_neg, neg_neg
-/
theorem J_inv : (J l R)⁻¹ = -J l R := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg]; rw [J_squared]
  exact neg_neg 1

/--
theorem `J_det_mul_J_det` / 定理 `J_det_mul_J_det`

English:
theorem J_det_mul_J_det
  statement: det (J l R) * det (J l R) = 1
  proof: by
  rw [← det_mul]; rw [J_squared]; rw [← one_smul R (-1 : Matrix _ _ R)]; rw [smul_neg]; rw [← neg_smul]; rw [det_smul]; rw [Fintype.card_sum]; rw [det_one]; rw [mul_one]
  apply Even.neg_one_pow
  exact Even.add_self _

中文:
定理 J_det_mul_J_det
  结论: det (J l R) * det (J l R) = 1
  证明: by
  rw [← det_mul]; rw [J_squared]; rw [← one_smul R (-1 : Matrix _ _ R)]; rw [smul_neg]; rw [← neg_smul]; rw [det_smul]; rw [Fintype.card_sum]; rw [det_one]; rw [mul_one]
  apply Even.neg_one_pow
  exact Even.add_self _

Depends on / 依赖: Even.add_self, Even.neg_one_pow, Fintype, Fintype.card_sum, J_squared, Matrix, add_self, card_sum, det_mul, det_one, det_smul, mul_one, neg_one_pow, neg_smul, one_smul, smul_neg
-/
theorem J_det_mul_J_det : det (J l R) * det (J l R) = 1 := by
  rw [← det_mul]; rw [J_squared]; rw [← one_smul R (-1 : Matrix _ _ R)]; rw [smul_neg]; rw [← neg_smul]; rw [det_smul]; rw [Fintype.card_sum]; rw [det_one]; rw [mul_one]
  apply Even.neg_one_pow
  exact Even.add_self _

/--
theorem `isUnit_det_J` / 定理 `isUnit_det_J`

English:
theorem isUnit_det_J
  statement: IsUnit (det (J l R))
  proof: isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

中文:
定理 isUnit_det_J
  结论: 是单位 (det (J l R))
  证明: isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

Depends on / 依赖: J_det_mul_J_det, isUnit_iff_exists_inv, isUnit_iff_exists_inv.mpr
-/
theorem isUnit_det_J : IsUnit (det (J l R)) :=
  isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

end JMatrixLemmas

variable [Fintype l]

/-- The group of symplectic matrices over a ring `R`. -/
@[wikidata Q936434]
/--
Definition of `symplecticGroup` / `symplecticGroup` 的定义

English:
definition symplecticGroup
  signature: : Submonoid (Matrix (l oplus l) (l oplus l) R) where
  body: { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc]; rw [a.mul_assoc]; rw [a.mul_assoc]; rw [hb]
    exact ha
  one_mem' := by simp

中文:
定义 symplecticGroup
  签名: : 子幺半群 (矩阵 (l oplus l) (l oplus l) R) where
  定义体: { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc]; rw [a.mul_assoc]; rw [a.mul_assoc]; rw [hb]
    exact ha
  one_mem' := by simp
-/
def symplecticGroup : Submonoid (Matrix (l oplus l) (l oplus l) R) where
  carrier := { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc]; rw [a.mul_assoc]; rw [a.mul_assoc]; rw [hb]
    exact ha
  one_mem' := by simp

end Matrix

namespace SymplecticGroup

variable [DecidableEq l] [Fintype l] [CommRing R]

open Matrix

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {A : Matrix (l oplus l) (l oplus l) R}
  proof: by simp [symplecticGroup]

中文:
定理 mem_iff
  条件: {A : 矩阵 (l oplus l) (l oplus l) R}
  证明: by simp [symplecticGroup]

Depends on / 依赖: symplecticGroup
-/
theorem mem_iff {A : Matrix (l oplus l) (l oplus l) R} :
    A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R := by simp [symplecticGroup]

/--
Instance `coeMatrix` / 实例 `coeMatrix`

English:
instance coeMatrix
  signature: : Coe (symplecticGroup l R) (Matrix (l oplus l) (l oplus l) R)
  body: ⟨Subtype.val⟩

中文:
实例 coeMatrix
  签名: : Coe (symplecticGroup l R) (矩阵 (l oplus l) (l oplus l) R)
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance coeMatrix : Coe (symplecticGroup l R) (Matrix (l oplus l) (l oplus l) R) :=
  ⟨Subtype.val⟩

section SymplecticJ

variable (l) (R)

/--
theorem `J_mem` / 定理 `J_mem`

English:
theorem J_mem
  statement: J l R in symplecticGroup l R
  proof: by
  rw [mem_iff]; rw [J]; rw [fromBlocks_multiply]; rw [fromBlocks_transpose]; rw [fromBlocks_multiply]
  simp

中文:
定理 J_mem
  结论: J l R in symplecticGroup l R
  证明: by
  rw [mem_iff]; rw [J]; rw [fromBlocks_multiply]; rw [fromBlocks_transpose]; rw [fromBlocks_multiply]
  simp

Depends on / 依赖: fromBlocks_multiply, fromBlocks_transpose, mem_iff
-/
theorem J_mem : J l R in symplecticGroup l R := by
  rw [mem_iff]; rw [J]; rw [fromBlocks_multiply]; rw [fromBlocks_transpose]; rw [fromBlocks_multiply]
  simp

/--
Definition of `symJ` / `symJ` 的定义

English:
definition symJ
  signature: : symplecticGroup l R
  body: ⟨J l R, J_mem l R⟩

中文:
定义 symJ
  签名: : symplecticGroup l R
  定义体: ⟨J l R, J_mem l R⟩

Depends on / 依赖: J_mem
-/
def symJ : symplecticGroup l R :=
  ⟨J l R, J_mem l R⟩

variable {l} {R}

@[simp]
/--
theorem `coe_J` / 定理 `coe_J`

English:
theorem coe_J
  statement: ↑(symJ l R) = J l R
  proof: rfl

中文:
定理 coe_J
  结论: ↑(symJ l R) = J l R
  证明: rfl
-/
theorem coe_J : ↑(symJ l R) = J l R := rfl

end SymplecticJ

variable {A : Matrix (l oplus l) (l oplus l) R}

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: (h : A in symplecticGroup l R)
  statement: -A in symplecticGroup l R
  proof: by
  rw [mem_iff] at h ⊢
  simp [h]

中文:
定理 neg_mem
  条件: (h : A in symplecticGroup l R)
  结论: -A in symplecticGroup l R
  证明: by
  rw [mem_iff] at h ⊢
  simp [h]

Depends on / 依赖: mem_iff
-/
theorem neg_mem (h : A in symplecticGroup l R) : -A in symplecticGroup l R := by
  rw [mem_iff] at h ⊢
  simp [h]

/--
theorem `symplectic_det` / 定理 `symplectic_det`

English:
theorem symplectic_det
  given: (hA : A in symplecticGroup l R)
  statement: IsUnit det A
  proof: by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine (isUnit_det_J l R).mul_left_cancel ?_
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det]; rw [mul_assoc] at hA
  exact hA

中文:
定理 symplectic_det
  条件: (hA : A in symplecticGroup l R)
  结论: 是单位 det A
  证明: by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine (isUnit_det_J l R).mul_left_cancel ?_
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det]; rw [mul_assoc] at hA
  exact hA

Depends on / 依赖: A.det, apply_fun, det_mul, det_transpose, isUnit_det_J, isUnit_iff_exists_inv, mem_iff, mul_assoc, mul_comm, mul_left_cancel, mul_one
-/
theorem symplectic_det (hA : A in symplecticGroup l R) : IsUnit det A := by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine (isUnit_det_J l R).mul_left_cancel ?_
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det]; rw [mul_assoc] at hA
  exact hA

/--
theorem `map_mem` / 定理 `map_mem`

English:
theorem map_mem
  statement: {F S : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
  proof: by
  simp_rw [mem_iff, ← transpose_map, ← map_J _ f, ← Matrix.map_mul, mem_iff.mp hA]

中文:
定理 map_mem
  结论: {F S : 类型} [交换环 S] [函数状 F R S] [环态射类 F R S]
  证明: by
  simp_rw [mem_iff, ← transpose_map, ← map_J _ f, ← Matrix.map_mul, mem_iff.mp hA]

Depends on / 依赖: Matrix, Matrix.map_mul, map_J, map_mul, mem_iff, mem_iff.mp, simp_rw, transpose_map
-/
theorem map_mem {F S : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (hA : A in symplecticGroup l R) (f : F) : A.map f in symplecticGroup l S := by
  simp_rw [mem_iff, ← transpose_map, ← map_J _ f, ← Matrix.map_mul, mem_iff.mp hA]

/--
theorem `transpose_mem` / 定理 `transpose_mem`

English:
theorem transpose_mem
  given: (hA : A in symplecticGroup l R)
  statement: Aᵀ in symplecticGroup l R
  proof: by
  rw [mem_iff] at hA ⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ * J l R * A = (-Aᵀ) * (J l R)⁻¹ * A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) * (A * J l R * Aᵀ)⁻¹ * A := by rw [hA]
    _ = -(Aᵀ * (Aᵀ⁻¹ * (J l R)⁻¹)) * A⁻¹ * A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT]; rw [nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]

@[simp]

中文:
定理 transpose_mem
  条件: (hA : A in symplecticGroup l R)
  结论: Aᵀ in symplecticGroup l R
  证明: by
  rw [mem_iff] at hA ⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ * J l R * A = (-Aᵀ) * (J l R)⁻¹ * A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) * (A * J l R * Aᵀ)⁻¹ * A := by rw [hA]
    _ = -(Aᵀ * (Aᵀ⁻¹ * (J l R)⁻¹)) * A⁻¹ * A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT]; rw [nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]

@[simp]

Depends on / 依赖: IsUnit, J_inv, Matrix, Matrix.det_transpose, Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.neg_mul, det_transpose, mem_iff, mul_assoc, mul_inv_rev, mul_nonsing_inv_cancel_left, neg_mul, nonsing_inv_mul_cancel_right, symplectic_det, transpose_transpose
-/
theorem transpose_mem (hA : A in symplecticGroup l R) : Aᵀ in symplecticGroup l R := by
  rw [mem_iff] at hA ⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ * J l R * A = (-Aᵀ) * (J l R)⁻¹ * A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) * (A * J l R * Aᵀ)⁻¹ * A := by rw [hA]
    _ = -(Aᵀ * (Aᵀ⁻¹ * (J l R)⁻¹)) * A⁻¹ * A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT]; rw [nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]

@[simp]
/--
theorem `transpose_mem_iff` / 定理 `transpose_mem_iff`

English:
theorem transpose_mem_iff
  statement: Aᵀ in symplecticGroup l R ↔ A in symplecticGroup l R
  proof: ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩

中文:
定理 transpose_mem_iff
  结论: Aᵀ in symplecticGroup l R ↔ A in symplecticGroup l R
  证明: ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩

Depends on / 依赖: transpose_mem
-/
theorem transpose_mem_iff : Aᵀ in symplecticGroup l R ↔ A in symplecticGroup l R :=
  ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩

/--
theorem `mem_iff'` / 定理 `mem_iff'`

English:
theorem mem_iff'
  statement: A in symplecticGroup l R ↔ Aᵀ * J l R * A = J l R
  proof: by
  rw [← transpose_mem_iff]; rw [mem_iff]; rw [transpose_transpose]

中文:
定理 mem_iff'
  结论: A in symplecticGroup l R ↔ Aᵀ * J l R * A = J l R
  证明: by
  rw [← transpose_mem_iff]; rw [mem_iff]; rw [transpose_transpose]

Depends on / 依赖: mem_iff, transpose_mem_iff, transpose_transpose
-/
theorem mem_iff' : A in symplecticGroup l R ↔ Aᵀ * J l R * A = J l R := by
  rw [← transpose_mem_iff]; rw [mem_iff]; rw [transpose_transpose]

/--
Instance `hasInv` / 实例 `hasInv`

English:
instance hasInv
  signature: : Inv (symplecticGroup l R) where
  body: ⟨(-J l R) * (A : Matrix (l oplus l) (l oplus l) R)ᵀ * J l R,
mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) J_mem _ _⟩

中文:
实例 hasInv
  签名: : 取逆 (symplecticGroup l R) where
  定义体: ⟨(-J l R) * (A : Matrix (l oplus l) (l oplus l) R)ᵀ * J l R,
mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) J_mem _ _⟩

Depends on / 依赖: Matrix
-/
instance hasInv : Inv (symplecticGroup l R) where
  inv A := ⟨(-J l R) * (A : Matrix (l oplus l) (l oplus l) R)ᵀ * J l R,
mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) J_mem _ _⟩

/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (A : symplecticGroup l R)
  statement: (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A)ᵀ * J l R
  proof: rfl

中文:
定理 coe_inv
  条件: (A : symplecticGroup l R)
  结论: (↑A⁻¹ : 矩阵 _ _ _) = (-J l R) * (↑A)ᵀ * J l R
  证明: rfl
-/
theorem coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A)ᵀ * J l R := rfl

/--
theorem `inv_left_mul_aux` / 定理 `inv_left_mul_aux`

English:
theorem inv_left_mul_aux
  given: (hA : A in symplecticGroup l R)
  statement: -(J l R * Aᵀ * J l R * A) = 1
  proof: calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]

中文:
定理 inv_left_mul_aux
  条件: (hA : A in symplecticGroup l R)
  结论: -(J l R * Aᵀ * J l R * A) = 1
  证明: calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]

Depends on / 依赖: J_squared, Matrix, Matrix.mul_assoc, Matrix.neg_mul, mem_iff, mul_assoc, neg_mul, neg_smul, neg_smul_neg, one_smul
-/
theorem inv_left_mul_aux (hA : A in symplecticGroup l R) : -(J l R * Aᵀ * J l R * A) = 1 :=
  calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]

/--
theorem `coe_inv'` / 定理 `coe_inv'`

English:
theorem coe_inv'
  given: (A : symplecticGroup l R)
  statement: (↑A⁻¹ : Matrix (l oplus l) (l oplus l) R) = (↑A)⁻¹
  proof: by
  refine (coe_inv A).trans (inv_eq_left_inv ?_).symm
  simp [inv_left_mul_aux]

中文:
定理 coe_inv'
  条件: (A : symplecticGroup l R)
  结论: (↑A⁻¹ : 矩阵 (l oplus l) (l oplus l) R) = (↑A)⁻¹
  证明: by
  refine (coe_inv A).trans (inv_eq_left_inv ?_).symm
  simp [inv_left_mul_aux]

Depends on / 依赖: coe_inv, inv_eq_left_inv, inv_left_mul_aux
-/
theorem coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (l oplus l) (l oplus l) R) = (↑A)⁻¹ := by
  refine (coe_inv A).trans (inv_eq_left_inv ?_).symm
  simp [inv_left_mul_aux]

/--
theorem `inv_eq_symplectic_inv` / 定理 `inv_eq_symplectic_inv`

English:
theorem inv_eq_symplectic_inv
  given: (A : Matrix (l oplus l) (l oplus l) R) (hA : A in symplecticGroup l R)
  proof: inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])

中文:
定理 inv_eq_symplectic_inv
  条件: (A : 矩阵 (l oplus l) (l oplus l) R) (hA : A in symplecticGroup l R)
  证明: inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])

Depends on / 依赖: Matrix, Matrix.neg_mul, inv_eq_left_inv, inv_left_mul_aux, neg_mul
-/
theorem inv_eq_symplectic_inv (A : Matrix (l oplus l) (l oplus l) R) (hA : A in symplecticGroup l R) :
    A⁻¹ = (-J l R) * Aᵀ * J l R :=
  inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (symplecticGroup l R)
  body: { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      exact inv_left_mul_aux A.2 }

中文:
实例 :
  签名: 群 (symplecticGroup l R)
  定义体: { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      exact inv_left_mul_aux A.2 }

Depends on / 依赖: Matrix, Matrix.neg_mul, Submonoid, Submonoid.coe_mul, Submonoid.coe_one, Submonoid.toMonoid, Subtype, Subtype.ext, SymplecticGroup, SymplecticGroup.hasInv, coe_inv, coe_mul, coe_one, hasInv, inv_left_mul_aux, inv_mul_cancel, neg_mul, toMonoid
-/
instance : Group (symplecticGroup l R) :=
  { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      exact inv_left_mul_aux A.2 }

section Determinant

variable {A B C D : Matrix l l R}

/--
theorem `fromBlocks_mem_iff` / 定理 `fromBlocks_mem_iff`

English:
theorem fromBlocks_mem_iff
  proof: by
  refine ⟨fun h => ?_, fun h => mem_iff'.2 ?_⟩
  · have h_final : fromBlocks (Cᵀ * A - Aᵀ * C) (Cᵀ * B - Aᵀ * D)
        (Dᵀ * A - Bᵀ * C) (Dᵀ * B - Bᵀ * D) = J l R := by
      simpa [mem_iff, fromBlocks_transpose, J, fromBlocks_multiply,
        sub_eq_add_neg] using transpose_mem h
    obtain ⟨h_eq1, h_eq2, _, h_eq3⟩ := fromBlocks_inj.1 h_final
    exact ⟨(sub_eq_zero.1 h_eq1).symm, (sub_eq_zero.1 h_eq3).symm, by grind⟩
  · simp only [fromBlocks_transpose, J, fromBlocks_multiply, mul_zero, mul_one, zero_add, mul_neg,
      add_zero, neg_mul, ← sub_eq_add_neg, fromBlocks_inj, sub_eq_zero]
    exact ⟨h.1.symm, by grind, by simpa using congr(transpose $(h.2.2)), h.2.1.symm⟩

中文:
定理 fromBlocks_mem_iff
  证明: by
  refine ⟨fun h => ?_, fun h => mem_iff'.2 ?_⟩
  · have h_final : fromBlocks (Cᵀ * A - Aᵀ * C) (Cᵀ * B - Aᵀ * D)
        (Dᵀ * A - Bᵀ * C) (Dᵀ * B - Bᵀ * D) = J l R := by
      simpa [mem_iff, fromBlocks_transpose, J, fromBlocks_multiply,
        sub_eq_add_neg] using transpose_mem h
    obtain ⟨h_eq1, h_eq2, _, h_eq3⟩ := fromBlocks_inj.1 h_final
    exact ⟨(sub_eq_zero.1 h_eq1).symm, (sub_eq_zero.1 h_eq3).symm, by grind⟩
  · simp only [fromBlocks_transpose, J, fromBlocks_multiply, mul_zero, mul_one, zero_add, mul_neg,
      add_zero, neg_mul, ← sub_eq_add_neg, fromBlocks_inj, sub_eq_zero]
    exact ⟨h.1.symm, by grind, by simpa using congr(transpose $(h.2.2)), h.2.1.symm⟩

Depends on / 依赖: add_zero, fromBlocks, fromBlocks_inj, fromBlocks_multiply, fromBlocks_transpose, h_eq1, h_eq2, h_eq3, h_final, mem_iff, mul_neg, mul_one, mul_zero, sub_eq_add_neg, sub_eq_zero, transpose_mem, zero_add
-/
theorem fromBlocks_mem_iff :
    fromBlocks A B C D in symplecticGroup l R ↔
      Aᵀ * C = Cᵀ * A ∧
      Bᵀ * D = Dᵀ * B ∧
      Aᵀ * D - Cᵀ * B = 1 := by
  refine ⟨fun h => ?_, fun h => mem_iff'.2 ?_⟩
  · have h_final : fromBlocks (Cᵀ * A - Aᵀ * C) (Cᵀ * B - Aᵀ * D)
        (Dᵀ * A - Bᵀ * C) (Dᵀ * B - Bᵀ * D) = J l R := by
      simpa [mem_iff, fromBlocks_transpose, J, fromBlocks_multiply,
        sub_eq_add_neg] using transpose_mem h
    obtain ⟨h_eq1, h_eq2, _, h_eq3⟩ := fromBlocks_inj.1 h_final
    exact ⟨(sub_eq_zero.1 h_eq1).symm, (sub_eq_zero.1 h_eq3).symm, by grind⟩
  · simp only [fromBlocks_transpose, J, fromBlocks_multiply, mul_zero, mul_one, zero_add, mul_neg,
      add_zero, neg_mul, ← sub_eq_add_neg, fromBlocks_inj, sub_eq_zero]
    exact ⟨h.1.symm, by grind, by simpa using congr(transpose $(h.2.2)), h.2.1.symm⟩

/--
lemma `det_one_if_fromBlocks_invertible` / 引理 `det_one_if_fromBlocks_invertible`

English:
lemma det_one_if_fromBlocks_invertible
  statement: [Invertible A]
  proof: by
  have h_block := fromBlocks_mem_iff.1 hA
  rw [det_fromBlocks₁₁]; rw [invOf_eq_nonsing_inv]; rw [← A.det_transpose]; rw [← det_mul]; rw [mul_sub]; rw [← mul_assoc]; rw [← mul_assoc]; rw [h_block.1]; rw [mul_assoc Cᵀ]; rw [mul_inv_of_invertible]; rw [mul_one]; rw [h_block.2.2]; rw [det_one]

中文:
引理 det_one_if_fromBlocks_invertible
  结论: [可逆 A]
  证明: by
  have h_block := fromBlocks_mem_iff.1 hA
  rw [det_fromBlocks₁₁]; rw [invOf_eq_nonsing_inv]; rw [← A.det_transpose]; rw [← det_mul]; rw [mul_sub]; rw [← mul_assoc]; rw [← mul_assoc]; rw [h_block.1]; rw [mul_assoc Cᵀ]; rw [mul_inv_of_invertible]; rw [mul_one]; rw [h_block.2.2]; rw [det_one]
-/
private lemma det_one_if_fromBlocks_invertible [Invertible A]
    (hA : fromBlocks A B C D in symplecticGroup l R) :
    (fromBlocks A B C D).det = 1 := by
  have h_block := fromBlocks_mem_iff.1 hA
  rw [det_fromBlocks₁₁]; rw [invOf_eq_nonsing_inv]; rw [← A.det_transpose]; rw [← det_mul]; rw [mul_sub]; rw [← mul_assoc]; rw [← mul_assoc]; rw [h_block.1]; rw [mul_assoc Cᵀ]; rw [mul_inv_of_invertible]; rw [mul_one]; rw [h_block.2.2]; rw [det_one]

/--
lemma `exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot` / 引理 `exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot`

English:
lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot
  statement: {R : Type*} [Field R]
  proof: by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) => x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x -> IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank oplus Fin (Fintype.card l - C.rank) -> R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul]; rw [f_mul]; rw [mul_assoc]; rw [mul_smul]; rw [IsUnit.smul_eq_zero]; rw [mul_smul]; rw [hf]; rw [smul_eq_mulVec]; rw [submatrix_mulVec_equiv]; rw [Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
exact s.surjective.injective_comp_right by simpa using hker _ heq1 heq2
    · exact f_unit hV
· exact f_unit isUnit_nonsing_inv_iff.2 V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ]; rw [hsymm]; rw [mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply]; rw [reindex_apply]; rw [← hf]; rw [← hf]; rw [f_mul]; rw [f_mul Pᵀ]; rw [heq]; rw [hf]; rw [← transpose_submatrix]; rw [← hf Q]; rw [← (f Q).fromBlocks_toBlocks]; rw [hf (_)ᵀ]; rw [hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin]; rw [← LinearMap.ker_eq_bot]
refine ker_mulVecLin_eq_bot_iff.2 fun x hx => Sum.elim_injective'
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank oplus Fin (Fintype.card l - C.rank)) (Fin C.rank oplus
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def]; rw [isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf]; rw [heq']; rw [IsUnit.mul_iff]; rw [IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
· exact f_unit isUnit_nonsing_inv_iff.2 hU

中文:
引理 存在_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot
  结论: {R : 类型} [域 R]
  证明: by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) => x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x -> IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank oplus Fin (Fintype.card l - C.rank) -> R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul]; rw [f_mul]; rw [mul_assoc]; rw [mul_smul]; rw [IsUnit.smul_eq_zero]; rw [mul_smul]; rw [hf]; rw [smul_eq_mulVec]; rw [submatrix_mulVec_equiv]; rw [Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
exact s.surjective.injective_comp_right by simpa using hker _ heq1 heq2
    · exact f_unit hV
· exact f_unit isUnit_nonsing_inv_iff.2 V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ]; rw [hsymm]; rw [mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply]; rw [reindex_apply]; rw [← hf]; rw [← hf]; rw [f_mul]; rw [f_mul Pᵀ]; rw [heq]; rw [hf]; rw [← transpose_submatrix]; rw [← hf Q]; rw [← (f Q).fromBlocks_toBlocks]; rw [hf (_)ᵀ]; rw [hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin]; rw [← LinearMap.ker_eq_bot]
refine ker_mulVecLin_eq_bot_iff.2 fun x hx => Sum.elim_injective'
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank oplus Fin (Fintype.card l - C.rank)) (Fin C.rank oplus
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def]; rw [isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf]; rw [heq']; rw [IsUnit.mul_iff]; rw [IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
· exact f_unit isUnit_nonsing_inv_iff.2 hU
-/
private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : forall (x : l -> R), (A • x = 0) -> (C • x = 0) -> x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    exists (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) => x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x -> IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank oplus Fin (Fintype.card l - C.rank) -> R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul]; rw [f_mul]; rw [mul_assoc]; rw [mul_smul]; rw [IsUnit.smul_eq_zero]; rw [mul_smul]; rw [hf]; rw [smul_eq_mulVec]; rw [submatrix_mulVec_equiv]; rw [Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
exact s.surjective.injective_comp_right by simpa using hker _ heq1 heq2
    · exact f_unit hV
· exact f_unit isUnit_nonsing_inv_iff.2 V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ]; rw [hsymm]; rw [mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply]; rw [reindex_apply]; rw [← hf]; rw [← hf]; rw [f_mul]; rw [f_mul Pᵀ]; rw [heq]; rw [hf]; rw [← transpose_submatrix]; rw [← hf Q]; rw [← (f Q).fromBlocks_toBlocks]; rw [hf (_)ᵀ]; rw [hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin]; rw [← LinearMap.ker_eq_bot]
refine ker_mulVecLin_eq_bot_iff.2 fun x hx => Sum.elim_injective'
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank oplus Fin (Fintype.card l - C.rank)) (Fin C.rank oplus
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def]; rw [isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf]; rw [heq']; rw [IsUnit.mul_iff]; rw [IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
· exact f_unit isUnit_nonsing_inv_iff.2 hU

/--
lemma `exists_symmetric_X_isUnit_det_add_mul_of_symplectic` / 引理 `exists_symmetric_X_isUnit_det_add_mul_of_symplectic`

English:
lemma exists_symmetric_X_isUnit_det_add_mul_of_symplectic
  statement: [IsLocalRing R]
  proof: by
  -- We utilize the previous result on field by mapping the symplectic matrix to residue field.
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [Matrix.fromBlocks_map]; rfl
  have hker (x : l -> k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have hv0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' hv0)).1
  -- Now we have a symmetric matrix `Y` over the residue field s.t. `A' + Y * C'` is invertible
  -- where `A'` and `C'` are images of `A` and `C` under quotient map from `R` to its residue field.
  obtain ⟨Y, hY_symm, hY_det⟩ :=
exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot hker by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul]; rw [(fromBlocks_mem_iff.1 hA).1]; rw [map_mul]
  -- Lift `Y` back to the ring `R` and we have the `X` we need.
  obtain ⟨X, hX_symm, hXY⟩ : exists X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j => hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  -- Ensure `A + X * C` is still invertible in `R`.
  rw [RingHom.map_det]; rw [map_add]; rw [map_mul]; rw [RingHom.mapMatrix_apply _ X]; rw [hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

中文:
引理 存在_symmetric_X_isUnit_det_add_mul_of_symplectic
  结论: [是局部环 R]
  证明: by
  -- We utilize the previous result on field by mapping the symplectic matrix to residue field.
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [Matrix.fromBlocks_map]; rfl
  have hker (x : l -> k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have hv0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' hv0)).1
  -- Now we have a symmetric matrix `Y` over the residue field s.t. `A' + Y * C'` is invertible
  -- where `A'` and `C'` are images of `A` and `C` under quotient map from `R` to its residue field.
  obtain ⟨Y, hY_symm, hY_det⟩ :=
exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot hker by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul]; rw [(fromBlocks_mem_iff.1 hA).1]; rw [map_mul]
  -- Lift `Y` back to the ring `R` and we have the `X` we need.
  obtain ⟨X, hX_symm, hXY⟩ : exists X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j => hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  -- Ensure `A + X * C` is still invertible in `R`.
  rw [RingHom.map_det]; rw [map_add]; rw [map_mul]; rw [RingHom.mapMatrix_apply _ X]; rw [hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

Depends on / 依赖: ENNReal, ENNReal.Tendsto.const_mul, ENNReal.coe_zero, ENNReal.tendsto_coe, NNReal, NNReal.coe_zero, NNReal.tendsto_coe, Tendsto, coe_nnnorm, coe_zero, const_mul, enorm_integral_le_lintegral_enorm, enorm_integral_le_lintegral_enorm.trans, mul_zero, ne_of_lt, simp_rw, tendsto_coe, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_setLIntegral_zero
-/
private lemma exists_symmetric_X_isUnit_det_add_mul_of_symplectic [IsLocalRing R]
    (hA : fromBlocks A B C D in symplecticGroup l R) :
    exists (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  -- We utilize the previous result on field by mapping the symplectic matrix to residue field.
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [Matrix.fromBlocks_map]; rfl
  have hker (x : l -> k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have hv0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' hv0)).1
  -- Now we have a symmetric matrix `Y` over the residue field s.t. `A' + Y * C'` is invertible
  -- where `A'` and `C'` are images of `A` and `C` under quotient map from `R` to its residue field.
  obtain ⟨Y, hY_symm, hY_det⟩ :=
exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot hker by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul]; rw [(fromBlocks_mem_iff.1 hA).1]; rw [map_mul]
  -- Lift `Y` back to the ring `R` and we have the `X` we need.
  obtain ⟨X, hX_symm, hXY⟩ : exists X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j => hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  -- Ensure `A + X * C` is still invertible in `R`.
  rw [RingHom.map_det]; rw [map_add]; rw [map_mul]; rw [RingHom.mapMatrix_apply _ X]; rw [hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

/--
lemma `det_eq_one_of_isLocalRing` / 引理 `det_eq_one_of_isLocalRing`

English:
lemma det_eq_one_of_isLocalRing
  statement: [IsLocalRing R] {M : Matrix (l oplus l) (l oplus l) R}
  proof: by
  set A := M.toBlocks₁₁; set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁; set D := M.toBlocks₂₂
obtain ⟨X, hX_symm, hA_isUnit⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    M.fromBlocks_toBlocks ▸ hM
  -- `fromBlocks 1 X 0 1` turns the upper-left block of `M` into an invertible matrix, here `X`
  -- is obtained via previous result.
  have Lx_mul : (fromBlocks 1 X 0 1) * M = fromBlocks (A + X * C) (B + X * D) C D := by
    rw [← M.fromBlocks_toBlocks]; rw [fromBlocks_multiply]
    simp only [one_mul, zero_mul, zero_add]; rfl
  have h_fromBlocks_in : fromBlocks (A + X * C) (B + X * D) C D in symplecticGroup l R := by
    rw [← Lx_mul]
    refine (symplecticGroup l R).mul_mem ?_ hM
    simp [mem_iff, fromBlocks_transpose, hX_symm.eq, J, fromBlocks_multiply]
  have _ : Invertible (A + X * C) := (A + X * C).invertibleOfIsUnitDet hA_isUnit
  -- And we know that a symmetric matrix with invertible upper-left block has determinant 1.
  have h_main : ((fromBlocks 1 X 0 1) * M).det = 1 := by
    rw [Lx_mul]; rw [det_one_if_fromBlocks_invertible h_fromBlocks_in]
  rwa [det_mul, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul] at h_main

中文:
引理 det_eq_one_of_isLocalRing
  结论: [是局部环 R] {M : 矩阵 (l oplus l) (l oplus l) R}
  证明: by
  set A := M.toBlocks₁₁; set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁; set D := M.toBlocks₂₂
obtain ⟨X, hX_symm, hA_isUnit⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    M.fromBlocks_toBlocks ▸ hM
  -- `fromBlocks 1 X 0 1` turns the upper-left block of `M` into an invertible matrix, here `X`
  -- is obtained via previous result.
  have Lx_mul : (fromBlocks 1 X 0 1) * M = fromBlocks (A + X * C) (B + X * D) C D := by
    rw [← M.fromBlocks_toBlocks]; rw [fromBlocks_multiply]
    simp only [one_mul, zero_mul, zero_add]; rfl
  have h_fromBlocks_in : fromBlocks (A + X * C) (B + X * D) C D in symplecticGroup l R := by
    rw [← Lx_mul]
    refine (symplecticGroup l R).mul_mem ?_ hM
    simp [mem_iff, fromBlocks_transpose, hX_symm.eq, J, fromBlocks_multiply]
  have _ : Invertible (A + X * C) := (A + X * C).invertibleOfIsUnitDet hA_isUnit
  -- And we know that a symmetric matrix with invertible upper-left block has determinant 1.
  have h_main : ((fromBlocks 1 X 0 1) * M).det = 1 := by
    rw [Lx_mul]; rw [det_one_if_fromBlocks_invertible h_fromBlocks_in]
  rwa [det_mul, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul] at h_main
-/
private lemma det_eq_one_of_isLocalRing [IsLocalRing R] {M : Matrix (l oplus l) (l oplus l) R}
    (hM : M in symplecticGroup l R) : M.det = 1 := by
  set A := M.toBlocks₁₁; set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁; set D := M.toBlocks₂₂
obtain ⟨X, hX_symm, hA_isUnit⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    M.fromBlocks_toBlocks ▸ hM
  -- `fromBlocks 1 X 0 1` turns the upper-left block of `M` into an invertible matrix, here `X`
  -- is obtained via previous result.
  have Lx_mul : (fromBlocks 1 X 0 1) * M = fromBlocks (A + X * C) (B + X * D) C D := by
    rw [← M.fromBlocks_toBlocks]; rw [fromBlocks_multiply]
    simp only [one_mul, zero_mul, zero_add]; rfl
  have h_fromBlocks_in : fromBlocks (A + X * C) (B + X * D) C D in symplecticGroup l R := by
    rw [← Lx_mul]
    refine (symplecticGroup l R).mul_mem ?_ hM
    simp [mem_iff, fromBlocks_transpose, hX_symm.eq, J, fromBlocks_multiply]
  have _ : Invertible (A + X * C) := (A + X * C).invertibleOfIsUnitDet hA_isUnit
  -- And we know that a symmetric matrix with invertible upper-left block has determinant 1.
  have h_main : ((fromBlocks 1 X 0 1) * M).det = 1 := by
    rw [Lx_mul]; rw [det_one_if_fromBlocks_invertible h_fromBlocks_in]
  rwa [det_mul, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul] at h_main

/--
theorem `det_eq_one` / 定理 `det_eq_one`

English:
theorem det_eq_one
  given: {M : Matrix (l oplus l) (l oplus l) R} (hM : M in symplecticGroup l R)
  proof: by
refine sub_eq_zero.1 eq_zero_of_localization _ fun _ _ => ?_
  simp [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_one_of_isLocalRing <| map_mem hM _]

中文:
定理 det_eq_one
  条件: {M : 矩阵 (l oplus l) (l oplus l) R} (hM : M in symplecticGroup l R)
  证明: by
refine sub_eq_zero.1 eq_zero_of_localization _ fun _ _ => ?_
  simp [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_one_of_isLocalRing <| map_mem hM _]

Depends on / 依赖: RingHom, RingHom.mapMatrix_apply, RingHom.map_det, det_eq_one_of_isLocalRing, eq_zero_of_localization, mapMatrix_apply, map_det, map_mem, sub_eq_zero
-/
theorem det_eq_one {M : Matrix (l oplus l) (l oplus l) R} (hM : M in symplecticGroup l R) :
    M.det = 1 := by
refine sub_eq_zero.1 eq_zero_of_localization _ fun _ _ => ?_
  simp [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_one_of_isLocalRing <| map_mem hM _]

end Determinant

end SymplecticGroup
