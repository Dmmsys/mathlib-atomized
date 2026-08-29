/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix results for barycentric co-ordinates

Results about the matrix of barycentric co-ordinates for a family of points in an affine space, with
respect to some affine basis.
-/

@[expose] public section


open Affine Matrix

open Set

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variable [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/--
Definition of `toMatrix` / `toMatrix` 的定义

English:
definition toMatrix
  signature: {ι' : Type*} (q : ι' -> P)
  body: fun i j => b.coord j (q i)

@[simp]

中文:
定义 toMatrix
  签名: {ι' : 类型} (q : ι' -> P)
  定义体: fun i j => b.coord j (q i)

@[simp]

Depends on / 依赖: b.coord
-/
noncomputable def toMatrix {ι' : Type*} (q : ι' -> P) : Matrix ι' ι k :=
  fun i j => b.coord j (q i)

@[simp]
/--
theorem `toMatrix_apply` / 定理 `toMatrix_apply`

English:
theorem toMatrix_apply
  given: {ι' : Type*} (q : ι' -> P) (i : ι') (j : ι)
  proof: rfl

@[simp]

中文:
定理 toMatrix_apply
  条件: {ι' : 类型} (q : ι' -> P) (i : ι') (j : ι)
  证明: rfl

@[simp]

Depends on / 依赖: isOpenPosMeasure, pi.isOpenPosMeasure
-/
theorem toMatrix_apply {ι' : Type*} (q : ι' -> P) (i : ι') (j : ι) :
    b.toMatrix q i j = b.coord j (q i) := rfl

@[simp]
/--
theorem `toMatrix_self` / 定理 `toMatrix_self`

English:
theorem toMatrix_self
  given: [DecidableEq ι]
  statement: b.toMatrix b = (1 : Matrix ι ι k)
  proof: by
  ext i j
  rw [toMatrix_apply]; rw [coord_apply]; rw [Matrix.one_eq_pi_single]; rw [Pi.single_apply]

中文:
定理 toMatrix_self
  条件: [DecidableEq ι]
  结论: b.toMatrix b = (1 : Matrix ι ι k)
  证明: by
  ext i j
  rw [toMatrix_apply]; rw [coord_apply]; rw [Matrix.one_eq_pi_single]; rw [Pi.single_apply]

Depends on / 依赖: Matrix, Matrix.one_eq_pi_single, Pi.single_apply, coord_apply, one_eq_pi_single, single_apply, toMatrix_apply
-/
theorem toMatrix_self [DecidableEq ι] : b.toMatrix b = (1 : Matrix ι ι k) := by
  ext i j
  rw [toMatrix_apply]; rw [coord_apply]; rw [Matrix.one_eq_pi_single]; rw [Pi.single_apply]

variable {ι' : Type*}

/--
theorem `toMatrix_row_sum_one` / 定理 `toMatrix_row_sum_one`

English:
theorem toMatrix_row_sum_one
  given: [Fintype ι] (q : ι' -> P) (i : ι')
  statement: ∑ j, b.toMatrix q i j = 1
  proof: by
  simp

中文:
定理 toMatrix_row_sum_one
  条件: [Fintype ι] (q : ι' -> P) (i : ι')
  结论: ∑ j, b.toMatrix q i j = 1
  证明: by
  simp

Depends on / 依赖: isFiniteMeasureOnCompacts, pi.isFiniteMeasureOnCompacts
-/
theorem toMatrix_row_sum_one [Fintype ι] (q : ι' -> P) (i : ι') : ∑ j, b.toMatrix q i j = 1 := by
  simp

/--
theorem `affineIndependent_of_toMatrix_right_inv` / 定理 `affineIndependent_of_toMatrix_right_inv`

English:
theorem affineIndependent_of_toMatrix_right_inv
  statement: [Fintype ι] [Finite ι'] [DecidableEq ι']
  proof: by
  cases nonempty_fintype ι'
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hweq
  have hweq' : w₁ ᵥ* b.toMatrix p = w₂ ᵥ* b.toMatrix p := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    rw [← Finset.univ.affineCombinat

中文:
定理 affineIndependent_of_toMatrix_right_inv
  结论: [Fintype ι] [Finite ι'] [DecidableEq ι']
  证明: by
  cases nonempty_fintype ι'
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hweq
  have hweq' : w₁ ᵥ* b.toMatrix p = w₂ ᵥ* b.toMatrix p := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    rw [← Finset.univ.affineCombinat

Depends on / 依赖: Finset, Finset.univ.affineCombination_eq_linear_combination, Finset.univ.map_aff, Finset.univ.map_affineCombination, Function, Function.comp_def, affineCombination_eq_linear_combination, affineIndependent_iff_eq_of_fintype_affineCombination_eq, b.coord, b.toMatrix, comp_def, isHaarMeasure, map_aff, map_affineCombination, nonempty_fintype, pi.isHaarMeasure, toMatrix
-/
theorem affineIndependent_of_toMatrix_right_inv [Fintype ι] [Finite ι'] [DecidableEq ι']
    (p : ι' -> P) {A : Matrix ι ι' k} (hA : b.toMatrix p * A = 1) : AffineIndependent k p := by
  cases nonempty_fintype ι'
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hweq
  have hweq' : w₁ ᵥ* b.toMatrix p = w₂ ᵥ* b.toMatrix p := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw₁]; rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw₂]; rw [← Function.comp_def (b.coord j) p]; rw [← Finset.univ.map_affineCombination p w₁ hw₁]; rw [← Finset.univ.map_affineCombination p w₂ hw₂]; rw [hweq]
  replace hweq' := congr_arg (fun w => w ᵥ* A) hweq'
  simpa only [Matrix.vecMul_vecMul, hA, Matrix.vecMul_one] using hweq'

/--
theorem `affineSpan_eq_top_of_toMatrix_left_inv` / 定理 `affineSpan_eq_top_of_toMatrix_left_inv`

English:
theorem affineSpan_eq_top_of_toMatrix_left_inv
  statement: [Finite ι] [Fintype ι'] [DecidableEq ι]
  proof: by
  cases nonempty_fintype ι
  suffices forall i, b i in affineSpan k (range p) by
    rw [eq_top_iff]; rw [← b.tot]; rw [affineSpan_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  have hAi : ∑ j, A i j = 1 := by
    calc
      ∑ j, A i j = ∑ j, A i j * ∑ l, b.toMatrix p j l := by simp
     

中文:
定理 affineSpan_eq_top_of_toMatrix_left_inv
  结论: [Finite ι] [Fintype ι'] [DecidableEq ι]
  证明: by
  cases nonempty_fintype ι
  suffices forall i, b i in affineSpan k (range p) by
    rw [eq_top_iff]; rw [← b.tot]; rw [affineSpan_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  have hAi : ∑ j, A i j = 1 := by
    calc
      ∑ j, A i j = ∑ j, A i j * ∑ l, b.toMatrix p j l := by simp
     

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_comm, Matrix, Matrix.one_apply, affineSpan, affineSpan_le, b.toMatrix, b.tot, eq_top_iff, mul_sum, nonempty_fintype, one_apply, simp_rw, sum_comm, toMatrix
-/
theorem affineSpan_eq_top_of_toMatrix_left_inv [Finite ι] [Fintype ι'] [DecidableEq ι]
    [Nontrivial k] (p : ι' -> P) {A : Matrix ι ι' k} (hA : A * b.toMatrix p = 1) :
    affineSpan k (range p) = ⊤ := by
  cases nonempty_fintype ι
  suffices forall i, b i in affineSpan k (range p) by
    rw [eq_top_iff]; rw [← b.tot]; rw [affineSpan_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  have hAi : ∑ j, A i j = 1 := by
    calc
      ∑ j, A i j = ∑ j, A i j * ∑ l, b.toMatrix p j l := by simp
      _ = ∑ j, ∑ l, A i j * b.toMatrix p j l := by simp_rw [Finset.mul_sum]
      _ = ∑ l, ∑ j, A i j * b.toMatrix p j l := by rw [Finset.sum_comm]
      _ = ∑ l, (A * b.toMatrix p) i l := rfl
      _ = 1 := by simp [hA, Matrix.one_apply]
  have hbi : b i = Finset.univ.affineCombination k p (A i) := by
    apply b.ext_elem
    intro j
    rw [b.coord_apply]; rw [Finset.univ.map_affineCombination _ _ hAi]; rw [Finset.univ.affineCombination_eq_linear_combination _ _ hAi]
    change _ = (A * b.toMatrix p) i j
    simp_rw [hA, Matrix.one_apply, @eq_comm _ i j]
  rw [hbi]
  exact affineCombination_mem_affineSpan hAi p

variable [Fintype ι] (b₂ : AffineBasis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_inv_vecMul_toMatrix`. -/
@[simp]
/--
theorem `toMatrix_vecMul_coords` / 定理 `toMatrix_vecMul_coords`

English:
theorem toMatrix_vecMul_coords
  given: (x : P)
  statement: b₂.coords x ᵥ* b.toMatrix b₂ = b.coords x
  proof: by
  ext j
  change _ = b.coord j x
  conv_rhs => rw [← b₂.affineCombination_coord_eq_self x]
  rw [Finset.map_affineCombination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  simp [Matrix.vecMul, dotProduct, toMatrix_apply, coords]

中文:
定理 toMatrix_vecMul_coords
  条件: (x : P)
  结论: b₂.coords x ᵥ* b.toMatrix b₂ = b.coords x
  证明: by
  ext j
  change _ = b.coord j x
  conv_rhs => rw [← b₂.affineCombination_coord_eq_self x]
  rw [Finset.map_affineCombination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  simp [Matrix.vecMul, dotProduct, toMatrix_apply, coords]

Depends on / 依赖: Finset, Finset.map_affineCombination, Matrix, Matrix.vecMul, affineCombination_coord_eq_self, b.coord, conv_rhs, coords, dotProduct, map_affineCombination, sum_coord_apply_eq_one, toMatrix_apply, vecMul
-/
theorem toMatrix_vecMul_coords (x : P) : b₂.coords x ᵥ* b.toMatrix b₂ = b.coords x := by
  ext j
  change _ = b.coord j x
  conv_rhs => rw [← b₂.affineCombination_coord_eq_self x]
  rw [Finset.map_affineCombination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  simp [Matrix.vecMul, dotProduct, toMatrix_apply, coords]

variable [DecidableEq ι]

/--
theorem `toMatrix_mul_toMatrix` / 定理 `toMatrix_mul_toMatrix`

English:
theorem toMatrix_mul_toMatrix
  statement: b.toMatrix b₂ * b₂.toMatrix b = 1
  proof: by
  ext l m
  change (b.coords (b₂ l) ᵥ* b₂.toMatrix b) m = _
  rw [toMatrix_vecMul_coords]; rw [coords_apply]; rw [← toMatrix_apply]; rw [toMatrix_self]

中文:
定理 toMatrix_mul_toMatrix
  结论: b.toMatrix b₂ * b₂.toMatrix b = 1
  证明: by
  ext l m
  change (b.coords (b₂ l) ᵥ* b₂.toMatrix b) m = _
  rw [toMatrix_vecMul_coords]; rw [coords_apply]; rw [← toMatrix_apply]; rw [toMatrix_self]

Depends on / 依赖: b.coords, coords, coords_apply, toMatrix, toMatrix_apply, toMatrix_self, toMatrix_vecMul_coords
-/
theorem toMatrix_mul_toMatrix : b.toMatrix b₂ * b₂.toMatrix b = 1 := by
  ext l m
  change (b.coords (b₂ l) ᵥ* b₂.toMatrix b) m = _
  rw [toMatrix_vecMul_coords]; rw [coords_apply]; rw [← toMatrix_apply]; rw [toMatrix_self]

/--
theorem `isUnit_toMatrix` / 定理 `isUnit_toMatrix`

English:
theorem isUnit_toMatrix
  statement: IsUnit (b.toMatrix b₂)
  proof: ⟨{ val := b.toMatrix b₂
      inv := b₂.toMatrix b
      val_inv := b.toMatrix_mul_toMatrix b₂
      inv_val := b₂.toMatrix_mul_toMatrix b }, rfl⟩

中文:
定理 isUnit_toMatrix
  结论: IsUnit (b.toMatrix b₂)
  证明: ⟨{ val := b.toMatrix b₂
      inv := b₂.toMatrix b
      val_inv := b.toMatrix_mul_toMatrix b₂
      inv_val := b₂.toMatrix_mul_toMatrix b }, rfl⟩

Depends on / 依赖: b.toMatrix, b.toMatrix_mul_toMatrix, inv_val, toMatrix, toMatrix_mul_toMatrix, val_inv
-/
theorem isUnit_toMatrix : IsUnit (b.toMatrix b₂) :=
  ⟨{ val := b.toMatrix b₂
      inv := b₂.toMatrix b
      val_inv := b.toMatrix_mul_toMatrix b₂
      inv_val := b₂.toMatrix_mul_toMatrix b }, rfl⟩

/--
theorem `isUnit_toMatrix_iff` / 定理 `isUnit_toMatrix_iff`

English:
theorem isUnit_toMatrix_iff
  given: [Nontrivial k] (p : ι -> P)
  proof: by
  constructor
  · rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.toMatrix p⟩
    exact ⟨b.affineIndependent_of_toMatrix_right_inv p hA,
      b.affineSpan_eq_top_of_toMatrix_left_inv p hA'⟩
  · rintro ⟨h_tot, h_ind⟩
    let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
    change IsUnit (b.toMatrix b')
    e

中文:
定理 isUnit_toMatrix_iff
  条件: [Nontrivial k] (p : ι -> P)
  证明: by
  constructor
  · rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.toMatrix p⟩
    exact ⟨b.affineIndependent_of_toMatrix_right_inv p hA,
      b.affineSpan_eq_top_of_toMatrix_left_inv p hA'⟩
  · rintro ⟨h_tot, h_ind⟩
    let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
    change IsUnit (b.toMatrix b')
    e

Depends on / 依赖: AffineBasis, IsUnit, affineIndependent_of_toMatrix_right_inv, affineSpan_eq_top_of_toMatrix_left_inv, b.affineIndependent_of_toMatrix_right_inv, b.affineSpan_eq_top_of_toMatrix_left_inv, b.isUnit_toMatrix, b.toMatrix, h_ind, h_tot, isUnit_toMatrix, toMatrix
-/
theorem isUnit_toMatrix_iff [Nontrivial k] (p : ι -> P) :
    IsUnit (b.toMatrix p) ↔ AffineIndependent k p ∧ affineSpan k (range p) = ⊤ := by
  constructor
  · rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.toMatrix p⟩
    exact ⟨b.affineIndependent_of_toMatrix_right_inv p hA,
      b.affineSpan_eq_top_of_toMatrix_left_inv p hA'⟩
  · rintro ⟨h_tot, h_ind⟩
    let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
    change IsUnit (b.toMatrix b')
    exact b.isUnit_toMatrix b'

end Ring

section CommRing

variable [CommRing k] [Module k V] [DecidableEq ι] [Fintype ι]
variable (b b₂ : AffineBasis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_vecMul_coords`. -/
@[simp]
/--
theorem `toMatrix_inv_vecMul_toMatrix` / 定理 `toMatrix_inv_vecMul_toMatrix`

English:
theorem toMatrix_inv_vecMul_toMatrix
  given: (x : P)
  proof: by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_vecMul_coords b₂]; rw [Matrix.vecMul_vecMul]; rw [Matrix.mul_nonsing_inv _ hu]; rw [Matrix.vecMul_one]

中文:
定理 toMatrix_inv_vecMul_toMatrix
  条件: (x : P)
  证明: by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_vecMul_coords b₂]; rw [Matrix.vecMul_vecMul]; rw [Matrix.mul_nonsing_inv _ hu]; rw [Matrix.vecMul_one]

Depends on / 依赖: Matrix, Matrix.isUnit_iff_isUnit_det, Matrix.mul_nonsing_inv, Matrix.vecMul_one, Matrix.vecMul_vecMul, b.isUnit_toMatrix, b.toMatrix_vecMul_coords, isUnit_iff_isUnit_det, isUnit_toMatrix, mul_nonsing_inv, toMatrix_vecMul_coords, vecMul_one, vecMul_vecMul
-/
theorem toMatrix_inv_vecMul_toMatrix (x : P) :
    b.coords x ᵥ* (b.toMatrix b₂)⁻¹ = b₂.coords x := by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_vecMul_coords b₂]; rw [Matrix.vecMul_vecMul]; rw [Matrix.mul_nonsing_inv _ hu]; rw [Matrix.vecMul_one]

/--
theorem `det_smul_coords_eq_cramer_coords` / 定理 `det_smul_coords_eq_cramer_coords`

English:
theorem det_smul_coords_eq_cramer_coords
  given: (x : P)
  proof: by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_inv_vecMul_toMatrix]; rw [Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ _ hu]

中文:
定理 det_smul_coords_eq_cramer_coords
  条件: (x : P)
  证明: by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_inv_vecMul_toMatrix]; rw [Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ _ hu]

Depends on / 依赖: Matrix, Matrix.det_smul_inv_vecMul_eq_cramer_transpose, Matrix.isUnit_iff_isUnit_det, b.isUnit_toMatrix, b.toMatrix_inv_vecMul_toMatrix, det_smul_inv_vecMul_eq_cramer_transpose, isUnit_iff_isUnit_det, isUnit_toMatrix, toMatrix_inv_vecMul_toMatrix
-/
theorem det_smul_coords_eq_cramer_coords (x : P) :
    (b.toMatrix b₂).det • b₂.coords x = (b.toMatrix b₂)ᵀ.cramer (b.coords x) := by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_inv_vecMul_toMatrix]; rw [Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ _ hu]

end CommRing

end AffineBasis
