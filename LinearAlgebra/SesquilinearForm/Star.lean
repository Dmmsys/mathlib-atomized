/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Sesquilinear forms over a star ring

This file provides some properties about sesquilinear forms `M →ₗ⋆[R] M →ₗ[R] R` when `R` is a
`StarRing`.
-/

public section

open Module LinearMap

variable {R M n : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
  [Fintype n] [DecidableEq n]
  {B : M ->ₗ⋆[R] M ->ₗ[R] R} (b : Basis n R M)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `LinearMap.isSymm_iff_basis` / 引理 `LinearMap.isSymm_iff_basis`

English:
lemma LinearMap.isSymm_iff_basis
  given: {ι : Type*} (b : Basis ι R M)
  proof: h.eq _ _
  mpr := by
    refine fun h => ⟨fun x y => ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x in Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y in Submodu

中文:
引理 线性映射.isSymm_iff_basis
  条件: {ι : 类型} (b : 基 ι R M)
  证明: h.eq _ _
  mpr := by
    refine fun h => ⟨fun x y => ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x in Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y in Submodu

Depends on / 依赖: h.eq
-/
lemma LinearMap.isSymm_iff_basis {ι : Type*} (b : Basis ι R M) :
    IsSymm B ↔ forall i j, star (B (b i) (b j)) = B (b j) (b i) where
  mp h i j := h.eq _ _
  mpr := by
    refine fun h => ⟨fun x y => ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x in Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y in Submodule.span R (Set.range b))
    rw [← hx]; rw [← hy]
    simp only [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, map_smul, coe_sum,
      Finset.sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum, map_mul, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ => Finset.sum_congr rfl fun b₂ h₂ => ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

/--
lemma `LinearMap.isSymm_iff_isHermitian_toMatrix` / 引理 `LinearMap.isSymm_iff_isHermitian_toMatrix`

English:
lemma LinearMap.isSymm_iff_isHermitian_toMatrix
  statement: B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian
  proof: by
  rw [isSymm_iff_basis b]; rw [Matrix.IsHermitian.ext_iff]; rw [forall_comm]
  simp [Eq.comm]

中文:
引理 线性映射.isSymm_iff_isHermitian_toMatrix
  结论: B.是Symm ↔ (toMatrix₂ b b B).IsHermitian
  证明: by
  rw [isSymm_iff_basis b]; rw [Matrix.IsHermitian.ext_iff]; rw [forall_comm]
  simp [Eq.comm]

Depends on / 依赖: Eq.comm, IsHermitian, Matrix, Matrix.IsHermitian.ext_iff, ext_iff, forall_comm, isSymm_iff_basis
-/
lemma LinearMap.isSymm_iff_isHermitian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian := by
  rw [isSymm_iff_basis b]; rw [Matrix.IsHermitian.ext_iff]; rw [forall_comm]
  simp [Eq.comm]

/--
lemma `star_dotProduct_toMatrix₂_mulVec` / 引理 `star_dotProduct_toMatrix₂_mulVec`

English:
lemma star_dotProduct_toMatrix₂_mulVec
  given: (x y : n -> R)
  proof: dotProduct_toMatrix₂_mulVec b b B x y

中文:
引理 star_dotProduct_toMatrix₂_mulVec
  条件: (x y : n -> R)
  证明: dotProduct_toMatrix₂_mulVec b b B x y
-/
lemma star_dotProduct_toMatrix₂_mulVec (x y : n -> R) :
    star x ⬝ᵥ (toMatrix₂ b b B).mulVec y = B (b.equivFun.symm x) (b.equivFun.symm y) :=
  dotProduct_toMatrix₂_mulVec b b B x y

/--
lemma `apply_eq_star_dotProduct_toMatrix₂_mulVec` / 引理 `apply_eq_star_dotProduct_toMatrix₂_mulVec`

English:
lemma apply_eq_star_dotProduct_toMatrix₂_mulVec
  given: (x y : M)
  proof: apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

中文:
引理 apply_eq_star_dotProduct_toMatrix₂_mulVec
  条件: (x y : M)
  证明: apply_eq_dotProduct_toMatrix₂_mulVec b b B x y
-/
lemma apply_eq_star_dotProduct_toMatrix₂_mulVec (x y : M) :
    B x y = star (b.repr x) ⬝ᵥ (toMatrix₂ b b B).mulVec (b.repr y) :=
  apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

variable {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [Module R M]
  {B : M ->ₗ⋆[R] M ->ₗ[R] R} (b : Basis n R M)

/--
lemma `LinearMap.isPosSemidef_iff_posSemidef_toMatrix` / 引理 `LinearMap.isPosSemidef_iff_posSemidef_toMatrix`

English:
lemma LinearMap.isPosSemidef_iff_posSemidef_toMatrix
  proof: by
  rw [isPosSemidef_def]; rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply and_congr (B.isSymm_iff_isHermitian_toMatrix b)
  rw [isNonneg_def]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
  

中文:
引理 线性映射.isPosSemidef_iff_posSemidef_toMatrix
  证明: by
  rw [isPosSemidef_def]; rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply and_congr (B.isSymm_iff_isHermitian_toMatrix b)
  rw [isNonneg_def]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
  

Depends on / 依赖: B.isSymm_iff_isHermitian_toMatrix, Matrix, Matrix.posSemidef_iff_dotProduct_mulVec, and_congr, isNonneg_def, isPosSemidef_def, isSymm_iff_isHermitian_toMatrix, posSemidef_iff_dotProduct_mulVec
-/
lemma LinearMap.isPosSemidef_iff_posSemidef_toMatrix :
    B.IsPosSemidef ↔ (toMatrix₂ b b B).PosSemidef := by
  rw [isPosSemidef_def]; rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply and_congr (B.isSymm_iff_isHermitian_toMatrix b)
  rw [isNonneg_def]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
    exact h _
