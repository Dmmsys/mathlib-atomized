/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Geometry.Euclidean.Volume.Measure

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Norm determinant of a linear map

Given a rectangular matrix $T$, it is common to talk about $\sqrt{det(T^{H}T)}$, where $T^{H}$ is
the conjugate transpose of $T$, as a generalization to the determinant of a square matrix. It is the
$m$-dimensional volume factor for linear maps $\mathbb{R}^m \to \mathbb{R}^n$. It is given various
names in the literature:
* "Jacobian" (definition 3.4 of [lawrenceronald2025]), in the context of volume factor
  for a non-linear map. However, we choose to reserve this name for the matrix consisting of
  derivatives.
* "Gram determinant", which is already used by `Matrix.gram`, and it is often referring to
  $det(T^{H}T)$ without the square root.
* "Nonnegative determinant" (definition 1 of [haruoyoshiohidetoki2006]).

Without a standardized name, we give a descriptive name `LinearMap.normDet` to reflect its
definition and show that it is a generalization of `‖(f : LinearMap 𝕜 U U).det‖`
(See `LinearMap.normDet_eq_norm_det`). We also construct this on linear maps between inner product
spaces instead of matrices, and allow the codomain to have infinite dimension.

## Main definition
* `LinearMap.normDet` : the norm determinant of a linear map.

## Main result
* `ContinuousLinearMap.normDet_sq` and `LinearMap.normDet_sq`: The square of `f.normDet`
  equals to the determinant of `f.adjoint ∘ₗ f`.
* `LinearMap.normDet_sq_eq_det_gram`: The square of `LinearMap.normDet` equals to the determinant of
  the Gram matrix formed by vectors mapped from an orthonormal basis.
* `LinearMap.normDet_eq_prod_singularValues`: `LinearMap.normDet` equals to the product of singular
  values.
* `LinearMap.hausdorffMeasure_image`: `LinearMap.normDet` is the volume factor for Hausdorff
  measure.

-/

public section

open Module

namespace LinearMap

variable {𝕜 U V W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [FiniteDimensional 𝕜 U] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W]

open Classical in
/--
Definition of `normDet` / `normDet` 的定义

English:
definition normDet
  signature: (f : U ->ₗ[𝕜] V)
  body: if h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) then
    ‖(f.rangeRestrict.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis h.some.toBasis).det‖
  else
    0

中文:
定义 normDet
  签名: (f : U ->ₗ[𝕜] V)
  定义体: if h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) then
    ‖(f.rangeRestrict.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis h.some.toBasis).det‖
  else
    0

Depends on / 依赖: Nonempty, OrthonormalBasis, f.range, f.rangeRestrict.toMatrix, finrank, h.some.toBasis, rangeRestrict, stdOrthonormalBasis, toBasis, toMatrix
-/
noncomputable def normDet (f : U ->ₗ[𝕜] V) : Real :=
  if h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) then
    ‖(f.rangeRestrict.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis h.some.toBasis).det‖
  else
    0

/--
theorem `normDet_nonneg` / 定理 `normDet_nonneg`

English:
theorem normDet_nonneg
  given: (f : U ->ₗ[𝕜] V)
  statement: 0 <= f.normDet
  proof: by
  unfold normDet
  split <;> simp

中文:
定理 normDet_nonneg
  条件: (f : U ->ₗ[𝕜] V)
  结论: 0 <= f.normDet
  证明: by
  unfold normDet
  split <;> simp

Depends on / 依赖: normDet
-/
theorem normDet_nonneg (f : U ->ₗ[𝕜] V) : 0 <= f.normDet := by
  unfold normDet
  split <;> simp

/--
theorem `normDet_eq_norm_det_toMatrix_rangeRestrict` / 定理 `normDet_eq_norm_det_toMatrix_rangeRestrict`

English:
theorem normDet_eq_norm_det_toMatrix_rangeRestrict
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι]
  proof: by
  have hrank : finrank 𝕜 U = finrank 𝕜 f.range := by
    rw [finrank_eq_nat_card_basis bu.toBasis]; rw [finrank_eq_nat_card_basis bv.toBasis]
  have h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) := by
    rw [hrank]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  simp only [normDet, h

中文:
定理 normDet_eq_norm_det_toMatrix_rangeRestrict
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι]
  证明: by
  have hrank : finrank 𝕜 U = finrank 𝕜 f.range := by
    rw [finrank_eq_nat_card_basis bu.toBasis]; rw [finrank_eq_nat_card_basis bv.toBasis]
  have h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) := by
    rw [hrank]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  simp only [normDet, h

Depends on / 依赖: Nonempty, OrthonormalBasis, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, bu.toBasis, bu.toBasis.toMatrix, bv.toBasis, f.range, finrank, finrank_eq_nat_card_basis, h.some.toBasis, normDet, reduceDIte, stdOrthonormalBasis, toBasis, toMatrix
-/
theorem normDet_eq_norm_det_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : U ->ₗ[𝕜] V) (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 f.range) :
    f.normDet = ‖(f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det‖ := by
  have hrank : finrank 𝕜 U = finrank 𝕜 f.range := by
    rw [finrank_eq_nat_card_basis bu.toBasis]; rw [finrank_eq_nat_card_basis bv.toBasis]
  have h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) := by
    rw [hrank]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  simp only [normDet, h, ↓reduceDIte]
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (stdOrthonormalBasis 𝕜 U).toBasis
    bu.toBasis h.some.toBasis bv.toBasis]
  have h1 : bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis = 1 :=
    Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis *
      bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis = 1 :=
    Basis.toMatrix_mul_toMatrix_flip _ _
  rw [← Matrix.det_comm' h1 h2]; rw [← Matrix.mul_assoc]; rw [Matrix.det_mul]; rw [norm_mul]
  suffices ‖(bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      h.some.toBasis.toMatrix ⇑bv.toBasis).det‖ = 1 by
    rw [this]; rw [one_mul]
refine CStarRing.norm_of_mem_unitary Matrix.det_of_mem_unitary ?_
  rw [Matrix.mem_unitaryGroup_iff]; rw [Matrix.star_eq_conjTranspose]; rw [Matrix.conjTranspose_mul]; rw [← Matrix.mul_assoc]; rw [Matrix.mul_assoc (bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis)]
  simp

/--
theorem `normDet_eq_zero_iff_ker_ne_bot` / 定理 `normDet_eq_zero_iff_ker_ne_bot`

English:
theorem normDet_eq_zero_iff_ker_ne_bot
  given: {f : U ->ₗ[𝕜] V}
  proof: by
    contrapose h
    let g : U ≃ₗ[𝕜] f.range := LinearEquiv.ofBijective f.rangeRestrict
      ⟨by simpa using ker_eq_bot.mp h, f.surjective_rangeRestrict⟩
    let bu := stdOrthonormalBasis 𝕜 U
    let bv := g.finrank_eq.symm ▸ stdOrthonormalBasis 𝕜 f.range
    rw [f.normDet_eq_norm_det_toMatrix_r

中文:
定理 normDet_eq_zero_iff_ker_ne_bot
  条件: {f : U ->ₗ[𝕜] V}
  证明: by
    contrapose h
    let g : U ≃ₗ[𝕜] f.range := LinearEquiv.ofBijective f.rangeRestrict
      ⟨by simpa using ker_eq_bot.mp h, f.surjective_rangeRestrict⟩
    let bu := stdOrthonormalBasis 𝕜 U
    let bv := g.finrank_eq.symm ▸ stdOrthonormalBasis 𝕜 f.range
    rw [f.normDet_eq_norm_det_toMatrix_r

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, Matrix, Matrix.det_conjTranspose, adjoint, bu.toBasis, bv.toBasis, contrapose, det_conjTranspose, f.normDet_eq_norm_det_toMatrix_rangeRestrict, f.range, f.rangeRestrict, f.rangeRestrict.adjoint.toMatrix, f.rangeRestrict.toMatrix, f.surjective_rangeRestrict, finrank_eq, g.finrank_eq.symm, ker_eq_bot, ker_eq_bot.mp, normDet_eq_norm_det_toMatrix_rangeRestrict
-/
theorem normDet_eq_zero_iff_ker_ne_bot {f : U ->ₗ[𝕜] V} :
    f.normDet = 0 ↔ f.ker != ⊥ where
  mp h := by
    contrapose h
    let g : U ≃ₗ[𝕜] f.range := LinearEquiv.ofBijective f.rangeRestrict
      ⟨by simpa using ker_eq_bot.mp h, f.surjective_rangeRestrict⟩
    let bu := stdOrthonormalBasis 𝕜 U
    let bv := g.finrank_eq.symm ▸ stdOrthonormalBasis 𝕜 f.range
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv]; rw [norm_eq_zero.not]
    suffices (f.rangeRestrict.adjoint.toMatrix bv.toBasis bu.toBasis).det *
        (f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det != 0 by
      simpa [toMatrix_adjoint, Matrix.det_conjTranspose] using this
    simpa [← Matrix.det_mul, ← LinearMap.toMatrix_comp, det_eq_zero_iff_ker_ne_bot,
      LinearMap.ker_adjoint_comp_self] using h
  mpr h := by
    suffices ¬ Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) by
      simp [normDet, this]
    contrapose h
    obtain ⟨b⟩ := h
    have hrank : finrank 𝕜 f.range = finrank 𝕜 U := by
      simpa using finrank_eq_card_basis b.toBasis
    simpa [hrank] using f.finrank_range_add_finrank_ker

/--
theorem `normDet_eq_zero_iff_rank_range_ne` / 定理 `normDet_eq_zero_iff_rank_range_ne`

English:
theorem normDet_eq_zero_iff_rank_range_ne
  given: {f : U ->ₗ[𝕜] V}
  proof: by
  simp [normDet_eq_zero_iff_ker_ne_bot, ← f.finrank_range_add_finrank_ker]

中文:
定理 normDet_eq_zero_iff_rank_range_ne
  条件: {f : U ->ₗ[𝕜] V}
  证明: by
  simp [normDet_eq_zero_iff_ker_ne_bot, ← f.finrank_range_add_finrank_ker]

Depends on / 依赖: f.finrank_range_add_finrank_ker, finrank_range_add_finrank_ker, normDet_eq_zero_iff_ker_ne_bot
-/
theorem normDet_eq_zero_iff_rank_range_ne {f : U ->ₗ[𝕜] V} :
    f.normDet = 0 ↔ finrank 𝕜 f.range != finrank 𝕜 U := by
  simp [normDet_eq_zero_iff_ker_ne_bot, ← f.finrank_range_add_finrank_ker]

/--
theorem `normDet_ne_zero_tfae` / 定理 `normDet_ne_zero_tfae`

English:
theorem normDet_ne_zero_tfae
  given: (f : U ->ₗ[𝕜] V)
  proof: by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot.not_left
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne.not_left
  tfae_have 3 -> 4 := by
    intro h
    rw [← h]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  tfae_have 4 -> 3 := by
    rintro ⟨b⟩
    simpa using Module.finrank_eq_ca

中文:
定理 normDet_ne_zero_tfae
  条件: (f : U ->ₗ[𝕜] V)
  证明: by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot.not_left
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne.not_left
  tfae_have 3 -> 4 := by
    intro h
    rw [← h]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  tfae_have 4 -> 3 := by
    rintro ⟨b⟩
    simpa using Module.finrank_eq_ca

Depends on / 依赖: Module, Module.finrank_eq_card_basis, b.toBasis, f.normDet_eq_zero_iff_ker_ne_bot.not_left, f.normDet_eq_zero_iff_rank_range_ne.not_left, f.range, finrank_eq_card_basis, ker_eq_bot, normDet_eq_zero_iff_ker_ne_bot, normDet_eq_zero_iff_rank_range_ne, not_left, stdOrthonormalBasis, tfae_finish, tfae_have, toBasis
-/
theorem normDet_ne_zero_tfae (f : U ->ₗ[𝕜] V) :
    List.TFAE [f.normDet != 0,
      f.ker = ⊥,
      finrank 𝕜 f.range = finrank 𝕜 U,
      Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range),
      Function.Injective f] := by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot.not_left
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne.not_left
  tfae_have 3 -> 4 := by
    intro h
    rw [← h]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  tfae_have 4 -> 3 := by
    rintro ⟨b⟩
    simpa using Module.finrank_eq_card_basis b.toBasis
  tfae_have 2 ↔ 5 := ker_eq_bot
  tfae_finish

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def orthonormalBasis_range {ι : Type*} [Fintype ι] {f : U ->ₗ[𝕜] V}
  body: let h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) :=
    (f.normDet_ne_zero_tfae.out 1 3).mp hf
  h.some.reindex (Fintype.equivFinOfCardEq <| (Module.finrank_eq_card_basis b.toBasis).symm).symm

中文:
定义 noncomputable
  签名: def orthonormalBasis_range {ι : 类型} [Fintype ι] {f : U ->ₗ[𝕜] V}
  定义体: let h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) :=
    (f.normDet_ne_zero_tfae.out 1 3).mp hf
  h.some.reindex (Fintype.equivFinOfCardEq <| (Module.finrank_eq_card_basis b.toBasis).symm).symm
-/
private noncomputable def orthonormalBasis_range {ι : Type*} [Fintype ι] {f : U ->ₗ[𝕜] V}
    (hf : f.ker = ⊥) (b : OrthonormalBasis ι 𝕜 U) : OrthonormalBasis ι 𝕜 f.range :=
  let h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) :=
    (f.normDet_ne_zero_tfae.out 1 3).mp hf
  h.some.reindex (Fintype.equivFinOfCardEq <| (Module.finrank_eq_card_basis b.toBasis).symm).symm

/--
theorem `normDet_eq_zero_tfae` / 定理 `normDet_eq_zero_tfae`

English:
theorem normDet_eq_zero_tfae
  given: (f : U ->ₗ[𝕜] V)
  proof: by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne
  tfae_have 3 ↔ 4 := by simpa using finrank_range_le f
  tfae_have 3 ↔ 5 := by
    have h := (f.normDet_ne_zero_tfae.out 2 3).not
    simpa using h
  tfae_have 2 ↔ 6 := ker_eq_bot.not
  

中文:
定理 normDet_eq_zero_tfae
  条件: (f : U ->ₗ[𝕜] V)
  证明: by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne
  tfae_have 3 ↔ 4 := by simpa using finrank_range_le f
  tfae_have 3 ↔ 5 := by
    have h := (f.normDet_ne_zero_tfae.out 2 3).not
    simpa using h
  tfae_have 2 ↔ 6 := ker_eq_bot.not
  

Depends on / 依赖: f.normDet_eq_zero_iff_ker_ne_bot, f.normDet_eq_zero_iff_rank_range_ne, f.normDet_ne_zero_tfae.out, finrank_range_le, ker_eq_bot, ker_eq_bot.not, normDet_eq_zero_iff_ker_ne_bot, normDet_eq_zero_iff_rank_range_ne, normDet_ne_zero_tfae, tfae_finish, tfae_have
-/
theorem normDet_eq_zero_tfae (f : U ->ₗ[𝕜] V) :
    List.TFAE [f.normDet = 0,
      f.ker != ⊥,
      finrank 𝕜 f.range != finrank 𝕜 U,
      finrank 𝕜 f.range < finrank 𝕜 U,
      IsEmpty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range),
      ¬Function.Injective f] := by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne
  tfae_have 3 ↔ 4 := by simpa using finrank_range_le f
  tfae_have 3 ↔ 5 := by
    have h := (f.normDet_ne_zero_tfae.out 2 3).not
    simpa using h
  tfae_have 2 ↔ 6 := ker_eq_bot.not
  tfae_finish

/--
theorem `normDet_eq_norm_det_toMatrix` / 定理 `normDet_eq_norm_det_toMatrix`

English:
theorem normDet_eq_norm_det_toMatrix
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V)
  proof: by
  have : FiniteDimensional 𝕜 V := bv.toBasis.finiteDimensional_of_finite
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · have h : f.range = ⊤ := by
      apply Submodule.eq_of_le_of_finrank_le le_top
      simp [finrank_eq_card_basis bv.toBasis, ← hrank, finrank_eq_card_basis bu.toBasis]


中文:
定理 normDet_eq_norm_det_toMatrix
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V)
  证明: by
  have : FiniteDimensional 𝕜 V := bv.toBasis.finiteDimensional_of_finite
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · have h : f.range = ⊤ := by
      apply Submodule.eq_of_le_of_finrank_le le_top
      simp [finrank_eq_card_basis bv.toBasis, ← hrank, finrank_eq_card_basis bu.toBasis]


Depends on / 依赖: FiniteDimensional, LinearIsometryEquiv, LinearIsometryEquiv.ofTop, OrthonormalBasis, Submodule, Submodule.eq_of_le_of_finrank_le, bu.toBasis, bv.map, bv.toBasis, bv.toBasis.finiteDimensional_of_finite, contrapo, eq_of_le_of_finrank_le, f.normDet_eq_norm_det_toMatrix_rangeRestrict, f.range, finiteDimensional_of_finite, finrank, finrank_eq_card_basis, hrank.symm, le_top, normDet_eq_norm_det_toMatrix_rangeRestrict
-/
theorem normDet_eq_norm_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V)
    (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 V) :
    f.normDet = ‖(f.toMatrix bu.toBasis bv.toBasis).det‖ := by
  have : FiniteDimensional 𝕜 V := bv.toBasis.finiteDimensional_of_finite
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · have h : f.range = ⊤ := by
      apply Submodule.eq_of_le_of_finrank_le le_top
      simp [finrank_eq_card_basis bv.toBasis, ← hrank, finrank_eq_card_basis bu.toBasis]
    let bv' : OrthonormalBasis ι 𝕜 f.range := bv.map (LinearIsometryEquiv.ofTop _ _ h).symm
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv']
    rfl
  · symm
    rw [normDet_eq_zero_iff_rank_range_ne.mpr hrank.symm]
    contrapose hrank with hdet
    have h : IsUnit ((f.toMatrix bu.toBasis bv.toBasis).det) := by
      simpa using hdet
    let f' := LinearEquiv.ofIsUnitDet h
    have hf : f.range = ⊤ := f'.range
    rw [hf]
    simpa using f'.finrank_eq

/--
theorem `normDet_eq_norm_det` / 定理 `normDet_eq_norm_det`

English:
theorem normDet_eq_norm_det
  given: (f : U ->ₗ[𝕜] U)
  statement: f.normDet = ‖f.det‖
  proof: by
  simp [f.normDet_eq_norm_det_toMatrix (stdOrthonormalBasis 𝕜 U) (stdOrthonormalBasis 𝕜 U)]

中文:
定理 normDet_eq_norm_det
  条件: (f : U ->ₗ[𝕜] U)
  结论: f.normDet = ‖f.det‖
  证明: by
  simp [f.normDet_eq_norm_det_toMatrix (stdOrthonormalBasis 𝕜 U) (stdOrthonormalBasis 𝕜 U)]

Depends on / 依赖: f.normDet_eq_norm_det_toMatrix, normDet_eq_norm_det_toMatrix, stdOrthonormalBasis
-/
theorem normDet_eq_norm_det (f : U ->ₗ[𝕜] U) : f.normDet = ‖f.det‖ := by
  simp [f.normDet_eq_norm_det_toMatrix (stdOrthonormalBasis 𝕜 U) (stdOrthonormalBasis 𝕜 U)]

/--
`LinearMap.normDet` of a linear isometry is 1.
-/
@[simp]
/--
theorem `_root_.LinearIsometry.normDet_eq_one` / 定理 `_root_.LinearIsometry.normDet_eq_one`

English:
theorem _root_.LinearIsometry.normDet_eq_one
  given: (f : U ->ₗᵢ[𝕜] V)
  statement: f.toLinearMap.normDet = 1
  proof: by
  obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 4 3).mp f.injective
  rw [normDet_eq_norm_det_toMatrix_rangeRestrict _ (stdOrthonormalBasis 𝕜 U) b]
  apply CStarRing.norm_of_mem_unitary
exact Matrix.det_of_mem_unitary (f.equivRange).toMatrix_mem_unitaryGroup _ _

@[simp]

中文:
定理 _root_.LinearIsometry.normDet_eq_one
  条件: (f : U ->ₗᵢ[𝕜] V)
  结论: f.toLinearMap.normDet = 1
  证明: by
  obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 4 3).mp f.injective
  rw [normDet_eq_norm_det_toMatrix_rangeRestrict _ (stdOrthonormalBasis 𝕜 U) b]
  apply CStarRing.norm_of_mem_unitary
exact Matrix.det_of_mem_unitary (f.equivRange).toMatrix_mem_unitaryGroup _ _

@[simp]

Depends on / 依赖: CStarRing, CStarRing.norm_of_mem_unitary, Matrix, Matrix.det_of_mem_unitary, det_of_mem_unitary, equivRange, f.equivRange, f.injective, f.normDet_ne_zero_tfae.out, injective, normDet_eq_norm_det_toMatrix_rangeRestrict, normDet_ne_zero_tfae, norm_of_mem_unitary, stdOrthonormalBasis, toMatrix_mem_unitaryGroup
-/
theorem _root_.LinearIsometry.normDet_eq_one (f : U ->ₗᵢ[𝕜] V) : f.toLinearMap.normDet = 1 := by
  obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 4 3).mp f.injective
  rw [normDet_eq_norm_det_toMatrix_rangeRestrict _ (stdOrthonormalBasis 𝕜 U) b]
  apply CStarRing.norm_of_mem_unitary
exact Matrix.det_of_mem_unitary (f.equivRange).toMatrix_mem_unitaryGroup _ _

@[simp]
/--
theorem `normDet_id` / 定理 `normDet_id`

English:
theorem normDet_id
  statement: (id : U ->ₗ[𝕜] U).normDet = 1
  proof: LinearIsometry.id.normDet_eq_one

@[simp]

中文:
定理 normDet_id
  结论: (id : U ->ₗ[𝕜] U).normDet = 1
  证明: LinearIsometry.id.normDet_eq_one

@[simp]

Depends on / 依赖: LinearIsometry, LinearIsometry.id.normDet_eq_one, normDet_eq_one
-/
theorem normDet_id : (id : U ->ₗ[𝕜] U).normDet = 1 :=
  LinearIsometry.id.normDet_eq_one

@[simp]
/--
theorem `normDet_subtype` / 定理 `normDet_subtype`

English:
theorem normDet_subtype
  given: (p : Submodule 𝕜 U)
  statement: p.subtype.normDet = 1
  proof: p.subtypeₗᵢ.normDet_eq_one

@[simp]

中文:
定理 normDet_subtype
  条件: (p : Submodule 𝕜 U)
  结论: p.subtype.normDet = 1
  证明: p.subtypeₗᵢ.normDet_eq_one

@[simp]

Depends on / 依赖: normDet_eq_one, p.subtype
-/
theorem normDet_subtype (p : Submodule 𝕜 U) : p.subtype.normDet = 1 :=
  p.subtypeₗᵢ.normDet_eq_one

@[simp]
/--
theorem `normDet_of_subsingleton` / 定理 `normDet_of_subsingleton`

English:
theorem normDet_of_subsingleton
  given: [Subsingleton U] (f : U ->ₗ[𝕜] V)
  statement: f.normDet = 1
  proof: by
  have h : f.ker = ⊥ := Submodule.eq_bot_of_subsingleton
  have hrank : finrank 𝕜 U = 0 := finrank_zero_iff.mpr ‹_›
  let bu : OrthonormalBasis (Fin 0) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (by rw [hrank])
  let bv := orthonormalBasis_range h bu
  simp [normDet_eq_norm_det_toMatrix_rangeRestri

中文:
定理 normDet_of_subsingleton
  条件: [Subsingleton U] (f : U ->ₗ[𝕜] V)
  结论: f.normDet = 1
  证明: by
  have h : f.ker = ⊥ := Submodule.eq_bot_of_subsingleton
  have hrank : finrank 𝕜 U = 0 := finrank_zero_iff.mpr ‹_›
  let bu : OrthonormalBasis (Fin 0) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (by rw [hrank])
  let bv := orthonormalBasis_range h bu
  simp [normDet_eq_norm_det_toMatrix_rangeRestri

Depends on / 依赖: OrthonormalBasis, Submodule, Submodule.eq_bot_of_subsingleton, eq_bot_of_subsingleton, f.ker, finrank, finrank_zero_iff, finrank_zero_iff.mpr, normDet_eq_norm_det_toMatrix_rangeRestrict, orthonormalBasis_range, reindex, stdOrthonormalBasis
-/
theorem normDet_of_subsingleton [Subsingleton U] (f : U ->ₗ[𝕜] V) : f.normDet = 1 := by
  have h : f.ker = ⊥ := Submodule.eq_bot_of_subsingleton
  have hrank : finrank 𝕜 U = 0 := finrank_zero_iff.mpr ‹_›
  let bu : OrthonormalBasis (Fin 0) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (by rw [hrank])
  let bv := orthonormalBasis_range h bu
  simp [normDet_eq_norm_det_toMatrix_rangeRestrict f bu bv]

@[simp]
/--
theorem `normDet_zero` / 定理 `normDet_zero`

English:
theorem normDet_zero
  statement: (0 : U ->ₗ[𝕜] V).normDet = 0 ^ finrank 𝕜 U
  proof: by
  nontriviality U
  simp [zero_pow finrank_pos.ne.symm, normDet_eq_zero_iff_ker_ne_bot]

@[simp]

中文:
定理 normDet_zero
  结论: (0 : U ->ₗ[𝕜] V).normDet = 0 ^ finrank 𝕜 U
  证明: by
  nontriviality U
  simp [zero_pow finrank_pos.ne.symm, normDet_eq_zero_iff_ker_ne_bot]

@[simp]

Depends on / 依赖: finrank_pos, finrank_pos.ne.symm, nontriviality, normDet_eq_zero_iff_ker_ne_bot, zero_pow
-/
theorem normDet_zero : (0 : U ->ₗ[𝕜] V).normDet = 0 ^ finrank 𝕜 U := by
  nontriviality U
  simp [zero_pow finrank_pos.ne.symm, normDet_eq_zero_iff_ker_ne_bot]

@[simp]
/--
theorem `normDet_smul` / 定理 `normDet_smul`

English:
theorem normDet_smul
  given: (f : U ->ₗ[𝕜] V) (c : 𝕜)
  proof: by
  by_cases hc : c = 0
  · nontriviality U
    simp [hc, zero_pow finrank_pos.ne.symm]
  by_cases h : f.ker = ⊥
  · obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    let bv' : OrthonormalBasis (Fin (finrank 𝕜 U

中文:
定理 normDet_smul
  条件: (f : U ->ₗ[𝕜] V) (c : 𝕜)
  证明: by
  by_cases hc : c = 0
  · nontriviality U
    simp [hc, zero_pow finrank_pos.ne.symm]
  by_cases h : f.ker = ⊥
  · obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    let bv' : OrthonormalBasis (Fin (finrank 𝕜 U

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ofEq, LinearMap, LinearMap.range_smul, OrthonormalBasis, bv.map, f.ker, f.normDet_eq_norm_det_toMatrix_rangeRestrict, f.normDet_ne_zero_tfae.out, finrank, finrank_pos, finrank_pos.ne.symm, nontriviality, normDet_eq_norm_det_toMatrix_rangeRestrict, normDet_ne_zero_tfae, range_smul, stdOrthonormalBasis, zero_pow
-/
theorem normDet_smul (f : U ->ₗ[𝕜] V) (c : 𝕜) :
    (c • f).normDet = ‖c‖ ^ finrank 𝕜 U * f.normDet := by
  by_cases hc : c = 0
  · nontriviality U
    simp [hc, zero_pow finrank_pos.ne.symm]
  by_cases h : f.ker = ⊥
  · obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    let bv' : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (c • f).range := bv.map
      (LinearIsometryEquiv.ofEq _ _ (LinearMap.range_smul _ _ hc).symm)
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv]; rw [(c • f).normDet_eq_norm_det_toMatrix_rangeRestrict bu bv']; rw [← norm_pow]; rw [← norm_mul]
    have : finrank 𝕜 U = Fintype.card (Fin (finrank 𝕜 U)) := by simp
    conv in c ^ finrank 𝕜 U => rw [this]
    rw [← Matrix.det_smul]; rw [← map_smul]
    rfl
  · have h' : (c • f).ker != ⊥ := by simpa [f.ker_smul _ hc] using h
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr h, normDet_eq_zero_iff_ker_ne_bot.mpr h']

@[simp]
/--
theorem `normDet_neg` / 定理 `normDet_neg`

English:
theorem normDet_neg
  given: (f : U ->ₗ[𝕜] V)
  statement: (-f).normDet = f.normDet
  proof: by
  simpa using f.normDet_smul (-1)

中文:
定理 normDet_neg
  条件: (f : U ->ₗ[𝕜] V)
  结论: (-f).normDet = f.normDet
  证明: by
  simpa using f.normDet_smul (-1)

Depends on / 依赖: f.normDet_smul, normDet_smul
-/
theorem normDet_neg (f : U ->ₗ[𝕜] V) : (-f).normDet = f.normDet := by
  simpa using f.normDet_smul (-1)

/--
theorem `_root_.ContinuousLinearMap.normDet_sq` / 定理 `_root_.ContinuousLinearMap.normDet_sq`

English:
theorem _root_.ContinuousLinearMap.normDet_sq
  given: [CompleteSpace V] (f : U ->L[𝕜] V)
  proof: FiniteDimensional.complete 𝕜 U
    ↑(f.normDet ^ 2) = (f.adjoint ∘L f).det := by
  have : CompleteSpace U := FiniteDimensional.complete 𝕜 U
  have : CompleteSpace f.range := FiniteDimensional.complete 𝕜 f.range
  let bu := stdOrthonormalBasis 𝕜 U
  by_cases h : f.ker = ⊥
  · obtain ⟨b⟩ := (f.normDet

中文:
定理 _root_.ContinuousLinearMap.normDet_sq
  条件: [CompleteSpace V] (f : U ->L[𝕜] V)
  证明: FiniteDimensional.complete 𝕜 U
    ↑(f.normDet ^ 2) = (f.adjoint ∘L f).det := by
  have : CompleteSpace U := FiniteDimensional.complete 𝕜 U
  have : CompleteSpace f.range := FiniteDimensional.complete 𝕜 f.range
  let bu := stdOrthonormalBasis 𝕜 U
  by_cases h : f.ker = ⊥
  · obtain ⟨b⟩ := (f.normDet

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem _root_.ContinuousLinearMap.normDet_sq [CompleteSpace V] (f : U ->L[𝕜] V) :
    haveI : CompleteSpace U := FiniteDimensional.complete 𝕜 U
    ↑(f.normDet ^ 2) = (f.adjoint ∘L f).det := by
  have : CompleteSpace U := FiniteDimensional.complete 𝕜 U
  have : CompleteSpace f.range := FiniteDimensional.complete 𝕜 f.range
  let bu := stdOrthonormalBasis 𝕜 U
  by_cases h : f.ker = ⊥
  · obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    have hf : f = f.range.subtypeₗᵢ.toContinuousLinearMap ∘L f.rangeRestrict := rfl
    conv_rhs => rw [hf]
    rw [ContinuousLinearMap.adjoint_comp]; rw [← ContinuousLinearMap.comp_assoc]; rw [ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _)]; rw [f.range.subtypeₗᵢ.adjoint_comp_self]; rw [ContinuousLinearMap.one_def]; rw [ContinuousLinearMap.comp_id]; rw [ContinuousLinearMap.det]; rw [ContinuousLinearMap.toLinearMap_comp]; rw [← det_toMatrix bu.toBasis]; rw [toMatrix_comp bu.toBasis b.toBasis bu.toBasis]; rw [← ContinuousLinearMap.adjoint_toLinearMap]; rw [toMatrix_adjoint]; rw [f.toLinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict bu b]
    simp [RCLike.conj_mul]
  · trans 0
    · simp [show f.normDet = 0 from (f.normDet_eq_zero_tfae.out 1 0).mp h]
    symm
    rw [det_eq_zero_iff_ker_ne_bot]; rw [ContinuousLinearMap.ker_adjoint_comp_self]
    exact h

/--
theorem `normDet_sq` / 定理 `normDet_sq`

English:
theorem normDet_sq
  given: [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V)
  proof: by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  exact f.toContinuousLinearMap.normDet_sq

中文:
定理 normDet_sq
  条件: [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V)
  证明: by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  exact f.toContinuousLinearMap.normDet_sq

Depends on / 依赖: CompleteSpace, FiniteDimensional, FiniteDimensional.complete, complete, f.toContinuousLinearMap.normDet_sq, normDet_sq, toContinuousLinearMap
-/
theorem normDet_sq [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) :
    ↑(f.normDet ^ 2) = (f.adjoint ∘ₗ f).det := by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  exact f.toContinuousLinearMap.normDet_sq

/--
theorem `normDet_sq_eq_det_gram` / 定理 `normDet_sq_eq_det_gram`

English:
theorem normDet_sq_eq_det_gram
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V)
  proof: by
  suffices ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f.rangeRestrict <| b ·)).det by
    simpa
  by_cases h : f.ker = ⊥
  · let bv := orthonormalBasis_range h b
    rw [Matrix.gram_eq_conjTranspose_mul bv]; rw [Matrix.det_mul]; rw [Matrix.det_conjTranspose]
    rw [RCLike.star_def]; rw [RCLike.conj_mul]

中文:
定理 normDet_sq_eq_det_gram
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V)
  证明: by
  suffices ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f.rangeRestrict <| b ·)).det by
    simpa
  by_cases h : f.ker = ⊥
  · let bv := orthonormalBasis_range h b
    rw [Matrix.gram_eq_conjTranspose_mul bv]; rw [Matrix.det_mul]; rw [Matrix.det_conjTranspose]
    rw [RCLike.star_def]; rw [RCLike.conj_mul]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.det_conjTranspose, Matrix.det_mul, Matrix.gram, Matrix.gram_eq_conjTranspose_mul, RCLike, RCLike.conj_mul, RCLike.star_def, conj_mul, det_conjTranspose, det_mul, f.ker, f.normDet, f.normDet_eq_norm_det_toMatrix_rangeRestrict, f.normDet_eq_zero_tfae.out, f.rangeRestrict, gram_eq_conjTranspose_mul, map_pow
-/
theorem normDet_sq_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V)
    (b : OrthonormalBasis ι 𝕜 U) :
    ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f <| b ·)).det := by
  suffices ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f.rangeRestrict <| b ·)).det by
    simpa
  by_cases h : f.ker = ⊥
  · let bv := orthonormalBasis_range h b
    rw [Matrix.gram_eq_conjTranspose_mul bv]; rw [Matrix.det_mul]; rw [Matrix.det_conjTranspose]
    rw [RCLike.star_def]; rw [RCLike.conj_mul]; rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict b bv]
    simp only [map_pow]
    congr
    ext i j
    simp [LinearMap.toMatrix_apply]
  · trans 0
    · simp [show f.normDet = 0 from (f.normDet_eq_zero_tfae.out 1 0).mp h]
    have hrank := (f.normDet_eq_zero_tfae.out 1 3).mp h
    symm
    contrapose! hrank with h0
    rw [finrank_eq_card_basis b.toBasis]
    exact (Matrix.linearIndependent_of_det_gram_ne_zero h0).fintype_card_le_finrank

/--
theorem `normDet_comp` / 定理 `normDet_comp`

English:
theorem normDet_comp
  given: (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W)
  proof: by
  by_cases hf : f.ker = ⊥
  · let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp hf
    by_cases hgf : (g ∘ₗ f).ker = ⊥
    · obtain ⟨bw⟩ := ((g ∘ₗ f).normDet_ne_zero_tfae.out 1 3).mp hgf
      let bw' : OrthonormalB

中文:
定理 normDet_comp
  条件: (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W)
  证明: by
  by_cases hf : f.ker = ⊥
  · let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp hf
    by_cases hgf : (g ∘ₗ f).ker = ⊥
    · obtain ⟨bw⟩ := ((g ∘ₗ f).normDet_ne_zero_tfae.out 1 3).mp hgf
      let bw' : OrthonormalB

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ofEq, LinearMap, LinearMap.range_comp, OrthonormalBasis, bw.map, domRestrict, f.ker, f.normDet_eq_norm_det_t, f.normDet_ne_zero_tfae.out, f.range, finrank, g.domRestrict, normDet_eq_norm_det_t, normDet_eq_norm_det_toMatrix_rangeRestrict, normDet_ne_zero_tfae, normDet_ne_zero_tfae.out, range_comp, stdOrthonormalBasis
-/
theorem normDet_comp (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W) :
    (g ∘ₗ f).normDet = (g.domRestrict f.range).normDet * f.normDet := by
  by_cases hf : f.ker = ⊥
  · let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp hf
    by_cases hgf : (g ∘ₗ f).ker = ⊥
    · obtain ⟨bw⟩ := ((g ∘ₗ f).normDet_ne_zero_tfae.out 1 3).mp hgf
      let bw' : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (g.domRestrict f.range).range :=
        bw.map (LinearIsometryEquiv.ofEq _ _ (by simp [LinearMap.range_comp]))
      rw [(g ∘ₗ f).normDet_eq_norm_det_toMatrix_rangeRestrict bu bw]; rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv]; rw [(g.domRestrict f.range).normDet_eq_norm_det_toMatrix_rangeRestrict bv bw']
      rw [← norm_mul]; rw [← Matrix.det_mul]; rw [← LinearMap.toMatrix_comp]
      rfl
    · have hg : (g.domRestrict f.range).ker != ⊥ := by
        contrapose hf with hgf'
        rw [← LinearMap.ker_rangeRestrict]; rw [← LinearMap.ker_comp_of_ker_eq_bot _ hgf']
        exact hgf
      simp [normDet_eq_zero_iff_ker_ne_bot.mpr hgf, normDet_eq_zero_iff_ker_ne_bot.mpr hg]
  · have hgf : (g ∘ₗ f).ker != ⊥ := by
      contrapose hf with hbot
      simpa [hbot] using ker_le_ker_comp f g
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr hf, normDet_eq_zero_iff_ker_ne_bot.mpr hgf]

/--
theorem `normDet_comp_of_finrank_eq` / 定理 `normDet_comp_of_finrank_eq`

English:
theorem normDet_comp_of_finrank_eq
  statement: [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W)
  proof: by
  by_cases htop : f.range = ⊤
  · rw [normDet_comp]
    congrm ?_ * _
    suffices (g.domRestrict f.range).normDet * (id : V ->ₗ[𝕜] V).normDet = g.normDet by simpa
    have : f.range = id.range := by simp [htop]
    convert! (normDet_comp LinearMap.id g).symm
  · have hker : f.ker != ⊥ := by
    

中文:
定理 normDet_comp_of_finrank_eq
  结论: [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W)
  证明: by
  by_cases htop : f.range = ⊤
  · rw [normDet_comp]
    congrm ?_ * _
    suffices (g.domRestrict f.range).normDet * (id : V ->ₗ[𝕜] V).normDet = g.normDet by simpa
    have : f.range = id.range := by simp [htop]
    convert! (normDet_comp LinearMap.id g).symm
  · have hker : f.ker != ⊥ := by
    

Depends on / 依赖: LinearMap, LinearMap.id, congrm, contrapose, convert, domRestrict, f.ker, f.range, g.domRestrict, g.normDet, id.range, ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank, ker_le_ker_comp, normDe, normDet, normDet_comp, normDet_eq_zero_iff_ker_ne_bot, normDet_eq_zero_iff_ker_ne_bot.mpr
-/
theorem normDet_comp_of_finrank_eq [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W)
    (h : finrank 𝕜 U = finrank 𝕜 V) :
    (g ∘ₗ f).normDet = g.normDet * f.normDet := by
  by_cases htop : f.range = ⊤
  · rw [normDet_comp]
    congrm ?_ * _
    suffices (g.domRestrict f.range).normDet * (id : V ->ₗ[𝕜] V).normDet = g.normDet by simpa
    have : f.range = id.range := by simp [htop]
    convert! (normDet_comp LinearMap.id g).symm
  · have hker : f.ker != ⊥ := by
      simpa [ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank h] using htop
    have hker' : (g ∘ₗ f).ker != ⊥ := by
      contrapose hker with hbot
      simpa [hbot] using ker_le_ker_comp f g
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr hker, normDet_eq_zero_iff_ker_ne_bot.mpr hker']

@[simp]
/--
theorem `normDet_codRestrict` / 定理 `normDet_codRestrict`

English:
theorem normDet_codRestrict
  given: {p : Submodule 𝕜 V} {f : U ->ₗ[𝕜] V} (h : forall c, f c in p)
  proof: by
  have : f = p.subtype ∘ₗ f.codRestrict p h := rfl
  conv_rhs => rw [this]
  rw [normDet_comp]
  have : (p.subtype.domRestrict (codRestrict p f h).range).normDet = 1 :=
    (p.subtypeₗᵢ.comp (codRestrict p f h).range.subtypeₗᵢ).normDet_eq_one
  simp [this]

中文:
定理 normDet_codRestrict
  条件: {p : Submodule 𝕜 V} {f : U ->ₗ[𝕜] V} (h : 对任意 c, f c in p)
  证明: by
  have : f = p.subtype ∘ₗ f.codRestrict p h := rfl
  conv_rhs => rw [this]
  rw [normDet_comp]
  have : (p.subtype.domRestrict (codRestrict p f h).range).normDet = 1 :=
    (p.subtypeₗᵢ.comp (codRestrict p f h).range.subtypeₗᵢ).normDet_eq_one
  simp [this]

Depends on / 依赖: codRestrict, conv_rhs, domRestrict, f.codRestrict, normDet, normDet_comp, normDet_eq_one, p.subtype, p.subtype.domRestrict, range.subtype, subtype
-/
theorem normDet_codRestrict {p : Submodule 𝕜 V} {f : U ->ₗ[𝕜] V} (h : forall c, f c in p) :
    (f.codRestrict p h).normDet = f.normDet := by
  have : f = p.subtype ∘ₗ f.codRestrict p h := rfl
  conv_rhs => rw [this]
  rw [normDet_comp]
  have : (p.subtype.domRestrict (codRestrict p f h).range).normDet = 1 :=
    (p.subtypeₗᵢ.comp (codRestrict p f h).range.subtypeₗᵢ).normDet_eq_one
  simp [this]

/--
theorem `normDet_eq_prod_singularValues` / 定理 `normDet_eq_prod_singularValues`

English:
theorem normDet_eq_prod_singularValues
  given: [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V)
  proof: by
  rw [← sq_eq_sq₀ f.normDet_nonneg (Finset.prod_nonneg fun i _ => f.singularValues_nonneg i)]; rw [← RCLike.ofReal_inj (K := 𝕜)]; rw [← Finset.prod_pow]; rw [← Fin.prod_univ_eq_prod_range]; rw [normDet_sq]
  simp_rw [sq_singularValues_fin]
  push_cast
  rw [← LinearMap.IsSymmetric.det_eq_prod_eig

中文:
定理 normDet_eq_prod_singularValues
  条件: [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V)
  证明: by
  rw [← sq_eq_sq₀ f.normDet_nonneg (Finset.prod_nonneg fun i _ => f.singularValues_nonneg i)]; rw [← RCLike.ofReal_inj (K := 𝕜)]; rw [← Finset.prod_pow]; rw [← Fin.prod_univ_eq_prod_range]; rw [normDet_sq]
  simp_rw [sq_singularValues_fin]
  push_cast
  rw [← LinearMap.IsSymmetric.det_eq_prod_eig

Depends on / 依赖: Fin.prod_univ_eq_prod_range, Finset, Finset.prod_nonneg, Finset.prod_pow, IsSymmetric, LinearMap, LinearMap.IsSymmetric.det_eq_prod_eigenvalues, RCLike, RCLike.ofReal_inj, det_eq_prod_eigenvalues, f.normDet_nonneg, f.singularValues_nonneg, normDet_nonneg, normDet_sq, ofReal_inj, prod_nonneg, prod_pow, prod_univ_eq_prod_range, simp_rw, singularValues_nonneg
-/
theorem normDet_eq_prod_singularValues [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) :
    f.normDet = ∏ i in Finset.range (finrank 𝕜 U), f.singularValues i := by
  rw [← sq_eq_sq₀ f.normDet_nonneg (Finset.prod_nonneg fun i _ => f.singularValues_nonneg i)]; rw [← RCLike.ofReal_inj (K := 𝕜)]; rw [← Finset.prod_pow]; rw [← Fin.prod_univ_eq_prod_range]; rw [normDet_sq]
  simp_rw [sq_singularValues_fin]
  push_cast
  rw [← LinearMap.IsSymmetric.det_eq_prod_eigenvalues]

section Real

open MeasureTheory Measure

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U] [FiniteDimensional Real U]
  [NormedAddCommGroup V] [InnerProductSpace Real V]

/--
theorem `normDet_eq_abs_det` / 定理 `normDet_eq_abs_det`

English:
theorem normDet_eq_abs_det
  given: (f : U ->ₗ[Real] U)
  statement: f.normDet = |f.det|
  proof: by
  simpa using f.normDet_eq_norm_det

中文:
定理 normDet_eq_abs_det
  条件: (f : U ->ₗ[实数] U)
  结论: f.normDet = |f.det|
  证明: by
  simpa using f.normDet_eq_norm_det

Depends on / 依赖: f.normDet_eq_norm_det, normDet_eq_norm_det
-/
theorem normDet_eq_abs_det (f : U ->ₗ[Real] U) : f.normDet = |f.det| := by
  simpa using f.normDet_eq_norm_det

/--
theorem `hausdorffMeasure_image` / 定理 `hausdorffMeasure_image`

English:
theorem hausdorffMeasure_image
  statement: [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  proof: by
  by_cases h : f.ker = ⊥
  · have hrank : finrank Real ↥f.range = finrank Real U := (f.normDet_ne_zero_tfae.out 1 2).mp h
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let g : U ≃ₗᵢ[Real] f.range := (stdOrthonormalBasis Real U).equiv bv (Equiv.refl _)
    suffices μH[finrank Real U

中文:
定理 hausdorffMeasure_image
  结论: [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  证明: by
  by_cases h : f.ker = ⊥
  · have hrank : finrank Real ↥f.range = finrank Real U := (f.normDet_ne_zero_tfae.out 1 2).mp h
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let g : U ≃ₗᵢ[Real] f.range := (stdOrthonormalBasis Real U).equiv bv (Equiv.refl _)
    suffices μH[finrank Real U

Depends on / 依赖: ENNReal, ENNReal.ofReal, Equiv.refl, LinearIsometry, LinearIsometry.isom, Set.image_image, f.ker, f.normDet, f.normDet_ne_zero_tfae.out, f.range, f.range.subtype, f.rangeRestrict, finrank, g.symm.toLinearIsometry.toLinearMap, g.toLinearIsometry, image_image, normDet, normDet_ne_zero_tfae, ofReal, rangeRestrict
-/
theorem hausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    (f : U ->ₗ[Real] V) (s : Set U) :
    μH[finrank Real U] (f '' s) = ENNReal.ofReal f.normDet * μH[finrank Real U] s := by
  by_cases h : f.ker = ⊥
  · have hrank : finrank Real ↥f.range = finrank Real U := (f.normDet_ne_zero_tfae.out 1 2).mp h
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let g : U ≃ₗᵢ[Real] f.range := (stdOrthonormalBasis Real U).equiv bv (Equiv.refl _)
    suffices μH[finrank Real U] ((f.range.subtypeₗᵢ.comp g.toLinearIsometry) ''
        ((g.symm.toLinearIsometry.toLinearMap ∘ₗ f.rangeRestrict) '' s)) =
        ENNReal.ofReal f.normDet * μH[finrank Real U] s by
      simpa [Set.image_image]
    rw [(LinearIsometry.isometry _).hausdorffMeasure_image (by simp)]; rw [addHaar_image_linearMap μH[finrank Real U], ← normDet_eq_abs_det,
      normDet_comp_of_finrank_eq _ _ hrank.symm, g.symm.toLinearIsometry.normDet_eq_one]
    simp
  · suffices μH[finrank Real U] (f.range.subtypeₗᵢ '' (f.rangeRestrict '' s)) = 0 by
      simpa [(f.normDet_eq_zero_tfae.out 1 0).mp h, Set.image_image]
    rw [(LinearIsometry.isometry _).hausdorffMeasure_image (by simp)]
    have h : (finrank Real f.range : Real) < finrank Real U := by
      exact_mod_cast (f.normDet_eq_zero_tfae.out 1 3).mp h
    simp [Real.hausdorffMeasure_of_finrank_lt h]

/--
theorem `euclideanHausdorffMeasure_image` / 定理 `euclideanHausdorffMeasure_image`

English:
theorem euclideanHausdorffMeasure_image
  statement: [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
  proof: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply,
    hausdorffMeasure_image]
  exact mul_left_comm _ _ _

中文:
定理 euclideanHausdorffMeasure_image
  结论: [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
  证明: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply,
    hausdorffMeasure_image]
  exact mul_left_comm _ _ _

Depends on / 依赖: Measure, Measure.smul_apply, euclideanHausdorffMeasure_def, hausdorffMeasure_image, mul_left_comm, nnreal_smul_coe_apply, simp_rw, smul_apply
-/
theorem euclideanHausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V] (f : U ->ₗ[Real] V) (s : Set U) :
    μHE[finrank Real U] (f '' s) = ENNReal.ofReal f.normDet * μHE[finrank Real U] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply,
    hausdorffMeasure_image]
  exact mul_left_comm _ _ _

/--
theorem `euclideanHausdorffMeasure_image_eq_normDet_mul_volume` / 定理 `euclideanHausdorffMeasure_image_eq_normDet_mul_volume`

English:
theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume
  statement: [MeasurableSpace U] [BorelSpace U]
  proof: by
  rw [f.euclideanHausdorffMeasure_image]; rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

中文:
定理 euclideanHausdorffMeasure_image_eq_normDet_mul_volume
  结论: [MeasurableSpace U] [BorelSpace U]
  证明: by
  rw [f.euclideanHausdorffMeasure_image]; rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, equivShrink, euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_image, f.euclideanHausdorffMeasure_image, normedAddCommGroup, symm.normedAddCommGroup
-/
theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace V] [BorelSpace V] (f : U ->ₗ[Real] V) (s : Set U) :
    μHE[finrank Real U] (f '' s) = ENNReal.ofReal f.normDet * volume s := by
  rw [f.euclideanHausdorffMeasure_image]; rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Real

end LinearMap
