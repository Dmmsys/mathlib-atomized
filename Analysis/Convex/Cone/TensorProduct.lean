/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Geometry.Convex.Cone.TensorProduct
public import Mathlib.Topology.Algebra.Module.TopDualPairing

/-!
# Tensor Products of Pointed Cones

This file proves that the minimal and maximal tensor products of pointed cones in
finite-dimensional real vector spaces are equal when one cone is simplicial and generating
and the other is proper (pointed and closed).

Finite-dimensionality of the proper cone ambient space is by explicit declaration and is required
for the `topDualPairing_isContPerfPair` instance (in `Topology.Algebra.Module.TopDualPairing`).
The simplicial and generating cone ambient space is implicitly finite dimensional by the
simplicial and generating assumption.

This file uses `topDualPairing` (the canonical pairing of a vector space and its topological dual)
to avoid explicit topology assumptions on `Module.Dual`.

The proof relies on the following result:

* **Bipolar theorem** (`ProperCone.dual_dual_flip`): The double dual of a proper cone is itself.

This requires:
- Local convexity and Hausdorff separation (for Hahn-Banach)
- A continuous perfect pairing between the module and its dual.

## Main results

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left`:
  If `C₁` is simplicial and generating and `C₂` is proper, then the minimal and
  maximal tensor products are equal.

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_right`:
  If `C₁` is a proper cone and `C₂` is a simplicial and generating cone, then their minimal
  and maximal tensor products are equal.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/

public section

/-! ### Equality of minimal and maximal tensor products -/

namespace PointedCone

section BasisCoordDual

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

open Module

/--
lemma `basis_coord_mem_dual` / 引理 `basis_coord_mem_dual`

English:
lemma basis_coord_mem_dual
  statement: {ι : Type*} (b : Basis ι R M) (C : PointedCone R M)
  proof: by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

中文:
引理 basis_coord_mem_dual
  结论: {ι : 类型} (b : 基 ι R M) (C : PointedCone R M)
  证明: by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

Depends on / 依赖: Finsupp, Finsupp.single_apply, classical, dual_le_dual, ite_nonneg, le_rfl, single_apply, zero_le_one
-/
lemma basis_coord_mem_dual {ι : Type*} (b : Basis ι R M) (C : PointedCone R M)
    (hC : (C : Set M) subseteq (hull R (Set.range b) : Set M)) (i : ι) :
    b.coord i in dual (Dual.eval R M) (C : Set M) := by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

end BasisCoordDual

section MainTheorems

variable {E F : Type*} [AddCommGroup E] [Module Real E] [AddCommGroup F] [Module Real F]

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
variable [FiniteDimensional Real F] [ContinuousSMul Real F] [LocallyConvexSpace Real F]

open TensorProduct Module

set_option backward.isDefEq.respectTransparency false in
/--
theorem `minTensorProduct_eq_max_of_simplicial_generating_left` / 定理 `minTensorProduct_eq_max_of_simplicial_generating_left`

English:
theorem minTensorProduct_eq_max_of_simplicial_generating_left
  statement: (C₁ : PointedCone Real E)
  proof: by
  classical
  obtain ⟨s, hs_fin, hs_lin, hs_span⟩ := h₁_simp
  have : Fintype s := hs_fin.fintype
  -- The conic hull (R≥0-span) is contained in the linear span (ℝ-span)
  have hull_sub_span : (hull Real s : Set E) subseteq Submodule.span Real s := by
    intro x hx
    rw [SetLike.mem_coe]; rw [

中文:
定理 minTensorProduct_eq_max_of_simplicial_generating_left
  结论: (C₁ : PointedCone 实数 E)
  证明: by
  classical
  obtain ⟨s, hs_fin, hs_lin, hs_span⟩ := h₁_simp
  have : Fintype s := hs_fin.fintype
  -- The conic hull (R≥0-span) is contained in the linear span (ℝ-span)
  have hull_sub_span : (hull Real s : Set E) subseteq Submodule.span Real s := by
    intro x hx
    rw [SetLike.mem_coe]; rw [

Depends on / 依赖: Fintype, classical, fintype, hs_fin, hs_fin.fintype, hs_lin, hs_span
-/
theorem minTensorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone Real E)
    (C₂ : ProperCone Real F) (h₁_simp : C₁.IsSimplicial) (h₁_gen : Submodule.span Real (C₁ : Set E) = ⊤) :
    minTensorProduct C₁ C₂.toPointedCone = maxTensorProduct C₁ C₂.toPointedCone := by
  classical
  obtain ⟨s, hs_fin, hs_lin, hs_span⟩ := h₁_simp
  have : Fintype s := hs_fin.fintype
  -- The conic hull (R≥0-span) is contained in the linear span (ℝ-span)
  have hull_sub_span : (hull Real s : Set E) subseteq Submodule.span Real s := by
    intro x hx
    rw [SetLike.mem_coe]; rw [PointedCone.mem_hull_set] at hx
    obtain ⟨c, hc_supp, _, hc_sum⟩ := hx
    exact hc_sum ▸ Submodule.sum_mem _ fun m hm =>
      Submodule.smul_mem _ _ (Submodule.subset_span (hc_supp hm))
  -- Extract basis from `C₁.IsSimplicial` + generating
let b := Basis.mk hs_lin by
    simpa only [id_eq, Subtype.range_coe] using!
      h₁_gen ▸ hs_span ▸ Submodule.span_le.mpr hull_sub_span
  -- Dual basis elements are in C₁*
  have h_coord_dual : forall i, b.coord i in dual (Dual.eval Real E) C₁ :=
    basis_coord_mem_dual _ _ (hs_span ▸ (Submodule.span_mono <| by simp [b]))
  -- Reduce to proving z ∈ max → z ∈ min
  apply le_antisymm (minTensorProduct_le_maxTensorProduct C₁ C₂.toPointedCone)
  intro z hz
  -- Express z using basis: z = ∑ b_i ⊗ y_i
  rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply z]; rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply]; rw [Finsupp.sum_fintype _ _ (by simp)]
  -- Show z ∈ min by showing b_i ∈ C₁ and y_i ∈ C₂
  refine Submodule.sum_mem _ fun i _ => tmul_mem_minTensorProduct ?_ ?_
  · simpa only [b, Basis.coe_mk] using! (hs_span ▸ subset_hull) i.prop
  · simp only [equivFinsuppOfBasisLeft_apply]
    rw [← ProperCone.dual_dual_flip (topDualPairing Real F) C₂]
    intro f (hf : (f : F ->ₗ[Real] Real) in dual (Dual.eval Real F) (C₂ : Set F))
    simp only [mem_maxTensorProduct] at hz
    have h_nonneg := hz (b.coord i) (h_coord_dual i) (f : F ->ₗ[Real] Real) hf
    have h_eq : dualDistrib Real E F ((b.coord i) otimesₜ[Real] (f : F ->ₗ[Real] Real)) =
        (f : F ->ₗ[Real] Real) ∘ₗ (TensorProduct.lid Real F) ∘ₗ (b.coord i).rTensor F := by
      ext; simp [mul_comm]
    simpa only [h_eq, LinearMap.comp_apply, LinearEquiv.coe_coe] using! h_nonneg

/--
theorem `minTensorProduct_eq_max_of_simplicial_generating_right` / 定理 `minTensorProduct_eq_max_of_simplicial_generating_right`

English:
theorem minTensorProduct_eq_max_of_simplicial_generating_right
  statement: (C₁ : ProperCone Real F)
  proof: by
  rw [← minTensorProduct_comm]; rw [← maxTensorProduct_comm]; rw [minTensorProduct_eq_max_of_simplicial_generating_left C₂ C₁ h₂_simp h₂_gen]

中文:
定理 minTensorProduct_eq_max_of_simplicial_generating_right
  结论: (C₁ : ProperCone 实数 F)
  证明: by
  rw [← minTensorProduct_comm]; rw [← maxTensorProduct_comm]; rw [minTensorProduct_eq_max_of_simplicial_generating_left C₂ C₁ h₂_simp h₂_gen]

Depends on / 依赖: InnerProductSpaceable, InnerProductSpaceable.to_uniformConvexSpace, UniformConvexSpace, infer_instance, maxTensorProduct_comm, minTensorProduct_comm, minTensorProduct_eq_max_of_simplicial_generating_left, nonempty_innerProductSpace, to_uniformConvexSpace
-/
theorem minTensorProduct_eq_max_of_simplicial_generating_right (C₁ : ProperCone Real F)
    (C₂ : PointedCone Real E) (h₂_simp : C₂.IsSimplicial)
    (h₂_gen : Submodule.span Real (C₂ : Set E) = ⊤) :
    minTensorProduct C₁.toPointedCone C₂ = maxTensorProduct C₁.toPointedCone C₂ := by
  rw [← minTensorProduct_comm]; rw [← maxTensorProduct_comm]; rw [minTensorProduct_eq_max_of_simplicial_generating_left C₂ C₁ h₂_simp h₂_gen]

end MainTheorems

end PointedCone
