/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! # Closures of convex sets in locally convex spaces

This file contains the standard result that if `E` is a vector space with two locally convex
topologies, then the closure of a convex set is the same in either topology, provided they have the
same collection of continuous linear functionals. In particular, the weak closure of a convex set
in a locally convex space coincides with the closure in the original topology.
Of course, we phrase this in terms of linear maps between locally convex spaces, rather than
creating two separate topologies on the same space.
-/

public section

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [Module Real E] [IsScalarTower Real 𝕜 E] [Module Real F] [IsScalarTower Real 𝕜 F]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace Real E]
variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace Real F]

set_option backward.isDefEq.respectTransparency.types false in
variable (𝕜) in
/--
theorem `Convex.toWeakSpace_closure` / 定理 `Convex.toWeakSpace_closure`

English:
theorem Convex.toWeakSpace_closure
  given: {s : Set E} (hs : Convex Real s)
  proof: by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx => ?_)
.symm.subset hx obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s)
  have : ContinuousSMul Real E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨

中文:
定理 凸.toWeakSpace_closure
  条件: {s : 集合 E} (hs : 凸 实数 s)
  证明: by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx => ?_)
.symm.subset hx obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s)
  have : ContinuousSMul Real E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨

Depends on / 依赖: ContinuousSMul, IsScalarTower, IsScalarTower.continuousSMul, RCLike, RCLike.geometric_hahn_banach_closed_point, Set.compl_subset_compl.mp, StrongDual, WeakSpace, closure, compl_subset_compl, continuousOn, continuousOn.image_closure, continuousSMul, geometric_hahn_banach_closed_point, hs.closure, image_closure, image_compl, isClosed_closure, le_antisymm, map_continuous
-/
theorem Convex.toWeakSpace_closure {s : Set E} (hs : Convex Real s) :
    (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s) := by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx => ?_)
.symm.subset hx obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s)
  have : ContinuousSMul Real E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨f, u, hus, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    hs.closure isClosed_closure (by simpa using hx)
  let f' : StrongDual 𝕜 (WeakSpace 𝕜 E) :=
    { toLinearMap := (f : E ->ₗ[𝕜] 𝕜).comp ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E ->ₗ[𝕜] E)
      cont := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip _ }
  have hux' : u < RCLike.reCLM.comp (f'.restrictScalars Real) (toWeakSpace 𝕜 E x) := by simpa [f']
  have hus' : closure (toWeakSpace 𝕜 E '' s) subseteq
      {y | RCLike.reCLM.comp (f'.restrictScalars Real) y <= u} := by
refine closure_minimal ?_ isClosed_le (by fun_prop) (by fun_prop)
    rintro - ⟨y, hy, rfl⟩
    simpa [f'] using (hus y <| subset_closure hy).le
  exact (hux'.not_ge <| hus' ·)

open ComplexOrder in
/--
theorem `toWeakSpace_closedConvexHull_eq` / 定理 `toWeakSpace_closedConvexHull_eq`

English:
theorem toWeakSpace_closedConvexHull_eq
  given: {s : Set E}
  proof: by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜)]; rw [((convex_convexHull 𝕜 s).lift Real).toWeakSpace_closure _]; rw [closedConvexHull_eq_closure_convexHull]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap s

中文:
定理 toWeakSpace_closedConvexHull_eq
  条件: {s : 集合 E}
  证明: by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜)]; rw [((convex_convexHull 𝕜 s).lift Real).toWeakSpace_closure _]; rw [closedConvexHull_eq_closure_convexHull]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap s

Depends on / 依赖: LinearMap, LinearMap.image_convexHull, closedConvexHull_eq_closure_convexHull, convex_convexHull, image_convexHull, toLinearMap, toWeakSpace, toWeakSpace_closure
-/
theorem toWeakSpace_closedConvexHull_eq {s : Set E} :
    (toWeakSpace 𝕜 E) '' (closedConvexHull 𝕜 s) = closedConvexHull 𝕜 (toWeakSpace 𝕜 E '' s) := by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜)]; rw [((convex_convexHull 𝕜 s).lift Real).toWeakSpace_closure _]; rw [closedConvexHull_eq_closure_convexHull]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap s

/--
theorem `LinearMap.image_closure_of_convex` / 定理 `LinearMap.image_closure_of_convex`

English:
theorem LinearMap.image_closure_of_convex
  statement: {s : Set E} (hs : Convex Real s) (e : E ->ₗ[𝕜] F)
  proof: by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex Real (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective]; rw [h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toW

中文:
定理 线性映射.image_closure_of_convex
  结论: {s : 集合 E} (hs : 凸 实数 s) (e : E ->ₗ[𝕜] F)
  证明: by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex Real (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective]; rw [h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toW

Depends on / 依赖: Continuous, Convex, LinearEquiv, LinearEquiv.symm_apply_apply, Set.image_image, Set.image_subset_image_iff, WeakBilin, WeakBilin.continuous_of_continuous_eval, WeakBilin.eval_continuous, continuousOn, continuousOn.image_closure, continuous_of_continuous_eval, eval_continuous, h_convex, h_convex.toWeakSpace_closure, hs.linear_image, hs.toWeakSpace_closure, image_closure, image_image, image_subset_image_iff
-/
theorem LinearMap.image_closure_of_convex {s : Set E} (hs : Convex Real s) (e : E ->ₗ[𝕜] F)
    (he : forall f : StrongDual 𝕜 F, Continuous (e.dualMap f)) :
    e '' (closure s) subseteq closure (e '' s) := by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex Real (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective]; rw [h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toWeakSpace_closure 𝕜, LinearEquiv.symm_apply_apply]
      using he'.continuousOn.image_closure (s := toWeakSpace 𝕜 E '' s)
  exact WeakBilin.continuous_of_continuous_eval _ fun f => WeakBilin.eval_continuous _ ({
      toLinearMap := e.dualMap f
      cont := by dsimp; fun_prop } : StrongDual 𝕜 E)

/--
theorem `LinearEquiv.image_closure_of_convex` / 定理 `LinearEquiv.image_closure_of_convex`

English:
theorem LinearEquiv.image_closure_of_convex
  statement: {s : Set E} (hs : Convex Real s) (e : E ≃ₗ[𝕜] F)
  proof: by
  refine le_antisymm ((e : E ->ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F ->ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E ->ₗ[𝕜] F)) he₂

中文:
定理 线性等价.image_closure_of_convex
  结论: {s : 集合 E} (hs : 凸 实数 s) (e : E ≃ₗ[𝕜] F)
  证明: by
  refine le_antisymm ((e : E ->ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F ->ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E ->ₗ[𝕜] F)) he₂

Depends on / 依赖: Set.image_image, Set.image_subset_image_iff, e.symm, e.symm.injective, hs.linear_image, image_closure_of_convex, image_image, image_subset_image_iff, injective, le_antisymm, linear_image
-/
theorem LinearEquiv.image_closure_of_convex {s : Set E} (hs : Convex Real s) (e : E ≃ₗ[𝕜] F)
    (he₁ : forall f : StrongDual 𝕜 F, Continuous (e.dualMap f))
    (he₂ : forall f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)) :
    e '' (closure s) = closure (e '' s) := by
  refine le_antisymm ((e : E ->ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F ->ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E ->ₗ[𝕜] F)) he₂

/--
theorem `LinearEquiv.image_closure_of_convex'` / 定理 `LinearEquiv.image_closure_of_convex'`

English:
theorem LinearEquiv.image_closure_of_convex'
  statement: {s : Set E} (hs : Convex Real s) (e : E ≃ₗ[𝕜] F)
  proof: by
  have he' (f : StrongDual 𝕜 E) : (e_dual.symm f : F ->ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : StrongDual 𝕜 E) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
  

中文:
定理 线性等价.image_closure_of_convex'
  结论: {s : 集合 E} (hs : 凸 实数 s) (e : E ≃ₗ[𝕜] F)
  证明: by
  have he' (f : StrongDual 𝕜 E) : (e_dual.symm f : F ->ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : StrongDual 𝕜 E) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
  

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, DFunLike, DFunLike.ext, LinearEquiv, LinearEquiv.dualMap_apply, StrongDual, _iff, apply_symm_apply, coe_coe, conv_rhs, dualMap, dualMap_apply, e.image_closure_of_convex, e.symm.dualMap, e_dual, e_dual.apply_symm_apply, e_dual.symm, image_closure_of_convex, map_co
-/
theorem LinearEquiv.image_closure_of_convex' {s : Set E} (hs : Convex Real s) (e : E ≃ₗ[𝕜] F)
    (e_dual : StrongDual 𝕜 F ≃ StrongDual 𝕜 E)
    (he : forall f : StrongDual 𝕜 F, (e_dual f : E ->ₗ[𝕜] 𝕜) = e.dualMap f) :
    e '' (closure s) = closure (e '' s) := by
  have he' (f : StrongDual 𝕜 E) : (e_dual.symm f : F ->ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : StrongDual 𝕜 E) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
    ext x
    conv_rhs => rw [LinearEquiv.dualMap_apply, ContinuousLinearMap.coe_coe, this]
    simp
  refine e.image_closure_of_convex hs ?_ ?_
  · simpa [← he] using fun f => map_continuous (e_dual f)
  · simpa [← he'] using fun f => map_continuous (e_dual.symm f)

/-- The weak topology on a space with separating dual is T2 (Hausdorff). -/
instance {R V : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]
    [ContinuousAdd R] [ContinuousConstSMul R R] [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [SeparatingDual R V] : T2Space (WeakSpace R V) :=
  (WeakBilin.isEmbedding (B := (topDualPairing R V).flip) fun _ _ h => by
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := R) hne
    exact hf (DFunLike.congr_fun h f)).t2Space
