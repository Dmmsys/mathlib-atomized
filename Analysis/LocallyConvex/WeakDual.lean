/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicitly give a neighborhood basis in terms of the family of seminorms
`fun x => ‖B x y‖` for `y : F`.

## Main definitions

* `LinearMap.toSeminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `fun x => ‖f x‖`.
* `LinearMap.toSeminormFamily`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
  `F → Seminorm 𝕜 E`.

## Main statements

* `LinearMap.hasBasis_weakBilin`: the seminorm balls of `B.toSeminormFamily` form a
  neighborhood basis of `0` in the weak topology.
* `LinearMap.toSeminormFamily.withSeminorms`: the topology of a weak space is induced by the
  family of seminorms `B.toSeminormFamily`.
* `WeakBilin.locallyConvexSpace`: a space endowed with a weak topology is locally convex.
* `LinearMap.rightDualEquiv`: When `B` is right-separating, `F` is linearly equivalent to the
  strong dual of `E` with the weak topology.
* `LinearMap.leftDualEquiv`: When `B` is left-separating, `E` is linearly equivalent to the
  strong dual of `F` with the weak topology.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]
* [Rudin, *Functional Analysis*][rudin1991]

## Tags

weak dual, seminorm
-/

@[expose] public section


variable {𝕜 E F : Type*}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/--
Definition of `toSeminorm` / `toSeminorm` 的定义

English:
definition toSeminorm
  signature: (f : E ->ₗ[𝕜] 𝕜)
  body: (normSeminorm 𝕜 𝕜).comp f

中文:
定义 toSeminorm
  签名: (f : E ->ₗ[𝕜] 𝕜)
  定义体: (normSeminorm 𝕜 𝕜).comp f

Depends on / 依赖: normSeminorm
-/
def toSeminorm (f : E ->ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f

/--
theorem `coe_toSeminorm` / 定理 `coe_toSeminorm`

English:
theorem coe_toSeminorm
  given: {f : E ->ₗ[𝕜] 𝕜}
  statement: ⇑f.toSeminorm = fun x => ‖f x‖
  proof: rfl

@[simp]

中文:
定理 coe_toSeminorm
  条件: {f : E ->ₗ[𝕜] 𝕜}
  结论: ⇑f.toSeminorm = fun x => ‖f x‖
  证明: rfl

@[simp]
-/
theorem coe_toSeminorm {f : E ->ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl

@[simp]
/--
theorem `toSeminorm_apply` / 定理 `toSeminorm_apply`

English:
theorem toSeminorm_apply
  given: {f : E ->ₗ[𝕜] 𝕜} {x : E}
  statement: f.toSeminorm x = ‖f x‖
  proof: rfl

中文:
定理 toSeminorm_apply
  条件: {f : E ->ₗ[𝕜] 𝕜} {x : E}
  结论: f.toSeminorm x = ‖f x‖
  证明: rfl
-/
theorem toSeminorm_apply {f : E ->ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl

/--
theorem `toSeminorm_ball_zero` / 定理 `toSeminorm_ball_zero`

English:
theorem toSeminorm_ball_zero
  given: {f : E ->ₗ[𝕜] 𝕜} {r : Real}
  proof: by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]

中文:
定理 toSeminorm_ball_zero
  条件: {f : E ->ₗ[𝕜] 𝕜} {r : 实数}
  证明: by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]

Depends on / 依赖: Seminorm, Seminorm.ball_zero_eq, ball_zero_eq, toSeminorm_apply
-/
theorem toSeminorm_ball_zero {f : E ->ₗ[𝕜] 𝕜} {r : Real} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]

/--
theorem `toSeminorm_comp` / 定理 `toSeminorm_comp`

English:
theorem toSeminorm_comp
  given: (f : F ->ₗ[𝕜] 𝕜) (g : E ->ₗ[𝕜] F)
  proof: by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

中文:
定理 toSeminorm_comp
  条件: (f : F ->ₗ[𝕜] 𝕜) (g : E ->ₗ[𝕜] F)
  证明: by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, Seminorm, Seminorm.comp_apply, coe_comp, comp_apply, toSeminorm_apply
-/
theorem toSeminorm_comp (f : F ->ₗ[𝕜] 𝕜) (g : E ->ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

/--
Definition of `toSeminormFamily` / `toSeminormFamily` 的定义

English:
definition toSeminormFamily
  signature: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  body: fun y =>
  (B.flip y).toSeminorm

@[simp]

中文:
定义 toSeminormFamily
  签名: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  定义体: fun y =>
  (B.flip y).toSeminorm

@[simp]
-/
def toSeminormFamily (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm

@[simp]
/--
theorem `toSeminormFamily_apply` / 定理 `toSeminormFamily_apply`

English:
theorem toSeminormFamily_apply
  given: {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} {x y}
  statement: (B.toSeminormFamily y) x = ‖B x y‖
  proof: rfl

中文:
定理 toSeminormFamily_apply
  条件: {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} {x y}
  结论: (B.toSeminormFamily y) x = ‖B x y‖
  证明: rfl
-/
theorem toSeminormFamily_apply {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl

/--
lemma `dualEmbedding_injective_of_separatingRight` / 引理 `dualEmbedding_injective_of_separatingRight`

English:
lemma dualEmbedding_injective_of_separatingRight
  given: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) (hr : B.SeparatingRight)
  proof: (injective_iff_map_eq_zero _).mpr (fun f hf =>
    (separatingRight_iff_linear_flip_nontrivial.mp hr) f (ContinuousLinearMap.coe_inj.mpr hf))

中文:
引理 dualEmbedding_injective_of_separatingRight
  条件: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) (hr : B.SeparatingRight)
  证明: (injective_iff_map_eq_zero _).mpr (fun f hf =>
    (separatingRight_iff_linear_flip_nontrivial.mp hr) f (ContinuousLinearMap.coe_inj.mpr hf))

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_inj.mpr, coe_inj, injective_iff_map_eq_zero, separatingRight_iff_linear_flip_nontrivial, separatingRight_iff_linear_flip_nontrivial.mp
-/
lemma dualEmbedding_injective_of_separatingRight (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) (hr : B.SeparatingRight) :
    Function.Injective (WeakBilin.eval B) :=
  (injective_iff_map_eq_zero _).mpr (fun f hf =>
    (separatingRight_iff_linear_flip_nontrivial.mp hr) f (ContinuousLinearMap.coe_inj.mpr hf))

variable {ι 𝕜 E F : Type*}

open Topology TopologicalSpace
open scoped NNReal

section

section TopologicalRing

variable [Finite ι] [Field 𝕜] [t𝕜 : TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [T0Space 𝕜]

/--
theorem `mem_span_iff_continuous_of_finite` / 定理 `mem_span_iff_continuous_of_finite`

English:
theorem mem_span_iff_continuous_of_finite
  given: {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜)
  proof: by
  let _ := ⨅ i, induced (f i) t𝕜
  constructor
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i => continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ => .add) (fun c _ _ h => h.const_smul c)
  · intro φ_cont
    refine mem_span_of_iInf_ker_le_ker fun x hx => ?_
    simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    have : Inseparable x 0 := by
      -- Maybe missing lemmas about `Inseparable`?
      simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
    simpa only [map_zero] using (this.map φ_cont).eq

中文:
定理 mem_span_iff_continuous_of_finite
  条件: {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜)
  证明: by
  let _ := ⨅ i, induced (f i) t𝕜
  constructor
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i => continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ => .add) (fun c _ _ h => h.const_smul c)
  · intro φ_cont
    refine mem_span_of_iInf_ker_le_ker fun x hx => ?_
    simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    have : Inseparable x 0 := by
      -- Maybe missing lemmas about `Inseparable`?
      simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
    simpa only [map_zero] using (this.map φ_cont).eq

Depends on / 依赖: Inseparable, LinearMap, LinearMap.mem_ker, Set.forall_mem_range.mpr, Submodule, Submodule.mem_iInf, Submodule.span_induction, const_smul, continuous_iInf_dom, continuous_induced_dom, continuous_zero, forall_mem_range, h.const_smul, induced, mem_iInf, mem_ker, mem_span_of_iInf_ker_le_ker, simp_rw, span_induction
-/
theorem mem_span_iff_continuous_of_finite {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) :
    φ in Submodule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i, induced (f i) t𝕜, t𝕜] φ := by
  let _ := ⨅ i, induced (f i) t𝕜
  constructor
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i => continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ => .add) (fun c _ _ h => h.const_smul c)
  · intro φ_cont
    refine mem_span_of_iInf_ker_le_ker fun x hx => ?_
    simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    have : Inseparable x 0 := by
      -- Maybe missing lemmas about `Inseparable`?
      simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
    simpa only [map_zero] using (this.map φ_cont).eq

end TopologicalRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
theorem `mem_span_iff_continuous` / 定理 `mem_span_iff_continuous`

English:
theorem mem_span_iff_continuous
  given: {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜)
  proof: by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t₁ : TopologicalSpace E := ⨅ i, induced (f i) t𝕜
  let t₂ (s : Finset ι) : TopologicalSpace E := ⨅ i : s, induced (f i) t𝕜
  suffices
      Continuous[t₁, t𝕜] φ ↔ exists s : Finset ι, Continuous[t₂ s, t𝕜] φ by
    simp_rw [this, ← mem_span_iff_continuous_of_finite, Submodule.span_range_eq_iSup,
      iSup_subtype]
    rw [Submodule.mem_iSup_iff_exists_finset]
  have t₁_group : @IsTopologicalAddGroup E t₁ _ :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have t₂_group (s : Finset ι) : @IsTopologicalAddGroup E (t₂ s) _ :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have t₁_smul : @ContinuousSMul 𝕜 E _ _ t₁ :=
    continuousSMul_iInf fun _ => continuousSMul_induced _
  have t₂_smul (s : Finset ι) : @ContinuousSMul 𝕜 E _ _ (t₂ s) :=
    continuousSMul_iInf fun _ => continuousSMul_induced _
  simp_rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const]
  conv in Continuous _ => rw [Seminorm.continuous_iff one_pos, nhds_iInf]
  conv in Continuous _ =>
    rw [letI := t₂ s; Seminorm.continuous_iff one_pos]; rw [nhds_iInf]; rw [iInf_subtype]
  rw [Filter.mem_iInf_finite]

中文:
定理 mem_span_iff_continuous
  条件: {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜)
  证明: by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t₁ : TopologicalSpace E := ⨅ i, induced (f i) t𝕜
  let t₂ (s : Finset ι) : TopologicalSpace E := ⨅ i : s, induced (f i) t𝕜
  suffices
      Continuous[t₁, t𝕜] φ ↔ exists s : Finset ι, Continuous[t₂ s, t𝕜] φ by
    simp_rw [this, ← mem_span_iff_continuous_of_finite, Submodule.span_range_eq_iSup,
      iSup_subtype]
    rw [Submodule.mem_iSup_iff_exists_finset]
  have t₁_group : @IsTopologicalAddGroup E t₁ _ :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have t₂_group (s : Finset ι) : @IsTopologicalAddGroup E (t₂ s) _ :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have t₁_smul : @ContinuousSMul 𝕜 E _ _ t₁ :=
    continuousSMul_iInf fun _ => continuousSMul_induced _
  have t₂_smul (s : Finset ι) : @ContinuousSMul 𝕜 E _ _ (t₂ s) :=
    continuousSMul_iInf fun _ => continuousSMul_induced _
  simp_rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const]
  conv in Continuous _ => rw [Seminorm.continuous_iff one_pos, nhds_iInf]
  conv in Continuous _ =>
    rw [letI := t₂ s; Seminorm.continuous_iff one_pos]; rw [nhds_iInf]; rw [iInf_subtype]
  rw [Filter.mem_iInf_finite]

Depends on / 依赖: Continuous, Finset, IsTopologicalAddGroup, Submodule, Submodule.mem_iSup_iff_exists_finset, Submodule.span_range_eq_iSup, TopologicalSpace, iSup_subtype, induced, mem_iSup_iff_exists_finset, mem_span_iff_continuous_of_finite, simp_rw, span_range_eq_iSup, topologicalAddGroup_iInf, topologicalAddGroup_induced
-/
theorem mem_span_iff_continuous {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) :
    φ in Submodule.span 𝕜 (Set.range f) ↔
    Continuous[⨅ i, induced (f i) inferInstance, inferInstance] φ := by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t₁ : TopologicalSpace E := ⨅ i, induced (f i) t𝕜
  let t₂ (s : Finset ι) : TopologicalSpace E := ⨅ i : s, induced (f i) t𝕜
  suffices
      Continuous[t₁, t𝕜] φ ↔ exists s : Finset ι, Continuous[t₂ s, t𝕜] φ by
    simp_rw [this, ← mem_span_iff_continuous_of_finite, Submodule.span_range_eq_iSup,
      iSup_subtype]
    rw [Submodule.mem_iSup_iff_exists_finset]
  have t₁_group : @IsTopologicalAddGroup E t₁ _ :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have t₂_group (s : Finset ι) : @IsTopologicalAddGroup E (t₂ s) _ :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have t₁_smul : @ContinuousSMul 𝕜 E _ _ t₁ :=
    continuousSMul_iInf fun _ => continuousSMul_induced _
  have t₂_smul (s : Finset ι) : @ContinuousSMul 𝕜 E _ _ (t₂ s) :=
    continuousSMul_iInf fun _ => continuousSMul_induced _
  simp_rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const]
  conv in Continuous _ => rw [Seminorm.continuous_iff one_pos, nhds_iInf]
  conv in Continuous _ =>
    rw [letI := t₂ s; Seminorm.continuous_iff one_pos]; rw [nhds_iInf]; rw [iInf_subtype]
  rw [Filter.mem_iInf_finite]

/--
theorem `mem_span_iff_bound` / 定理 `mem_span_iff_bound`

English:
theorem mem_span_iff_bound
  given: {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜)
  proof: by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t := ⨅ i, induced (f i) t𝕜
  have : IsTopologicalAddGroup E := topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have : WithSeminorms (fun i => (f i).toSeminorm) := by
    simp_rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, nhds_iInf, nhds_induced, map_zero,
      ← comap_norm_nhds_zero (E := 𝕜), Filter.comap_comap]
    rfl
  rw [LinearMap.mem_span_iff_continuous]
  constructor <;> intro H
  · rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const] at H
    rcases Seminorm.bound_of_continuous this _ H with ⟨s, C, -, hC⟩
    exact ⟨s, C, hC⟩
  · exact WithSeminorms.continuous_normedSpace_rng _ this _ H

中文:
定理 mem_span_iff_bound
  条件: {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜)
  证明: by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t := ⨅ i, induced (f i) t𝕜
  have : IsTopologicalAddGroup E := topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have : WithSeminorms (fun i => (f i).toSeminorm) := by
    simp_rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, nhds_iInf, nhds_induced, map_zero,
      ← comap_norm_nhds_zero (E := 𝕜), Filter.comap_comap]
    rfl
  rw [LinearMap.mem_span_iff_continuous]
  constructor <;> intro H
  · rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const] at H
    rcases Seminorm.bound_of_continuous this _ H with ⟨s, C, -, hC⟩
    exact ⟨s, C, hC⟩
  · exact WithSeminorms.continuous_normedSpace_rng _ this _ H

Depends on / 依赖: Filter, Filter.comap_comap, IsTopologicalAddGroup, LinearMap, LinearMap.mem_span_iff_continuous, SeminormFamily, SeminormFamily.withSeminorms_iff_nhds_eq_iInf, TopologicalSpace, WithSeminorms, WithSeminorms.continuous_iff_continuous_comp, comap_comap, comap_norm_nhds_zero, continuous_iff_continuous_comp, induced, map_zero, mem_span_iff_continuous, nhds_iInf, nhds_induced, norm_, simp_rw
-/
theorem mem_span_iff_bound {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) :
    φ in Submodule.span 𝕜 (Set.range f) ↔
    exists s : Finset ι, exists c : Real>=0, φ.toSeminorm <=
      c • (s.sup fun i => (f i).toSeminorm) := by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t := ⨅ i, induced (f i) t𝕜
  have : IsTopologicalAddGroup E := topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _
  have : WithSeminorms (fun i => (f i).toSeminorm) := by
    simp_rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, nhds_iInf, nhds_induced, map_zero,
      ← comap_norm_nhds_zero (E := 𝕜), Filter.comap_comap]
    rfl
  rw [LinearMap.mem_span_iff_continuous]
  constructor <;> intro H
  · rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const] at H
    rcases Seminorm.bound_of_continuous this _ H with ⟨s, C, -, hC⟩
    exact ⟨s, C, hC⟩
  · exact WithSeminorms.continuous_normedSpace_rng _ this _ H

variable [AddCommGroup F] [Module 𝕜 F] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)

/--
theorem `dualEmbedding_surjective` / 定理 `dualEmbedding_surjective`

English:
theorem dualEmbedding_surjective
  statement: Function.Surjective (WeakBilin.eval B)
  proof: fun f => by
  have : f.toLinearMap in
      Submodule.span 𝕜 (ContinuousLinearMap.coeLM 𝕜 ∘ₗ WeakBilin.eval B).range := by
    simpa [coe_range, mem_span_iff_continuous, continuous_iff_le_induced, ← induced_to_pi] using!
      f.continuous.le_induced
  simpa

中文:
定理 dualEmbedding_surjective
  结论: 函数.满射 (WeakBilin.eval B)
  证明: fun f => by
  have : f.toLinearMap in
      Submodule.span 𝕜 (ContinuousLinearMap.coeLM 𝕜 ∘ₗ WeakBilin.eval B).range := by
    simpa [coe_range, mem_span_iff_continuous, continuous_iff_le_induced, ← induced_to_pi] using!
      f.continuous.le_induced
  simpa

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeLM, Submodule, Submodule.span, WeakBilin, WeakBilin.eval, coe_range, continuous, continuous_iff_le_induced, f.continuous.le_induced, f.toLinearMap, induced_to_pi, le_induced, mem_span_iff_continuous, toLinearMap
-/
theorem dualEmbedding_surjective : Function.Surjective (WeakBilin.eval B) := fun f => by
  have : f.toLinearMap in
      Submodule.span 𝕜 (ContinuousLinearMap.coeLM 𝕜 ∘ₗ WeakBilin.eval B).range := by
    simpa [coe_range, mem_span_iff_continuous, continuous_iff_le_induced, ← induced_to_pi] using!
      f.continuous.le_induced
  simpa

/--
Definition of `rightDualEquiv` / `rightDualEquiv` 的定义

English:
definition rightDualEquiv
  signature: (hr : B.SeparatingRight)
  body: LinearEquiv.ofBijective (WeakBilin.eval B)
    ⟨dualEmbedding_injective_of_separatingRight B hr, dualEmbedding_surjective B⟩

中文:
定义 rightDualEquiv
  签名: (hr : B.SeparatingRight)
  定义体: LinearEquiv.ofBijective (WeakBilin.eval B)
    ⟨dualEmbedding_injective_of_separatingRight B hr, dualEmbedding_surjective B⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, WeakBilin, WeakBilin.eval, dualEmbedding_injective_of_separatingRight, dualEmbedding_surjective, ofBijective
-/
noncomputable def rightDualEquiv (hr : B.SeparatingRight) : F ≃ₗ[𝕜] StrongDual 𝕜 (WeakBilin B) :=
  LinearEquiv.ofBijective (WeakBilin.eval B)
    ⟨dualEmbedding_injective_of_separatingRight B hr, dualEmbedding_surjective B⟩

/--
Definition of `leftDualEquiv` / `leftDualEquiv` 的定义

English:
definition leftDualEquiv
  signature: (hl : B.SeparatingLeft)
  body: rightDualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

中文:
定义 leftDualEquiv
  签名: (hl : B.SeparatingLeft)
  定义体: rightDualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

Depends on / 依赖: LinearMap, LinearMap.flip_separatingRight.mpr, flip_separatingRight, rightDualEquiv
-/
noncomputable def leftDualEquiv (hl : B.SeparatingLeft) : E ≃ₗ[𝕜] StrongDual 𝕜 (WeakBilin B.flip) :=
  rightDualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

end NontriviallyNormedField

end

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/--
theorem `LinearMap.weakBilin_withSeminorms` / 定理 `LinearMap.weakBilin_withSeminorms`

English:
theorem LinearMap.weakBilin_withSeminorms
  given: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  proof: let e : F ≃ (Σ _ : F, Fin 1) := .symm .sigmaUnique _ _
  withSeminorms_induced (withSeminorms_pi (fun _ => norm_withSeminorms 𝕜 𝕜))
.congr_equiv e (LinearMap.ltoFun 𝕜 F 𝕜 𝕜 ∘ₗ B : (WeakBilin B) ->ₗ[𝕜] (F -> 𝕜))

中文:
定理 线性映射.weakBilin_withSeminorms
  条件: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  证明: let e : F ≃ (Σ _ : F, Fin 1) := .symm .sigmaUnique _ _
  withSeminorms_induced (withSeminorms_pi (fun _ => norm_withSeminorms 𝕜 𝕜))
.congr_equiv e (LinearMap.ltoFun 𝕜 F 𝕜 𝕜 ∘ₗ B : (WeakBilin B) ->ₗ[𝕜] (F -> 𝕜))

Depends on / 依赖: LinearMap, LinearMap.ltoFun, WeakBilin, congr_equiv, ltoFun, norm_withSeminorms, sigmaUnique, withSeminorms_induced, withSeminorms_pi
-/
theorem LinearMap.weakBilin_withSeminorms (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F -> Seminorm 𝕜 (WeakBilin B)) :=
let e : F ≃ (Σ _ : F, Fin 1) := .symm .sigmaUnique _ _
  withSeminorms_induced (withSeminorms_pi (fun _ => norm_withSeminorms 𝕜 𝕜))
.congr_equiv e (LinearMap.ltoFun 𝕜 F 𝕜 𝕜 ∘ₗ B : (WeakBilin B) ->ₗ[𝕜] (F -> 𝕜))

/--
theorem `LinearMap.hasBasis_weakBilin` / 定理 `LinearMap.hasBasis_weakBilin`

English:
theorem LinearMap.hasBasis_weakBilin
  given: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  proof: .hasBasis LinearMap.weakBilin_withSeminorms B

中文:
定理 线性映射.hasBasis_weakBilin
  条件: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  证明: .hasBasis LinearMap.weakBilin_withSeminorms B

Depends on / 依赖: LinearMap, LinearMap.weakBilin_withSeminorms, hasBasis, weakBilin_withSeminorms
-/
theorem LinearMap.hasBasis_weakBilin (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis (· in B.toSeminormFamily.basisSets) _root_.id :=
.hasBasis LinearMap.weakBilin_withSeminorms B

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [NormedSpace Real 𝕜] [Module Real E] [IsScalarTower Real 𝕜 E]

/--
Instance `WeakBilin.locallyConvexSpace` / 实例 `WeakBilin.locallyConvexSpace`

English:
instance WeakBilin.locallyConvexSpace
  signature: {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜}
  body: B.weakBilin_withSeminorms.toLocallyConvexSpace

中文:
实例 WeakBilin.locallyConvexSpace
  签名: {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜}
  定义体: B.weakBilin_withSeminorms.toLocallyConvexSpace

Depends on / 依赖: B.weakBilin_withSeminorms.toLocallyConvexSpace, toLocallyConvexSpace, weakBilin_withSeminorms
-/
instance WeakBilin.locallyConvexSpace {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} :
    LocallyConvexSpace Real (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex
