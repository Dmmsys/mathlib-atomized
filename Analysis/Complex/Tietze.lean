/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
/-!
# Finite-dimensional topological vector spaces over `ℝ` satisfy the Tietze extension property

There are two main results here:

- `RCLike.instTietzeExtensionTVS`: finite-dimensional topological vector spaces over `ℝ` (or `ℂ`)
  have the Tietze extension property.
- `BoundedContinuousFunction.exists_norm_eq_domRestrict_eq`: when mapping into a finite-dimensional
  normed vector space over `ℝ` (or `ℂ`), the extension can be chosen to preserve the norm of the
  bounded continuous function it extends.

-/

public section

universe u u₁ v w

-- this is not an instance because Lean cannot determine `𝕜`.
/--
theorem `TietzeExtension.of_tvs` / 定理 `TietzeExtension.of_tvs`

English:
theorem TietzeExtension.of_tvs
  statement: (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
  proof: .of_homeo .equivFun.toContinuousLinearEquiv.toHomeomorph Module.Basis.ofVectorSpace 𝕜 E

中文:
定理 TietzeExtension.of_tvs
  结论: (𝕜 : 类型v) [NontriviallyNormedField 𝕜] {E : 类型 w}
  证明: .of_homeo .equivFun.toContinuousLinearEquiv.toHomeomorph Module.Basis.ofVectorSpace 𝕜 E

Depends on / 依赖: Module, Module.Basis.ofVectorSpace, equivFun, equivFun.toContinuousLinearEquiv.toHomeomorph, ofVectorSpace, of_homeo, toContinuousLinearEquiv, toHomeomorph
-/
theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    [TietzeExtension.{u, v} 𝕜] : TietzeExtension.{u, w} E :=
.of_homeo .equivFun.toContinuousLinearEquiv.toHomeomorph Module.Basis.ofVectorSpace 𝕜 E

/--
Instance `Complex.instTietzeExtension` / 实例 `Complex.instTietzeExtension`

English:
instance Complex.instTietzeExtension
  signature: : TietzeExtension Complex
  body: TietzeExtension.of_tvs Real

中文:
实例 复形.instTietzeExtension
  签名: : TietzeExtension 复形
  定义体: TietzeExtension.of_tvs Real

Depends on / 依赖: TietzeExtension, TietzeExtension.of_tvs, of_tvs
-/
instance Complex.instTietzeExtension : TietzeExtension Complex :=
  TietzeExtension.of_tvs Real

instance (priority := 900) RCLike.instTietzeExtension {𝕜 : Type*} [RCLike 𝕜] :
    TietzeExtension 𝕜 := TietzeExtension.of_tvs Real

/--
Instance `RCLike.instTietzeExtensionTVS` / 实例 `RCLike.instTietzeExtensionTVS`

English:
instance RCLike.instTietzeExtensionTVS
  signature: {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
  body: TietzeExtension.of_tvs 𝕜

中文:
实例 RCLike.instTietzeExtensionTVS
  签名: {𝕜 : 类型v} [RCLike 𝕜] {E : 类型 w}
  定义体: TietzeExtension.of_tvs 𝕜

Depends on / 依赖: TietzeExtension, TietzeExtension.of_tvs, of_tvs
-/
instance RCLike.instTietzeExtensionTVS {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} E :=
  TietzeExtension.of_tvs 𝕜

/--
Instance `Set.instTietzeExtensionUnitBall` / 实例 `Set.instTietzeExtensionUnitBall`

English:
instance Set.instTietzeExtensionUnitBall
  signature: {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
  body: have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  .of_homeo Homeomorph.unitBall.symm

中文:
实例 集合.instTietzeExtensionUnitBall
  签名: {𝕜 : 类型v} [RCLike 𝕜] {E : 类型 w}
  定义体: have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  .of_homeo Homeomorph.unitBall.symm

Depends on / 依赖: Homeomorph, Homeomorph.unitBall.symm, NormedSpace, NormedSpace.restrictScalars, of_homeo, restrictScalars, unitBall
-/
instance Set.instTietzeExtensionUnitBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.ball (0 : E) 1) :=
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  .of_homeo Homeomorph.unitBall.symm

/--
Instance `Set.instTietzeExtensionUnitClosedBall` / 实例 `Set.instTietzeExtensionUnitClosedBall`

English:
instance Set.instTietzeExtensionUnitClosedBall
  signature: {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
  body: by
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  have : IsScalarTower Real 𝕜 E := Real.isScalarTower
  -- I didn't find this retract in Mathlib.
  let g : E -> E := fun x => ‖x‖⁻¹ • x
  classical
  suffices this : Continuous (piecewise (Metric.closedBall 0 1) id g) by
    refine .of_retract ⟨Subtype.val, by fun_prop⟩ ⟨_, this.codRestrict fun x => ?_⟩ ?_
    · by_cases hx : x in Metric.closedBall 0 1
      · simpa [piecewise_eq_of_mem (hi := hx)] using hx
      · simp only [g, piecewise_eq_of_notMem (hi := hx), RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        by_cases hx' : x = 0 <;> simp [hx']
    · ext x
      simp
  refine continuous_piecewise (fun x hx => ?_) continuousOn_id ?_
  · replace hx : ‖x‖ = 1 := by simpa [frontier_closedBall (0 : E) one_ne_zero] using hx
    simp [g, hx]
.smul continuousOn_id · refine continuousOn_id.norm.inv₀ ?_
    simp only [closure_compl, interior_closedBall (0 : E) one_ne_zero, mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt, id_eq, ne_eq, norm_eq_zero]
exact fun x hx => norm_pos_iff.mp one_pos.trans_le hx

中文:
实例 集合.instTietzeExtensionUnitClosedBall
  签名: {𝕜 : 类型v} [RCLike 𝕜] {E : 类型 w}
  定义体: by
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  have : IsScalarTower Real 𝕜 E := Real.isScalarTower
  -- I didn't find this retract in Mathlib.
  let g : E -> E := fun x => ‖x‖⁻¹ • x
  classical
  suffices this : Continuous (piecewise (Metric.closedBall 0 1) id g) by
    refine .of_retract ⟨Subtype.val, by fun_prop⟩ ⟨_, this.codRestrict fun x => ?_⟩ ?_
    · by_cases hx : x in Metric.closedBall 0 1
      · simpa [piecewise_eq_of_mem (hi := hx)] using hx
      · simp only [g, piecewise_eq_of_notMem (hi := hx), RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        by_cases hx' : x = 0 <;> simp [hx']
    · ext x
      simp
  refine continuous_piecewise (fun x hx => ?_) continuousOn_id ?_
  · replace hx : ‖x‖ = 1 := by simpa [frontier_closedBall (0 : E) one_ne_zero] using hx
    simp [g, hx]
.smul continuousOn_id · refine continuousOn_id.norm.inv₀ ?_
    simp only [closure_compl, interior_closedBall (0 : E) one_ne_zero, mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt, id_eq, ne_eq, norm_eq_zero]
exact fun x hx => norm_pos_iff.mp one_pos.trans_le hx

Depends on / 依赖: IsScalarTower, NormedSpace, NormedSpace.restrictScalars, Real.isScalarTower, isScalarTower, restrictScalars
-/
instance Set.instTietzeExtensionUnitClosedBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.closedBall (0 : E) 1) := by
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  have : IsScalarTower Real 𝕜 E := Real.isScalarTower
  -- I didn't find this retract in Mathlib.
  let g : E -> E := fun x => ‖x‖⁻¹ • x
  classical
  suffices this : Continuous (piecewise (Metric.closedBall 0 1) id g) by
    refine .of_retract ⟨Subtype.val, by fun_prop⟩ ⟨_, this.codRestrict fun x => ?_⟩ ?_
    · by_cases hx : x in Metric.closedBall 0 1
      · simpa [piecewise_eq_of_mem (hi := hx)] using hx
      · simp only [g, piecewise_eq_of_notMem (hi := hx), RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        by_cases hx' : x = 0 <;> simp [hx']
    · ext x
      simp
  refine continuous_piecewise (fun x hx => ?_) continuousOn_id ?_
  · replace hx : ‖x‖ = 1 := by simpa [frontier_closedBall (0 : E) one_ne_zero] using hx
    simp [g, hx]
.smul continuousOn_id · refine continuousOn_id.norm.inv₀ ?_
    simp only [closure_compl, interior_closedBall (0 : E) one_ne_zero, mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt, id_eq, ne_eq, norm_eq_zero]
exact fun x hx => norm_pos_iff.mp one_pos.trans_le hx

/--
theorem `Metric.instTietzeExtensionBall` / 定理 `Metric.instTietzeExtensionBall`

English:
theorem Metric.instTietzeExtensionBall
  statement: {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
  proof: have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
.of_homeo show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
.toHomeomorphSourceTarget.symm OpenPartialHomeomorph.unitBallBall (0 : E) r hr

中文:
定理 Metric.instTietzeExtensionBall
  结论: {𝕜 : 类型v} [RCLike 𝕜] {E : 类型 w}
  证明: have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
.of_homeo show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
.toHomeomorphSourceTarget.symm OpenPartialHomeomorph.unitBallBall (0 : E) r hr

Depends on / 依赖: Metric, Metric.ball, NormedSpace, NormedSpace.restrictScalars, OpenPartialHomeomorph, OpenPartialHomeomorph.unitBallBall, of_homeo, restrictScalars, toHomeomorphSourceTarget, toHomeomorphSourceTarget.symm, unitBallBall
-/
theorem Metric.instTietzeExtensionBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : Real} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.ball (0 : E) r) :=
  have : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
.of_homeo show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
.toHomeomorphSourceTarget.symm OpenPartialHomeomorph.unitBallBall (0 : E) r hr

/--
theorem `Metric.instTietzeExtensionClosedBall` / 定理 `Metric.instTietzeExtensionClosedBall`

English:
theorem Metric.instTietzeExtensionClosedBall
  statement: (𝕜 : Type v) [RCLike 𝕜] {E : Type w}
  proof: .of_homeo (Z := Metric.closedBall (0 : E) 1) by
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

中文:
定理 Metric.instTietzeExtensionClosedBall
  结论: (𝕜 : 类型v) [RCLike 𝕜] {E : 类型 w}
  证明: .of_homeo (Z := Metric.closedBall (0 : E) 1) by
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

Depends on / 依赖: DilationEquiv, DilationEquiv.coe_toHomeomorph, DilationEquiv.smulTorsor, DilationEquiv.smulTorsor_apply, Metric, Metric.closedBall, RCLike, RCLike.norm_ofReal, Set.mem_preimage, abs_of_nonneg, closedBall, coe_toHomeomorph, dist_add_self_left, dist_zero_right, hr.le, hr.ne, mem_closedBall, mem_preimage, mul_le_iff_le_one_right, norm_ofReal
-/
theorem Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : Real} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.closedBall y r) :=
.of_homeo (Z := Metric.closedBall (0 : E) 1) by
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

/--
Instance `unitInterval.instTietzeExtension` / 实例 `unitInterval.instTietzeExtension`

English:
instance unitInterval.instTietzeExtension
  signature: : TietzeExtension unitInterval
  body: by
  rw [unitInterval.eq_closedBall]
  exact Metric.instTietzeExtensionClosedBall Real _ (by norm_num)

中文:
实例 unit整数erval.instTietzeExtension
  签名: : TietzeExtension unit整数erval
  定义体: by
  rw [unitInterval.eq_closedBall]
  exact Metric.instTietzeExtensionClosedBall Real _ (by norm_num)

Depends on / 依赖: Metric, Metric.instTietzeExtensionClosedBall, eq_closedBall, instTietzeExtensionClosedBall, unitInterval, unitInterval.eq_closedBall
-/
instance unitInterval.instTietzeExtension : TietzeExtension unitInterval := by
  rw [unitInterval.eq_closedBall]
  exact Metric.instTietzeExtensionClosedBall Real _ (by norm_num)

variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X} (hs : IsClosed s)
variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace BoundedContinuousFunction

include 𝕜 hs in
/--
theorem `exists_norm_eq_domRestrict_eq` / 定理 `exists_norm_eq_domRestrict_eq`

English:
theorem exists_norm_eq_domRestrict_eq
  given: (f : s ->ᵇ E)
  proof: by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x in Metric.closedBall 0 ‖f‖ := by simpa using! f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X ->ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x => ?_
  have hx : f x = g' x := by simpa using! congr($(hg) x).symm
  rw [hx]
.mp le_rfl x exact g'.norm_le (norm_nonneg g')

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq := exists_norm_eq_domRestrict_eq

中文:
定理 存在_norm_eq_domRestrict_eq
  条件: (f : s ->ᵇ E)
  证明: by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x in Metric.closedBall 0 ‖f‖ := by simpa using! f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X ->ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x => ?_
  have hx : f x = g' x := by simpa using! congr($(hg) x).symm
  rw [hx]
.mp le_rfl x exact g'.norm_le (norm_nonneg g')

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq := exists_norm_eq_domRestrict_eq

Depends on / 依赖: Metric, Metric.closedBall, Metric.instTietzeExtensionClosedBall, Metric.mem_closedBall, closedBall, congrm, dist_zero_right, exists_forall_mem_restrict_eq, f.norm_coe_le_norm, hg_mem, instTietzeExtensionClosedBall, le_antisymm, map_continuous, mem_closedBall, norm_coe_le_norm, ofNormedAddCommGroup
-/
theorem exists_norm_eq_domRestrict_eq (f : s ->ᵇ E) :
    exists g : X ->ᵇ E, ‖g‖ = ‖f‖ ∧ g.domRestrict s = f := by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x in Metric.closedBall 0 ‖f‖ := by simpa using! f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X ->ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x => ?_
  have hx : f x = g' x := by simpa using! congr($(hg) x).symm
  rw [hx]
.mp le_rfl x exact g'.norm_le (norm_nonneg g')

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq := exists_norm_eq_domRestrict_eq

end BoundedContinuousFunction
