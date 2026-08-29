/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Polar sets in the strong dual of a normed space

In this file we study polar sets in the strong dual `StrongDual` of a normed space.

## Main definitions

* `polar 𝕜 s` is the subset of `StrongDual 𝕜 E` consisting of those functionals `x'` for which
  `‖x' z‖ ≤ 1` for every `z ∈ s`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

strong dual, polar
-/

public section

noncomputable section

open Topology Bornology

namespace NormedSpace

section PolarSets

open Metric Set StrongDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `isClosed_polar` / 定理 `isClosed_polar`

English:
theorem isClosed_polar
  given: (s : Set E)
  statement: IsClosed (StrongDual.polar 𝕜 s)
  proof: by
  dsimp only [StrongDual.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm

@[simp]

中文:
定理 isClosed_polar
  条件: (s : 集合 E)
  结论: 是闭集 (StrongDual.polar 𝕜 s)
  证明: by
  dsimp only [StrongDual.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, LinearMap, LinearMap.flip_apply, LinearMap.polar_eq_iInter, StrongDual, StrongDual.polar, continuous, continuous.norm, flip_apply, isClosed_Iic, isClosed_Iic.preimage, isClosed_biInter, polar_eq_iInter, preimage
-/
theorem isClosed_polar (s : Set E) : IsClosed (StrongDual.polar 𝕜 s) := by
  dsimp only [StrongDual.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm

@[simp]
/--
theorem `polar_closure` / 定理 `polar_closure`

English:
theorem polar_closure
  given: (s : Set E)
  statement: StrongDual.polar 𝕜 (closure s) = StrongDual.polar 𝕜 s
  proof: ((topDualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm
(topDualPairing 𝕜 E).flip.polar_gc.l_le
closure_minimal ((topDualPairing 𝕜 E).flip.polar_gc.le_u_l s) by
        simpa [LinearMap.flip_flip] using!
          (isClosed_polar _ _).preimage (ContinuousLinearMap.apply 𝕜 𝕜 (E := E)).continuous

中文:
定理 polar_closure
  条件: (s : 集合 E)
  结论: StrongDual.polar 𝕜 (closure s) = StrongDual.polar 𝕜 s
  证明: ((topDualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm
(topDualPairing 𝕜 E).flip.polar_gc.l_le
closure_minimal ((topDualPairing 𝕜 E).flip.polar_gc.le_u_l s) by
        simpa [LinearMap.flip_flip] using!
          (isClosed_polar _ _).preimage (ContinuousLinearMap.apply 𝕜 𝕜 (E := E)).continuous

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, LinearMap, LinearMap.flip_flip, antisymm, closure_minimal, continuous, flip.polar_antitone, flip.polar_gc.l_le, flip.polar_gc.le_u_l, flip_flip, isClosed_polar, l_le, le_u_l, polar_antitone, polar_gc, preimage, subset_closure, topDualPairing
-/
theorem polar_closure (s : Set E) : StrongDual.polar 𝕜 (closure s) = StrongDual.polar 𝕜 s :=
((topDualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm
(topDualPairing 𝕜 E).flip.polar_gc.l_le
closure_minimal ((topDualPairing 𝕜 E).flip.polar_gc.le_u_l s) by
        simpa [LinearMap.flip_flip] using!
          (isClosed_polar _ _).preimage (ContinuousLinearMap.apply 𝕜 𝕜 (E := E)).continuous

variable {𝕜}

/--
theorem `smul_mem_polar` / 定理 `smul_mem_polar`

English:
theorem smul_mem_polar
  given: {s : Set E} {x' : StrongDual 𝕜 E} {c : 𝕜} (hc : forall z, z in s -> ‖x' z‖ <= ‖c‖)
  proof: by
  by_cases c_zero : c = 0
  · simp only [c_zero, inv_zero, zero_smul]
    exact (topDualPairing 𝕜 E).flip.zero_mem_polar _
  have eq : forall z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : forall z, z in s -> ‖c⁻¹ • x' z‖ <= ‖c⁻¹‖ * ‖c‖ := by
    intro z hzs
    rw [eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel₀, norm_inv]
  rwa [cancel] at le

中文:
定理 smul_mem_polar
  条件: {s : 集合 E} {x' : StrongDual 𝕜 E} {c : 𝕜} (hc : 对任意 z, z in s -> ‖x' z‖ <= ‖c‖)
  证明: by
  by_cases c_zero : c = 0
  · simp only [c_zero, inv_zero, zero_smul]
    exact (topDualPairing 𝕜 E).flip.zero_mem_polar _
  have eq : forall z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : forall z, z in s -> ‖c⁻¹ • x' z‖ <= ‖c⁻¹‖ * ‖c‖ := by
    intro z hzs
    rw [eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel₀, norm_inv]
  rwa [cancel] at le

Depends on / 依赖: c_zero, cancel, flip.zero_mem_polar, inv_zero, le_of_eq, mul_le_mul, norm_eq_zero, norm_inv, norm_nonneg, norm_smul, not_false_iff, topDualPairing, zero_mem_polar, zero_smul
-/
theorem smul_mem_polar {s : Set E} {x' : StrongDual 𝕜 E} {c : 𝕜} (hc : forall z, z in s -> ‖x' z‖ <= ‖c‖) :
    c⁻¹ • x' in StrongDual.polar 𝕜 s := by
  by_cases c_zero : c = 0
  · simp only [c_zero, inv_zero, zero_smul]
    exact (topDualPairing 𝕜 E).flip.zero_mem_polar _
  have eq : forall z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : forall z, z in s -> ‖c⁻¹ • x' z‖ <= ‖c⁻¹‖ * ‖c‖ := by
    intro z hzs
    rw [eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel₀, norm_inv]
  rwa [cancel] at le

/--
theorem `polar_ball_subset_closedBall_div` / 定理 `polar_ball_subset_closedBall_div`

English:
theorem polar_ball_subset_closedBall_div
  given: {c : 𝕜} (hc : 1 < ‖c‖) {r : Real} (hr : 0 < r)
  proof: by
  intro x' hx'
  rw [StrongDual.mem_polar_iff] at hx'
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ <= 1 := hx' _ h₂
    _ <= ‖c‖ / r * ‖x‖ := (inv_le_iff_one_le_mul₀' hcr).1 (by rwa [inv_div])

中文:
定理 polar_ball_subset_closedBall_div
  条件: {c : 𝕜} (hc : 1 < ‖c‖) {r : 实数} (hr : 0 < r)
  证明: by
  intro x' hx'
  rw [StrongDual.mem_polar_iff] at hx'
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ <= 1 := hx' _ h₂
    _ <= ‖c‖ / r * ‖x‖ := (inv_le_iff_one_le_mul₀' hcr).1 (by rwa [inv_div])

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_of_shell, StrongDual, StrongDual.mem_polar_iff, div_pos, hcr.le, inv_div, mem_ball_zero_iff, mem_closedBall_zero_iff, mem_polar_iff, opNorm_le_of_shell, zero_lt_one, zero_lt_one.trans
-/
theorem polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : Real} (hr : 0 < r) :
    StrongDual.polar 𝕜 (ball (0 : E) r) subseteq closedBall (0 : StrongDual 𝕜 E) (‖c‖ / r) := by
  intro x' hx'
  rw [StrongDual.mem_polar_iff] at hx'
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ <= 1 := hx' _ h₂
    _ <= ‖c‖ / r * ‖x‖ := (inv_le_iff_one_le_mul₀' hcr).1 (by rwa [inv_div])

variable (𝕜)

/--
theorem `closedBall_inv_subset_polar_closedBall` / 定理 `closedBall_inv_subset_polar_closedBall`

English:
theorem closedBall_inv_subset_polar_closedBall
  given: {r : Real}
  proof: fun x' hx' x hx =>
  calc
    ‖x' x‖ <= ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ <= r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := inv_mul_eq_div _ _
    _ <= 1 := div_self_le_one r

中文:
定理 closedBall_inv_subset_polar_closedBall
  条件: {r : 实数}
  证明: fun x' hx' x hx =>
  calc
    ‖x' x‖ <= ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ <= r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := inv_mul_eq_div _ _
    _ <= 1 := div_self_le_one r

Depends on / 依赖: dist_nonneg, dist_nonneg.trans, div_self_le_one, inv_mul_eq_div, le_opNorm, mem_closedBall_zero_iff, mul_le_mul, norm_nonneg
-/
theorem closedBall_inv_subset_polar_closedBall {r : Real} :
    closedBall (0 : StrongDual 𝕜 E) r⁻¹ subseteq StrongDual.polar 𝕜 (closedBall (0 : E) r) :=
  fun x' hx' x hx =>
  calc
    ‖x' x‖ <= ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ <= r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := inv_mul_eq_div _ _
    _ <= 1 := div_self_le_one r

/--
theorem `polar_closedBall` / 定理 `polar_closedBall`

English:
theorem polar_closedBall
  statement: {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real}
  proof: by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using! LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z

中文:
定理 polar_closedBall
  结论: {𝕜 E : 类型} [RCLike 𝕜] [赋范交换加群 E] [赋范空间 𝕜 E] {r : 实数}
  证明: by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using! LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_of_ball, LinearMap, LinearMap.bound_of_ball_bound, Subset, Subset.antisymm, antisymm, bound_of_ball_bound, closedBall_inv_subset_polar_closedBall, hr.le, inv_nonneg, inv_nonneg.mpr, mem_closedBall_zero_iff, one_div, opNorm_le_of_ball, toLinearMap
-/
theorem polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real}
    (hr : 0 < r) :
    StrongDual.polar 𝕜 (closedBall (0 : E) r) = closedBall (0 : StrongDual 𝕜 E) r⁻¹ := by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using! LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z

/--
theorem `polar_ball` / 定理 `polar_ball`

English:
theorem polar_ball
  statement: {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real}
  proof: by
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  rw [← polar_closedBall hr]; rw [← closure_ball _ hr.ne']; rw [polar_closure]

中文:
定理 polar_ball
  结论: {𝕜 E : 类型} [RCLike 𝕜] [赋范交换加群 E] [赋范空间 𝕜 E] {r : 实数}
  证明: by
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  rw [← polar_closedBall hr]; rw [← closure_ball _ hr.ne']; rw [polar_closure]

Depends on / 依赖: NormedSpace, closure_ball, hr.ne, polar_closedBall, polar_closure, restrictScalars
-/
theorem polar_ball {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real}
    (hr : 0 < r) : StrongDual.polar 𝕜 (ball (0 : E) r) = closedBall (0 : StrongDual 𝕜 E) r⁻¹ := by
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  rw [← polar_closedBall hr]; rw [← closure_ball _ hr.ne']; rw [polar_closure]

/--
theorem `isBounded_polar_of_mem_nhds_zero` / 定理 `isBounded_polar_of_mem_nhds_zero`

English:
theorem isBounded_polar_of_mem_nhds_zero
  given: {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  proof: by
  obtain ⟨a, ha⟩ : exists a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : exists r : Real, 0 < r ∧ ball 0 r subseteq s := Metric.mem_nhds_iff.1 s_nhds
  exact isBounded_closedBall.subset
    (((topDualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)

中文:
定理 isBounded_polar_of_mem_nhds_zero
  条件: {s : 集合 E} (s_nhds : s in 𝓝 (0 : E))
  证明: by
  obtain ⟨a, ha⟩ : exists a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : exists r : Real, 0 < r ∧ ball 0 r subseteq s := Metric.mem_nhds_iff.1 s_nhds
  exact isBounded_closedBall.subset
    (((topDualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)

Depends on / 依赖: Metric, Metric.mem_nhds_iff, NormedField, NormedField.exists_one_lt_norm, exists_one_lt_norm, flip.polar_antitone, isBounded_closedBall, isBounded_closedBall.subset, mem_nhds_iff, polar_antitone, polar_ball_subset_closedBall_div, r_ball, r_pos, s_nhds, subset, subseteq, topDualPairing
-/
theorem isBounded_polar_of_mem_nhds_zero {s : Set E} (s_nhds : s in 𝓝 (0 : E)) :
    IsBounded (StrongDual.polar 𝕜 s) := by
  obtain ⟨a, ha⟩ : exists a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : exists r : Real, 0 < r ∧ ball 0 r subseteq s := Metric.mem_nhds_iff.1 s_nhds
  exact isBounded_closedBall.subset
    (((topDualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)

/--
theorem `sInter_polar_eq_closedBall` / 定理 `sInter_polar_eq_closedBall`

English:
theorem sInter_polar_eq_closedBall
  statement: {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  conv_rhs => rw [← inv_inv r]
  rw [← polar_closedBall (inv_pos_of_pos hr)]; rw [StrongDual.polar]; rw [(topDualPairing 𝕜 E).flip.sInter_polar_finite_subset_eq_polar (closedBall (0 : E) r⁻¹)]

中文:
定理 s整数er_polar_eq_closedBall
  结论: {𝕜 E : 类型} [RCLike 𝕜] [赋范交换加群 E] [赋范空间 𝕜 E]
  证明: by
  conv_rhs => rw [← inv_inv r]
  rw [← polar_closedBall (inv_pos_of_pos hr)]; rw [StrongDual.polar]; rw [(topDualPairing 𝕜 E).flip.sInter_polar_finite_subset_eq_polar (closedBall (0 : E) r⁻¹)]

Depends on / 依赖: StrongDual, StrongDual.polar, closedBall, conv_rhs, flip.sInter_polar_finite_subset_eq_polar, inv_inv, inv_pos_of_pos, polar_closedBall, sInter_polar_finite_subset_eq_polar, topDualPairing
-/
theorem sInter_polar_eq_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {r : Real} (hr : 0 < r) :
    ⋂₀ (StrongDual.polar 𝕜 '' { F | F.Finite ∧ F subseteq closedBall (0 : E) r⁻¹ }) = closedBall 0 r := by
  conv_rhs => rw [← inv_inv r]
  rw [← polar_closedBall (inv_pos_of_pos hr)]; rw [StrongDual.polar]; rw [(topDualPairing 𝕜 E).flip.sInter_polar_finite_subset_eq_polar (closedBall (0 : E) r⁻¹)]

end PolarSets

end NormedSpace

namespace LinearMap

section NormedField

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (s : Set E)

open ComplexOrder in
/--
theorem `polar_AbsConvex` / 定理 `polar_AbsConvex`

English:
theorem polar_AbsConvex
  statement: AbsConvex 𝕜 (B.polar s)
  proof: by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F ->ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall 0 1)).linear_preimage _⟩

中文:
定理 polar_AbsConvex
  结论: AbsConvex 𝕜 (B.polar s)
  证明: by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F ->ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall 0 1)).linear_preimage _⟩

Depends on / 依赖: AbsConvex, AbsConvex.iInter, RingHom, RingHom.id, balanced_closedBall_zero, balanced_closedBall_zero.mulActionHom_preimage, convex_RCLike_iff_convex_real, convex_RCLike_iff_convex_real.mpr, convex_closedBall, linear_preimage, mulActionHom_preimage, polar_eq_biInter_preimage
-/
theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F ->ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall 0 1)).linear_preimage _⟩

end NormedField

end LinearMap

section Deprecated

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[deprecated SeparatingDual.eq_zero_of_forall_dual_eq_zero (since := "2026-03-18")]
/--
theorem `NormedSpace.eq_zero_of_forall_dual_eq_zero` / 定理 `NormedSpace.eq_zero_of_forall_dual_eq_zero`

English:
theorem NormedSpace.eq_zero_of_forall_dual_eq_zero
  statement: {x : E}
  proof: SeparatingDual.eq_zero_of_forall_dual_eq_zero h

@[deprecated SeparatingDual.eq_zero_iff_forall_dual_eq_zero (since := "2026-03-18")]

中文:
定理 赋范空间.eq_zero_of_对任意_dual_eq_zero
  结论: {x : E}
  证明: SeparatingDual.eq_zero_of_forall_dual_eq_zero h

@[deprecated SeparatingDual.eq_zero_iff_forall_dual_eq_zero (since := "2026-03-18")]

Depends on / 依赖: SeparatingDual, SeparatingDual.eq_zero_of_forall_dual_eq_zero, eq_zero_of_forall_dual_eq_zero
-/
theorem NormedSpace.eq_zero_of_forall_dual_eq_zero {x : E}
    (h : forall f : StrongDual 𝕜 E, f x = 0) : x = 0 :=
  SeparatingDual.eq_zero_of_forall_dual_eq_zero h

@[deprecated SeparatingDual.eq_zero_iff_forall_dual_eq_zero (since := "2026-03-18")]
/--
theorem `NormedSpace.eq_zero_iff_forall_dual_eq_zero` / 定理 `NormedSpace.eq_zero_iff_forall_dual_eq_zero`

English:
theorem NormedSpace.eq_zero_iff_forall_dual_eq_zero
  given: (x : E)
  proof: SeparatingDual.eq_zero_iff_forall_dual_eq_zero x

@[deprecated SeparatingDual.eq_iff_forall_dual_eq (since := "2026-03-18")]

中文:
定理 赋范空间.eq_zero_iff_对任意_dual_eq_zero
  条件: (x : E)
  证明: SeparatingDual.eq_zero_iff_forall_dual_eq_zero x

@[deprecated SeparatingDual.eq_iff_forall_dual_eq (since := "2026-03-18")]

Depends on / 依赖: SeparatingDual, SeparatingDual.eq_zero_iff_forall_dual_eq_zero, eq_zero_iff_forall_dual_eq_zero
-/
theorem NormedSpace.eq_zero_iff_forall_dual_eq_zero (x : E) :
    x = 0 ↔ forall g : StrongDual 𝕜 E, g x = 0 :=
  SeparatingDual.eq_zero_iff_forall_dual_eq_zero x

@[deprecated SeparatingDual.eq_iff_forall_dual_eq (since := "2026-03-18")]
/--
theorem `NormedSpace.eq_iff_forall_dual_eq` / 定理 `NormedSpace.eq_iff_forall_dual_eq`

English:
theorem NormedSpace.eq_iff_forall_dual_eq
  given: {x y : E}
  proof: SeparatingDual.eq_iff_forall_dual_eq

中文:
定理 赋范空间.eq_iff_对任意_dual_eq
  条件: {x y : E}
  证明: SeparatingDual.eq_iff_forall_dual_eq

Depends on / 依赖: SeparatingDual, SeparatingDual.eq_iff_forall_dual_eq, eq_iff_forall_dual_eq
-/
theorem NormedSpace.eq_iff_forall_dual_eq {x y : E} :
    x = y ↔ forall g : StrongDual 𝕜 E, g x = g y :=
  SeparatingDual.eq_iff_forall_dual_eq

end Deprecated
