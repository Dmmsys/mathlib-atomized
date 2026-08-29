/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane, and show it is
invariant under Moebius transformations. We also calculate the derivative, and give an explicit
formula for its Jacobian determinant over `ℝ` (used in proving that the action preserves
a suitable measure).
-/

@[expose] public section

open Filter

open scoped Manifold ContDiff MatrixGroups Topology

variable {n : Nat∞ω}

namespace UpperHalfPlane

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChartedSpace Complex ℍ
  body: isOpenEmbedding_coe.singletonChartedSpace

中文:
实例 :
  签名: ChartedSpace Complex ℍ
  定义体: isOpenEmbedding_coe.singletonChartedSpace

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.singletonChartedSpace, singletonChartedSpace
-/
noncomputable instance : ChartedSpace Complex ℍ :=
  isOpenEmbedding_coe.singletonChartedSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsManifold 𝓘(Complex) ω ℍ
  body: isOpenEmbedding_coe.isManifold_singleton

中文:
实例 :
  签名: IsManifold 𝓘(Complex) ω ℍ
  定义体: isOpenEmbedding_coe.isManifold_singleton

Depends on / 依赖: isManifold_singleton, isOpenEmbedding_coe, isOpenEmbedding_coe.isManifold_singleton
-/
instance : IsManifold 𝓘(Complex) ω ℍ :=
  isOpenEmbedding_coe.isManifold_singleton

/--
theorem `contMDiff_coe` / 定理 `contMDiff_coe`

English:
theorem contMDiff_coe
  statement: CMDiff n ((↑) : ℍ -> Complex)
  proof: fun _ => contMDiffAt_extChartAt

中文:
定理 contMDiff_coe
  结论: CMDiff n ((↑) : ℍ -> Complex)
  证明: fun _ => contMDiffAt_extChartAt

Depends on / 依赖: contMDiffAt_extChartAt
-/
theorem contMDiff_coe : CMDiff n ((↑) : ℍ -> Complex) :=
  fun _ => contMDiffAt_extChartAt

/--
theorem `mdifferentiable_coe` / 定理 `mdifferentiable_coe`

English:
theorem mdifferentiable_coe
  statement: MDiff ((↑) : ℍ -> Complex)
  proof: contMDiff_coe.mdifferentiable one_ne_zero

中文:
定理 mdifferentiable_coe
  结论: MDiff ((↑) : ℍ -> Complex)
  证明: contMDiff_coe.mdifferentiable one_ne_zero

Depends on / 依赖: contMDiff_coe, contMDiff_coe.mdifferentiable, mdifferentiable, one_ne_zero
-/
theorem mdifferentiable_coe : MDiff ((↑) : ℍ -> Complex) :=
  contMDiff_coe.mdifferentiable one_ne_zero

/--
lemma `contMDiffAt_ofComplex` / 引理 `contMDiffAt_ofComplex`

English:
lemma contMDiffAt_ofComplex
  given: {z : Complex} (hz : 0 < z.im)
  statement: CMDiffAt n ofComplex z
  proof: by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt]; rw [nhds_induced]; rw [tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using! tendsto_id
  · -- smoothness in local chart
    simpa

中文:
引理 contMDiffAt_ofComplex
  条件: {z : Complex} (hz : 0 < z.im)
  结论: CMDiffAt n ofComplex z
  证明: by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt]; rw [nhds_induced]; rw [tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using! tendsto_id
  · -- smoothness in local chart
    simpa

Depends on / 依赖: ContinuousAt, Tendsto, Tendsto.congr, congr_of_eventuallyEq, contDiffAt_id, contDiffAt_id.congr_of_eventuallyEq, contMDiffAt_iff, continuity, eventuallyEq_coe_comp_ofComplex, nhds_induced, ofComplex_apply_of_im_pos, smoothness, tendsto_comap_iff, tendsto_id
-/
lemma contMDiffAt_ofComplex {z : Complex} (hz : 0 < z.im) : CMDiffAt n ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt]; rw [nhds_induced]; rw [tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using! tendsto_id
  · -- smoothness in local chart
    simpa using! contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

/--
lemma `mdifferentiableAt_ofComplex` / 引理 `mdifferentiableAt_ofComplex`

English:
lemma mdifferentiableAt_ofComplex
  given: {z : Complex} (hz : 0 < z.im)
  statement: MDiffAt ofComplex z
  proof: (contMDiffAt_ofComplex hz).mdifferentiableAt one_ne_zero

中文:
引理 mdifferentiableAt_ofComplex
  条件: {z : Complex} (hz : 0 < z.im)
  结论: MDiffAt ofComplex z
  证明: (contMDiffAt_ofComplex hz).mdifferentiableAt one_ne_zero

Depends on / 依赖: contMDiffAt_ofComplex, mdifferentiableAt, one_ne_zero
-/
lemma mdifferentiableAt_ofComplex {z : Complex} (hz : 0 < z.im) : MDiffAt ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt one_ne_zero

/--
lemma `contMDiffAt_iff` / 引理 `contMDiffAt_iff`

English:
lemma contMDiffAt_iff
  given: {f : ℍ -> Complex} {τ : ℍ}
  proof: by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)

中文:
引理 contMDiffAt_iff
  条件: {f : ℍ -> Complex} {τ : ℍ}
  证明: by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)

Depends on / 依赖: Function, Function.comp_def, comp_def, contMDiffAt_iff_contDiffAt, contMDiffAt_ofComplex, contMDiff_coe, hf.comp, im_pos, ofComplex_apply
-/
lemma contMDiffAt_iff {f : ℍ -> Complex} {τ : ℍ} :
    CMDiffAt n f τ ↔ ContDiffAt Complex n (f ∘ ofComplex) τ := by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)

/--
lemma `mdifferentiableAt_iff` / 引理 `mdifferentiableAt_iff`

English:
lemma mdifferentiableAt_iff
  given: {f : ℍ -> Complex} {τ : ℍ}
  proof: by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

中文:
引理 mdifferentiableAt_iff
  条件: {f : ℍ -> Complex} {τ : ℍ}
  证明: by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

Depends on / 依赖: Function, Function.comp_def, comp_def, hf.comp, im_pos, mdifferentiableAt_iff_differentiableAt, mdifferentiableAt_ofComplex, mdifferentiable_coe, ofComplex_apply
-/
lemma mdifferentiableAt_iff {f : ℍ -> Complex} {τ : ℍ} :
    MDiffAt f τ ↔ DifferentiableAt Complex (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

/--
lemma `mdifferentiable_iff` / 引理 `mdifferentiable_iff`

English:
lemma mdifferentiable_iff
  given: {f : ℍ -> Complex}
  proof: ⟨fun h z hz => (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
fun h ⟨z, hz⟩ => mdifferentiableAt_iff.mpr (h z hz).differentiableAt
 isOpen_upperHalfPlaneSet.mem_nhds hz⟩

中文:
引理 mdifferentiable_iff
  条件: {f : ℍ -> Complex}
  证明: ⟨fun h z hz => (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
fun h ⟨z, hz⟩ => mdifferentiableAt_iff.mpr (h z hz).differentiableAt
 isOpen_upperHalfPlaneSet.mem_nhds hz⟩

Depends on / 依赖: differentiableAt, differentiableWithinAt, isOpen_upperHalfPlaneSet, isOpen_upperHalfPlaneSet.mem_nhds, mdifferentiableAt_iff, mdifferentiableAt_iff.mp, mdifferentiableAt_iff.mpr, mem_nhds
-/
lemma mdifferentiable_iff {f : ℍ -> Complex} :
    MDiff f ↔ DifferentiableOn Complex (f ∘ ofComplex) {z | 0 < z.im} :=
  ⟨fun h z hz => (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
fun h ⟨z, hz⟩ => mdifferentiableAt_iff.mpr (h z hz).differentiableAt
 isOpen_upperHalfPlaneSet.mem_nhds hz⟩

/--
lemma `contMDiff_num` / 引理 `contMDiff_num`

English:
lemma contMDiff_num
  given: (g : GL (Fin 2) Real)
  statement: CMDiff n (fun τ : ℍ => num g τ)
  proof: (contMDiff_const.mul contMDiff_coe).add contMDiff_const

中文:
引理 contMDiff_num
  条件: (g : GL (Fin 2) 实数)
  结论: CMDiff n (fun τ : ℍ => num g τ)
  证明: (contMDiff_const.mul contMDiff_coe).add contMDiff_const

Depends on / 依赖: contMDiff_coe, contMDiff_const, contMDiff_const.mul
-/
lemma contMDiff_num (g : GL (Fin 2) Real) : CMDiff n (fun τ : ℍ => num g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const

/--
lemma `contMDiff_denom` / 引理 `contMDiff_denom`

English:
lemma contMDiff_denom
  given: (g : GL (Fin 2) Real)
  statement: CMDiff n (fun τ : ℍ => denom g τ)
  proof: (contMDiff_const.mul contMDiff_coe).add contMDiff_const

中文:
引理 contMDiff_denom
  条件: (g : GL (Fin 2) 实数)
  结论: CMDiff n (fun τ : ℍ => denom g τ)
  证明: (contMDiff_const.mul contMDiff_coe).add contMDiff_const

Depends on / 依赖: contMDiff_coe, contMDiff_const, contMDiff_const.mul
-/
lemma contMDiff_denom (g : GL (Fin 2) Real) : CMDiff n (fun τ : ℍ => denom g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const

/--
lemma `contMDiff_denom_zpow` / 引理 `contMDiff_denom_zpow`

English:
lemma contMDiff_denom_zpow
  given: (g : GL (Fin 2) Real) (k : Int)
  statement: CMDiff n (denom g · ^ k : ℍ -> Complex)
  proof: by
  intro τ
  have : AnalyticAt Complex (· ^ k) (denom g τ) := (differentiableOn_zpow k _ (by tauto)).analyticOnNhd
    isOpen_compl_singleton _ (denom_ne_zero g τ)
  exact this.contDiffAt.contMDiffAt.comp τ (contMDiff_denom g τ)

中文:
引理 contMDiff_denom_zpow
  条件: (g : GL (Fin 2) 实数) (k : 整数)
  结论: CMDiff n (denom g · ^ k : ℍ -> Complex)
  证明: by
  intro τ
  have : AnalyticAt Complex (· ^ k) (denom g τ) := (differentiableOn_zpow k _ (by tauto)).analyticOnNhd
    isOpen_compl_singleton _ (denom_ne_zero g τ)
  exact this.contDiffAt.contMDiffAt.comp τ (contMDiff_denom g τ)

Depends on / 依赖: AnalyticAt, analyticOnNhd, contDiffAt, contMDiffAt, contMDiff_denom, denom_ne_zero, differentiableOn_zpow, isOpen_compl_singleton, this.contDiffAt.contMDiffAt.comp
-/
lemma contMDiff_denom_zpow (g : GL (Fin 2) Real) (k : Int) : CMDiff n (denom g · ^ k : ℍ -> Complex) := by
  intro τ
  have : AnalyticAt Complex (· ^ k) (denom g τ) := (differentiableOn_zpow k _ (by tauto)).analyticOnNhd
    isOpen_compl_singleton _ (denom_ne_zero g τ)
  exact this.contDiffAt.contMDiffAt.comp τ (contMDiff_denom g τ)

/--
lemma `contMDiff_inv_denom` / 引理 `contMDiff_inv_denom`

English:
lemma contMDiff_inv_denom
  given: (g : GL (Fin 2) Real)
  statement: CMDiff n (fun τ : ℍ => (denom g τ)⁻¹)
  proof: by
  simpa using contMDiff_denom_zpow g (-1)

中文:
引理 contMDiff_inv_denom
  条件: (g : GL (Fin 2) 实数)
  结论: CMDiff n (fun τ : ℍ => (denom g τ)⁻¹)
  证明: by
  simpa using contMDiff_denom_zpow g (-1)

Depends on / 依赖: contMDiff_denom_zpow
-/
lemma contMDiff_inv_denom (g : GL (Fin 2) Real) : CMDiff n (fun τ : ℍ => (denom g τ)⁻¹) := by
  simpa using contMDiff_denom_zpow g (-1)

/--
lemma `contMDiff_smul` / 引理 `contMDiff_smul`

English:
lemma contMDiff_smul
  given: {g : GL (Fin 2) Real} (hg : 0 < g.det.val)
  statement: CMDiff n (fun τ : ℍ => g • τ)
  proof: by
  intro τ
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using! (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)

中文:
引理 contMDiff_smul
  条件: {g : GL (Fin 2) 实数} (hg : 0 < g.det.val)
  结论: CMDiff n (fun τ : ℍ => g • τ)
  证明: by
  intro τ
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using! (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)

Depends on / 依赖: contMDiffAt_iff_target, contMDiffAt_iff_target.mpr, contMDiff_inv_denom, contMDiff_num, continuousAt, continuous_const_smul, glPos_smul_def
-/
lemma contMDiff_smul {g : GL (Fin 2) Real} (hg : 0 < g.det.val) : CMDiff n (fun τ : ℍ => g • τ) := by
  intro τ
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using! (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)

/--
lemma `mdifferentiable_num` / 引理 `mdifferentiable_num`

English:
lemma mdifferentiable_num
  given: (g : GL (Fin 2) Real)
  statement: MDiff (fun τ : ℍ => num g τ)
  proof: (contMDiff_num g).mdifferentiable one_ne_zero

中文:
引理 mdifferentiable_num
  条件: (g : GL (Fin 2) 实数)
  结论: MDiff (fun τ : ℍ => num g τ)
  证明: (contMDiff_num g).mdifferentiable one_ne_zero

Depends on / 依赖: contMDiff_num, mdifferentiable, one_ne_zero
-/
lemma mdifferentiable_num (g : GL (Fin 2) Real) : MDiff (fun τ : ℍ => num g τ) :=
  (contMDiff_num g).mdifferentiable one_ne_zero

/--
lemma `mdifferentiable_denom` / 引理 `mdifferentiable_denom`

English:
lemma mdifferentiable_denom
  given: (g : GL (Fin 2) Real)
  statement: MDiff (fun τ : ℍ => denom g τ)
  proof: (contMDiff_denom g).mdifferentiable one_ne_zero

中文:
引理 mdifferentiable_denom
  条件: (g : GL (Fin 2) 实数)
  结论: MDiff (fun τ : ℍ => denom g τ)
  证明: (contMDiff_denom g).mdifferentiable one_ne_zero

Depends on / 依赖: contMDiff_denom, mdifferentiable, one_ne_zero
-/
lemma mdifferentiable_denom (g : GL (Fin 2) Real) : MDiff (fun τ : ℍ => denom g τ) :=
  (contMDiff_denom g).mdifferentiable one_ne_zero

/--
lemma `mdifferentiable_denom_zpow` / 引理 `mdifferentiable_denom_zpow`

English:
lemma mdifferentiable_denom_zpow
  given: (g : GL (Fin 2) Real) (k : Int)
  statement: MDiff (denom g · ^ k : ℍ -> Complex)
  proof: (contMDiff_denom_zpow g k).mdifferentiable one_ne_zero

中文:
引理 mdifferentiable_denom_zpow
  条件: (g : GL (Fin 2) 实数) (k : 整数)
  结论: MDiff (denom g · ^ k : ℍ -> Complex)
  证明: (contMDiff_denom_zpow g k).mdifferentiable one_ne_zero

Depends on / 依赖: contMDiff_denom_zpow, mdifferentiable, one_ne_zero
-/
lemma mdifferentiable_denom_zpow (g : GL (Fin 2) Real) (k : Int) : MDiff (denom g · ^ k : ℍ -> Complex) :=
  (contMDiff_denom_zpow g k).mdifferentiable one_ne_zero

/--
lemma `mdifferentiable_inv_denom` / 引理 `mdifferentiable_inv_denom`

English:
lemma mdifferentiable_inv_denom
  given: (g : GL (Fin 2) Real)
  statement: MDiff (fun τ : ℍ => (denom g τ)⁻¹)
  proof: (contMDiff_inv_denom g).mdifferentiable one_ne_zero

中文:
引理 mdifferentiable_inv_denom
  条件: (g : GL (Fin 2) 实数)
  结论: MDiff (fun τ : ℍ => (denom g τ)⁻¹)
  证明: (contMDiff_inv_denom g).mdifferentiable one_ne_zero

Depends on / 依赖: contMDiff_inv_denom, mdifferentiable, one_ne_zero
-/
lemma mdifferentiable_inv_denom (g : GL (Fin 2) Real) : MDiff (fun τ : ℍ => (denom g τ)⁻¹) :=
  (contMDiff_inv_denom g).mdifferentiable one_ne_zero

/--
lemma `mdifferentiable_smul` / 引理 `mdifferentiable_smul`

English:
lemma mdifferentiable_smul
  given: {g : GL (Fin 2) Real} (hg : 0 < g.det.val)
  statement: MDiff (fun τ : ℍ => g • τ)
  proof: (contMDiff_smul hg).mdifferentiable one_ne_zero

中文:
引理 mdifferentiable_smul
  条件: {g : GL (Fin 2) 实数} (hg : 0 < g.det.val)
  结论: MDiff (fun τ : ℍ => g • τ)
  证明: (contMDiff_smul hg).mdifferentiable one_ne_zero

Depends on / 依赖: contMDiff_smul, mdifferentiable, one_ne_zero
-/
lemma mdifferentiable_smul {g : GL (Fin 2) Real} (hg : 0 < g.det.val) : MDiff (fun τ : ℍ => g • τ) :=
  (contMDiff_smul hg).mdifferentiable one_ne_zero

/--
lemma `eq_zero_of_frequently` / 引理 `eq_zero_of_frequently`

English:
lemma eq_zero_of_frequently
  given: {f : ℍ -> Complex} (hf : MDiff f) {τ : ℍ} (hτ : existsᶠ z in 𝓝[!=] τ, f z = 0)
  proof: by
  rw [mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  ext w
  convert! this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ τ.2 ?_ w.im_pos
  · rw [Function.comp_apply, ofComplex_apply]
  · exact (Complex.isConnected_of_upperHalfPlane subset_rfl (by 

中文:
引理 eq_zero_of_frequently
  条件: {f : ℍ -> Complex} (hf : MDiff f) {τ : ℍ} (hτ : 存在ᶠ z in 𝓝[!=] τ, f z = 0)
  证明: by
  rw [mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  ext w
  convert! this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ τ.2 ?_ w.im_pos
  · rw [Function.comp_apply, ofComplex_apply]
  · exact (Complex.isConnected_of_upperHalfPlane subset_rfl (by 

Depends on / 依赖: Complex.isConnected_of_upperHalfPlane, Function, Function.comp_apply, analyticOnNhd, comp_apply, contrapose, convert, eqOn_zero_of_preconnected_of_frequently_eq_zero, eventually_map, eventually_nhdsWithin_iff, filter_upwards, hf.analyticOnNhd, im_pos, isConnected_of_upperHalfPlane, isOpenEmbedding_coe, isOpenEmbedding_coe.map_nhds_eq, isOpen_upperHalfPlaneSet, isPreconnected, map_nhds_eq, mdifferentiable_iff
-/
lemma eq_zero_of_frequently {f : ℍ -> Complex} (hf : MDiff f) {τ : ℍ} (hτ : existsᶠ z in 𝓝[!=] τ, f z = 0) :
    f = 0 := by
  rw [mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  ext w
  convert! this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ τ.2 ?_ w.im_pos
  · rw [Function.comp_apply, ofComplex_apply]
  · exact (Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)).isPreconnected
  · contrapose! hτ
    rw [eventually_nhdsWithin_iff]; rw [← isOpenEmbedding_coe.map_nhds_eq]; rw [eventually_map] at hτ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hτ] with a ha
    simpa using ha

/--
lemma `mul_eq_zero_iff` / 引理 `mul_eq_zero_iff`

English:
lemma mul_eq_zero_iff
  given: {f g : ℍ -> Complex} (hf : MDiff f) (hg : MDiff g)
  statement: f * g = 0 ↔ f = 0 ∨ g = 0
  proof: ⟨fun hfg => (frequently_or_distrib.mp <| .of_forall <| by simpa using congrFun hfg).imp
    (eq_zero_of_frequently (τ := I) hf) (eq_zero_of_frequently hg), by grind⟩

中文:
引理 mul_eq_zero_iff
  条件: {f g : ℍ -> Complex} (hf : MDiff f) (hg : MDiff g)
  结论: f * g = 0 ↔ f = 0 ∨ g = 0
  证明: ⟨fun hfg => (frequently_or_distrib.mp <| .of_forall <| by simpa using congrFun hfg).imp
    (eq_zero_of_frequently (τ := I) hf) (eq_zero_of_frequently hg), by grind⟩

Depends on / 依赖: eq_zero_of_frequently, frequently_or_distrib, frequently_or_distrib.mp, of_forall
-/
lemma mul_eq_zero_iff {f g : ℍ -> Complex} (hf : MDiff f) (hg : MDiff g) : f * g = 0 ↔ f = 0 ∨ g = 0 :=
  ⟨fun hfg => (frequently_or_distrib.mp <| .of_forall <| by simpa using congrFun hfg).imp
    (eq_zero_of_frequently (τ := I) hf) (eq_zero_of_frequently hg), by grind⟩

/--
lemma `prod_eq_zero_iff` / 引理 `prod_eq_zero_iff`

English:
lemma prod_eq_zero_iff
  statement: {ι : Type*} {f : ι -> ℍ -> Complex} {s : Finset ι}
  proof: by
  refine ⟨fun h0 => ?_, fun ⟨i, hi, hi'⟩ => Finset.prod_eq_zero hi hi'⟩
have : existsᶠ τ in 𝓝[!=] I, ∏ i in s, f i τ = 0 := .of_forall by simpa using congrFun h0
  simp only [Finset.prod_eq_zero_iff, Finset.frequently_exists] at this
  exact this.imp fun i hi => ⟨hi.1, eq_zero_of_frequently (hf i

中文:
引理 prod_eq_zero_iff
  结论: {ι : 类型} {f : ι -> ℍ -> Complex} {s : Finset ι}
  证明: by
  refine ⟨fun h0 => ?_, fun ⟨i, hi, hi'⟩ => Finset.prod_eq_zero hi hi'⟩
have : existsᶠ τ in 𝓝[!=] I, ∏ i in s, f i τ = 0 := .of_forall by simpa using congrFun h0
  simp only [Finset.prod_eq_zero_iff, Finset.frequently_exists] at this
  exact this.imp fun i hi => ⟨hi.1, eq_zero_of_frequently (hf i

Depends on / 依赖: Finset, Finset.frequently_exists, Finset.prod_eq_zero, Finset.prod_eq_zero_iff, eq_zero_of_frequently, frequently_exists, of_forall, prod_eq_zero, prod_eq_zero_iff, this.imp
-/
lemma prod_eq_zero_iff {ι : Type*} {f : ι -> ℍ -> Complex} {s : Finset ι}
    (hf : forall i in s, MDiff (f i)) :
    ∏ i in s, f i = 0 ↔ exists i in s, f i = 0 := by
  refine ⟨fun h0 => ?_, fun ⟨i, hi, hi'⟩ => Finset.prod_eq_zero hi hi'⟩
have : existsᶠ τ in 𝓝[!=] I, ∏ i in s, f i τ = 0 := .of_forall by simpa using congrFun h0
  simp only [Finset.prod_eq_zero_iff, Finset.frequently_exists] at this
  exact this.imp fun i hi => ⟨hi.1, eq_zero_of_frequently (hf i hi.1) hi.2⟩

section deriv
/-!
## Explicit calculations of the derivative of `τ ↦ g • τ`

TODO: would it be better to reimplement these using `mfderiv` together with a trivialization of
the tangent space of `ℍ`, rather than using `ofComplex` as we currently do? Or would that bring
more pain than gain?

TODO(MR): investigate if using `mvfderiv` can avoid the "pain" above, and be a cleaner design!
-/

section Complex

/--
lemma `hasDerivAt_denom_zpow` / 引理 `hasDerivAt_denom_zpow`

English:
lemma hasDerivAt_denom_zpow
  given: (g : GL (Fin 2) Real) (k : Int) (τ : ℍ)
  proof: by
  have hd : HasDerivAt (denom g ·) (g 1 0) τ := by
.add_const (g 1 1 : Complex) .const_mul _ simpa [denom] using hasDerivAt_id _
  have := (hasDerivAt_zpow k (denom g τ) (Or.inl (denom_ne_zero g τ))).comp _ hd
  simpa only [Function.comp_def, mul_right_comm] using this

中文:
引理 hasDerivAt_denom_zpow
  条件: (g : GL (Fin 2) 实数) (k : 整数) (τ : ℍ)
  证明: by
  have hd : HasDerivAt (denom g ·) (g 1 0) τ := by
.add_const (g 1 1 : Complex) .const_mul _ simpa [denom] using hasDerivAt_id _
  have := (hasDerivAt_zpow k (denom g τ) (Or.inl (denom_ne_zero g τ))).comp _ hd
  simpa only [Function.comp_def, mul_right_comm] using this

Depends on / 依赖: Function, Function.comp_def, HasDerivAt, Or.inl, add_const, comp_def, const_mul, denom_ne_zero, hasDerivAt_id, hasDerivAt_zpow, mul_right_comm
-/
lemma hasDerivAt_denom_zpow (g : GL (Fin 2) Real) (k : Int) (τ : ℍ) :
    HasDerivAt (fun z => denom g z ^ k) (k * g 1 0 * denom g τ ^ (k - 1)) τ := by
  have hd : HasDerivAt (denom g ·) (g 1 0) τ := by
.add_const (g 1 1 : Complex) .const_mul _ simpa [denom] using hasDerivAt_id _
  have := (hasDerivAt_zpow k (denom g τ) (Or.inl (denom_ne_zero g τ))).comp _ hd
  simpa only [Function.comp_def, mul_right_comm] using this

/--
lemma `deriv_denom_zpow` / 引理 `deriv_denom_zpow`

English:
lemma deriv_denom_zpow
  given: (g : GL (Fin 2) Real) (k : Int) (τ : ℍ)
  proof: (hasDerivAt_denom_zpow g k τ).deriv

中文:
引理 deriv_denom_zpow
  条件: (g : GL (Fin 2) 实数) (k : 整数) (τ : ℍ)
  证明: (hasDerivAt_denom_zpow g k τ).deriv

Depends on / 依赖: hasDerivAt_denom_zpow
-/
lemma deriv_denom_zpow (g : GL (Fin 2) Real) (k : Int) (τ : ℍ) :
    deriv (fun z => denom g z ^ k) τ = k * g 1 0 * denom g τ ^ (k - 1) :=
  (hasDerivAt_denom_zpow g k τ).deriv

/--
lemma `hasStrictDerivAt_smul` / 引理 `hasStrictDerivAt_smul`

English:
lemma hasStrictDerivAt_smul
  given: {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ)
  proof: by
  suffices HasStrictDerivAt (num g / denom g) (g.val.det / denom g τ ^ 2) τ by
    refine this.congr_of_eventuallyEq ?_
    rw [← isOpenEmbedding_coe.map_nhds_eq]; rw [eventuallyEq_map]
    simp [Function.comp_def, coe_smul_of_det_pos hg]
  convert!
    ((hasStrictDerivAt_id (τ : Complex)).const_

中文:
引理 hasStrictDerivAt_smul
  条件: {g : GL (Fin 2) 实数} (hg : 0 < g.val.det) (τ : ℍ)
  证明: by
  suffices HasStrictDerivAt (num g / denom g) (g.val.det / denom g τ ^ 2) τ by
    refine this.congr_of_eventuallyEq ?_
    rw [← isOpenEmbedding_coe.map_nhds_eq]; rw [eventuallyEq_map]
    simp [Function.comp_def, coe_smul_of_det_pos hg]
  convert!
    ((hasStrictDerivAt_id (τ : Complex)).const_

Depends on / 依赖: Function, Function.comp_def, HasStrictDerivAt, Matrix, Matrix.det_fin_two, add_const, coe_smul_of_det_pos, comp_def, congr_of_eventuallyEq, const_mul, convert, denom_ne_zero, det_fin_two, eventuallyEq_map, g.val.det, hasStrictDerivAt_id, isOpenEmbedding_coe, isOpenEmbedding_coe.map_nhds_eq, map_nhds_eq, this.congr_of_eventuallyEq
-/
lemma hasStrictDerivAt_smul {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) :
    HasStrictDerivAt (fun z => ↑(g • ofComplex z) : Complex -> Complex) (g.val.det / denom g τ ^ 2) τ := by
  suffices HasStrictDerivAt (num g / denom g) (g.val.det / denom g τ ^ 2) τ by
    refine this.congr_of_eventuallyEq ?_
    rw [← isOpenEmbedding_coe.map_nhds_eq]; rw [eventuallyEq_map]
    simp [Function.comp_def, coe_smul_of_det_pos hg]
  convert!
    ((hasStrictDerivAt_id (τ : Complex)).const_mul _ |>.add_const _).div
      ((hasStrictDerivAt_id (τ : Complex)).const_mul _ |>.add_const _) _ using 2
  · simp [Matrix.det_fin_two]; ring
  · apply denom_ne_zero

/--
lemma `deriv_smul` / 引理 `deriv_smul`

English:
lemma deriv_smul
  given: {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ)
  proof: .deriv .hasDerivAt hasStrictDerivAt_smul hg τ

中文:
引理 deriv_smul
  条件: {g : GL (Fin 2) 实数} (hg : 0 < g.val.det) (τ : ℍ)
  证明: .deriv .hasDerivAt hasStrictDerivAt_smul hg τ

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_smul
-/
lemma deriv_smul {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z => ↑(g • ofComplex z) : Complex -> Complex) τ = g.val.det / denom g τ ^ 2 :=
.deriv .hasDerivAt hasStrictDerivAt_smul hg τ

/--
lemma `deriv_smul_ne_zero` / 引理 `deriv_smul_ne_zero`

English:
lemma deriv_smul_ne_zero
  given: {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ)
  proof: by
  rw [deriv_smul hg]
  apply div_ne_zero
  · exact_mod_cast hg.ne'
  · exact pow_ne_zero _ (denom_ne_zero g τ)

中文:
引理 deriv_smul_ne_zero
  条件: {g : GL (Fin 2) 实数} (hg : 0 < g.val.det) (τ : ℍ)
  证明: by
  rw [deriv_smul hg]
  apply div_ne_zero
  · exact_mod_cast hg.ne'
  · exact pow_ne_zero _ (denom_ne_zero g τ)

Depends on / 依赖: denom_ne_zero, deriv_smul, div_ne_zero, hg.ne, pow_ne_zero
-/
lemma deriv_smul_ne_zero {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z => ↑(g • ofComplex z) : Complex -> Complex) τ != 0 := by
  rw [deriv_smul hg]
  apply div_ne_zero
  · exact_mod_cast hg.ne'
  · exact pow_ne_zero _ (denom_ne_zero g τ)

/--
lemma `analyticAt_smul` / 引理 `analyticAt_smul`

English:
lemma analyticAt_smul
  given: {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ)
  proof: by
  refine DifferentiableOn.analyticAt (fun z hz => ?_) (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  apply DifferentiableAt.differentiableWithinAt
  simpa [mdifferentiableAt_iff] using!
    (mdifferentiable_coe.comp <| (mdifferentiable_smul hg)).mdifferentiableAt (x := ⟨z, hz⟩)

中文:
引理 analyticAt_smul
  条件: {g : GL (Fin 2) 实数} (hg : 0 < g.val.det) (τ : ℍ)
  证明: by
  refine DifferentiableOn.analyticAt (fun z hz => ?_) (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  apply DifferentiableAt.differentiableWithinAt
  simpa [mdifferentiableAt_iff] using!
    (mdifferentiable_coe.comp <| (mdifferentiable_smul hg)).mdifferentiableAt (x := ⟨z, hz⟩)

Depends on / 依赖: DifferentiableAt, DifferentiableAt.differentiableWithinAt, DifferentiableOn, DifferentiableOn.analyticAt, analyticAt, differentiableWithinAt, im_pos, isOpen_upperHalfPlaneSet, isOpen_upperHalfPlaneSet.mem_nhds, mdifferentiableAt, mdifferentiableAt_iff, mdifferentiable_coe, mdifferentiable_coe.comp, mdifferentiable_smul, mem_nhds
-/
lemma analyticAt_smul {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) :
    AnalyticAt Complex (fun z => ↑(g • ofComplex z) : Complex -> Complex) τ := by
  refine DifferentiableOn.analyticAt (fun z hz => ?_) (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  apply DifferentiableAt.differentiableWithinAt
  simpa [mdifferentiableAt_iff] using!
    (mdifferentiable_coe.comp <| (mdifferentiable_smul hg)).mdifferentiableAt (x := ⟨z, hz⟩)

/--
lemma `meromorphicOrderAt_comp_smul` / 引理 `meromorphicOrderAt_comp_smul`

English:
lemma meromorphicOrderAt_comp_smul
  given: {f : ℍ -> Complex} {τ : ℍ} {g : GL (Fin 2) Real} (hg : 0 < g.val.det)
  proof: by
  let G z : Complex := ↑(g • ofComplex z)
  let F z := f (ofComplex z)
  have : (fun z : Complex => f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [this]; rw [meromorphicOrderAt_comp_of_deriv_ne_zero]
  · simp [F, G]
  · exact τ.analyticAt_smul hg
  · exact τ.deriv_smul_ne_zero hg

中文:
引理 meromorphicOrderAt_comp_smul
  条件: {f : ℍ -> Complex} {τ : ℍ} {g : GL (Fin 2) 实数} (hg : 0 < g.val.det)
  证明: by
  let G z : Complex := ↑(g • ofComplex z)
  let F z := f (ofComplex z)
  have : (fun z : Complex => f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [this]; rw [meromorphicOrderAt_comp_of_deriv_ne_zero]
  · simp [F, G]
  · exact τ.analyticAt_smul hg
  · exact τ.deriv_smul_ne_zero hg

Depends on / 依赖: analyticAt_smul, deriv_smul_ne_zero, meromorphicOrderAt_comp_of_deriv_ne_zero, ofComplex
-/
lemma meromorphicOrderAt_comp_smul {f : ℍ -> Complex} {τ : ℍ} {g : GL (Fin 2) Real} (hg : 0 < g.val.det) :
    meromorphicOrderAt (fun z => f (g • ofComplex z)) τ =
      meromorphicOrderAt (fun z => f (ofComplex z)) ↑(g • τ) := by
  let G z : Complex := ↑(g • ofComplex z)
  let F z := f (ofComplex z)
  have : (fun z : Complex => f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [this]; rw [meromorphicOrderAt_comp_of_deriv_ne_zero]
  · simp [F, G]
  · exact τ.analyticAt_smul hg
  · exact τ.deriv_smul_ne_zero hg

end Complex


section Real

/--
Definition of `smulFDeriv` / `smulFDeriv` 的定义

English:
definition smulFDeriv
  signature: (g : GL (Fin 2) Real) (z : Complex)
  body: (σ g) ∘L (ContinuousLinearMap.toSpanSingleton Complex (g.det.val / denom g z ^ 2)).restrictScalars Real

@[simp]

中文:
定义 smulFDeriv
  签名: (g : GL (Fin 2) 实数) (z : Complex)
  定义体: (σ g) ∘L (ContinuousLinearMap.toSpanSingleton Complex (g.det.val / denom g z ^ 2)).restrictScalars Real

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toSpanSingleton, g.det.val, restrictScalars, toSpanSingleton
-/
noncomputable def smulFDeriv (g : GL (Fin 2) Real) (z : Complex) : Complex ->L[Real] Complex :=
  (σ g) ∘L (ContinuousLinearMap.toSpanSingleton Complex (g.det.val / denom g z ^ 2)).restrictScalars Real

@[simp]
/--
theorem `smulFDeriv_J_mul` / 定理 `smulFDeriv_J_mul`

English:
theorem smulFDeriv_J_mul
  given: (g : GL (Fin 2) Real) (z : Complex)
  proof: by
  ext
  by_cases hg : 0 < g.val.det
  · simp [smulFDeriv, σ, hg, hg.not_gt, neg_div]
  · simp [smulFDeriv, σ, hg, g.det_ne_zero.lt_or_gt.resolve_right hg, neg_div]

中文:
定理 smulFDeriv_J_mul
  条件: (g : GL (Fin 2) 实数) (z : Complex)
  证明: by
  ext
  by_cases hg : 0 < g.val.det
  · simp [smulFDeriv, σ, hg, hg.not_gt, neg_div]
  · simp [smulFDeriv, σ, hg, g.det_ne_zero.lt_or_gt.resolve_right hg, neg_div]

Depends on / 依赖: det_ne_zero, g.det_ne_zero.lt_or_gt.resolve_right, g.val.det, hg.not_gt, lt_or_gt, neg_div, not_gt, resolve_right, smulFDeriv
-/
theorem smulFDeriv_J_mul (g : GL (Fin 2) Real) (z : Complex) :
    smulFDeriv (J * g) z = -Complex.conjCLE ∘L smulFDeriv g z := by
  ext
  by_cases hg : 0 < g.val.det
  · simp [smulFDeriv, σ, hg, hg.not_gt, neg_div]
  · simp [smulFDeriv, σ, hg, g.det_ne_zero.lt_or_gt.resolve_right hg, neg_div]

/--
lemma `det_smulFDeriv` / 引理 `det_smulFDeriv`

English:
lemma det_smulFDeriv
  given: (g : GL (Fin 2) Real) (z : Complex)
  proof: by
  simp only [smulFDeriv, σ]
  rcases g.det_ne_zero.lt_or_gt with h | h
  · simp [h.not_gt, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul, sign_neg h, neg_div]
  · simp [ContinuousLinearMap.det, h, LinearMap.det_restrict

中文:
引理 det_smulFDeriv
  条件: (g : GL (Fin 2) 实数) (z : Complex)
  证明: by
  simp only [smulFDeriv, σ]
  rcases g.det_ne_zero.lt_or_gt with h | h
  · simp [h.not_gt, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul, sign_neg h, neg_div]
  · simp [ContinuousLinearMap.det, h, LinearMap.det_restrict

Depends on / 依赖: Algebra, Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ContinuousLinearMap, ContinuousLinearMap.det, LinearMap, LinearMap.det_restrictScalars, det_ne_zero, det_restrictScalars, g.det_ne_zero.lt_or_gt, h.not_gt, lt_or_gt, neg_div, normSq_eq_norm_sq, norm_complex_eq, not_gt, pow_mul, sign_neg, smulFDeriv
-/
lemma det_smulFDeriv (g : GL (Fin 2) Real) (z : Complex) :
    (smulFDeriv g z).det =
      SignType.sign g.det.val * g.det ^ 2 / ‖denom g z‖ ^ 4 := by
  simp only [smulFDeriv, σ]
  rcases g.det_ne_zero.lt_or_gt with h | h
  · simp [h.not_gt, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul, sign_neg h, neg_div]
  · simp [ContinuousLinearMap.det, h, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul]

/--
lemma `hasStrictFDerivAt_smul` / 引理 `hasStrictFDerivAt_smul`

English:
lemma hasStrictFDerivAt_smul
  given: (g : GL (Fin 2) Real) (τ : ℍ)
  proof: by
  wlog hg : 0 < g.det.val generalizing g
  · replace hg := g.det.ne_zero.lt_or_gt.resolve_right hg
    convert! Complex.conjCLE.hasStrictFDerivAt.neg.comp _ (this (J * g) (by simpa))
    · simp [mul_smul, coe_J_smul]
    · ext
      simp
  have := (hasStrictDerivAt_smul hg τ).hasStrictFDerivAt.re

中文:
引理 hasStrictFDerivAt_smul
  条件: (g : GL (Fin 2) 实数) (τ : ℍ)
  证明: by
  wlog hg : 0 < g.det.val generalizing g
  · replace hg := g.det.ne_zero.lt_or_gt.resolve_right hg
    convert! Complex.conjCLE.hasStrictFDerivAt.neg.comp _ (this (J * g) (by simpa))
    · simp [mul_smul, coe_J_smul]
    · ext
      simp
  have := (hasStrictDerivAt_smul hg τ).hasStrictFDerivAt.re

Depends on / 依赖: Complex.conjCLE.hasStrictFDerivAt.neg.comp, coe_J_smul, conjCLE, convert, g.det.ne_zero.lt_or_gt.resolve_right, g.det.val, generalizing, hasStrictDerivAt_smul, hasStrictFDerivAt, hasStrictFDerivAt.restrictScalars, lt_or_gt, mul_smul, ne_zero, replace, resolve_right, restrictScalars, smulFDeriv
-/
lemma hasStrictFDerivAt_smul (g : GL (Fin 2) Real) (τ : ℍ) :
    HasStrictFDerivAt (fun z => ↑(g • ofComplex z) : Complex -> Complex) (smulFDeriv g τ) τ := by
  wlog hg : 0 < g.det.val generalizing g
  · replace hg := g.det.ne_zero.lt_or_gt.resolve_right hg
    convert! Complex.conjCLE.hasStrictFDerivAt.neg.comp _ (this (J * g) (by simpa))
    · simp [mul_smul, coe_J_smul]
    · ext
      simp
  have := (hasStrictDerivAt_smul hg τ).hasStrictFDerivAt.restrictScalars Real
  simp_all [smulFDeriv, σ]

end Real

end deriv

end UpperHalfPlane
