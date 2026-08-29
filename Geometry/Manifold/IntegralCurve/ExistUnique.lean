/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Geometry.Manifold.IntegralCurve.Transform
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Notation

/-!
# Existence and uniqueness of integral curves

## Main results

* `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`: Existence of local integral curves for a
  $C^1$ vector field. This follows from the existence theorem for solutions to ODEs
  (`exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt`).
* `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`: Uniqueness of local integral curves for a
  $C^1$ vector field. This follows from the uniqueness theorem for solutions to ODEs
  (`ODE_solution_unique_of_mem_set_Ioo`). This requires the manifold to be Hausdorff (`T2Space`).

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a TODO.

We state simpler versions of the theorem for boundaryless manifolds as corollaries.

## TODO

* The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
  Lee. May require submanifolds.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field, local existence, uniqueness
-/

public section

open scoped Topology

open Function Manifold Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : Real -> M} {v : (x : M) -> TangentSpace I x} {s s' : Set Real} (t₀ : Real) {x₀ : M}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_isMIntegralCurveAt_of_contMDiffAt` / 定理 `exists_isMIntegralCurveAt_of_contMDiffAt`

English:
theorem exists_isMIntegralCurveAt_of_contMDiffAt
  statement: [CompleteSpace E]
  proof: by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, hf2⟩ := hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)
.snd.e

中文:
定理 exists_isMIntegralCurveAt_of_contMDiffAt
  结论: [CompleteSpace E]
  证明: by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, hf2⟩ := hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)
.snd.e
-/
theorem exists_isMIntegralCurveAt_of_contMDiffAt [CompleteSpace E]
    (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    exists γ : Real -> M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀ := by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, hf2⟩ := hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)
.snd.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  simp_rw [← Real.ball_eq_Ioo, ← Metric.eventually_nhds_iff_ball] at hf2
  -- use continuity of `f` so that `f t` remains inside `interior (extChartAt I x₀).target`
  have ⟨a, ha, hf2'⟩ := Metric.eventually_nhds_iff_ball.mp hf2
  have hcont := (hf2' t₀ (Metric.mem_ball_self ha)).continuousAt
  rw [continuousAt_def]; rw [hf1] at hcont
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) in 𝓝 t₀ :=
    hcont _ (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx))
  rw [← eventually_mem_nhds_iff] at hnhds
  -- obtain a neighbourhood `s` so that the above conditions both hold in `s`
  obtain ⟨s, hs, haux⟩ := (hf2.and hnhds).exists_mem
  -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
  refine ⟨(extChartAt I x₀).symm ∘ f,
    Eq.symm (by rw [Function.comp_apply, hf1, PartialEquiv.left_inv _ (mem_extChartAt_source ..)]),
    isMIntegralCurveAt_iff.mpr ⟨s, hs, ?_⟩⟩
  intro t ht
  -- collect useful terms in convenient forms
  let xₜ : M := (extChartAt I x₀).symm (f t) -- `xₜ := γ t`
have h : HasDerivAt f (x := t) fderivWithin Real (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ) := (haux t ht).1
  rw [← tangentCoordChange_def] at h
have hf3 := mem_preimage.mp mem_of_mem_nhds (haux t ht).2
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
have hft1 := mem_preimage.mp
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  -- express the derivative of the integral curve in the local chart
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt` on `h`
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2]; rw [← tangentCoordChange_comp (x := x₀) ⟨⟨hft2]; rw [hft1⟩]; rw [hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/--
lemma `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` / 引理 `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`

English:
lemma exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
  proof: exists_isMIntegralCurveAt_of_contMDiffAt t₀ hv BoundarylessManifold.isInteriorPoint

中文:
引理 exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
  证明: exists_isMIntegralCurveAt_of_contMDiffAt t₀ hv BoundarylessManifold.isInteriorPoint

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, exists_isMIntegralCurveAt_of_contMDiffAt, isInteriorPoint
-/
lemma exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    [CompleteSpace E] [BoundarylessManifold I M]
    (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    exists γ : Real -> M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀ :=
  exists_isMIntegralCurveAt_of_contMDiffAt t₀ hv BoundarylessManifold.isInteriorPoint

variable {t₀}

/--
theorem `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt` / 定理 `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt`

English:
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
  statement: (hγt₀ : I.IsInteriorPoint (γ t₀))
  proof: by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E -> E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((ex

中文:
定理 isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
  结论: (hγt₀ : I.Is整数eriorPoint (γ t₀))
  证明: by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E -> E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((ex
-/
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (γ t₀))
    (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E -> E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  -- extract a set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : exists K, exists s in 𝓝 _, LipschitzOnWith K v' s :=
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint hγt₀)).snd.exists_lipschitzOnWith
  have hlip (t : Real) : LipschitzOnWith K ((fun _ => v') t) ((fun _ => s) t) := hlip
  -- internal lemmas to reduce code duplication
  have hsrc {g} (hg : IsMIntegralCurveAt g v t₀) :
forallᶠ t in 𝓝 t₀, g ⁻¹' (extChartAt I (g t₀)).source in 𝓝 t := eventually_mem_nhds_iff.mpr
continuousAt_def.mp hg.continuousAt _ extChartAt_source_mem_nhds (g t₀)
  have hmem {g : Real -> M} {t} (ht : g ⁻¹' (extChartAt I (g t₀)).source in 𝓝 t) :
g t in (extChartAt I (g t₀)).source := mem_preimage.mp mem_of_mem_nhds ht
  have hdrv {g} (hg : IsMIntegralCurveAt g v t₀) (h' : γ t₀ = g t₀) : forallᶠ t in 𝓝 t₀,
      HasDerivAt ((extChartAt I (g t₀)) ∘ g) ((fun _ => v') t (((extChartAt I (g t₀)) ∘ g) t)) t ∧
      ((extChartAt I (g t₀)) ∘ g) t in (fun _ => s) t := by
    apply Filter.Eventually.and
    · apply (hsrc hg |>.and hg.eventually_hasDerivAt).mono
      rintro t ⟨ht1, ht2⟩
      rw [hv']; rw [h']
      apply ht2.congr_deriv
      congr <;>
      rw [Function.comp_apply]; rw [PartialEquiv.left_inv _ (hmem ht1)]
    · apply ((continuousAt_extChartAt (g t₀)).comp hg.continuousAt).preimage_mem_nhds
      rw [Function.comp_apply]; rw [← h']
      exact hs
  have heq {g} (hg : IsMIntegralCurveAt g v t₀) :
    g =ᶠ[𝓝 t₀] (extChartAt I (g t₀)).symm ∘ ↑(extChartAt I (g t₀)) ∘ g := by
    apply (hsrc hg).mono
    intro t ht
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [PartialEquiv.left_inv _ (hmem ht)]
  -- main proof
  suffices (extChartAt I (γ t₀)) ∘ γ =ᶠ[𝓝 t₀] (extChartAt I (γ' t₀)) ∘ γ' from
(heq hγ).trans (this.fun_comp (extChartAt I (γ t₀)).symm).trans (h ▸ (heq hγ').symm)
  exact ODE_solution_unique_of_eventually (.of_forall hlip)
    (hdrv hγ rfl) (hdrv hγ' h) (by rw [Function.comp_apply, Function.comp_apply, h])

/--
theorem `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless` / 定理 `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`

English:
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
  statement: [BoundarylessManifold I M]
  proof: isMIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h

中文:
定理 isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
  结论: [BoundarylessManifold I M]
  证明: isMIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, isInteriorPoint, isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
-/
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless [BoundarylessManifold I M]
    (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' :=
  isMIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h

variable [T2Space M] {a b : Real}

/--
theorem `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` / 定理 `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`

English:
theorem isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
  statement: (ht₀ : t₀ in Ioo a b)
  proof: by
  set s := {t | γ t = γ' t} inter Ioo a b with hs
  -- since `Ioo a b` is connected, we get `s = Ioo a b` by showing that `s` is clopen in `Ioo a b`
  -- in the subtype topology (`s` is also non-empty by assumption)
  -- here we use a slightly weaker alternative theorem
  suffices hsub : Ioo a b 

中文:
定理 isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
  结论: (ht₀ : t₀ in Ioo a b)
  证明: by
  set s := {t | γ t = γ' t} inter Ioo a b with hs
  -- since `Ioo a b` is connected, we get `s = Ioo a b` by showing that `s` is clopen in `Ioo a b`
  -- in the subtype topology (`s` is also non-empty by assumption)
  -- here we use a slightly weaker alternative theorem
  suffices hsub : Ioo a b 
-/
theorem isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (ht₀ : t₀ in Ioo a b)
    (hγt : forall t in Ioo a b, I.IsInteriorPoint (γ t))
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  set s := {t | γ t = γ' t} inter Ioo a b with hs
  -- since `Ioo a b` is connected, we get `s = Ioo a b` by showing that `s` is clopen in `Ioo a b`
  -- in the subtype topology (`s` is also non-empty by assumption)
  -- here we use a slightly weaker alternative theorem
  suffices hsub : Ioo a b subseteq s from fun t ht => mem_ofPred.mp ((subset_def ▸ hsub) t ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · -- is this really the most convenient way to pass to subtype topology?
    -- TODO: shorten this when better API around subtype topology exists
    rw [hs]; rw [inter_comm]; rw [← Subtype.image_preimage_val]; rw [inter_comm]; rw [← Subtype.image_preimage_val]; rw [image_subset_image_iff Subtype.val_injective]; rw [preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage]; rw [← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
.continuousAt (Ioo_mem_nhds ht.1 ht.2) exact hγ.continuousWithinAt ht
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
.continuousAt (Ioo_mem_nhds ht.1 ht.2) exact hγ'.continuousWithinAt ht
  · rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hmem := Ioo_mem_nhds ht₁.2.1 ht₁.2.2
    have heq : γ =ᶠ[𝓝 t₁] γ' := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
      (hγt _ ht₁.2) hv.contMDiffAt (hγ.isMIntegralCurveAt hmem) (hγ'.isMIntegralCurveAt hmem) ht₁.1
    apply (heq.and hmem).mono
    exact fun _ ht => ht

/--
theorem `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` / 定理 `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`

English:
theorem isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
  statement: [BoundarylessManifold I M]
  proof: isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
    ht₀ (fun _ _ => BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

中文:
定理 isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
  结论: [BoundarylessManifold I M]
  证明: isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
    ht₀ (fun _ _ => BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, isInteriorPoint, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
-/
theorem isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (ht₀ : t₀ in Ioo a b)
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
    ht₀ (fun _ _ => BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

/--
theorem `isMIntegralCurve_eq_of_contMDiff` / 定理 `isMIntegralCurve_eq_of_contMDiff`

English:
theorem isMIntegralCurve_eq_of_contMDiff
  statement: (hγt : forall t, I.IsInteriorPoint (γ t))
  proof: by
  ext t
  obtain ⟨T, ht₀, ht⟩ : exists T, t in Ioo (-T) T ∧ t₀ in Ioo (-T) T := by
    obtain ⟨T, hT₁, hT₂⟩ := exists_abs_lt t
    obtain ⟨hT₂, hT₃⟩ := abs_lt.mp hT₂
    obtain ⟨S, hS₁, hS₂⟩ := exists_abs_lt t₀
    obtain ⟨hS₂, hS₃⟩ := abs_lt.mp hS₂
    exact ⟨T + S, by constructor <;> constructo

中文:
定理 isMIntegralCurve_eq_of_contMDiff
  结论: (hγt : 对任意 t, I.Is整数eriorPoint (γ t))
  证明: by
  ext t
  obtain ⟨T, ht₀, ht⟩ : exists T, t in Ioo (-T) T ∧ t₀ in Ioo (-T) T := by
    obtain ⟨T, hT₁, hT₂⟩ := exists_abs_lt t
    obtain ⟨hT₂, hT₃⟩ := abs_lt.mp hT₂
    obtain ⟨S, hS₁, hS₂⟩ := exists_abs_lt t₀
    obtain ⟨hS₂, hS₃⟩ := abs_lt.mp hS₂
    exact ⟨T + S, by constructor <;> constructo

Depends on / 依赖: abs_lt, abs_lt.mp, exists_abs_lt, isMIntegralCurveOn, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff, subset_univ
-/
theorem isMIntegralCurve_eq_of_contMDiff (hγt : forall t, I.IsInteriorPoint (γ t))
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' := by
  ext t
  obtain ⟨T, ht₀, ht⟩ : exists T, t in Ioo (-T) T ∧ t₀ in Ioo (-T) T := by
    obtain ⟨T, hT₁, hT₂⟩ := exists_abs_lt t
    obtain ⟨hT₂, hT₃⟩ := abs_lt.mp hT₂
    obtain ⟨S, hS₁, hS₂⟩ := exists_abs_lt t₀
    obtain ⟨hS₂, hS₃⟩ := abs_lt.mp hS₂
    exact ⟨T + S, by constructor <;> constructor <;> linarith⟩
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff ht (fun t _ => hγt t) hv
    ((hγ.isMIntegralCurveOn _).mono (subset_univ _))
    ((hγ'.isMIntegralCurveOn _).mono (subset_univ _)) h ht₀

/--
theorem `isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless` / 定理 `isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless`

English:
theorem isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
  statement: [BoundarylessManifold I M]
  proof: isMIntegralCurve_eq_of_contMDiff (fun _ => BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

中文:
定理 isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
  结论: [BoundarylessManifold I M]
  证明: isMIntegralCurve_eq_of_contMDiff (fun _ => BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, isInteriorPoint, isMIntegralCurve_eq_of_contMDiff
-/
theorem isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_eq_of_contMDiff (fun _ => BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

/--
lemma `IsMIntegralCurve.periodic_of_eq` / 引理 `IsMIntegralCurve.periodic_of_eq`

English:
lemma IsMIntegralCurve.periodic_of_eq
  statement: [BoundarylessManifold I M]
  proof: by
apply congrFun
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := b) hv (hγ.comp_add _) hγ _
  rw [comp_apply]; rw [add_sub_cancel]; rw [heq]

中文:
引理 IsMIntegralCurve.periodic_of_eq
  结论: [BoundarylessManifold I M]
  证明: by
apply congrFun
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := b) hv (hγ.comp_add _) hγ _
  rw [comp_apply]; rw [add_sub_cancel]; rw [heq]

Depends on / 依赖: add_sub_cancel, comp_add, comp_apply, isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
-/
lemma IsMIntegralCurve.periodic_of_eq [BoundarylessManifold I M]
    (hγ : IsMIntegralCurve γ v)
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (heq : γ a = γ b) : Periodic γ (a - b) := by
apply congrFun
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := b) hv (hγ.comp_add _) hγ _
  rw [comp_apply]; rw [add_sub_cancel]; rw [heq]

/--
lemma `IsMIntegralCurve.periodic_xor_injective` / 引理 `IsMIntegralCurve.periodic_xor_injective`

English:
lemma IsMIntegralCurve.periodic_xor_injective
  statement: [BoundarylessManifold I M]
  proof: by
  rw [xor_iff_iff_not]
  refine ⟨fun ⟨T, hT, hf⟩ => hf.not_injective (ne_of_gt hT), ?_⟩
  intro h
  rw [Injective] at h
  push Not at h
  obtain ⟨a, b, heq, hne⟩ := h
  refine ⟨|a - b|, ?_, ?_⟩
  · rw [gt_iff_lt, abs_pos, sub_ne_zero]
    exact hne
  · by_cases! hab : a - b < 0
    · rw [abs_of_n

中文:
引理 IsMIntegralCurve.periodic_xor_injective
  结论: [BoundarylessManifold I M]
  证明: by
  rw [xor_iff_iff_not]
  refine ⟨fun ⟨T, hT, hf⟩ => hf.not_injective (ne_of_gt hT), ?_⟩
  intro h
  rw [Injective] at h
  push Not at h
  obtain ⟨a, b, heq, hne⟩ := h
  refine ⟨|a - b|, ?_, ?_⟩
  · rw [gt_iff_lt, abs_pos, sub_ne_zero]
    exact hne
  · by_cases! hab : a - b < 0
    · rw [abs_of_n

Depends on / 依赖: Injective, abs_of_neg, abs_of_nonneg, abs_pos, gt_iff_lt, heq.symm, hf.not_injective, ne_of_gt, neg_sub, not_injective, periodic_of_eq, sub_ne_zero, xor_iff_iff_not
-/
lemma IsMIntegralCurve.periodic_xor_injective [BoundarylessManifold I M]
    (hγ : IsMIntegralCurve γ v)
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    Xor (exists T > 0, Periodic γ T) (Injective γ) := by
  rw [xor_iff_iff_not]
  refine ⟨fun ⟨T, hT, hf⟩ => hf.not_injective (ne_of_gt hT), ?_⟩
  intro h
  rw [Injective] at h
  push Not at h
  obtain ⟨a, b, heq, hne⟩ := h
  refine ⟨|a - b|, ?_, ?_⟩
  · rw [gt_iff_lt, abs_pos, sub_ne_zero]
    exact hne
  · by_cases! hab : a - b < 0
    · rw [abs_of_neg hab, neg_sub]
      exact hγ.periodic_of_eq hv heq.symm
    · rw [abs_of_nonneg hab]
      exact hγ.periodic_of_eq hv heq
