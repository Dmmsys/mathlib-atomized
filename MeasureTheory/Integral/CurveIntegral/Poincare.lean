/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.Homotopy.Affine

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Poincaré lemma for 1-forms

In this file we prove Poincaré lemma for 1-forms for convex sets.
Namely, we show that a closed 1-form on a convex subset of a normed space is exact.

We also prove that the integrals of a closed 1-form
along 2 curves that are joined by a `C²`-smooth homotopy are equal.
In the future, this will allow us to prove Poincaré lemma for simply connected open sets
and, more generally, for simply connected locally convex sets.

## Implementation notes

In this file, we represent a 1-form as `ω : E → E →L[𝕜] F`, where `𝕜` is `ℝ` or `ℂ`,
not as `ω : E → E [⋀^Fin 1]→L[𝕜] F`.
A 1-form represented this way is closed
iff its Fréchet derivative `dω : E → E →L[𝕜] E →L[𝕜] F` is symmetric, `dω a x y = dω a y x`.
-/

public section

open scoped unitInterval Interval Pointwise Topology
open AffineMap Filter Function MeasureTheory Set

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousMap.Homotopy

variable [NormedSpace Real E] [NormedSpace Real F] {a b c d : E}
    {γ₁ : Path a b} {γ₂ : Path c d} {s : Set (I × I)} {t : Set E}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real` / 定理 `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real`

English:
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
  proof: by
  -- The overall plan of the proof is to pullback the 1-form to the unit square along the homotopy,
  -- prove that it's a closed 1-form, then apply the divergence theorem.
  -- Let `U` be the interior of the unit square
  -- Warning: throughout the proof, we sometimes have `0` or `1` in product 

中文:
定理 curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
  证明: by
  -- The overall plan of the proof is to pullback the 1-form to the unit square along the homotopy,
  -- prove that it's a closed 1-form, then apply the divergence theorem.
  -- Let `U` be the interior of the unit square
  -- Warning: throughout the proof, we sometimes have `0` or `1` in product 
-/
private theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
    {ω : E -> E ->L[Real] F} {dω : E -> E ->L[Real] E ->L[Real] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : forall a in Ioo 0 1, forall b in Ioo 0 1, φ (a, b) in t)
    (hω : forall a in Ioo (0 : I) 1, forall b in Ioo (0 : I) 1, (a, b) ∉ s ->
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))) (hωc : ContinuousOn ω (closure t))
    (hdω_symm : forall a in Ioo (0 : I) 1, forall b in Ioo (0 : I) 1, (a, b) ∉ s ->
      forall u in tangentConeAt Real t (φ (a, b)), forall v in tangentConeAt Real t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn Real 2
      (fun xy : Real × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  -- The overall plan of the proof is to pullback the 1-form to the unit square along the homotopy,
  -- prove that it's a closed 1-form, then apply the divergence theorem.
  -- Let `U` be the interior of the unit square
  -- Warning: throughout the proof, we sometimes have `0` or `1` in product spaces,
  -- not only in `I` or `ℝ`, so, e.g., `Icc 0 1` may refer to the unit square
  -- in `ℝ × ℝ`.
  set U : Set (Real × Real) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hinterior : interior (Icc 0 1) = U := by
    rw [hU]; rw [← interior_Icc]; rw [← interior_prod_eq]
    simp [Prod.mk_zero_zero, Prod.mk_one_one]
  have hunique : UniqueDiffOn Real (Icc 0 1 : Set (Real × Real)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hU_subset : U subseteq Icc 0 1 := hinterior ▸ interior_subset
  have hclosure : closure U = Icc 0 1 := by
    simp [hU, closure_prod_eq, Prod.mk_zero_zero, Prod.mk_one_one]
  -- Extend the homotopy `φ` to a continuous map `ψ : ℝ × ℝ → E`
  set ψ : Real × Real -> E := fun xy : Real × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2 with hψ
  have hψφ : forall a b : I, ψ (a, b) = φ (a, b) := by simp [ψ]
  have hψ_cont : Continuous ψ := by fun_prop
  have hψUt : MapsTo ψ U t := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    lift a to I using Ioo_subset_Icc_self ha
    lift b to I using Ioo_subset_Icc_self hb
    simpa [hψφ] using hφt a ha b hb
  -- Let `dψ` be its derivative.
  set dψ : Real × Real -> Real × Real ->L[Real] E := fderivWithin Real ψ (Icc 0 1)
  -- Let `s'` be the set `s` interpreted as a set in `ℝ × ℝ`
  set s' : Set (Real × Real) := Prod.map (↑) (↑) '' s with hs'
  have hmem_s' (x y : I) : (↑x, ↑y) in s' ↔ (x, y) in s := by
    rw [hs']; rw [← Prod.map_apply]; rw [Injective.mem_set_image]
    apply Injective.prodMap <;> apply Subtype.val_injective
  have hs'c : s'.Countable := hs.image _
  have hdψ : forall a in U, HasFDerivAt ψ (dψ a) a := by
    rintro a haU
    refine hcontdiff.differentiableOn (by decide) a (hU_subset haU)
.hasFDerivAt ?_ .hasFDerivWithinAt
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Let `d2ψ` be its second derivative
  set d2ψ : Real × Real -> Real × Real ->L[Real] Real × Real ->L[Real] E := fderivWithin Real dψ (Icc 0 1)
  have hd2ψ : forall a in U, HasFDerivAt dψ (d2ψ a) a := by
    rintro a haU
.differentiableOn_one a (hU_subset haU) refine hcontdiff.fderivWithin hunique (by decide)
.hasFDerivAt ?_ .hasFDerivWithinAt
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Note that `d2ψ` is symmetric
  have hd2ψ_symm : forall a in Icc 0 1, forall x y, d2ψ a x y = d2ψ a y x := by
    intro a ha
    exact (hcontdiff a ha).isSymmSndFDerivWithinAt (by simp) hunique
      (by simp [hinterior, hclosure, ha]) ha
  -- Consider `η a = ω (ψ a) ∘L dψ a`.
  set η : Real × Real -> Real × Real ->L[Real] F := fun a => ω (ψ a) ∘L dψ a
  -- Put `f a = η a (0, 1)`, `g a = -η a (1, 0)`.
  set f : Real × Real -> F := fun a => η a (0, 1)
  have hf : forall a in Icc 0 1, f a = ω (ψ a) (derivWithin (ψ ∘ (a.1, ·)) I a.2) := by
    intro a ha
    simp only [f, η, dψ, ContinuousLinearMap.comp_apply]
    congr 1
    have : HasDerivWithinAt (a.1, ·) (0, 1) I a.2 :=
      .prodMk (hasDerivWithinAt_const ..) (hasDerivWithinAt_id ..)
.comp_hasDerivWithinAt _ this ?_ refine DifferentiableWithinAt.hasFDerivWithinAt ?_
.symm .derivWithin ?_
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht => ⟨⟨ha.1.1, ht.1⟩, ⟨ha.2.1, ht.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.2, ha.2.2⟩
  set g : Real × Real -> F := fun a => -η a (1, 0)
  have hg : forall a in Icc 0 1, g a = ω (ψ a) (-derivWithin (ψ ∘ (·, a.2)) I a.1) := by
    intro a ha
    simp only [g, η, dψ, ContinuousLinearMap.comp_apply, map_neg]
    congr 2
    have : HasDerivWithinAt (·, a.2) (1, 0) I a.1 :=
      .prodMk (hasDerivWithinAt_id ..) (hasDerivWithinAt_const ..)
.comp_hasDerivWithinAt _ this ?_ refine DifferentiableWithinAt.hasFDerivWithinAt ?_
.symm .derivWithin ?_
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht => ⟨⟨ht.1, ha.1.2⟩, ⟨ht.2, ha.2.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.1, ha.2.1⟩
  -- Then our goal is to prove that the integral of `η`
  -- along the boundary of the unit square is zero.
  suffices (((∫ x in 0..1, g (x, 1)) - ∫ x in 0..1, g (x, 0)) +
      ∫ y in 0..1, f (1, y)) - ∫ y in 0..1, f (0, y) = 0 by
    have hfi (s : I) :
        ∫ t in 0..1, f (s, t) = ∫ᶜ x in ⟨φ.curry s, rfl, rfl⟩, ω x := by
      simp only [curveIntegral_def, curveIntegralFun_def]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro t ht
      simp [Path.extend, hf (s, t), Prod.le_def, s.2.1, s.2.2, ht.1, ht.2, Function.comp_def, hψ]
    have hf₀ : ∫ t in 0..1, f (0, t) = ∫ᶜ x in γ₁, ω x := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 0
    have hf₁ : ∫ t in 0..1, f (1, t) = curveIntegral ω γ₂ := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 1
    have hgi (t : I) : ∫ᶜ x in φ.evalAt t, ω x = -∫ s in 0..1, g (s, t) := by
      simp only [curveIntegral_def, curveIntegralFun_def, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro s hs
      simp only [hs, Path.extend_apply, φ.evalAt_apply]
      simp [hg (s, t), Prod.le_def, hs.1, hs.2, t.2.1, t.2.2, Function.comp_def, hψ]
    rw [← hf₀]; rw [← hf₁]; rw [hgi]; rw [hgi]
    linear_combination (norm := {dsimp; abel}) -this
  -- Write a formula for the derivative of `η`.
  set dη : Real × Real -> Real × Real ->L[Real] Real × Real ->L[Real] F := fun a =>
    .compL Real (Real × Real) E F (ω (ψ a)) ∘L d2ψ a + (dω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hdη : forall a in U \ s', HasFDerivAt η (dη a) a := by
    rintro a ⟨haU, has⟩
.clm_comp (hd2ψ a haU) refine HasFDerivWithinAt.comp_hasFDerivAt (t := t) a ?_ ?_ ?_
    · rcases a with ⟨x, y⟩
      lift x to I using Ioo_subset_Icc_self haU.1
      lift y to I using Ioo_subset_Icc_self haU.2
      apply hω
      · simpa using haU.1
      · simpa using haU.2
      · simpa [hmem_s'] using has
    · exact hdψ a haU
    · filter_upwards [hUopen.mem_nhds haU] using hψUt
  have hdη_symm : forall a in U \ s', forall u v, dη a u v = dη a v u := by
    rintro ⟨a, b⟩ ⟨hU, hs'⟩ u v
    lift a to I using Ioo_subset_Icc_self hU.1
    lift b to I using Ioo_subset_Icc_self hU.2
    have hdψ_mem (u) : dψ (a, b) u in tangentConeAt Real t (φ (a, b)) := by
      refine tangentConeAt_mono hψUt.image_subset ?_
      rw [← hψφ]
      refine (hdψ _ hU).hasFDerivWithinAt.mapsTo_tangent_cone ?_
      simp [tangentConeAt_of_mem_nhds (hUopen.mem_nhds hU)]
    have := hdω_symm a hU.1 b hU.2 (by simpa [hmem_s'] using hs') _ (hdψ_mem u) _ (hdψ_mem v)
    simp [dη, hψφ, this, hd2ψ_symm _ (hU_subset hU)]
  -- It gives formulas for the derivatives of `f` and `g`
  set f' : Real × Real -> Real × Real ->L[Real] F := fun a => ContinuousLinearMap.apply Real F (0, 1) ∘L dη a
  have hf' : forall a in U \ s', HasFDerivAt f (f' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply Real F (0, 1)).hasFDerivAt.comp a (hdη a ha)
  set g' : Real × Real -> Real × Real ->L[Real] F := fun a => -(ContinuousLinearMap.apply Real F (1, 0) ∘L dη a)
  have hg' : forall a in U \ s', HasFDerivAt g (g' a) a := by
    intro a ha
.neg exact (ContinuousLinearMap.apply Real F (1, 0)).hasFDerivAt.comp a (hdη a ha)
  -- Note that the divergence of `(f, g)` is a.e. zero.
  have hf'g' : (fun a => f' a (1, 0) + g' a (0, 1)) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    rw [Icc_prod_eq]; rw [Measure.volume_eq_prod]; rw [Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo), hs'c.ae_notMem _]
      with a hU hs
    simp [f', g', hdη_symm a ⟨hU, hs⟩ (0, 1)]
  suffices ∫ a : Real × Real in Icc 0 1, f' a (1, 0) + g' a (0, 1) = 0 by
    have hηc : ContinuousOn η (Icc 0 1) := by
      refine .clm_comp (hωc.comp hψ_cont.continuousOn ?_) ?_
      · rw [← hclosure]
        refine MapsTo.closure (fun a ha => ?_) hψ_cont
        lift a to I × I using ⟨Ioo_subset_Icc_self ha.1, Ioo_subset_Icc_self ha.2⟩
        simpa [ψ] using hφt a.1 ha.1 a.2 ha.2
      · exact hcontdiff.continuousOn_fderivWithin hunique (by decide)
    rwa [integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le] at this
    · exact zero_le_one
    · exact s'
    · exact hs'c
    · fun_prop
    · fun_prop
    · exact hf'
    · exact hg'
    · rw [integrableOn_congr_fun_ae hf'g']
      apply integrableOn_zero
  simp [integral_congr_ae hf'g']

/--
theorem `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable` / 定理 `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable`

English:
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
  proof: by
  simp only [← curveIntegral_restrictScalars (𝕜 := 𝕜) (𝕝 := Real)]
  set e := ContinuousLinearMap.restrictScalarsL 𝕜 E F Real Real
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real hs hφt
    (dω := fun x => e ∘L dω x)
    (fun a ha b hb hs => e.hasFDerivAt.comp

中文:
定理 curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
  证明: by
  simp only [← curveIntegral_restrictScalars (𝕜 := 𝕜) (𝕝 := Real)]
  set e := ContinuousLinearMap.restrictScalarsL 𝕜 E F Real Real
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real hs hφt
    (dω := fun x => e ∘L dω x)
    (fun a ha b hb hs => e.hasFDerivAt.comp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.restrictScalarsL, comp_continuousOn, comp_hasFDerivWithinAt, continuous, curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real, curveIntegral_restrictScalars, e.continuous.comp_continuousOn, e.hasFDerivAt.comp_hasFDerivWithinAt, hasFDerivAt, hcontdiff, restrictScalarsL
-/
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
    {ω : E -> E ->L[𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : forall a in Ioo 0 1, forall b in Ioo 0 1, φ (a, b) in t)
    (hω : forall a in Ioo (0 : I) 1, forall b in Ioo (0 : I) 1, (a, b) ∉ s ->
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b)))
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : forall a in Ioo (0 : I) 1, forall b in Ioo (0 : I) 1, (a, b) ∉ s ->
      forall u in tangentConeAt Real t (φ (a, b)), forall v in tangentConeAt Real t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn Real 2
      (fun xy : Real × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  simp only [← curveIntegral_restrictScalars (𝕜 := 𝕜) (𝕝 := Real)]
  set e := ContinuousLinearMap.restrictScalarsL 𝕜 E F Real Real
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real hs hφt
    (dω := fun x => e ∘L dω x)
    (fun a ha b hb hs => e.hasFDerivAt.comp_hasFDerivWithinAt _ (hω a ha b hb hs))
    (e.continuous.comp_continuousOn hωc) hdω_symm hcontdiff

/--
theorem `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt` / 定理 `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`

English:
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
  proof: φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable (s := ∅) (by simp)
    hφt (fun a ha b hb _ => hω _ <| hφt a ha b hb) hωc
    (fun a ha b hb _ => hdω_symm _ <| hφt a ha b hb) hcontdiff

中文:
定理 curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
  证明: φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable (s := ∅) (by simp)
    hφt (fun a ha b hb _ => hω _ <| hφt a ha b hb) hωc
    (fun a ha b hb _ => hdω_symm _ <| hφt a ha b hb) hcontdiff

Depends on / 依赖: curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable, hcontdiff
-/
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    {ω : E -> E ->L[𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : forall a in Ioo 0 1, forall b in Ioo 0 1, φ (a, b) in t)
    (hω : forall x in t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : forall x in t, forall u in tangentConeAt Real t x, forall v in tangentConeAt Real t x, dω x u v = dω x v u)
    (hcontdiff : ContDiffOn Real 2
      (fun xy : Real × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable (s := ∅) (by simp)
    hφt (fun a ha b hb _ => hω _ <| hφt a ha b hb) hωc
    (fun a ha b hb _ => hdω_symm _ <| hφt a ha b hb) hcontdiff

/--
theorem `curveIntegral_add_curveIntegral_eq_of_diffContOnCl` / 定理 `curveIntegral_add_curveIntegral_eq_of_diffContOnCl`

English:
theorem curveIntegral_add_curveIntegral_eq_of_diffContOnCl
  proof: φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    hφt (fun t ht => (hω.differentiableOn t ht).hasFDerivWithinAt) hω.continuousOn
    hdω_symm hcontdiff

中文:
定理 curveIntegral_add_curveIntegral_eq_of_diffContOnCl
  证明: φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    hφt (fun t ht => (hω.differentiableOn t ht).hasFDerivWithinAt) hω.continuousOn
    hdω_symm hcontdiff

Depends on / 依赖: continuousOn, curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt, differentiableOn, hasFDerivWithinAt, hcontdiff
-/
theorem curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    {ω : E -> E ->L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : forall a in Ioo 0 1, forall b in Ioo 0 1, φ (a, b) in t)
    (hω : DiffContOnCl Real ω t)
    (hdω_symm : forall x in t, forall u in tangentConeAt Real t x, forall v in tangentConeAt Real t x,
      fderivWithin Real ω t x u v = fderivWithin Real ω t x v u)
    (hcontdiff : ContDiffOn Real 2
      (fun xy : Real × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    hφt (fun t ht => (hω.differentiableOn t ht).hasFDerivWithinAt) hω.continuousOn
    hdω_symm hcontdiff

end ContinuousMap.Homotopy

namespace Convex

variable [NormedSpace Real E] [NormedSpace Real F]
  {a b c : E} {s : Set E} {ω : E -> E ->L[𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric` / 定理 `curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric`

English:
theorem curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
  statement: (hs : Convex Real s)
  proof: by
  set φ := ContinuousMap.Homotopy.affine (Path.segment a b : C(I, E)) (Path.segment a c)
  have hφs : range φ subseteq s := by
    rw [range_subset_iff]
    intro x
    simp [φ, ha, hb, hc, hs.lineMap_mem]
  have := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := range φ) (ω := ω)

中文:
定理 curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
  结论: (hs : Convex 实数 s)
  证明: by
  set φ := ContinuousMap.Homotopy.affine (Path.segment a b : C(I, E)) (Path.segment a c)
  have hφs : range φ subseteq s := by
    rw [range_subset_iff]
    intro x
    simp [φ, ha, hb, hc, hs.lineMap_mem]
  have := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := range φ) (ω := ω)

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy.affine, Homotopy, Path.cast_segment, Path.segment, affine, cast_segment, convert, curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt, curveIntegral_cast, hs.lineMap_mem, lineMap_apply_one, lineMap_apply_zero, lineMap_mem, range_subset_iff, segment, subseteq
-/
theorem curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric (hs : Convex Real s)
    (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : forall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real s a, dω a x y = dω a y x)
    (ha : a in s) (hb : b in s) (hc : c in s) :
    (∫ᶜ x in .segment a b, ω x) + ∫ᶜ x in .segment b c, ω x = ∫ᶜ x in .segment a c, ω x := by
  set φ := ContinuousMap.Homotopy.affine (Path.segment a b : C(I, E)) (Path.segment a c)
  have hφs : range φ subseteq s := by
    rw [range_subset_iff]
    intro x
    simp [φ, ha, hb, hc, hs.lineMap_mem]
  have := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := range φ) (ω := ω)
    (dω := dω) ?_ ?_ ?_ ?_ ?_
  · convert! this using 2
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_one a b) (lineMap_apply_one a c)]; rw [curveIntegral_cast]
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_zero a b) (lineMap_apply_zero a c)]
      simp
  · intros
    apply mem_range_self
  · exact fun x hx => (hω x (hφs hx)).mono hφs
  · rw [(isCompact_range <| map_continuous _).isClosed.closure_eq]
    exact fun x hx => (hω x <| hφs hx).continuousWithinAt.mono hφs
  · intro x hx u hu v hv
    apply hdω <;> grw [← hφs] <;> assumption
  · have : EqOn (fun x : Real × Real => IccExtend zero_le_one (φ.extend x.1) x.2)
        (fun x => lineMap (lineMap a b x.2) (lineMap a c x.2) x.1) (Icc 0 1) := by
      rw [Icc_prod_eq]
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to I using hx
      lift y to I using hy
      simp [φ]
    exact .congr (by fun_prop) this

variable [CompleteSpace F]

/--
theorem `hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric` / 定理 `hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric`

English:
theorem hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
  statement: (hs : Convex Real s)
  proof: by
  suffices HasFDerivWithinAt (∫ᶜ x in .segment a b, ω x + ∫ᶜ x in .segment b ·, ω x) (ω b) s b from
    this.congr' (fun _ h =>
      (hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
refine .const_add _ ?_
  refine HasFDerivWithinAt.curveIntegral_segment_so

中文:
定理 hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
  结论: (hs : Convex 实数 s)
  证明: by
  suffices HasFDerivWithinAt (∫ᶜ x in .segment a b, ω x + ∫ᶜ x in .segment b ·, ω x) (ω b) s b from
    this.congr' (fun _ h =>
      (hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
refine .const_add _ ?_
  refine HasFDerivWithinAt.curveIntegral_segment_so

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.curveIntegral_segment_source, const_add, continuousWithinAt, curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric, curveIntegral_segment_source, hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric, segment, this.congr
-/
theorem hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric (hs : Convex Real s)
    (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : forall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real s a, dω a x y = dω a y x)
    (ha : a in s) (hb : b in s) :
    HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω b) s b := by
  suffices HasFDerivWithinAt (∫ᶜ x in .segment a b, ω x + ∫ᶜ x in .segment b ·, ω x) (ω b) s b from
    this.congr' (fun _ h =>
      (hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
refine .const_add _ ?_
  refine HasFDerivWithinAt.curveIntegral_segment_source hs ?_ hb
  exact fun x hx => (hω x hx).continuousWithinAt

/--
theorem `exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric` / 定理 `exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric`

English:
theorem exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (curveIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

中文:
定理 exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (curveIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

Depends on / 依赖: curveIntegral, eq_empty_or_nonempty, hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric, hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric, s.eq_empty_or_nonempty, segment
-/
theorem exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (hs : Convex Real s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : forall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real s a, dω a x y = dω a y x) :
    exists f, forall a in s, HasFDerivWithinAt f (ω a) s a := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (curveIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

/--
theorem `exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric` / 定理 `exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric`

English:
theorem exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric
  proof: hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha => (hω a ha).hasFDerivWithinAt) hdω

中文:
定理 exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric
  证明: hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha => (hω a ha).hasFDerivWithinAt) hdω

Depends on / 依赖: exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric, hasFDerivWithinAt, hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
-/
theorem exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric
    (hs : Convex Real s) (hω : DifferentiableOn Real ω s)
    (hdω : forall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real s a,
      fderivWithin Real ω s a x y = fderivWithin Real ω s a y x) :
    exists f, forall a in s, HasFDerivWithinAt f (ω a) s a :=
  hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha => (hω a ha).hasFDerivWithinAt) hdω

/--
theorem `exists_forall_hasFDerivAt_of_fderiv_symmetric` / 定理 `exists_forall_hasFDerivAt_of_fderiv_symmetric`

English:
theorem exists_forall_hasFDerivAt_of_fderiv_symmetric
  statement: (hs : Convex Real s) (hso : IsOpen s)
  proof: by
  obtain ⟨f, hf⟩ : exists f, forall a in s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ => ?_
    rw [fderivWithin_eq_fderiv]; rw [hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)

中文:
定理 exists_forall_hasFDerivAt_of_fderiv_symmetric
  结论: (hs : Convex 实数 s) (hso : IsOpen s)
  证明: by
  obtain ⟨f, hf⟩ : exists f, forall a in s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ => ?_
    rw [fderivWithin_eq_fderiv]; rw [hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)

Depends on / 依赖: HasFDerivWithinAt, differentiableAt, exacts, exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric, fderivWithin_eq_fderiv, hasFDerivAt, hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric, hso.mem_nhds, hso.uniqueDiffOn, mem_nhds, uniqueDiffOn
-/
theorem exists_forall_hasFDerivAt_of_fderiv_symmetric (hs : Convex Real s) (hso : IsOpen s)
    (hω : DifferentiableOn Real ω s) (hdω : forall a in s, forall x y, fderiv Real ω a x y = fderiv Real ω a y x) :
    exists f, forall a in s, HasFDerivAt f (ω a) a := by
  obtain ⟨f, hf⟩ : exists f, forall a in s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ => ?_
    rw [fderivWithin_eq_fderiv]; rw [hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)]
  exact ⟨f, fun a ha => (hf a ha).hasFDerivAt (hso.mem_nhds ha)⟩

end Convex

namespace Convex

variable [CompleteSpace E] {f : 𝕜 -> E} {s : Set 𝕜}

/--
theorem `exists_forall_hasDerivWithinAt` / 定理 `exists_forall_hasDerivWithinAt`

English:
theorem exists_forall_hasDerivWithinAt
  given: (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s)
  proof: by
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  apply hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  · intro a ha
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1).hasFDerivAt
.restrictScalars Real .comp_hasDerivWithinAt a (hf a ha).hasDerivWithinAt
  · rintro a ha

中文:
定理 exists_forall_hasDerivWithinAt
  条件: (hs : Convex 实数 s) (hf : DifferentiableOn 𝕜 f s)
  证明: by
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  apply hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  · intro a ha
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1).hasFDerivAt
.restrictScalars Real .comp_hasDerivWithinAt a (hf a ha).hasDerivWithinAt
  · rintro a ha

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRightL, NormedSpace, comp_hasDerivWithinAt, exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric, hasDerivWithinAt, hasFDerivAt, hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric, restrictScalars, smulRightL, smul_comm
-/
theorem exists_forall_hasDerivWithinAt (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s) :
    exists g : 𝕜 -> E, forall a in s, HasDerivWithinAt g (f a) s a := by
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  apply hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  · intro a ha
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1).hasFDerivAt
.restrictScalars Real .comp_hasDerivWithinAt a (hf a ha).hasDerivWithinAt
  · rintro a ha x - y -
    simpa using smul_comm ..

end Convex
