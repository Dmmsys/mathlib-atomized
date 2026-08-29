/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Derivative as the limit of the slope

In this file we relate the derivative of a function with its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`.
Since we are talking about functions taking values in a normed space instead of the base field, we
use `slope f x y = (y - x)⁻¹ • (f y - f x)` instead of division.

We also prove some estimates on the upper/lower limits of the slope in terms of the derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, slope
-/

public section

universe u v

open scoped Topology

open Filter TopologicalSpace Set

section NormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 -> F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}

/--
theorem `hasDerivAtFilter_iff_tendsto_slope` / 定理 `hasDerivAtFilter_iff_tendsto_slope`

English:
theorem hasDerivAtFilter_iff_tendsto_slope
  given: {x : 𝕜} {L : Filter 𝕜}
  proof: calc HasDerivAtFilter f f' (L ×ˢ pure x)
    _ ↔ Tendsto (fun y => slope f x y - (y - x)⁻¹ • (y - x) • f') L (𝓝 0) := by
      simp only [hasDerivAtFilter_iff_tendsto, prod_pure, tendsto_map'_iff, Function.comp_def,
        ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero, slope_def_mod

中文:
定理 hasDerivAtFilter_iff_tendsto_slope
  条件: {x : 𝕜} {L : Filter 𝕜}
  证明: calc HasDerivAtFilter f f' (L ×ˢ pure x)
    _ ↔ Tendsto (fun y => slope f x y - (y - x)⁻¹ • (y - x) • f') L (𝓝 0) := by
      simp only [hasDerivAtFilter_iff_tendsto, prod_pure, tendsto_map'_iff, Function.comp_def,
        ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero, slope_def_mod

Depends on / 依赖: Function, Function.comp_def, HasDerivAtFilter, Tendsto, _iff, comp_def, hasDerivAtFilter_iff_tendsto, norm_inv, norm_smul, prod_pure, slope_def_module, smul_sub, tendsto_inf_principal_nhds_iff_of_forall_eq, tendsto_map, tendsto_zero_iff_norm_tendsto_zero
-/
theorem hasDerivAtFilter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' (L ×ˢ pure x) ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') :=
  calc HasDerivAtFilter f f' (L ×ˢ pure x)
    _ ↔ Tendsto (fun y => slope f x y - (y - x)⁻¹ • (y - x) • f') L (𝓝 0) := by
      simp only [hasDerivAtFilter_iff_tendsto, prod_pure, tendsto_map'_iff, Function.comp_def,
        ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero, slope_def_module, smul_sub]
    _ ↔ Tendsto (fun y => slope f x y - (y - x)⁻¹ • (y - x) • f') (L ⊓ 𝓟 {x}ᶜ) (𝓝 0) :=
.symm tendsto_inf_principal_nhds_iff_of_forall_eq by simp
_ ↔ Tendsto (fun y => slope f x y - f') (L ⊓ 𝓟 {x}ᶜ) (𝓝 0) := tendsto_congr' by
      refine (EqOn.eventuallyEq fun y hy => ?_).filter_mono inf_le_right
      rw [inv_smul_smul₀ (sub_ne_zero.2 hy) f']
    _ ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') := by
      rw [← nhds_translation_sub f']; rw [tendsto_comap_iff]; rfl

/--
theorem `hasDerivWithinAt_iff_tendsto_slope` / 定理 `hasDerivWithinAt_iff_tendsto_slope`

English:
theorem hasDerivWithinAt_iff_tendsto_slope
  proof: by
  simp only [HasDerivWithinAt, nhdsWithin, sdiff_eq, ← inf_assoc, inf_principal.symm]
  exact hasDerivAtFilter_iff_tendsto_slope

中文:
定理 hasDerivWithinAt_iff_tendsto_slope
  证明: by
  simp only [HasDerivWithinAt, nhdsWithin, sdiff_eq, ← inf_assoc, inf_principal.symm]
  exact hasDerivAtFilter_iff_tendsto_slope

Depends on / 依赖: HasDerivWithinAt, hasDerivAtFilter_iff_tendsto_slope, inf_assoc, inf_principal, inf_principal.symm, nhdsWithin, sdiff_eq
-/
theorem hasDerivWithinAt_iff_tendsto_slope :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') := by
  simp only [HasDerivWithinAt, nhdsWithin, sdiff_eq, ← inf_assoc, inf_principal.symm]
  exact hasDerivAtFilter_iff_tendsto_slope

/--
theorem `hasDerivWithinAt_iff_tendsto_slope'` / 定理 `hasDerivWithinAt_iff_tendsto_slope'`

English:
theorem hasDerivWithinAt_iff_tendsto_slope'
  given: (hs : x ∉ s)
  proof: by
  rw [hasDerivWithinAt_iff_tendsto_slope]; rw [sdiff_singleton_eq_self hs]

中文:
定理 hasDerivWithinAt_iff_tendsto_slope'
  条件: (hs : x ∉ s)
  证明: by
  rw [hasDerivWithinAt_iff_tendsto_slope]; rw [sdiff_singleton_eq_self hs]

Depends on / 依赖: hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self
-/
theorem hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f') := by
  rw [hasDerivWithinAt_iff_tendsto_slope]; rw [sdiff_singleton_eq_self hs]

/--
theorem `hasDerivAt_iff_tendsto_slope` / 定理 `hasDerivAt_iff_tendsto_slope`

English:
theorem hasDerivAt_iff_tendsto_slope
  statement: HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f')
  proof: hasDerivAtFilter_iff_tendsto_slope

alias ⟨HasDerivAt.tendsto_slope, _⟩ := hasDerivAt_iff_tendsto_slope

中文:
定理 hasDerivAt_iff_tendsto_slope
  结论: HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f')
  证明: hasDerivAtFilter_iff_tendsto_slope

alias ⟨HasDerivAt.tendsto_slope, _⟩ := hasDerivAt_iff_tendsto_slope

Depends on / 依赖: hasDerivAtFilter_iff_tendsto_slope
-/
theorem hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f') :=
  hasDerivAtFilter_iff_tendsto_slope

alias ⟨HasDerivAt.tendsto_slope, _⟩ := hasDerivAt_iff_tendsto_slope

/--
theorem `hasDerivAt_iff_tendsto_slope_left_right` / 定理 `hasDerivAt_iff_tendsto_slope_left_right`

English:
theorem hasDerivAt_iff_tendsto_slope_left_right
  given: [LinearOrder 𝕜]
  statement: HasDerivAt f f' x ↔
  proof: by
  simp [hasDerivAt_iff_tendsto_slope, ← Iio_union_Ioi, nhdsWithin_union]

中文:
定理 hasDerivAt_iff_tendsto_slope_left_right
  条件: [LinearOrder 𝕜]
  结论: HasDerivAt f f' x ↔
  证明: by
  simp [hasDerivAt_iff_tendsto_slope, ← Iio_union_Ioi, nhdsWithin_union]

Depends on / 依赖: Iio_union_Ioi, hasDerivAt_iff_tendsto_slope, nhdsWithin_union
-/
theorem hasDerivAt_iff_tendsto_slope_left_right [LinearOrder 𝕜] : HasDerivAt f f' x ↔
    Tendsto (slope f x) (𝓝[<] x) (𝓝 f') ∧ Tendsto (slope f x) (𝓝[>] x) (𝓝 f') := by
  simp [hasDerivAt_iff_tendsto_slope, ← Iio_union_Ioi, nhdsWithin_union]

/--
theorem `hasDerivAt_iff_tendsto_slope_zero` / 定理 `hasDerivAt_iff_tendsto_slope_zero`

English:
theorem hasDerivAt_iff_tendsto_slope_zero
  proof: by
  have : 𝓝[!=] x = Filter.map (fun t => x + t) (𝓝[!=] 0) := by simp
  simp [hasDerivAt_iff_tendsto_slope, this, -map_add_left_nhdsNE, slope, Function.comp_def]

alias ⟨HasDerivAt.tendsto_slope_zero, _⟩ := hasDerivAt_iff_tendsto_slope_zero

中文:
定理 hasDerivAt_iff_tendsto_slope_zero
  证明: by
  have : 𝓝[!=] x = Filter.map (fun t => x + t) (𝓝[!=] 0) := by simp
  simp [hasDerivAt_iff_tendsto_slope, this, -map_add_left_nhdsNE, slope, Function.comp_def]

alias ⟨HasDerivAt.tendsto_slope_zero, _⟩ := hasDerivAt_iff_tendsto_slope_zero

Depends on / 依赖: Filter, Filter.map, Function, Function.comp_def, comp_def, hasDerivAt_iff_tendsto_slope, map_add_left_nhdsNE
-/
theorem hasDerivAt_iff_tendsto_slope_zero :
    HasDerivAt f f' x ↔ Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[!=] 0) (𝓝 f') := by
  have : 𝓝[!=] x = Filter.map (fun t => x + t) (𝓝[!=] 0) := by simp
  simp [hasDerivAt_iff_tendsto_slope, this, -map_add_left_nhdsNE, slope, Function.comp_def]

alias ⟨HasDerivAt.tendsto_slope_zero, _⟩ := hasDerivAt_iff_tendsto_slope_zero

/--
theorem `HasDerivAt.tendsto_slope_zero_right` / 定理 `HasDerivAt.tendsto_slope_zero_right`

English:
theorem HasDerivAt.tendsto_slope_zero_right
  given: [Preorder 𝕜] (h : HasDerivAt f f' x)
  proof: h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

中文:
定理 HasDerivAt.tendsto_slope_zero_right
  条件: [Preorder 𝕜] (h : HasDerivAt f f' x)
  证明: h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

Depends on / 依赖: h.tendsto_slope_zero.mono_left, mono_left, nhdsGT_le_nhdsNE, tendsto_slope_zero
-/
theorem HasDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[>] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

/--
theorem `HasDerivAt.tendsto_slope_zero_left` / 定理 `HasDerivAt.tendsto_slope_zero_left`

English:
theorem HasDerivAt.tendsto_slope_zero_left
  given: [Preorder 𝕜] (h : HasDerivAt f f' x)
  proof: h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

中文:
定理 HasDerivAt.tendsto_slope_zero_left
  条件: [Preorder 𝕜] (h : HasDerivAt f f' x)
  证明: h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

Depends on / 依赖: h.tendsto_slope_zero.mono_left, mono_left, nhdsLT_le_nhdsNE, tendsto_slope_zero
-/
theorem HasDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[<] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

/--
theorem `range_derivWithin_subset_closure_span_image` / 定理 `range_derivWithin_subset_closure_span_image`

English:
theorem range_derivWithin_subset_closure_span_image
  proof: by
  rintro - ⟨x, rfl⟩
  by_cases H : UniqueDiffWithinAt 𝕜 s x; swap
  · simpa [derivWithin_zero_of_not_uniqueDiffWithinAt H] using subset_closure (zero_mem _)
  by_cases H' : DifferentiableWithinAt 𝕜 f s x; swap
  · rw [derivWithin_zero_of_not_differentiableWithinAt H']
    exact subset_closure (ze

中文:
定理 range_derivWithin_subset_closure_span_image
  证明: by
  rintro - ⟨x, rfl⟩
  by_cases H : UniqueDiffWithinAt 𝕜 s x; swap
  · simpa [derivWithin_zero_of_not_uniqueDiffWithinAt H] using subset_closure (zero_mem _)
  by_cases H' : DifferentiableWithinAt 𝕜 f s x; swap
  · rw [derivWithin_zero_of_not_differentiableWithinAt H']
    exact subset_closure (ze

Depends on / 依赖: DifferentiableWithinAt, H.mono_closure, Tendsto, UniqueDiffWithinAt, accPt_principal_iff_nhdsWithin, derivWithin_zero_of_not_differentiableWithinAt, derivWithin_zero_of_not_uniqueDiffWithinAt, mono_closure, subset_closure, uniqueDiffWithinAt_iff_accPt, zero_mem
-/
theorem range_derivWithin_subset_closure_span_image
    (f : 𝕜 -> F) {s t : Set 𝕜} (h : s subseteq closure (s inter t)) :
    range (derivWithin f s) subseteq closure (Submodule.span 𝕜 (f '' t)) := by
  rintro - ⟨x, rfl⟩
  by_cases H : UniqueDiffWithinAt 𝕜 s x; swap
  · simpa [derivWithin_zero_of_not_uniqueDiffWithinAt H] using subset_closure (zero_mem _)
  by_cases H' : DifferentiableWithinAt 𝕜 f s x; swap
  · rw [derivWithin_zero_of_not_differentiableWithinAt H']
    exact subset_closure (zero_mem _)
  have I : (𝓝[(s inter t) \ {x}] x).NeBot := by
    rw [← accPt_principal_iff_nhdsWithin]; rw [← uniqueDiffWithinAt_iff_accPt]
    exact H.mono_closure h
  have : Tendsto (slope f x) (𝓝[(s inter t) \ {x}] x) (𝓝 (derivWithin f s x)) := by
    apply Tendsto.mono_left (hasDerivWithinAt_iff_tendsto_slope.1 H'.hasDerivWithinAt)
    rw [inter_comm]; rw [inter_sdiff_assoc]
    exact nhdsWithin_mono _ inter_subset_right
  rw [← closure_closure]; rw [← Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto this
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope, vsub_eq_sub, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact mem_image_of_mem _ hy.1.2
  · apply Submodule.closure_subset_topologicalClosure_span
    suffices A : f x in closure (f '' (s inter t)) from
      closure_mono (image_mono inter_subset_right) A
    apply ContinuousWithinAt.mem_closure_image
    · apply H'.continuousWithinAt.mono inter_subset_left
    rw [mem_closure_iff_nhdsWithin_neBot]
    exact I.mono (nhdsWithin_mono _ sdiff_subset)

/--
theorem `range_deriv_subset_closure_span_image` / 定理 `range_deriv_subset_closure_span_image`

English:
theorem range_deriv_subset_closure_span_image
  proof: by
  rw [← derivWithin_univ]
  apply range_derivWithin_subset_closure_span_image
  simp [dense_iff_closure_eq.1 h]

中文:
定理 range_deriv_subset_closure_span_image
  证明: by
  rw [← derivWithin_univ]
  apply range_derivWithin_subset_closure_span_image
  simp [dense_iff_closure_eq.1 h]

Depends on / 依赖: dense_iff_closure_eq, derivWithin_univ, range_derivWithin_subset_closure_span_image
-/
theorem range_deriv_subset_closure_span_image
    (f : 𝕜 -> F) {t : Set 𝕜} (h : Dense t) :
    range (deriv f) subseteq closure (Submodule.span 𝕜 (f '' t)) := by
  rw [← derivWithin_univ]
  apply range_derivWithin_subset_closure_span_image
  simp [dense_iff_closure_eq.1 h]

/--
theorem `isSeparable_range_derivWithin` / 定理 `isSeparable_range_derivWithin`

English:
theorem isSeparable_range_derivWithin
  given: [SeparableSpace 𝕜] (f : 𝕜 -> F) (s : Set 𝕜)
  proof: by
  obtain ⟨t, ts, t_count, ht⟩ : exists t, t subseteq s ∧ Set.Countable t ∧ s subseteq closure t :=
    (IsSeparable.of_separableSpace s).exists_countable_dense_subset
  have : s subseteq closure (s inter t) := by rwa [inter_eq_self_of_subset_right ts]
  apply IsSeparable.mono _ (range_derivWithin

中文:
定理 isSeparable_range_derivWithin
  条件: [SeparableSpace 𝕜] (f : 𝕜 -> F) (s : Set 𝕜)
  证明: by
  obtain ⟨t, ts, t_count, ht⟩ : exists t, t subseteq s ∧ Set.Countable t ∧ s subseteq closure t :=
    (IsSeparable.of_separableSpace s).exists_countable_dense_subset
  have : s subseteq closure (s inter t) := by rwa [inter_eq_self_of_subset_right ts]
  apply IsSeparable.mono _ (range_derivWithin

Depends on / 依赖: Countable, Countable.image, IsSeparable, IsSeparable.mono, IsSeparable.of_separableSpace, Set.Countable, closure, exists_countable_dense_subset, inter_eq_self_of_subset_right, isSeparable, isSeparable.span.closure, of_separableSpace, range_derivWithin_subset_closure_span_image, subseteq, t_count
-/
theorem isSeparable_range_derivWithin [SeparableSpace 𝕜] (f : 𝕜 -> F) (s : Set 𝕜) :
    IsSeparable (range (derivWithin f s)) := by
  obtain ⟨t, ts, t_count, ht⟩ : exists t, t subseteq s ∧ Set.Countable t ∧ s subseteq closure t :=
    (IsSeparable.of_separableSpace s).exists_countable_dense_subset
  have : s subseteq closure (s inter t) := by rwa [inter_eq_self_of_subset_right ts]
  apply IsSeparable.mono _ (range_derivWithin_subset_closure_span_image f this)
  exact (Countable.image t_count f).isSeparable.span.closure

/--
theorem `isSeparable_range_deriv` / 定理 `isSeparable_range_deriv`

English:
theorem isSeparable_range_deriv
  given: [SeparableSpace 𝕜] (f : 𝕜 -> F)
  proof: by
  rw [← derivWithin_univ]
  exact isSeparable_range_derivWithin _ _

中文:
定理 isSeparable_range_deriv
  条件: [SeparableSpace 𝕜] (f : 𝕜 -> F)
  证明: by
  rw [← derivWithin_univ]
  exact isSeparable_range_derivWithin _ _

Depends on / 依赖: derivWithin_univ, isSeparable_range_derivWithin
-/
theorem isSeparable_range_deriv [SeparableSpace 𝕜] (f : 𝕜 -> F) :
    IsSeparable (range (deriv f)) := by
  rw [← derivWithin_univ]
  exact isSeparable_range_derivWithin _ _

/--
lemma `HasDerivAt.continuousAt_div` / 引理 `HasDerivAt.continuousAt_div`

English:
lemma HasDerivAt.continuousAt_div
  given: [DecidableEq 𝕜] {f : 𝕜 -> 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c)
  proof: by
  rw [← slope_fun_def_field]
exact continuousAt_update_same.mpr hasDerivAt_iff_tendsto_slope.mp hf

中文:
引理 HasDerivAt.continuousAt_div
  条件: [DecidableEq 𝕜] {f : 𝕜 -> 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c)
  证明: by
  rw [← slope_fun_def_field]
exact continuousAt_update_same.mpr hasDerivAt_iff_tendsto_slope.mp hf

Depends on / 依赖: continuousAt_update_same, continuousAt_update_same.mpr, hasDerivAt_iff_tendsto_slope, hasDerivAt_iff_tendsto_slope.mp, slope_fun_def_field
-/
lemma HasDerivAt.continuousAt_div [DecidableEq 𝕜] {f : 𝕜 -> 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c) :
    ContinuousAt (Function.update (fun x => (f x - f c) / (x - c)) c a) c := by
  rw [← slope_fun_def_field]
exact continuousAt_update_same.mpr hasDerivAt_iff_tendsto_slope.mp hf

section Order

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {g : 𝕜 -> 𝕜} {g' : 𝕜}

/--
lemma `HasDerivWithinAt.nonneg_of_monotoneOn` / 引理 `HasDerivWithinAt.nonneg_of_monotoneOn`

English:
lemma HasDerivWithinAt.nonneg_of_monotoneOn
  statement: (hx : AccPt x (𝓟 s))
  proof: by
  have : (𝓝[s \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp hx
  have h'g : MonotoneOn g (insert x s) :=
    hg.insert_of_continuousWithinAt hx.clusterPt hd.continuousWithinAt
  have : Tendsto (slope g x) (𝓝[s \ {x}] x) (𝓝 g') := hasDerivWithinAt_iff_tendsto_slope.mp hd
  apply ge_of_tends

中文:
引理 HasDerivWithinAt.nonneg_of_monotoneOn
  结论: (hx : AccPt x (𝓟 s))
  证明: by
  have : (𝓝[s \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp hx
  have h'g : MonotoneOn g (insert x s) :=
    hg.insert_of_continuousWithinAt hx.clusterPt hd.continuousWithinAt
  have : Tendsto (slope g x) (𝓝[s \ {x}] x) (𝓝 g') := hasDerivWithinAt_iff_tendsto_slope.mp hd
  apply ge_of_tends

Depends on / 依赖: MonotoneOn, Set.mem_sdiff, Tendsto, accPt_principal_iff_nhdsWithin, accPt_principal_iff_nhdsWithin.mp, clusterPt, continuousWithinAt, filter_upwards, g.slope_nonneg, ge_of_tendsto, hasDerivWithinAt_iff_tendsto_slope, hasDerivWithinAt_iff_tendsto_slope.mp, hd.continuousWithinAt, hg.insert_of_continuousWithinAt, hx.clusterPt, insert, insert_of_continuousWithinAt, mem_sdiff, mem_singleton_iff, self_mem_nhdsWithin
-/
lemma HasDerivWithinAt.nonneg_of_monotoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s) : 0 <= g' := by
  have : (𝓝[s \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp hx
  have h'g : MonotoneOn g (insert x s) :=
    hg.insert_of_continuousWithinAt hx.clusterPt hd.continuousWithinAt
  have : Tendsto (slope g x) (𝓝[s \ {x}] x) (𝓝 g') := hasDerivWithinAt_iff_tendsto_slope.mp hd
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Set.mem_sdiff, mem_singleton_iff] at hy
  exact h'g.slope_nonneg (by simp) (by simp [hy])

/--
lemma `MonotoneOn.derivWithin_nonneg` / 引理 `MonotoneOn.derivWithin_nonneg`

English:
lemma MonotoneOn.derivWithin_nonneg
  given: (hg : MonotoneOn g s)
  proof: by
  by_cases hd : DifferentiableWithinAt 𝕜 g s x; swap
  · simp [derivWithin_zero_of_not_differentiableWithinAt hd]
  by_cases hx : AccPt x (𝓟 s); swap
  · simp [derivWithin_zero_of_not_accPt hx]
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hx hg

中文:
引理 MonotoneOn.derivWithin_nonneg
  条件: (hg : MonotoneOn g s)
  证明: by
  by_cases hd : DifferentiableWithinAt 𝕜 g s x; swap
  · simp [derivWithin_zero_of_not_differentiableWithinAt hd]
  by_cases hx : AccPt x (𝓟 s); swap
  · simp [derivWithin_zero_of_not_accPt hx]
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hx hg

Depends on / 依赖: DifferentiableWithinAt, derivWithin_zero_of_not_accPt, derivWithin_zero_of_not_differentiableWithinAt, hasDerivWithinAt, hd.hasDerivWithinAt.nonneg_of_monotoneOn, nonneg_of_monotoneOn
-/
lemma MonotoneOn.derivWithin_nonneg (hg : MonotoneOn g s) :
    0 <= derivWithin g s x := by
  by_cases hd : DifferentiableWithinAt 𝕜 g s x; swap
  · simp [derivWithin_zero_of_not_differentiableWithinAt hd]
  by_cases hx : AccPt x (𝓟 s); swap
  · simp [derivWithin_zero_of_not_accPt hx]
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hx hg

/--
lemma `HasDerivAt.nonneg_of_monotone` / 引理 `HasDerivAt.nonneg_of_monotone`

English:
lemma HasDerivAt.nonneg_of_monotone
  given: (hd : HasDerivAt g g' x) (hg : Monotone g)
  statement: 0 <= g'
  proof: by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonneg_of_monotoneOn _ (hg.monotoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

中文:
引理 HasDerivAt.nonneg_of_monotone
  条件: (hd : HasDerivAt g g' x) (hg : Monotone g)
  结论: 0 <= g'
  证明: by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonneg_of_monotoneOn _ (hg.monotoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

Depends on / 依赖: PerfectSpace, PerfectSpace.univ_preperfect, hasDerivWithinAt_univ, hd.nonneg_of_monotoneOn, hg.monotoneOn, mem_univ, monotoneOn, nonneg_of_monotoneOn, univ_preperfect
-/
lemma HasDerivAt.nonneg_of_monotone (hd : HasDerivAt g g' x) (hg : Monotone g) : 0 <= g' := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonneg_of_monotoneOn _ (hg.monotoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/--
lemma `Monotone.deriv_nonneg` / 引理 `Monotone.deriv_nonneg`

English:
lemma Monotone.deriv_nonneg
  given: (hg : Monotone g)
  statement: 0 <= deriv g x
  proof: by
  rw [← derivWithin_univ]
  exact (hg.monotoneOn univ).derivWithin_nonneg

中文:
引理 Monotone.deriv_nonneg
  条件: (hg : Monotone g)
  结论: 0 <= deriv g x
  证明: by
  rw [← derivWithin_univ]
  exact (hg.monotoneOn univ).derivWithin_nonneg

Depends on / 依赖: derivWithin_nonneg, derivWithin_univ, hg.monotoneOn, monotoneOn
-/
lemma Monotone.deriv_nonneg (hg : Monotone g) : 0 <= deriv g x := by
  rw [← derivWithin_univ]
  exact (hg.monotoneOn univ).derivWithin_nonneg

/--
lemma `HasDerivWithinAt.nonpos_of_antitoneOn` / 引理 `HasDerivWithinAt.nonpos_of_antitoneOn`

English:
lemma HasDerivWithinAt.nonpos_of_antitoneOn
  statement: (hx : AccPt x (𝓟 s))
  proof: by
  have : MonotoneOn (-g) s := fun x hx y hy hxy => by simpa using hg hx hy hxy
  simpa using hd.neg.nonneg_of_monotoneOn hx this

中文:
引理 HasDerivWithinAt.nonpos_of_antitoneOn
  结论: (hx : AccPt x (𝓟 s))
  证明: by
  have : MonotoneOn (-g) s := fun x hx y hy hxy => by simpa using hg hx hy hxy
  simpa using hd.neg.nonneg_of_monotoneOn hx this

Depends on / 依赖: MonotoneOn, hd.neg.nonneg_of_monotoneOn, nonneg_of_monotoneOn
-/
lemma HasDerivWithinAt.nonpos_of_antitoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : AntitoneOn g s) : g' <= 0 := by
  have : MonotoneOn (-g) s := fun x hx y hy hxy => by simpa using hg hx hy hxy
  simpa using hd.neg.nonneg_of_monotoneOn hx this

/--
lemma `AntitoneOn.derivWithin_nonpos` / 引理 `AntitoneOn.derivWithin_nonpos`

English:
lemma AntitoneOn.derivWithin_nonpos
  given: (hg : AntitoneOn g s)
  proof: by
  simpa [derivWithin.fun_neg] using hg.neg.derivWithin_nonneg

中文:
引理 AntitoneOn.derivWithin_nonpos
  条件: (hg : AntitoneOn g s)
  证明: by
  simpa [derivWithin.fun_neg] using hg.neg.derivWithin_nonneg

Depends on / 依赖: derivWithin, derivWithin.fun_neg, derivWithin_nonneg, fun_neg, hg.neg.derivWithin_nonneg
-/
lemma AntitoneOn.derivWithin_nonpos (hg : AntitoneOn g s) :
    derivWithin g s x <= 0 := by
  simpa [derivWithin.fun_neg] using hg.neg.derivWithin_nonneg

/--
lemma `HasDerivAt.nonpos_of_antitone` / 引理 `HasDerivAt.nonpos_of_antitone`

English:
lemma HasDerivAt.nonpos_of_antitone
  given: (hd : HasDerivAt g g' x) (hg : Antitone g)
  statement: g' <= 0
  proof: by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonpos_of_antitoneOn _ (hg.antitoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

中文:
引理 HasDerivAt.nonpos_of_antitone
  条件: (hd : HasDerivAt g g' x) (hg : Antitone g)
  结论: g' <= 0
  证明: by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonpos_of_antitoneOn _ (hg.antitoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

Depends on / 依赖: PerfectSpace, PerfectSpace.univ_preperfect, antitoneOn, hasDerivWithinAt_univ, hd.nonpos_of_antitoneOn, hg.antitoneOn, mem_univ, nonpos_of_antitoneOn, univ_preperfect
-/
lemma HasDerivAt.nonpos_of_antitone (hd : HasDerivAt g g' x) (hg : Antitone g) : g' <= 0 := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonpos_of_antitoneOn _ (hg.antitoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/--
lemma `Antitone.deriv_nonpos` / 引理 `Antitone.deriv_nonpos`

English:
lemma Antitone.deriv_nonpos
  given: (hg : Antitone g)
  statement: deriv g x <= 0
  proof: by
  rw [← derivWithin_univ]
  exact (hg.antitoneOn univ).derivWithin_nonpos

中文:
引理 Antitone.deriv_nonpos
  条件: (hg : Antitone g)
  结论: deriv g x <= 0
  证明: by
  rw [← derivWithin_univ]
  exact (hg.antitoneOn univ).derivWithin_nonpos

Depends on / 依赖: antitoneOn, derivWithin_nonpos, derivWithin_univ, hg.antitoneOn
-/
lemma Antitone.deriv_nonpos (hg : Antitone g) : deriv g x <= 0 := by
  rw [← derivWithin_univ]
  exact (hg.antitoneOn univ).derivWithin_nonpos

end Order

end NormedField

/-! ### Upper estimates on liminf and limsup -/

section Real

variable {f : Real -> Real} {f' : Real} {s : Set Real} {x : Real} {r : Real}

/--
theorem `HasDerivWithinAt.limsup_slope_le` / 定理 `HasDerivWithinAt.limsup_slope_le`

English:
theorem HasDerivWithinAt.limsup_slope_le
  given: (hf : HasDerivWithinAt f f' s x) (hr : f' < r)
  proof: hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)

中文:
定理 HasDerivWithinAt.limsup_slope_le
  条件: (hf : HasDerivWithinAt f f' s x) (hr : f' < r)
  证明: hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, hasDerivWithinAt_iff_tendsto_slope, isOpen_Iio, mem_nhds
-/
theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    forallᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
  hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)

/--
theorem `HasDerivWithinAt.limsup_slope_le'` / 定理 `HasDerivWithinAt.limsup_slope_le'`

English:
theorem HasDerivWithinAt.limsup_slope_le'
  statement: (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
  proof: (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)

中文:
定理 HasDerivWithinAt.limsup_slope_le'
  结论: (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
  证明: (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, hasDerivWithinAt_iff_tendsto_slope, isOpen_Iio, mem_nhds
-/
theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
    (hr : f' < r) : forallᶠ z in 𝓝[s] x, slope f x z < r :=
  (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)

/--
theorem `HasDerivWithinAt.liminf_right_slope_le` / 定理 `HasDerivWithinAt.liminf_right_slope_le`

English:
theorem HasDerivWithinAt.liminf_right_slope_le
  statement: (hf : HasDerivWithinAt f f' (Ici x) x)
  proof: (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

中文:
定理 HasDerivWithinAt.liminf_right_slope_le
  结论: (hf : HasDerivWithinAt f f' (Ici x) x)
  证明: (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

Depends on / 依赖: Ioi_of_Ici, frequently, hf.Ioi_of_Ici.limsup_slope_le, limsup_slope_le, lt_irrefl
-/
theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : f' < r) : existsᶠ z in 𝓝[>] x, slope f x z < r :=
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

end Real

section RealSpace

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] {f : Real -> E} {f' : E} {s : Set Real}
  {x r : Real}

/--
theorem `HasDerivWithinAt.limsup_norm_slope_le` / 定理 `HasDerivWithinAt.limsup_norm_slope_le`

English:
theorem HasDerivWithinAt.limsup_norm_slope_le
  given: (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r)
  proof: by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : forallᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ in Iio r :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)
  have B : forallᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ in Iio r :=
    mem_o

中文:
定理 HasDerivWithinAt.limsup_norm_slope_le
  条件: (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r)
  证明: by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : forallᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ in Iio r :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)
  have B : forallᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ in Iio r :=
    mem_o

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, filter_upwards, hasDerivWithinAt_iff_tendsto_slope, isOpen_Iio, lt_of_le_of_lt, mem_nhds, mem_of_superset, mem_sup, nhdsWithin_union, norm_nonneg, sdiff_union_self, self_mem_nhdsWithin, singleton_subset_iff
-/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    forallᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r := by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : forallᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ in Iio r :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)
  have B : forallᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ in Iio r :=
    mem_of_superset self_mem_nhdsWithin (singleton_subset_iff.2 <| by simp [hr₀])
  have C := mem_sup.2 ⟨A, B⟩
  rw [← nhdsWithin_union]; rw [sdiff_union_self]; rw [nhdsWithin_union]; rw [mem_sup] at C
  filter_upwards [C.1]
  simp only [norm_smul, mem_Iio, norm_inv]
  exact fun _ => id

/--
theorem `HasDerivWithinAt.limsup_slope_norm_le` / 定理 `HasDerivWithinAt.limsup_slope_norm_le`

English:
theorem HasDerivWithinAt.limsup_slope_norm_le
  given: (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r)
  proof: by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) (by positivity)) hz

中文:
定理 HasDerivWithinAt.limsup_slope_norm_le
  条件: (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r)
  证明: by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) (by positivity)) hz

Depends on / 依赖: hf.limsup_norm_slope_le, limsup_norm_slope_le, lt_of_le_of_lt, mul_le_mul_of_nonneg_left, norm_sub_norm_le
-/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    forallᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) (by positivity)) hz

/--
theorem `HasDerivWithinAt.liminf_right_norm_slope_le` / 定理 `HasDerivWithinAt.liminf_right_norm_slope_le`

English:
theorem HasDerivWithinAt.liminf_right_norm_slope_le
  statement: (hf : HasDerivWithinAt f f' (Ici x) x)
  proof: (hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

中文:
定理 HasDerivWithinAt.liminf_right_norm_slope_le
  结论: (hf : HasDerivWithinAt f f' (Ici x) x)
  证明: (hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

Depends on / 依赖: Ioi_of_Ici, frequently, hf.Ioi_of_Ici.limsup_norm_slope_le, limsup_norm_slope_le
-/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : existsᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
  (hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

/--
theorem `HasDerivWithinAt.liminf_right_slope_norm_le` / 定理 `HasDerivWithinAt.liminf_right_slope_norm_le`

English:
theorem HasDerivWithinAt.liminf_right_slope_norm_le
  statement: (hf : HasDerivWithinAt f f' (Ici x) x)
  proof: by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently
  refine this.mp (Eventually.mono self_mem_nhdsWithin fun z hxz hz => ?_)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz

中文:
定理 HasDerivWithinAt.liminf_right_slope_norm_le
  结论: (hf : HasDerivWithinAt f f' (Ici x) x)
  证明: by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently
  refine this.mp (Eventually.mono self_mem_nhdsWithin fun z hxz hz => ?_)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz

Depends on / 依赖: Eventually, Eventually.mono, Ioi_of_Ici, Real.norm_eq_abs, abs_of_pos, frequently, hf.Ioi_of_Ici.limsup_slope_norm_le, limsup_slope_norm_le, norm_eq_abs, self_mem_nhdsWithin, sub_pos_of_lt, this.mp
-/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : existsᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently
  refine this.mp (Eventually.mono self_mem_nhdsWithin fun z hxz hz => ?_)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz

end RealSpace
