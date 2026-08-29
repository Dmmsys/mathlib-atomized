/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Holomorphic functions on complex manifolds

Thanks to the rigidity of complex-differentiability compared to real-differentiability, there are
many results about complex manifolds with no analogue for manifolds over a general normed field. For
now, this file contains just two (closely related) such results:

## Main results

* `MDifferentiable.isLocallyConstant`: A complex-differentiable function on a compact complex
  manifold is locally constant.
* `MDifferentiable.exists_eq_const_of_compactSpace`: A complex-differentiable function on a compact
  preconnected complex manifold is constant.

## TODO

There is a whole theory to develop here. Maybe a next step would be to develop a theory of
holomorphic vector/line bundles, including:
* the finite-dimensionality of the space of sections of a holomorphic vector bundle
* Siegel's theorem: for any `n + 1` formal ratios `g 0 / h 0`, `g 1 / h 1`, .... `g n / h n` of
  sections of a fixed line bundle `L` over a complex `n`-manifold, there exists a polynomial
  relationship `P (g 0 / h 0, g 1 / h 1, .... g n / h n) = 0`

Another direction would be to develop the relationship with sheaf theory, building the sheaves of
holomorphic and meromorphic functions on a complex manifold and proving algebraic results about the
stalks, such as the Weierstrass preparation theorem.

-/

public section

open scoped Manifold Topology Filter
open Function Set Filter Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Complex F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Complex E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/--
theorem `Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax` / 定理 `Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax`

English:
theorem Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax
  statement: {f : M -> F} {c : M}
  proof: by
  set e := extChartAt I c
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e c) = 𝓝 (e c) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e c)) = 𝓝 c := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]; rw [H₁]
  rw [← H₂]; rw [eventually_map]
  replace hd : forallᶠ y in 𝓝 (e c), DifferentiableAt Complex (f ∘ e.symm) y := by
    have : e.target in 𝓝 (e c) := H₁ ▸ extChartAt_target_mem_nhdsWithin c
    filter_upwards [this, Tendsto.eventually H₂.le hd] with y hyt hy₂
    have hys : e.symm y in (chartAt H c).source := by
      rw [← extChartAt_source I c]
      exact (extChartAt I c).map_target hyt
    have hfy : f (e.symm y) in (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy]; rw [hI]; rw [differentiableWithinAt_univ]; rw [e.right_inv hyt] at hy₂
    exact hy₂.2
  convert! norm_eventually_eq_of_isLocalMax hd _
  · exact congr_arg f (extChartAt_to_inv _).symm
  · simpa only [e, IsLocalMax, IsMaxFilter, ← H₂, (· ∘ ·), extChartAt_to_inv] using! hc

中文:
定理 复形.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax
  结论: {f : M -> F} {c : M}
  证明: by
  set e := extChartAt I c
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e c) = 𝓝 (e c) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e c)) = 𝓝 c := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]; rw [H₁]
  rw [← H₂]; rw [eventually_map]
  replace hd : forallᶠ y in 𝓝 (e c), DifferentiableAt Complex (f ∘ e.symm) y := by
    have : e.target in 𝓝 (e c) := H₁ ▸ extChartAt_target_mem_nhdsWithin c
    filter_upwards [this, Tendsto.eventually H₂.le hd] with y hyt hy₂
    have hys : e.symm y in (chartAt H c).source := by
      rw [← extChartAt_source I c]
      exact (extChartAt I c).map_target hyt
    have hfy : f (e.symm y) in (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy]; rw [hI]; rw [differentiableWithinAt_univ]; rw [e.right_inv hyt] at hy₂
    exact hy₂.2
  convert! norm_eventually_eq_of_isLocalMax hd _
  · exact congr_arg f (extChartAt_to_inv _).symm
  · simpa only [e, IsLocalMax, IsMaxFilter, ← H₂, (· ∘ ·), extChartAt_to_inv] using! hc

Depends on / 依赖: Boundaryless, DifferentiableAt, ModelWithCorners, ModelWithCorners.Boundaryless.range_eq_univ, Tendsto, Tendsto.eventually, e.symm, e.target, eventually, eventually_map, extChartAt, extChartAt_target_mem_nhdsWithin, filter_upwards, map_extChartAt_symm_nhdsWithin_range, nhdsWithin_univ, range_eq_univ, replace, target
-/
theorem Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax {f : M -> F} {c : M}
    (hd : forallᶠ z in 𝓝 c, MDiffAt f z) (hc : IsLocalMax (norm ∘ f) c) :
    forallᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  set e := extChartAt I c
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e c) = 𝓝 (e c) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e c)) = 𝓝 c := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]; rw [H₁]
  rw [← H₂]; rw [eventually_map]
  replace hd : forallᶠ y in 𝓝 (e c), DifferentiableAt Complex (f ∘ e.symm) y := by
    have : e.target in 𝓝 (e c) := H₁ ▸ extChartAt_target_mem_nhdsWithin c
    filter_upwards [this, Tendsto.eventually H₂.le hd] with y hyt hy₂
    have hys : e.symm y in (chartAt H c).source := by
      rw [← extChartAt_source I c]
      exact (extChartAt I c).map_target hyt
    have hfy : f (e.symm y) in (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy]; rw [hI]; rw [differentiableWithinAt_univ]; rw [e.right_inv hyt] at hy₂
    exact hy₂.2
  convert! norm_eventually_eq_of_isLocalMax hd _
  · exact congr_arg f (extChartAt_to_inv _).symm
  · simpa only [e, IsLocalMax, IsMaxFilter, ← H₂, (· ∘ ·), extChartAt_to_inv] using! hc

/-!
### Functions holomorphic on a set
-/

namespace MDifferentiableOn

/--
theorem `norm_eqOn_of_isPreconnected_of_isMaxOn` / 定理 `norm_eqOn_of_isPreconnected_of_isMaxOn`

English:
theorem norm_eqOn_of_isPreconnected_of_isMaxOn
  statement: {f : M -> F} {U : Set M} {c : M}
  proof: by
  set V := {z in U | ‖f z‖ = ‖f c‖}
  suffices U subseteq V from fun x hx => (this hx).2
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 fun x hx => inter_mem (ho.mem_nhds hx.1) ?_
    replace hm : IsLocalMax (‖f ·‖) x :=
      mem_of_superset (ho.mem_nhds hx.1) fun z hz => (hm hz).out.trans_eq hx.2.symm
    replace hd : forallᶠ y in 𝓝 x, MDiffAt f y :=
      (eventually_mem_nhds_iff.2 (ho.mem_nhds hx.1)).mono fun z => hd.mdifferentiableAt
    exact (Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hm).mono fun _ =>
      (Eq.trans · hx.2)
  have hVne : (U inter V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  set W := U inter {z | ‖f z‖ = ‖f c‖}ᶜ
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hUVW : U subseteq V union W := fun x hx => (eq_or_ne ‖f x‖ ‖f c‖).imp (.intro hx) (.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

中文:
定理 norm_eqOn_of_isPreconnected_of_isMaxOn
  结论: {f : M -> F} {U : 集合 M} {c : M}
  证明: by
  set V := {z in U | ‖f z‖ = ‖f c‖}
  suffices U subseteq V from fun x hx => (this hx).2
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 fun x hx => inter_mem (ho.mem_nhds hx.1) ?_
    replace hm : IsLocalMax (‖f ·‖) x :=
      mem_of_superset (ho.mem_nhds hx.1) fun z hz => (hm hz).out.trans_eq hx.2.symm
    replace hd : forallᶠ y in 𝓝 x, MDiffAt f y :=
      (eventually_mem_nhds_iff.2 (ho.mem_nhds hx.1)).mono fun z => hd.mdifferentiableAt
    exact (Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hm).mono fun _ =>
      (Eq.trans · hx.2)
  have hVne : (U inter V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  set W := U inter {z | ‖f z‖ = ‖f c‖}ᶜ
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hUVW : U subseteq V union W := fun x hx => (eq_or_ne ‖f x‖ ‖f c‖).imp (.intro hx) (.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

Depends on / 依赖: Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax, IsLocalMax, IsOpen, MDiffAt, eventually_mem_nhds_iff, hd.mdifferentiableAt, ho.mem_nhds, inter_mem, isOpen_iff_mem_nhds, mdifferentiableAt, mem_nhds, mem_of_superset, norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax, out.trans_eq, replace, subseteq, trans_eq
-/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : M -> F} {U : Set M} {c : M}
    (hd : MDiff[U] f) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const M ‖f c‖) U := by
  set V := {z in U | ‖f z‖ = ‖f c‖}
  suffices U subseteq V from fun x hx => (this hx).2
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 fun x hx => inter_mem (ho.mem_nhds hx.1) ?_
    replace hm : IsLocalMax (‖f ·‖) x :=
      mem_of_superset (ho.mem_nhds hx.1) fun z hz => (hm hz).out.trans_eq hx.2.symm
    replace hd : forallᶠ y in 𝓝 x, MDiffAt f y :=
      (eventually_mem_nhds_iff.2 (ho.mem_nhds hx.1)).mono fun z => hd.mdifferentiableAt
    exact (Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hm).mono fun _ =>
      (Eq.trans · hx.2)
  have hVne : (U inter V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  set W := U inter {z | ‖f z‖ = ‖f c‖}ᶜ
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hUVW : U subseteq V union W := fun x hx => (eq_or_ne ‖f x‖ ‖f c‖).imp (.intro hx) (.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

/--
theorem `eqOn_of_isPreconnected_of_isMaxOn_norm` / 定理 `eqOn_of_isPreconnected_of_isMaxOn_norm`

English:
theorem eqOn_of_isPreconnected_of_isMaxOn_norm
  statement: [StrictConvexSpace Real F] {f : M -> F} {U : Set M}
  proof: fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := hd.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm hx
  have hd' : MDiff[U] (f · + f c) := hd.add mdifferentiableOn_const
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    hd'.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm.norm_add_self hx
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

中文:
定理 eqOn_of_isPreconnected_of_isMaxOn_norm
  结论: [严格凸空间 实数 F] {f : M -> F} {U : 集合 M}
  证明: fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := hd.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm hx
  have hd' : MDiff[U] (f · + f c) := hd.add mdifferentiableOn_const
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    hd'.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm.norm_add_self hx
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]
-/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm [StrictConvexSpace Real F] {f : M -> F} {U : Set M}
    {c : M} (hd : MDiff[U] f) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const M (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := hd.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm hx
  have hd' : MDiff[U] (f · + f c) := hd.add mdifferentiableOn_const
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    hd'.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm.norm_add_self hx
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

/--
theorem `apply_eq_of_isPreconnected_isCompact_isOpen` / 定理 `apply_eq_of_isPreconnected_isCompact_isOpen`

English:
theorem apply_eq_of_isPreconnected_isCompact_isOpen
  statement: {f : M -> F} {U : Set M} {a b : M}
  proof: by
  -- Subtract `f b` to avoid the assumption `[StrictConvexSpace ℝ F]`
  wlog hb₀ : f b = 0 generalizing f
  -- TODO: Add `MDifferentiableOn.sub` etc
  · have hd' : MDiff[U] (f · - f b) := fun x hx =>
      ⟨(hd x hx).1.sub continuousWithinAt_const, (hd x hx).2.sub_const _⟩
    simpa [sub_eq_zero] using this hd' (sub_self _)
  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
  have : forall x in U, ‖f x‖ = ‖f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hd hpc ho hcU hc
  rw [hb₀]; rw [← norm_eq_zero]; rw [this a ha]; rw [← this b hb]; rw [hb₀]; rw [norm_zero]

中文:
定理 apply_eq_of_isPreconnected_isCompact_isOpen
  结论: {f : M -> F} {U : 集合 M} {a b : M}
  证明: by
  -- Subtract `f b` to avoid the assumption `[StrictConvexSpace ℝ F]`
  wlog hb₀ : f b = 0 generalizing f
  -- TODO: Add `MDifferentiableOn.sub` etc
  · have hd' : MDiff[U] (f · - f b) := fun x hx =>
      ⟨(hd x hx).1.sub continuousWithinAt_const, (hd x hx).2.sub_const _⟩
    simpa [sub_eq_zero] using this hd' (sub_self _)
  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
  have : forall x in U, ‖f x‖ = ‖f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hd hpc ho hcU hc
  rw [hb₀]; rw [← norm_eq_zero]; rw [this a ha]; rw [← this b hb]; rw [hb₀]; rw [norm_zero]
-/
theorem apply_eq_of_isPreconnected_isCompact_isOpen {f : M -> F} {U : Set M} {a b : M}
    (hd : MDiff[U] f) (hpc : IsPreconnected U) (hc : IsCompact U)
    (ho : IsOpen U) (ha : a in U) (hb : b in U) : f a = f b := by
  -- Subtract `f b` to avoid the assumption `[StrictConvexSpace ℝ F]`
  wlog hb₀ : f b = 0 generalizing f
  -- TODO: Add `MDifferentiableOn.sub` etc
  · have hd' : MDiff[U] (f · - f b) := fun x hx =>
      ⟨(hd x hx).1.sub continuousWithinAt_const, (hd x hx).2.sub_const _⟩
    simpa [sub_eq_zero] using this hd' (sub_self _)
  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
  have : forall x in U, ‖f x‖ = ‖f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hd hpc ho hcU hc
  rw [hb₀]; rw [← norm_eq_zero]; rw [this a ha]; rw [← this b hb]; rw [hb₀]; rw [norm_zero]

end MDifferentiableOn

/-!
### Functions holomorphic on the whole manifold

Lemmas in this section were generalized from `𝓘(ℂ, E)` to an unspecified boundaryless
model so that it works, e.g., on a product of two manifolds without a boundary. This can break
`apply MDifferentiable.apply_eq_of_compactSpace`, use
`apply MDifferentiable.apply_eq_of_compactSpace (I := I)` instead or dot notation on an existing
`MDifferentiable` hypothesis.
-/

namespace MDifferentiable

variable [CompactSpace M]

/--
theorem `isLocallyConstant` / 定理 `isLocallyConstant`

English:
theorem isLocallyConstant
  given: {f : M -> F} (hf : MDiff f)
  proof: haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  IsLocallyConstant.of_constant_on_preconnected_clopens fun _ hpc hclo _a ha _b hb =>
    hf.mdifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen hpc
      hclo.isClosed.isCompact hclo.isOpen hb ha

中文:
定理 isLocallyConstant
  条件: {f : M -> F} (hf : MDiff f)
  证明: haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  IsLocallyConstant.of_constant_on_preconnected_clopens fun _ hpc hclo _a ha _b hb =>
    hf.mdifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen hpc
      hclo.isClosed.isCompact hclo.isOpen hb ha
-/
protected theorem isLocallyConstant {f : M -> F} (hf : MDiff f) :
    IsLocallyConstant f :=
  haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  IsLocallyConstant.of_constant_on_preconnected_clopens fun _ hpc hclo _a ha _b hb =>
    hf.mdifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen hpc
      hclo.isClosed.isCompact hclo.isOpen hb ha

/--
theorem `apply_eq_of_compactSpace` / 定理 `apply_eq_of_compactSpace`

English:
theorem apply_eq_of_compactSpace
  statement: [PreconnectedSpace M] {f : M -> F}
  proof: hf.isLocallyConstant.apply_eq_of_preconnectedSpace _ _

中文:
定理 apply_eq_of_compactSpace
  结论: [预连通空间 M] {f : M -> F}
  证明: hf.isLocallyConstant.apply_eq_of_preconnectedSpace _ _

Depends on / 依赖: apply_eq_of_preconnectedSpace, hf.isLocallyConstant.apply_eq_of_preconnectedSpace, isLocallyConstant
-/
theorem apply_eq_of_compactSpace [PreconnectedSpace M] {f : M -> F}
    (hf : MDiff f) (a b : M) : f a = f b :=
  hf.isLocallyConstant.apply_eq_of_preconnectedSpace _ _

/--
theorem `exists_eq_const_of_compactSpace` / 定理 `exists_eq_const_of_compactSpace`

English:
theorem exists_eq_const_of_compactSpace
  given: [PreconnectedSpace M] {f : M -> F} (hf : MDiff f)
  proof: hf.isLocallyConstant.exists_eq_const

中文:
定理 存在_eq_const_of_compactSpace
  条件: [预连通空间 M] {f : M -> F} (hf : MDiff f)
  证明: hf.isLocallyConstant.exists_eq_const

Depends on / 依赖: exists_eq_const, hf.isLocallyConstant.exists_eq_const, isLocallyConstant
-/
theorem exists_eq_const_of_compactSpace [PreconnectedSpace M] {f : M -> F} (hf : MDiff f) :
    exists v : F, f = Function.const M v :=
  hf.isLocallyConstant.exists_eq_const

end MDifferentiable
