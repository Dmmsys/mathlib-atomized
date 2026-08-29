/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# The open mapping theorem for holomorphic functions

This file proves the open mapping theorem for holomorphic functions, namely that an analytic
function on a preconnected set of the complex plane is either constant or open. The main step is to
show a local version of the theorem that states that if `f` is analytic at a point `z₀`, then either
it is constant in a neighborhood of `z₀` or it maps any neighborhood of `z₀` to a neighborhood of
its image `f z₀`. The results extend in higher dimension to `g : E → ℂ`.

The proof of the local version on `ℂ` goes through two main steps: first, assuming that the function
is not constant around `z₀`, use the isolated zero principle to show that `‖f z‖` is bounded below
on a small `sphere z₀ r` around `z₀`, and then use the maximum principle applied to the auxiliary
function `(fun z ↦ ‖f z - v‖)` to show that any `v` close enough to `f z₀` is in `f '' ball z₀ r`.
That second step is implemented in `DiffContOnCl.ball_subset_image_closedBall`.

## Main results

* `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` is the local version of the open mapping
  theorem around a point;
* `AnalyticOnNhd.is_constant_or_isOpen` is the open mapping theorem on a connected open set.

As an immediate corollary, we show that a holomorphic function whose real part is constant is itself
constant.
-/

public section


open Set Filter Metric Complex

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {U : Set E} {f : Complex -> Complex} {g : E -> Complex}
  {z₀ : Complex} {ε r : Real}

/--
theorem `DiffContOnCl.ball_subset_image_closedBall` / 定理 `DiffContOnCl.ball_subset_image_closedBall`

English:
theorem DiffContOnCl.ball_subset_image_closedBall
  statement: (h : DiffContOnCl Complex f (ball z₀ r)) (hr : 0 < r)
  proof: by
  /- This is a direct application of the maximum principle. Pick `v` close to `f z₀`, and look at
    the function `fun z ↦ ‖f z - v‖`: it is bounded below on the circle, and takes a small value
    at `z₀` so it is not constant on the disk, which implies that its infimum is equal to `0` and
    

中文:
定理 DiffContOnCl.ball_subset_image_closedBall
  结论: (h : DiffContOnCl 复形 f (ball z₀ r)) (hr : 0 < r)
  证明: by
  /- This is a direct application of the maximum principle. Pick `v` close to `f z₀`, and look at
    the function `fun z ↦ ‖f z - v‖`: it is bounded below on the circle, and takes a small value
    at `z₀` so it is not constant on the disk, which implies that its infimum is equal to `0` and
    
-/
theorem DiffContOnCl.ball_subset_image_closedBall (h : DiffContOnCl Complex f (ball z₀ r)) (hr : 0 < r)
    (hf : forall z in sphere z₀ r, ε <= ‖f z - f z₀‖) (hz₀ : existsᶠ z in 𝓝 z₀, f z != f z₀) :
    ball (f z₀) (ε / 2) subseteq f '' closedBall z₀ r := by
  /- This is a direct application of the maximum principle. Pick `v` close to `f z₀`, and look at
    the function `fun z ↦ ‖f z - v‖`: it is bounded below on the circle, and takes a small value
    at `z₀` so it is not constant on the disk, which implies that its infimum is equal to `0` and
    hence that `v` is in the range of `f`. -/
  rintro v hv
  have h1 : DiffContOnCl Complex (fun z => f z - v) (ball z₀ r) := h.sub_const v
  have h2 : ContinuousOn (fun z => ‖f z - v‖) (closedBall z₀ r) :=
    continuous_norm.comp_continuousOn (closure_ball z₀ hr.ne.symm ▸ h1.continuousOn)
  have h3 : AnalyticOnNhd Complex f (ball z₀ r) := h.differentiableOn.analyticOnNhd isOpen_ball
  have h4 : forall z in sphere z₀ r, ε / 2 <= ‖f z - v‖ := fun z hz => by
    linarith [hf z hz, show ‖v - f z₀‖ < ε / 2 from mem_ball_iff_norm.1 hv,
      norm_sub_sub_norm_sub_le_norm_sub (f z) v (f z₀)]
  have h5 : ‖f z₀ - v‖ < ε / 2 := by simpa [← dist_eq_norm, dist_comm] using mem_ball.mp hv
  obtain ⟨z, hz1, hz2⟩ : exists z in ball z₀ r, IsLocalMin (fun z => ‖f z - v‖) z :=
    exists_isLocalMin_mem_ball h2 (mem_closedBall_self hr.le) fun z hz => h5.trans_le (h4 z hz)
  refine ⟨z, ball_subset_closedBall hz1, sub_eq_zero.mp ?_⟩
  have h6 := h1.differentiableOn.eventually_differentiableAt (isOpen_ball.mem_nhds hz1)
  refine (eventually_eq_or_eq_zero_of_isLocalMin_norm h6 hz2).resolve_left fun key => ?_
  have h7 : forallᶠ w in 𝓝 z, f w = f z := by filter_upwards [key] with h; simp
  replace h7 : existsᶠ w in 𝓝[!=] z, f w = f z := (h7.filter_mono nhdsWithin_le_nhds).frequently
  have h8 : IsPreconnected (ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have h9 := h3.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const h8 hz1 h7
  have h10 : f z = f z₀ := (h9 (mem_ball_self hr)).symm
  exact not_eventually.mpr hz₀ (mem_of_superset (ball_mem_nhds z₀ hr) (h10 ▸ h9))

/--
theorem `AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux` / 定理 `AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`

English:
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux
  given: (hf : AnalyticAt Complex f z₀)
  proof: by
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
    is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
    every small enough circle around `z₀` and then `DiffContOnCl.ball_subset_image_closedBall`
  

中文:
定理 AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux
  条件: (hf : AnalyticAt 复形 f z₀)
  证明: by
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
    is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
    every small enough circle around `z₀` and then `DiffContOnCl.ball_subset_image_closedBall`
  
-/
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux (hf : AnalyticAt Complex f z₀) :
    (forallᶠ z in 𝓝 z₀, f z = f z₀) ∨ 𝓝 (f z₀) <= map f (𝓝 z₀) := by
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
    is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
    every small enough circle around `z₀` and then `DiffContOnCl.ball_subset_image_closedBall`
    provides an explicit ball centered at `f z₀` contained in the range of `f`. -/
  refine or_iff_not_imp_left.mpr fun h => ?_
  refine (nhds_basis_ball.le_basis_iff (nhds_basis_closedBall.map f)).mpr fun R hR => ?_
  have h1 := (hf.eventually_eq_or_eventually_ne analyticAt_const).resolve_left h
  have h2 : forallᶠ z in 𝓝 z₀, AnalyticAt Complex f z := (isOpen_analyticAt Complex f).eventually_mem hf
  obtain ⟨ρ, hρ, h3, h4⟩ :
    exists ρ > 0, AnalyticOnNhd Complex f (closedBall z₀ ρ) ∧ forall z in closedBall z₀ ρ, z != z₀ -> f z != f z₀ := by
    simpa only [ofPred_and, subset_inter_iff] using!
      nhds_basis_closedBall.mem_iff.mp (h2.and (eventually_nhdsWithin_iff.mp h1))
  replace h3 : DiffContOnCl Complex f (ball z₀ ρ) :=
    ⟨h3.differentiableOn.mono ball_subset_closedBall,
      (closure_ball z₀ hρ.lt.ne.symm).symm ▸ h3.continuousOn⟩
  let r := ρ ⊓ R
  have hr : 0 < r := lt_inf_iff.mpr ⟨hρ, hR⟩
  have h5 : closedBall z₀ r subseteq closedBall z₀ ρ := closedBall_subset_closedBall inf_le_left
  have h6 : DiffContOnCl Complex f (ball z₀ r) := h3.mono (ball_subset_ball inf_le_left)
  have h7 : forall z in sphere z₀ r, f z != f z₀ := fun z hz =>
    h4 z (h5 (sphere_subset_closedBall hz)) (ne_of_mem_sphere hz hr.ne.symm)
  have h8 : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have h9 : ContinuousOn (fun x => ‖f x - f z₀‖) (sphere z₀ r) := continuous_norm.comp_continuousOn
    ((h6.sub_const (f z₀)).continuousOn_ball.mono sphere_subset_closedBall)
  obtain ⟨x, hx, hfx⟩ := (isCompact_sphere z₀ r).exists_isMinOn h8 h9
  refine ⟨‖f x - f z₀‖ / 2, half_pos (norm_sub_pos_iff.mpr (h7 x hx)), ?_⟩
  exact (h6.ball_subset_image_closedBall hr (fun z hz => hfx hz) (not_eventually.mp h)).trans
    (by gcongr; exact inf_le_right)

/--
theorem `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` / 定理 `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`

English:
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds
  given: {z₀ : E} (hg : AnalyticAt Complex g z₀)
  proof: by
  /- The idea of the proof is to use the one-dimensional version applied to the restriction of `g`
    to lines going through `z₀` (indexed by `sphere (0 : E) 1`). If the restriction is eventually
    constant along each of these lines, then the identity theorem implies that `g` is constant on
  

中文:
定理 AnalyticAt.eventually_constant_or_nhds_le_map_nhds
  条件: {z₀ : E} (hg : AnalyticAt 复形 g z₀)
  证明: by
  /- The idea of the proof is to use the one-dimensional version applied to the restriction of `g`
    to lines going through `z₀` (indexed by `sphere (0 : E) 1`). If the restriction is eventually
    constant along each of these lines, then the identity theorem implies that `g` is constant on
  
-/
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds {z₀ : E} (hg : AnalyticAt Complex g z₀) :
    (forallᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) <= map g (𝓝 z₀) := by
  /- The idea of the proof is to use the one-dimensional version applied to the restriction of `g`
    to lines going through `z₀` (indexed by `sphere (0 : E) 1`). If the restriction is eventually
    constant along each of these lines, then the identity theorem implies that `g` is constant on
    any ball centered at `z₀` on which it is analytic, and in particular `g` is eventually constant.
    If on the other hand there is one line along which `g` is not eventually constant, then the
    one-dimensional version of the open mapping theorem can be used to conclude. -/
  let ray : E -> Complex -> E := fun z t => z₀ + t • z
  let gray : E -> Complex -> Complex := fun z => g ∘ ray z
  obtain ⟨r, hr, hgr⟩ := isOpen_iff.mp (isOpen_analyticAt Complex g) z₀ hg
  have h1 : forall z in sphere (0 : E) 1, AnalyticOnNhd Complex (gray z) (ball 0 r) := by
    refine fun z hz t ht => AnalyticAt.comp ?_ ?_
    · exact hgr (by simpa [ray, norm_smul, mem_sphere_zero_iff_norm.mp hz] using! ht)
    · exact analyticAt_const.add
        ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id Complex Complex) z).analyticAt t)
  by_cases h : forall z in sphere (0 : E) 1, forallᶠ t in 𝓝 0, gray z t = gray z 0
  · left
    -- If g is eventually constant along every direction, then it is eventually constant
    refine eventually_of_mem (ball_mem_nhds z₀ hr) fun z hz => ?_
    refine (eq_or_ne z z₀).casesOn (congr_arg g) fun h' => ?_
    replace h' : ‖z - z₀‖ != 0 := by simpa only [Ne, norm_eq_zero, sub_eq_zero]
    let w : E := ‖z - z₀‖⁻¹ • (z - z₀)
    have h3 : forall t in ball (0 : Complex) r, gray w t = g z₀ := by
      have e1 : IsPreconnected (ball (0 : Complex) r) := (convex_ball 0 r).isPreconnected
      have e2 : w in sphere (0 : E) 1 := by simp [w, norm_smul, inv_mul_cancel₀ h']
      specialize h1 w e2
      apply h1.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const e1 (mem_ball_self hr)
      simpa [ray, gray] using! h w e2
    have h4 : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using! mem_ball.mp hz
    replace h4 : ↑‖z - z₀‖ in ball (0 : Complex) r := by simpa
    simpa only [ray, gray, w, smul_smul, mul_inv_cancel₀ h', one_smul, add_sub_cancel,
      Function.comp_apply, coe_smul] using! h3 (↑‖z - z₀‖) h4
  · right
    simp only [not_forall] at h
    -- Otherwise, it is open along at least one direction and that implies the result
    obtain ⟨z, hz, hrz⟩ := h
    specialize h1 z hz 0 (mem_ball_self hr)
    have h7 := h1.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hrz
    rw [show gray z 0 = g z₀ by simp [gray]; rw [ray], ← map_compose] at h7
    refine h7.trans (map_mono ?_)
    have h10 : Continuous fun t : Complex => z₀ + t • z := by fun_prop
    simpa using! h10.tendsto 0

/--
theorem `AnalyticOnNhd.is_constant_or_isOpen` / 定理 `AnalyticOnNhd.is_constant_or_isOpen`

English:
theorem AnalyticOnNhd.is_constant_or_isOpen
  given: (hg : AnalyticOnNhd Complex g U) (hU : IsPreconnected U)
  proof: by
  by_cases h : exists z₀ in U, forallᶠ z in 𝓝 z₀, g z = g z₀
  · obtain ⟨z₀, hz₀, h⟩ := h
    exact Or.inl ⟨g z₀, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀ h⟩
  · simp only [not_exists, not_and] at h
    refine Or.inr fun s hs1 hs2 => isOpen_iff_mem_nhds.mpr ?_
    rintro

中文:
定理 AnalyticOnNhd.is_constant_or_isOpen
  条件: (hg : AnalyticOnNhd 复形 g U) (hU : 是预连通 U)
  证明: by
  by_cases h : exists z₀ in U, forallᶠ z in 𝓝 z₀, g z = g z₀
  · obtain ⟨z₀, hz₀, h⟩ := h
    exact Or.inl ⟨g z₀, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀ h⟩
  · simp only [not_exists, not_and] at h
    refine Or.inr fun s hs1 hs2 => isOpen_iff_mem_nhds.mpr ?_
    rintro

Depends on / 依赖: Or.inl, Or.inr, analyticOnNhd_const, eqOn_of_preconnected_of_eventuallyEq, eventually_constant_or_nhds_le_map_nhds, eventually_constant_or_nhds_le_map_nhds.resolve_left, hg.eqOn_of_preconnected_of_eventuallyEq, hs2.mem_nhds, image_mem_map, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, mem_nhds, not_and, not_exists, resolve_left
-/
theorem AnalyticOnNhd.is_constant_or_isOpen (hg : AnalyticOnNhd Complex g U) (hU : IsPreconnected U) :
    (exists w, forall z in U, g z = w) ∨ forall s subseteq U, IsOpen s -> IsOpen (g '' s) := by
  by_cases h : exists z₀ in U, forallᶠ z in 𝓝 z₀, g z = g z₀
  · obtain ⟨z₀, hz₀, h⟩ := h
    exact Or.inl ⟨g z₀, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀ h⟩
  · simp only [not_exists, not_and] at h
    refine Or.inr fun s hs1 hs2 => isOpen_iff_mem_nhds.mpr ?_
    rintro z ⟨w, hw1, rfl⟩
    exact (hg w (hs1 hw1)).eventually_constant_or_nhds_le_map_nhds.resolve_left (h w (hs1 hw1))
        (image_mem_map (hs2.mem_nhds hw1))

/--
theorem `AnalyticOnNhd.is_constant_or_isOpenMap` / 定理 `AnalyticOnNhd.is_constant_or_isOpenMap`

English:
theorem AnalyticOnNhd.is_constant_or_isOpenMap
  given: (hg : AnalyticOnNhd Complex g .univ)
  proof: (hg.is_constant_or_isOpen PreconnectedSpace.isPreconnected_univ).imp
    (fun ⟨w, eq⟩ => ⟨w, fun z => eq z ⟨⟩⟩) (· · <| subset_univ _)

中文:
定理 AnalyticOnNhd.is_constant_or_isOpenMap
  条件: (hg : AnalyticOnNhd 复形 g .univ)
  证明: (hg.is_constant_or_isOpen PreconnectedSpace.isPreconnected_univ).imp
    (fun ⟨w, eq⟩ => ⟨w, fun z => eq z ⟨⟩⟩) (· · <| subset_univ _)

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.isPreconnected_univ, hg.is_constant_or_isOpen, isPreconnected_univ, is_constant_or_isOpen, subset_univ
-/
theorem AnalyticOnNhd.is_constant_or_isOpenMap (hg : AnalyticOnNhd Complex g .univ) :
    (exists w, forall z, g z = w) ∨ IsOpenMap g :=
  (hg.is_constant_or_isOpen PreconnectedSpace.isPreconnected_univ).imp
    (fun ⟨w, eq⟩ => ⟨w, fun z => eq z ⟨⟩⟩) (· · <| subset_univ _)

/-!
## Holomorphic Functions with Constant Real or Imaginary Part
-/

/--
theorem `AnalyticOnNhd.eq_const_of_re_eq_const` / 定理 `AnalyticOnNhd.eq_const_of_re_eq_const`

English:
theorem AnalyticOnNhd.eq_const_of_re_eq_const
  statement: {U : Set Complex} {c₀ : Real} (h₁f : AnalyticOnNhd Complex f U)
  proof: by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : Real), (by aesop : (re '' f '' U) = { c₀ }), isOpenMap_re
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

中文:
定理 AnalyticOnNhd.eq_const_of_re_eq_const
  结论: {U : 集合 复形} {c₀ : 实数} (h₁f : AnalyticOnNhd 复形 f U)
  证明: by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : Real), (by aesop : (re '' f '' U) = { c₀ }), isOpenMap_re
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

Depends on / 依赖: U.isPreconnected, U.nonempty, f.is_constant_or_isOpen, isOpenMap_re, isPreconnected, is_constant_or_isOpen, nonempty, not_isOpen_singleton, resolve_left
-/
theorem AnalyticOnNhd.eq_const_of_re_eq_const {U : Set Complex} {c₀ : Real} (h₁f : AnalyticOnNhd Complex f U)
    (h₂f : forall x in U, (f x).re = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    exists c, forall x in U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : Real), (by aesop : (re '' f '' U) = { c₀ }), isOpenMap_re
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

/--
theorem `AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const` / 定理 `AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const`

English:
theorem AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const
  statement: {U : Set Complex} {c₀ : Real}
  proof: by
  obtain ⟨cc, hcc⟩ := eq_const_of_re_eq_const h₁f h₂f h₁U h₂U
  use cc.im
  simp_rw [Complex.ext_iff]
  aesop

中文:
定理 AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const
  结论: {U : 集合 复形} {c₀ : 实数}
  证明: by
  obtain ⟨cc, hcc⟩ := eq_const_of_re_eq_const h₁f h₂f h₁U h₂U
  use cc.im
  simp_rw [Complex.ext_iff]
  aesop

Depends on / 依赖: Complex.ext_iff, cc.im, eq_const_of_re_eq_const, ext_iff, simp_rw
-/
theorem AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const {U : Set Complex} {c₀ : Real}
    (h₁f : AnalyticOnNhd Complex f U) (h₂f : forall x in U, (f x).re = c₀) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    exists (c : Real), forall x in U, f x = c₀ + c * I := by
  obtain ⟨cc, hcc⟩ := eq_const_of_re_eq_const h₁f h₂f h₁U h₂U
  use cc.im
  simp_rw [Complex.ext_iff]
  aesop

/--
theorem `AnalyticOnNhd.eq_const_of_im_eq_const` / 定理 `AnalyticOnNhd.eq_const_of_im_eq_const`

English:
theorem AnalyticOnNhd.eq_const_of_im_eq_const
  statement: {U : Set Complex} {c₀ : Real} (h₁f : AnalyticOnNhd Complex f U)
  proof: by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : Real), (by aesop : (im '' f '' U) = { c₀ }), isOpenMap_im
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

中文:
定理 AnalyticOnNhd.eq_const_of_im_eq_const
  结论: {U : 集合 复形} {c₀ : 实数} (h₁f : AnalyticOnNhd 复形 f U)
  证明: by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : Real), (by aesop : (im '' f '' U) = { c₀ }), isOpenMap_im
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

Depends on / 依赖: U.isPreconnected, U.nonempty, f.is_constant_or_isOpen, isOpenMap_im, isPreconnected, is_constant_or_isOpen, nonempty, not_isOpen_singleton, resolve_left
-/
theorem AnalyticOnNhd.eq_const_of_im_eq_const {U : Set Complex} {c₀ : Real} (h₁f : AnalyticOnNhd Complex f U)
    (h₂f : forall x in U, (f x).im = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    exists c, forall x in U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : Real), (by aesop : (im '' f '' U) = { c₀ }), isOpenMap_im
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

/--
theorem `AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const` / 定理 `AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const`

English:
theorem AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const
  statement: {U : Set Complex} {c₀ : Real}
  proof: by
  obtain ⟨cc, hcc⟩ := AnalyticOnNhd.eq_const_of_im_eq_const h₁f h₂f h₁U h₂U
  use cc.re
  simp_rw [Complex.ext_iff]
  aesop

中文:
定理 AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const
  结论: {U : 集合 复形} {c₀ : 实数}
  证明: by
  obtain ⟨cc, hcc⟩ := AnalyticOnNhd.eq_const_of_im_eq_const h₁f h₂f h₁U h₂U
  use cc.re
  simp_rw [Complex.ext_iff]
  aesop

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.eq_const_of_im_eq_const, Complex.ext_iff, cc.re, eq_const_of_im_eq_const, ext_iff, simp_rw
-/
theorem AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const {U : Set Complex} {c₀ : Real}
    (h₁f : AnalyticOnNhd Complex f U) (h₂f : forall x in U, (f x).im = c₀) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    exists (c : Real), forall x in U, f x = c + c₀ * I := by
  obtain ⟨cc, hcc⟩ := AnalyticOnNhd.eq_const_of_im_eq_const h₁f h₂f h₁U h₂U
  use cc.re
  simp_rw [Complex.ext_iff]
  aesop


/--
theorem `Polynomial.C_eq_or_isOpenQuotientMap_eval` / 定理 `Polynomial.C_eq_or_isOpenQuotientMap_eval`

English:
theorem Polynomial.C_eq_or_isOpenQuotientMap_eval
  given: (p : Polynomial Complex)
  proof: by
  refine or_iff_not_imp_left.mpr fun h => ?_
  obtain ⟨x, eq⟩ | hp := (AnalyticOnNhd.eval_polynomial p).is_constant_or_isOpenMap
  · exact (h ⟨x, funext <| by simpa [eq_comm (a := x)]⟩).elim
· exact ⟨IsAlgClosed.eval_surjective natDegree_eq_zero.not.mpr h, p.continuous_aeval, hp⟩

中文:
定理 多项式.C_eq_or_isOpenQuotientMap_eval
  条件: (p : 多项式 复形)
  证明: by
  refine or_iff_not_imp_left.mpr fun h => ?_
  obtain ⟨x, eq⟩ | hp := (AnalyticOnNhd.eval_polynomial p).is_constant_or_isOpenMap
  · exact (h ⟨x, funext <| by simpa [eq_comm (a := x)]⟩).elim
· exact ⟨IsAlgClosed.eval_surjective natDegree_eq_zero.not.mpr h, p.continuous_aeval, hp⟩

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.eval_polynomial, IsAlgClosed, IsAlgClosed.eval_surjective, continuous_aeval, eq_comm, eval_polynomial, eval_surjective, is_constant_or_isOpenMap, natDegree_eq_zero, natDegree_eq_zero.not.mpr, or_iff_not_imp_left, or_iff_not_imp_left.mpr, p.continuous_aeval
-/
theorem Polynomial.C_eq_or_isOpenQuotientMap_eval (p : Polynomial Complex) :
    (exists x, C x = p) ∨ IsOpenQuotientMap p.eval := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  obtain ⟨x, eq⟩ | hp := (AnalyticOnNhd.eval_polynomial p).is_constant_or_isOpenMap
  · exact (h ⟨x, funext <| by simpa [eq_comm (a := x)]⟩).elim
· exact ⟨IsAlgClosed.eval_surjective natDegree_eq_zero.not.mpr h, p.continuous_aeval, hp⟩

/--
theorem `Polynomial.isOpenQuotientMap_eval` / 定理 `Polynomial.isOpenQuotientMap_eval`

English:
theorem Polynomial.isOpenQuotientMap_eval
  given: (p : Polynomial Complex) (hp : p.natDegree != 0)
  proof: p.C_eq_or_isOpenQuotientMap_eval.resolve_left natDegree_eq_zero.not.mp hp

中文:
定理 多项式.isOpenQuotientMap_eval
  条件: (p : 多项式 复形) (hp : p.natDegree != 0)
  证明: p.C_eq_or_isOpenQuotientMap_eval.resolve_left natDegree_eq_zero.not.mp hp

Depends on / 依赖: C_eq_or_isOpenQuotientMap_eval, natDegree_eq_zero, natDegree_eq_zero.not.mp, p.C_eq_or_isOpenQuotientMap_eval.resolve_left, resolve_left
-/
theorem Polynomial.isOpenQuotientMap_eval (p : Polynomial Complex) (hp : p.natDegree != 0) :
    IsOpenQuotientMap p.eval :=
p.C_eq_or_isOpenQuotientMap_eval.resolve_left natDegree_eq_zero.not.mp hp

namespace Complex

/--
theorem `isOpenQuotientMap_pow` / 定理 `isOpenQuotientMap_pow`

English:
theorem isOpenQuotientMap_pow
  given: (n : Nat) [NeZero n]
  statement: IsOpenQuotientMap (· ^ n : Complex -> Complex)
  proof: by
  convert! Polynomial.isOpenQuotientMap_eval (.X ^ n) _
  · simp
  · simpa using NeZero.ne n

中文:
定理 isOpenQuotientMap_pow
  条件: (n : 自然数) [NeZero n]
  结论: 是OpenQuotient映射 (· ^ n : 复形 -> 复形)
  证明: by
  convert! Polynomial.isOpenQuotientMap_eval (.X ^ n) _
  · simp
  · simpa using NeZero.ne n

Depends on / 依赖: NeZero, NeZero.ne, Polynomial, Polynomial.isOpenQuotientMap_eval, convert, isOpenQuotientMap_eval
-/
theorem isOpenQuotientMap_pow (n : Nat) [NeZero n] : IsOpenQuotientMap (· ^ n : Complex -> Complex) := by
  convert! Polynomial.isOpenQuotientMap_eval (.X ^ n) _
  · simp
  · simpa using NeZero.ne n

/--
theorem `isOpenQuotientMap_pow_compl_zero` / 定理 `isOpenQuotientMap_pow_compl_zero`

English:
theorem isOpenQuotientMap_pow_compl_zero
  given: (n : Nat) [NeZero n]
  proof: have ⟨w, h⟩ := (isOpenQuotientMap_pow n).surjective z
    ⟨⟨w, by rintro rfl; exact z.2 (by simpa [zero_pow (NeZero.ne n)] using h.symm)⟩, Subtype.ext h⟩
  continuous := by fun_prop
isOpenMap := (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr
    (isOpenQuotientMap_pow n).

中文:
定理 isOpenQuotientMap_pow_compl_zero
  条件: (n : 自然数) [NeZero n]
  证明: have ⟨w, h⟩ := (isOpenQuotientMap_pow n).surjective z
    ⟨⟨w, by rintro rfl; exact z.2 (by simpa [zero_pow (NeZero.ne n)] using h.symm)⟩, Subtype.ext h⟩
  continuous := by fun_prop
isOpenMap := (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr
    (isOpenQuotientMap_pow n).

Depends on / 依赖: isOpenQuotientMap_pow, surjective
-/
theorem isOpenQuotientMap_pow_compl_zero (n : Nat) [NeZero n] :
    IsOpenQuotientMap
      fun z : {z : Complex // z != 0} => (⟨z ^ n, pow_ne_zero n z.2⟩ : {z : Complex // z != 0}) where
  surjective z := have ⟨w, h⟩ := (isOpenQuotientMap_pow n).surjective z
    ⟨⟨w, by rintro rfl; exact z.2 (by simpa [zero_pow (NeZero.ne n)] using h.symm)⟩, Subtype.ext h⟩
  continuous := by fun_prop
isOpenMap := (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr
    (isOpenQuotientMap_pow n).isOpenMap.comp isClosed_singleton.1.isOpenMap_subtype_val

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isOpenQuotientMap_zpow_compl_zero` / 定理 `isOpenQuotientMap_zpow_compl_zero`

English:
theorem isOpenQuotientMap_zpow_compl_zero
  given: (n : Int) [NeZero n]
  proof: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · have : NeZero n := ⟨Nat.cast_ne_zero.mp (NeZero.ne (n : Int))⟩
    exact isOpenQuotientMap_pow_compl_zero n
· have : NeZero n := ⟨Nat.cast_ne_zero.mp neg_ne_zero.mp (NeZero.ne (-n : Int))⟩
    convert! (isOpenQuotientMap_pow_compl_zero n).comp (Homeo

中文:
定理 isOpenQuotientMap_zpow_compl_zero
  条件: (n : 整数) [NeZero n]
  证明: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · have : NeZero n := ⟨Nat.cast_ne_zero.mp (NeZero.ne (n : Int))⟩
    exact isOpenQuotientMap_pow_compl_zero n
· have : NeZero n := ⟨Nat.cast_ne_zero.mp neg_ne_zero.mp (NeZero.ne (-n : Int))⟩
    convert! (isOpenQuotientMap_pow_compl_zero n).comp (Homeo

Depends on / 依赖: Homeomorph, Homeomorph.inv, Nat.cast_ne_zero.mp, NeZero, NeZero.ne, cast_ne_zero, convert, eq_nat_or_neg, isOpenQuotientMap, isOpenQuotientMap_pow_compl_zero, n.eq_nat_or_neg, neg_ne_zero, neg_ne_zero.mp
-/
theorem isOpenQuotientMap_zpow_compl_zero (n : Int) [NeZero n] :
    IsOpenQuotientMap
      fun z : {z : Complex // z != 0} => (⟨z ^ n, zpow_ne_zero n z.2⟩ : {z : Complex // z != 0}) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · have : NeZero n := ⟨Nat.cast_ne_zero.mp (NeZero.ne (n : Int))⟩
    exact isOpenQuotientMap_pow_compl_zero n
· have : NeZero n := ⟨Nat.cast_ne_zero.mp neg_ne_zero.mp (NeZero.ne (-n : Int))⟩
    convert! (isOpenQuotientMap_pow_compl_zero n).comp (Homeomorph.inv₀ Complex).isOpenQuotientMap
    simp [Homeomorph.inv₀]

end Complex
