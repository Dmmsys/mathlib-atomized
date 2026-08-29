/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `Complex.norm_deriv_le_div_of_mapsTo_ball`. Let `f : ℂ → E` be a complex analytic function
  on an open disk with center `c` and a positive radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`.

* `Complex.dist_le_div_mul_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c` and radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.

* `Complex.norm_deriv_le_one_of_mapsTo_ball`. If `f : ℂ → E` is complex analytic
  on an open disk with center `c` and a positive radius `R₁`,
  and it sends this disk to a closed ball with center `f c` and radius the same radius,
  then the norm of the derivative of `f` at the center of this disk is at most `1`.

* `Complex.dist_le_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c`.
  If `f` sends this ball to a closed ball with center `f c` and the same radius,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.

* `Complex.norm_le_norm_of_mapsTo_ball`:
  Let `f : E → F` be a complex analytic on an open ball with center at the origin.
  If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
  then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`.

## Implementation notes

Traditionally, the Schwarz lemma is formulated for maps `f : ℂ → ℂ`.
We generalize all versions of the lemma to the case of maps to any normed space.
For the versions that don't use `deriv` or `dslope`,
we state it for maps between any two normed spaces.

## TODO

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open Metric Set Function Filter TopologicalSpace

open scoped Topology ComplexConjugate

namespace Complex

/--
theorem `schwarz_aux` / 定理 `schwarz_aux`

English:
theorem schwarz_aux
  statement: {f : Complex -> Complex} {c z : Complex} {R₁ R₂ : Real} {n : Nat}
  proof: by
  -- By slightly reducing `R₁`, we can assume that `f` is differentiable on `closedBall c R₁`
  -- and it maps this ball to the closed ball in the codomain.
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  wlog hd' : DifferentiableOn Complex f (closedBall c R₁) ∧
    MapsTo f (closedBall c R₁) (c

中文:
定理 schwarz_aux
  结论: {f : Complex -> Complex} {c z : Complex} {R₁ R₂ : 实数} {n : 自然数}
  证明: by
  -- By slightly reducing `R₁`, we can assume that `f` is differentiable on `closedBall c R₁`
  -- and it maps this ball to the closed ball in the codomain.
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  wlog hd' : DifferentiableOn Complex f (closedBall c R₁) ∧
    MapsTo f (closedBall c R₁) (c
-/
theorem schwarz_aux {f : Complex -> Complex} {c z : Complex} {R₁ R₂ : Real} {n : Nat}
    (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w => (w - c) ^ n)) (hz : z in ball c R₁) :
    ‖f z - f c‖ <= R₂ * (‖z - c‖ / R₁) ^ (n + 1) := by
  -- By slightly reducing `R₁`, we can assume that `f` is differentiable on `closedBall c R₁`
  -- and it maps this ball to the closed ball in the codomain.
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  wlog hd' : DifferentiableOn Complex f (closedBall c R₁) ∧
    MapsTo f (closedBall c R₁) (closedBall (f c) R₂) generalizing R₁
  · suffices forallᶠ r in 𝓝[<] R₁, ‖f z - f c‖ <= R₂ * (‖z - c‖ / r) ^ (n + 1) by
      refine ge_of_tendsto ?_ this
      refine ContinuousAt.continuousWithinAt ?_
      fun_prop (disch := positivity)
    rw [mem_ball_iff_norm] at hz
    filter_upwards [Ioo_mem_nhdsLT hz] with r ⟨hzr, hrR₁⟩
    apply this
· exact hd.mono by gcongr
· exact h_maps.mono_left by gcongr
    · rwa [mem_ball_iff_norm]
    · exact (norm_nonneg _).trans_lt hzr
· exact ⟨hd.mono closedBall_subset_ball hrR₁, h_maps.mono_left
        closedBall_subset_ball hrR₁⟩
  -- Cleanup, discard the case `z = c`.
  clear hd h_maps
  rcases hd' with ⟨hd, h_maps⟩
  rcases eq_or_ne z c with rfl | hne
  · simp
  -- Consider the function given by `g w := ((w - c) ^ (n + 1))⁻¹ * (f w - f c)`.
  -- It is differentiable away from `c` and satisfies `g w = o((w - c)⁻¹)`,
  -- thus it can be extended to a function g'` differentiable on the whole closed ball
  -- with center c` and radius `R₁`.
  set g : Complex -> Complex := fun w => ((w - c) ^ (n + 1))⁻¹ * (f w - f c)
  set g' := update g c (limUnder (𝓝[!=] c) g)
  have hdg' : DifferentiableOn Complex g' (closedBall c R₁) := by
    refine .mono ?_ (subset_insert_sdiff_singleton c _)
    apply differentiableOn_update_limUnder_insert_of_isLittleO
    · exact sdiff_mem_nhdsWithin_compl (closedBall_mem_nhds _ hR₁) _
    · refine .mul ?_ (hd.mono sdiff_subset |>.sub_const _)
      fun_prop (disch := simp +contextual [sub_eq_zero])
.mul_isLittleO hn · refine Asymptotics.isBigO_refl (fun w => ((w - c) ^ (n + 1))⁻¹) _
.congr' ?_ ?_ .mono (nhdsWithin_le_nhds (s := {c}ᶜ))
      · simp [g]
      · refine eventually_mem_nhdsWithin.mono fun w hw => ?_
        rw [mem_compl_singleton_iff]; rw [← sub_ne_zero] at hw
        simp [pow_succ, field]
  -- Finally, we apply the maximum modulus principle to this function.
  -- On the sphere `dist w c = R₁`, its norm is bounded by `R₂ / R₁ ^ (n + 1)`,
  -- thus it's bounded by the same constant on the whole closed ball,
  -- in particular, at `w = z`.
  suffices ‖g' z‖ <= R₂ / R₁ ^ (n + 1) by
    have hz' : ‖z - c‖ != 0 := by simpa [sub_eq_zero] using hne
    simpa [g', hne, g, div_pow, mul_comm, field] using this
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdg'.diffContOnCl_ball subset_rfl)
    ?_ ?_
  · grw [frontier_ball_subset_sphere]
    intro w hw
    have hwc := ne_of_mem_sphere hw hR₁.ne'
    have hfw : ‖f w - f c‖ <= R₂ := by
      simpa [dist_eq_norm] using h_maps (sphere_subset_closedBall hw)
    rw [mem_sphere_iff_norm] at hw
    simpa [g', hwc, g, hw, field]
  · exact subset_closure hz

public section

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Complex E] [NormedAddCommGroup F] [NormedSpace Complex F]
  {R R₁ R₂ : Real} {f : E -> F} {c z : E}

set_option backward.isDefEq.respectTransparency.types false in
open AffineMap in
/--
theorem `dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO` / 定理 `dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`

English:
theorem dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
  statement: {f : E -> F} {c z : E} {R₁ R₂ : Real} {n : Nat}
  proof: by
  -- Note that `0 < R₁`, `0 ≤ R₂`, then discard the trivial case `f z = f c`.
  have hR₁ : 0 < R₁ := nonempty_ball.mp ⟨_, hz⟩
  have hR₂ : 0 <= R₂ := nonempty_closedBall.mp ⟨_, h_maps hz⟩
  rcases eq_or_ne (f z) (f c) with heq | hfne
  · trans 0 <;> [simp [heq]; positivity]
  have hne : z != c :=

中文:
定理 dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
  结论: {f : E -> F} {c z : E} {R₁ R₂ : 实数} {n : 自然数}
  证明: by
  -- Note that `0 < R₁`, `0 ≤ R₂`, then discard the trivial case `f z = f c`.
  have hR₁ : 0 < R₁ := nonempty_ball.mp ⟨_, hz⟩
  have hR₂ : 0 <= R₂ := nonempty_closedBall.mp ⟨_, h_maps hz⟩
  rcases eq_or_ne (f z) (f c) with heq | hfne
  · trans 0 <;> [simp [heq]; positivity]
  have hne : z != c :=
-/
theorem dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO {f : E -> F} {c z : E} {R₁ R₂ : Real} {n : Nat}
    (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w => ‖w - c‖ ^ n)) (hz : z in ball c R₁) :
    dist (f z) (f c) <= R₂ * (dist z c / R₁) ^ (n + 1) := by
  -- Note that `0 < R₁`, `0 ≤ R₂`, then discard the trivial case `f z = f c`.
  have hR₁ : 0 < R₁ := nonempty_ball.mp ⟨_, hz⟩
  have hR₂ : 0 <= R₂ := nonempty_closedBall.mp ⟨_, h_maps hz⟩
  rcases eq_or_ne (f z) (f c) with heq | hfne
  · trans 0 <;> [simp [heq]; positivity]
  have hne : z != c := ne_of_apply_ne _ hfne
  -- Let `g : F → ℂ` be a continuous linear function such that `‖g‖ = 1`
  -- and `‖g (f z - f c)‖ = ‖f z - f c‖`.
  rcases exists_dual_vector Complex _ (norm_sub_eq_zero_iff.not.mpr hfne) with ⟨g, hg, hgf⟩
  -- Consider `h : ℂ → ℂ` given by `h w = g (f (c + w * (z - c)))`.
  set h : Complex -> Complex := g ∘ f ∘ lineMap c z
  -- This map is differentiable on the ball with center at the origin and radius `R₁ / dist z c`
  -- and it sends this ball to the closed ball with center `h 0 = f c` and radius R₂`.
  have hmaps_line : MapsTo (lineMap c z) (ball (0 : Complex) (R₁ / dist z c)) (ball c R₁) := by
    intro w hw
    simpa [lt_div_iff₀, hne, dist_comm c] using hw
  have hmaps : MapsTo h (ball 0 (R₁ / dist z c)) (closedBall (h 0) R₂) := by
    refine MapsTo.comp ?_ (h_maps.comp hmaps_line)
    simpa [hg, h] using g.lipschitz.mapsTo_closedBall (f c) R₂
  have hdiff : DifferentiableOn Complex h (ball 0 (R₁ / dist z c)) :=
g.differentiable.comp_differentiableOn hd.comp (lineMap c z).differentiableOn hmaps_line
  -- This map also satisfies `h(w) - h(0) = o(w ^ n)`, thus we can apply the auxiliary lemma above.
  have hn : (h · - h 0) =o[𝓝 0] (fun w => (w - 0) ^ n) := by
    simp only [h, ← map_sub, Function.comp_apply, sub_zero]
    refine (g.isBigO_comp _ _).trans_isLittleO ?_
    rw [← lineMap_apply_zero (k := Complex) c z] at hn
.trans_isBigO ?_ refine hn.comp_tendsto ?_
    · exact Continuous.tendsto (by fun_prop) 0
    · simpa [Function.comp_def, ← dist_eq_norm_sub, mul_pow, mul_comm]
        using (Asymptotics.isBigO_refl (· ^ n) (𝓝 (0 : Complex))).norm_left.const_mul_left _
  have hmem : 1 in ball (0 : Complex) (R₁ / dist z c) := by
    simpa [lt_div_iff₀, hne]
  rw [map_sub] at hgf
  simpa [hgf, h, dist_eq_norm_sub] using schwarz_aux hdiff hmaps hn hmem

/--
theorem `dist_le_div_mul_dist_of_mapsTo_ball` / 定理 `dist_le_div_mul_dist_of_mapsTo_ball`

English:
theorem dist_le_div_mul_dist_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R₁))
  proof: by
.trans_eq ?_ refine dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 0) hd h_maps ?_ hz
  · simpa using hd.continuousOn.continuousAt
.sub_const (f c) (ball_mem_nhds _ <| nonempty_ball.mp ⟨_, hz⟩)
  · simp [field]

中文:
定理 dist_le_div_mul_dist_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R₁))
  证明: by
.trans_eq ?_ refine dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 0) hd h_maps ?_ hz
  · simpa using hd.continuousOn.continuousAt
.sub_const (f c) (ball_mem_nhds _ <| nonempty_ball.mp ⟨_, hz⟩)
  · simp [field]

Depends on / 依赖: ball_mem_nhds, continuousAt, continuousOn, dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO, h_maps, hd.continuousOn.continuousAt, nonempty_ball, nonempty_ball.mp, sub_const, trans_eq
-/
theorem dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z in ball c R₁) :
    dist (f z) (f c) <= R₂ / R₁ * dist z c := by
.trans_eq ?_ refine dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 0) hd h_maps ?_ hz
  · simpa using hd.continuousOn.continuousAt
.sub_const (f c) (ball_mem_nhds _ <| nonempty_ball.mp ⟨_, hz⟩)
  · simp [field]

/--
theorem `norm_fderiv_le_div_of_mapsTo_ball` / 定理 `norm_fderiv_le_div_of_mapsTo_ball`

English:
theorem norm_fderiv_le_div_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R₁))
  proof: by
have : 0 <= R₂ := nonempty_closedBall.mp h_maps.nonempty nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

中文:
定理 norm_fderiv_le_div_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R₁))
  证明: by
have : 0 <= R₂ := nonempty_closedBall.mp h_maps.nonempty nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

Depends on / 依赖: ball_mem_nhds, dist_eq_norm_sub, dist_le_div_mul_dist_of_mapsTo_ball, filter_upwards, h_maps, h_maps.nonempty, nonempty, nonempty_ball, nonempty_ball.mpr, nonempty_closedBall, nonempty_closedBall.mp, norm_fderiv_le_of_lip
-/
theorem norm_fderiv_le_div_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖fderiv Complex f c‖ <= R₂ / R₁ := by
have : 0 <= R₂ := nonempty_closedBall.mp h_maps.nonempty nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

/--
theorem `dist_le_dist_of_mapsTo_ball` / 定理 `dist_le_dist_of_mapsTo_ball`

English:
theorem dist_le_dist_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R))
  proof: by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

@[deprecated (since := "2026-01-03")]
alias dist_le_dist_of_mapsTo_ball_self := dist_le_dist_of_mapsTo_ball

中文:
定理 dist_le_dist_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R))
  证明: by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

@[deprecated (since := "2026-01-03")]
alias dist_le_dist_of_mapsTo_ball_self := dist_le_dist_of_mapsTo_ball

Depends on / 依赖: dist_le_div_mul_dist_of_mapsTo_ball, h_maps, nonempty_ball
-/
theorem dist_le_dist_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hz : z in ball c R) :
    dist (f z) (f c) <= dist z c := by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

@[deprecated (since := "2026-01-03")]
alias dist_le_dist_of_mapsTo_ball_self := dist_le_dist_of_mapsTo_ball

/--
theorem `norm_fderiv_le_one_of_mapsTo_ball` / 定理 `norm_fderiv_le_one_of_mapsTo_ball`

English:
theorem norm_fderiv_le_one_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R))
  proof: by
  simpa [hR.ne'] using norm_fderiv_le_div_of_mapsTo_ball hd h_maps hR

中文:
定理 norm_fderiv_le_one_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R))
  证明: by
  simpa [hR.ne'] using norm_fderiv_le_div_of_mapsTo_ball hd h_maps hR

Depends on / 依赖: hR.ne, h_maps, norm_fderiv_le_div_of_mapsTo_ball
-/
theorem norm_fderiv_le_one_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hR : 0 < R) :
    ‖fderiv Complex f c‖ <= 1 := by
  simpa [hR.ne'] using norm_fderiv_le_div_of_mapsTo_ball hd h_maps hR

/--
theorem `norm_le_norm_of_mapsTo_ball` / 定理 `norm_le_norm_of_mapsTo_ball`

English:
theorem norm_le_norm_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball 0 R))
  proof: by
  simpa [h₀] using dist_le_dist_of_mapsTo_ball hd (by rwa [h₀]) (mem_ball_zero_iff.mpr hz)

@[deprecated (since := "2026-01-03")]
alias norm_le_norm_of_mapsTo_ball_self := norm_le_norm_of_mapsTo_ball

中文:
定理 norm_le_norm_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball 0 R))
  证明: by
  simpa [h₀] using dist_le_dist_of_mapsTo_ball hd (by rwa [h₀]) (mem_ball_zero_iff.mpr hz)

@[deprecated (since := "2026-01-03")]
alias norm_le_norm_of_mapsTo_ball_self := norm_le_norm_of_mapsTo_ball

Depends on / 依赖: dist_le_dist_of_mapsTo_ball, mem_ball_zero_iff, mem_ball_zero_iff.mpr
-/
theorem norm_le_norm_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball 0 R))
    (h_maps : MapsTo f (ball 0 R) (closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ <= ‖z‖ := by
  simpa [h₀] using dist_le_dist_of_mapsTo_ball hd (by rwa [h₀]) (mem_ball_zero_iff.mpr hz)

@[deprecated (since := "2026-01-03")]
alias norm_le_norm_of_mapsTo_ball_self := norm_le_norm_of_mapsTo_ball

end NormedSpace

section DimOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {R R₁ R₂ : Real} {f : Complex -> E}
  {c z z₀ : Complex}

/--
theorem `norm_deriv_le_div_of_mapsTo_ball` / 定理 `norm_deriv_le_div_of_mapsTo_ball`

English:
theorem norm_deriv_le_div_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R₁))
  proof: by
  rw [norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_le_div_of_mapsTo_ball hd h_maps h₀

中文:
定理 norm_deriv_le_div_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R₁))
  证明: by
  rw [norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_le_div_of_mapsTo_ball hd h_maps h₀

Depends on / 依赖: h_maps, norm_deriv_eq_norm_fderiv, norm_fderiv_le_div_of_mapsTo_ball
-/
theorem norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖deriv f c‖ <= R₂ / R₁ := by
  rw [norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_le_div_of_mapsTo_ball hd h_maps h₀

/--
theorem `norm_deriv_le_one_of_mapsTo_ball` / 定理 `norm_deriv_le_one_of_mapsTo_ball`

English:
theorem norm_deriv_le_one_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R))
  proof: (norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀).trans_eq (div_self h₀.ne')

中文:
定理 norm_deriv_le_one_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R))
  证明: (norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀).trans_eq (div_self h₀.ne')

Depends on / 依赖: div_self, h_maps, norm_deriv_le_div_of_mapsTo_ball, trans_eq
-/
theorem norm_deriv_le_one_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (h₀ : 0 < R) : ‖deriv f c‖ <= 1 :=
  (norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀).trans_eq (div_self h₀.ne')

/--
theorem `norm_dslope_le_div_of_mapsTo_ball` / 定理 `norm_dslope_le_div_of_mapsTo_ball`

English:
theorem norm_dslope_le_div_of_mapsTo_ball
  statement: (hd : DifferentiableOn Complex f (ball c R₁))
  proof: by
  rcases eq_or_ne z c with rfl | hne
  · simpa using norm_deriv_le_div_of_mapsTo_ball hd h_maps (by simpa using hz)
  · rw [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, ← dist_eq_norm_sub,
      ← dist_eq_norm_sub, ← div_eq_inv_mul, div_le_iff₀]
    · exact dist_le_div_mul_dist_of_m

中文:
定理 norm_dslope_le_div_of_mapsTo_ball
  结论: (hd : DifferentiableOn Complex f (ball c R₁))
  证明: by
  rcases eq_or_ne z c with rfl | hne
  · simpa using norm_deriv_le_div_of_mapsTo_ball hd h_maps (by simpa using hz)
  · rw [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, ← dist_eq_norm_sub,
      ← dist_eq_norm_sub, ← div_eq_inv_mul, div_le_iff₀]
    · exact dist_le_div_mul_dist_of_m

Depends on / 依赖: dist_eq_norm_sub, dist_le_div_mul_dist_of_mapsTo_ball, div_eq_inv_mul, dslope_of_ne, eq_or_ne, h_maps, norm_deriv_le_div_of_mapsTo_ball, norm_inv, norm_smul, slope_def_module
-/
theorem norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z in ball c R₁) :
    ‖dslope f c z‖ <= R₂ / R₁ := by
  rcases eq_or_ne z c with rfl | hne
  · simpa using norm_deriv_le_div_of_mapsTo_ball hd h_maps (by simpa using hz)
  · rw [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, ← dist_eq_norm_sub,
      ← dist_eq_norm_sub, ← div_eq_inv_mul, div_le_iff₀]
    · exact dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz
    · simpa

/--
theorem `affine_of_mapsTo_ball_of_norm_dslope_eq_div` / 定理 `affine_of_mapsTo_ball_of_norm_dslope_eq_div`

English:
theorem affine_of_mapsTo_ball_of_norm_dslope_eq_div
  statement: [StrictConvexSpace Real E]
  proof: by
  set e : E ->L[Complex] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  set g := dslope (e ∘ f) c
  rintro z hz
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have hg' : g = e ∘ dslope f c := by
    ext w
    simp only [g]
    rw [e.dslope_comp]; rw [Function.comp_apply]
  

中文:
定理 affine_of_mapsTo_ball_of_norm_dslope_eq_div
  结论: [StrictConvexSpace 实数 E]
  证明: by
  set e : E ->L[Complex] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  set g := dslope (e ∘ f) c
  rintro z hz
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have hg' : g = e ∘ dslope f c := by
    ext w
    simp only [g]
    rw [e.dslope_comp]; rw [Function.comp_apply]
  

Depends on / 依赖: Completion, Function, Function.comp_apply, UniformSpace, UniformSpace.Completion, UniformSpace.Completion.toComplL, ball_mem_nhds, comp_apply, comp_differentiableOn, differentiable, differentiableAt, dslope, dslope_comp, e.differentiable.comp_differentiableOn, e.dslope_comp, g_le_div, hd.differentiableAt, nonempty_ball, nonempty_ball.mp, norm_dslope_le_div_of_mapsTo_ball
-/
theorem affine_of_mapsTo_ball_of_norm_dslope_eq_div [StrictConvexSpace Real E]
    (hd : DifferentiableOn Complex f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : z₀ in ball c R₁) (h_eq : ‖dslope f c z₀‖ = R₂ / R₁) :
    Set.EqOn f (fun z => f c + (z - c) • dslope f c z₀) (ball c R₁) := by
  set e : E ->L[Complex] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  set g := dslope (e ∘ f) c
  rintro z hz
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have hg' : g = e ∘ dslope f c := by
    ext w
    simp only [g]
    rw [e.dslope_comp]; rw [Function.comp_apply]
    rintro rfl
exact hd.differentiableAt ball_mem_nhds _ h_R₁
  have g_le_div : forall z in ball c R₁, ‖g z‖ <= R₂ / R₁ := fun z hz =>
    norm_dslope_le_div_of_mapsTo_ball (e.differentiable.comp_differentiableOn hd)
      (fun w hw => by simpa [e] using h_maps hw) hz
  have g_max : IsMaxOn (norm ∘ g) (ball c R₁) z₀ :=
    isMaxOn_iff.mpr fun z hz => by simpa [h_eq, hg', e] using g_le_div z hz
  have g_diff : DifferentiableOn Complex g (ball c R₁) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self h_R₁))).mpr
      (e.differentiable.comp_differentiableOn hd)
  have heq : ‖dslope f c z‖ = ‖dslope f c z₀‖ := by
    simpa [hg', e] using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
      isOpen_ball g_diff h_z₀ g_max hz
  have heq_add : ‖dslope f c z + dslope f c z₀‖ = ‖dslope f c z₀ + dslope f c z₀‖ := by
    simpa [hg', e, ← UniformSpace.Completion.coe_add]
      using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
        isOpen_ball (g_diff.add_const (g z₀)) h_z₀ g_max.norm_add_self hz
have : dslope f c z = dslope f c z₀ := eq_of_norm_eq_of_norm_add_eq heq by
    simp only [heq, SameRay.rfl.norm_add, heq_add]
  simp [← this]

@[deprecated (since := "2026-01-03")]
alias affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div :=
  affine_of_mapsTo_ball_of_norm_dslope_eq_div

/--
theorem `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'` / 定理 `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'`

English:
theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
  proof: let ⟨z₀, h_z₀, h_eq⟩ := h_z₀
  ⟨dslope f c z₀, h_eq, affine_of_mapsTo_ball_of_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

中文:
定理 affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
  证明: let ⟨z₀, h_z₀, h_eq⟩ := h_z₀
  ⟨dslope f c z₀, h_eq, affine_of_mapsTo_ball_of_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

Depends on / 依赖: affine_of_mapsTo_ball_of_norm_dslope_eq_div, dslope, h_eq, h_maps
-/
theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
    [StrictConvexSpace Real E] (hd : DifferentiableOn Complex f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : exists z₀ in ball c R₁, ‖dslope f c z₀‖ = R₂ / R₁) :
    exists C : E, ‖C‖ = R₂ / R₁ ∧ Set.EqOn f (fun z => f c + (z - c) • C) (ball c R₁) :=
  let ⟨z₀, h_z₀, h_eq⟩ := h_z₀
  ⟨dslope f c z₀, h_eq, affine_of_mapsTo_ball_of_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

end DimOne

end -- public section

end Complex
