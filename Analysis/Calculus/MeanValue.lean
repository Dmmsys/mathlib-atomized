/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `Convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `RCLike`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `‖f x‖ ≤ B x` from upper estimates on `f'` or `‖f'‖`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `‖f x‖ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `‖f x - f a‖ ≤ C * ‖x - a‖`; several versions deal with
  right derivative and derivative within `[a, b]` (`HasDerivWithinAt` or `derivWithin`).

* `Convex.is_const_of_fderivWithin_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` : a C^1 function over the reals is
  strictly differentiable. (This is a corollary of the mean value inequality.)
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace Real F]

open Metric Set Asymptotics ContinuousLinearMap Filter

open scoped Topology NNReal

/-! ### One-dimensional fencing inequalities -/


/--
theorem `image_le_of_liminf_slope_right_lt_deriv_boundary'` / 定理 `image_le_of_liminf_slope_right_lt_deriv_boundary'`

English:
theorem image_le_of_liminf_slope_right_lt_deriv_boundary'
  statement: {f f' : Real -> Real} {a b : Real}
  proof: by
  change Icc a b subseteq { x | f x <= B x }
  set s := { x | f x <= B x } inter Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClo

中文:
定理 image_le_of_liminf_slope_right_lt_deriv_boundary'
  结论: {f f' : 实数 -> 实数} {a b : 实数}
  证明: by
  change Icc a b subseteq { x | f x <= B x }
  set s := { x | f x <= B x } inter Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClo

Depends on / 依赖: A.preimage_isClosed_of_isClosed, ContinuousOn, Icc_subset_of_forall_exists_gt, IsClosed, OrderClosedTopology, OrderClosedTopology.isClosed_le, continuity, hf.prodMk, hxB.lt_or_eq, inter_comm, isClosed_Icc, isClosed_le, lt_or_eq, nonempty_of_mem, preimage_isClosed_of_isClosed, prodMk, subseteq, this.Icc_subset_of_forall_exists_gt
-/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : forall x in Ico a b, forall r, f' x < r -> existsᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : Real -> Real} (ha : f a <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : forall x in Ico a b, f x = B x -> f' x < B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B x := by
  change Icc a b subseteq { x | f x <= B x }
  set s := { x | f x <= B x } inter Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x <= B x, xab⟩ y hy
  rcases hxB.lt_or_eq with hxB | hxB
  · -- If `f x < B x`, then all we need is continuity of both sides
    refine nonempty_of_mem (inter_mem ?_ (Ioc_mem_nhdsGT hy))
    have : forallᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hxB)
    have : forallᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
    exact this.mono fun y => le_of_lt
  · rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩
    specialize hf' x xab r hfr
    have HB : forallᶠ z in 𝓝[>] x, r < slope B x z :=
      (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
        (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : exists z, slope f x z < r ∧ r < slope B x z ∧ z in Ioc x y :=
.exists hf'.and_eventually (HB.and (Ioc_mem_nhdsGT hy))
    refine ⟨z, ?_, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this

/--
theorem `image_le_of_liminf_slope_right_lt_deriv_boundary` / 定理 `image_le_of_liminf_slope_right_lt_deriv_boundary`

English:
theorem image_le_of_liminf_slope_right_lt_deriv_boundary
  statement: {f f' : Real -> Real} {a b : Real}
  proof: image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

中文:
定理 image_le_of_liminf_slope_right_lt_deriv_boundary
  结论: {f f' : 实数 -> 实数} {a b : 实数}
  证明: image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hasDerivWithinAt, image_le_of_liminf_slope_right_lt_deriv_boundary
-/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : Real -> Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : forall x in Ico a b, forall r, f' x < r -> existsᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : Real -> Real} (ha : f a <= B a) (hB : forall x, HasDerivAt B (B' x) x)
    (bound : forall x in Ico a b, f x = B x -> f' x < B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/--
theorem `image_le_of_liminf_slope_right_le_deriv_boundary` / 定理 `image_le_of_liminf_slope_right_le_deriv_boundary`

English:
theorem image_le_of_liminf_slope_right_le_deriv_boundary
  statement: {f : Real -> Real} {a b : Real}
  proof: by
  have Hr : forall x in Icc a b, forall r > 0, f x <= B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · i

中文:
定理 image_le_of_liminf_slope_right_le_deriv_boundary
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: by
  have Hr : forall x in Icc a b, forall r > 0, f x <= B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · i

Depends on / 依赖: ContinuousWithinAt, add_zero, const_mul, continuousOn_const, continuousOn_const.mul, continuousOn_id, continuousOn_id.sub, hB.add, hasDerivWithinAt_id, image_le_of_liminf_slope_right_lt_deriv_boundary, lt_add_iff_pos_right, mul_one, mul_zero, sub_const, sub_self
-/
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : Real -> Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b)) {B B' : Real -> Real} (ha : f a <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    -- `bound` actually says `liminf (f z - f x) / (z - x) ≤ B' x`
    (bound : forall x in Ico a b, forall r, B' x < r -> existsᶠ z in 𝓝[>] x, slope f x z < r) :
    forall ⦃x⦄, x in Icc a b -> f x <= B x := by
  have Hr : forall x in Icc a b, forall r > 0, f x <= B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      exact (hB' x hx).add (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul r)
    · intro x _ _
      rw [mul_one]
      exact (lt_add_iff_pos_right _).2 hr
    exact hx
  intro x hx
  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 := by fun_prop
  convert! continuousWithinAt_const.closure_le _ this (Hr x hx) using 1 <;> simp

/--
theorem `image_le_of_deriv_right_lt_deriv_boundary'` / 定理 `image_le_of_deriv_right_lt_deriv_boundary'`

English:
theorem image_le_of_deriv_right_lt_deriv_boundary'
  statement: {f f' : Real -> Real} {a b : Real}
  proof: image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

中文:
定理 image_le_of_deriv_right_lt_deriv_boundary'
  结论: {f f' : 实数 -> 实数} {a b : 实数}
  证明: image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

Depends on / 依赖: image_le_of_liminf_slope_right_lt_deriv_boundary, liminf_right_slope_le
-/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : Real -> Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : f a <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : forall x in Ico a b, f x = B x -> f' x < B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

/--
theorem `image_le_of_deriv_right_lt_deriv_boundary` / 定理 `image_le_of_deriv_right_lt_deriv_boundary`

English:
theorem image_le_of_deriv_right_lt_deriv_boundary
  statement: {f f' : Real -> Real} {a b : Real}
  proof: image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

中文:
定理 image_le_of_deriv_right_lt_deriv_boundary
  结论: {f f' : 实数 -> 实数} {a b : 实数}
  证明: image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hasDerivWithinAt, image_le_of_deriv_right_lt_deriv_boundary
-/
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : Real -> Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : f a <= B a) (hB : forall x, HasDerivAt B (B' x) x)
    (bound : forall x in Ico a b, f x = B x -> f' x < B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/--
theorem `image_le_of_deriv_right_le_deriv_boundary` / 定理 `image_le_of_deriv_right_le_deriv_boundary`

English:
theorem image_le_of_deriv_right_le_deriv_boundary
  statement: {f f' : Real -> Real} {a b : Real}
  proof: image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

中文:
定理 image_le_of_deriv_right_le_deriv_boundary
  结论: {f f' : 实数 -> 实数} {a b : 实数}
  证明: image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

Depends on / 依赖: image_le_of_liminf_slope_right_le_deriv_boundary, liminf_right_slope_le, lt_of_le_of_lt
-/
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : Real -> Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : f a <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : forall x in Ico a b, f' x <= B' x) : forall ⦃x⦄, x in Icc a b -> f x <= B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/


section

variable {f : Real -> E} {a b : Real}

/--
theorem `image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary` / 定理 `image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary`

English:
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary
  statement: {E : Type*}
  proof: image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound

中文:
定理 image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary
  结论: {E : 类型}
  证明: image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound

Depends on / 依赖: comp_continuousOn, continuous_norm, continuous_norm.comp_continuousOn, image_le_of_liminf_slope_right_lt_deriv_boundary
-/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*}
    [NormedAddCommGroup E] {f : Real -> E} {f' : Real -> Real} (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (‖f z‖ - ‖f x‖) / (z - x) ≤ f' x`
    (hf' : forall x in Ico a b, forall r, f' x < r -> existsᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r)
    {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : forall x in Ico a b, ‖f x‖ = B x -> f' x < B' x) : forall ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound

/--
theorem `image_norm_le_of_norm_deriv_right_lt_deriv_boundary'` / 定理 `image_norm_le_of_norm_deriv_right_lt_deriv_boundary'`

English:
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
  statement: {f' : Real -> E}
  proof: image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

中文:
定理 image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
  结论: {f' : 实数 -> E}
  证明: image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

Depends on / 依赖: image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary, liminf_right_slope_norm_le
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : Real -> E}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : forall x in Ico a b, ‖f x‖ = B x -> ‖f' x‖ < B' x) : forall ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/--
theorem `image_norm_le_of_norm_deriv_right_lt_deriv_boundary` / 定理 `image_norm_le_of_norm_deriv_right_lt_deriv_boundary`

English:
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary
  statement: {f' : Real -> E}
  proof: image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

中文:
定理 image_norm_le_of_norm_deriv_right_lt_deriv_boundary
  结论: {f' : 实数 -> E}
  证明: image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hasDerivWithinAt, image_norm_le_of_norm_deriv_right_lt_deriv_boundary
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : Real -> E}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : forall x, HasDerivAt B (B' x) x)
    (bound : forall x in Ico a b, ‖f x‖ = B x -> ‖f' x‖ < B' x) : forall ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/--
theorem `image_norm_le_of_norm_deriv_right_le_deriv_boundary'` / 定理 `image_norm_le_of_norm_deriv_right_le_deriv_boundary'`

English:
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary'
  statement: {f' : Real -> E}
  proof: image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)

中文:
定理 image_norm_le_of_norm_deriv_right_le_deriv_boundary'
  结论: {f' : 实数 -> E}
  证明: image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)

Depends on / 依赖: comp_continuousOn, continuous_norm, continuous_norm.comp_continuousOn, image_le_of_liminf_slope_right_le_deriv_boundary, liminf_right_slope_norm_le, trans_lt
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : Real -> E}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : ContinuousOn B (Icc a b))
    (hB' : forall x in Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : forall x in Ico a b, ‖f' x‖ <= B' x) : forall ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)

/--
theorem `image_norm_le_of_norm_deriv_right_le_deriv_boundary` / 定理 `image_norm_le_of_norm_deriv_right_le_deriv_boundary`

English:
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary
  statement: {f' : Real -> E}
  proof: image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

中文:
定理 image_norm_le_of_norm_deriv_right_le_deriv_boundary
  结论: {f' : 实数 -> E}
  证明: image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hasDerivWithinAt, image_norm_le_of_norm_deriv_right_le_deriv_boundary
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : Real -> E}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : Real -> Real} (ha : ‖f a‖ <= B a) (hB : forall x, HasDerivAt B (B' x) x)
    (bound : forall x in Ico a b, ‖f' x‖ <= B' x) : forall ⦃x⦄, x in Icc a b -> ‖f x‖ <= B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/--
theorem `norm_image_sub_le_of_norm_deriv_right_le_segment` / 定理 `norm_image_sub_le_of_norm_deriv_right_le_segment`

English:
theorem norm_image_sub_le_of_norm_deriv_right_le_segment
  statement: {f' : Real -> E} {C : Real}
  proof: by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuousOn_const
  have hg' : forall x in Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simp [g, hf' x hx]
  let B x := C * (x - a)
  have hB : forall x, HasDerivAt B C x := by
    intro x
    simpa us

中文:
定理 norm_image_sub_le_of_norm_deriv_right_le_segment
  结论: {f' : 实数 -> E} {C : 实数}
  证明: by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuousOn_const
  have hg' : forall x in Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simp [g, hf' x hx]
  let B x := C * (x - a)
  have hB : forall x, HasDerivAt B C x := by
    intro x
    simpa us

Depends on / 依赖: ContinuousOn, HasDerivAt, HasDerivWithinAt, continuousOn_const, convert, hasDerivAt_const, hasDerivAt_id, hf.sub, image_norm_le_of_norm_deriv_right_le_deriv_boundary, mul_zero, norm_zero, sub_self
-/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : Real -> E} {C : Real}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (bound : forall x in Ico a b, ‖f' x‖ <= C) : forall x in Icc a b, ‖f x - f a‖ <= C * (x - a) := by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuousOn_const
  have hg' : forall x in Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simp [g, hf' x hx]
  let B x := C * (x - a)
  have hB : forall x, HasDerivAt B C x := by
    intro x
    simpa using! (hasDerivAt_const x C).mul ((hasDerivAt_id x).sub (hasDerivAt_const x a))
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound
  simp only [g, B]; rw [sub_self, norm_zero, sub_self, mul_zero]

/--
theorem `norm_image_sub_le_of_norm_deriv_le_segment'` / 定理 `norm_image_sub_le_of_norm_deriv_le_segment'`

English:
theorem norm_image_sub_le_of_norm_deriv_le_segment'
  statement: {f' : Real -> E} {C : Real}
  proof: by
  refine
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => ?_) bound
  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

中文:
定理 norm_image_sub_le_of_norm_deriv_le_segment'
  结论: {f' : 实数 -> E} {C : 实数}
  证明: by
  refine
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => ?_) bound
  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

Depends on / 依赖: Icc_mem_nhdsGE_of_mem, Ico_subset_Icc_self, continuousWithinAt, mono_of_mem_nhdsWithin, norm_image_sub_le_of_norm_deriv_right_le_segment
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : Real -> E} {C : Real}
    (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : forall x in Ico a b, ‖f' x‖ <= C) : forall x in Icc a b, ‖f x - f a‖ <= C * (x - a) := by
  refine
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => ?_) bound
  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/--
theorem `norm_image_sub_le_of_norm_deriv_le_segment` / 定理 `norm_image_sub_le_of_norm_deriv_le_segment`

English:
theorem norm_image_sub_le_of_norm_deriv_le_segment
  statement: {C : Real} (hf : DifferentiableOn Real f (Icc a b))
  proof: by
  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt

中文:
定理 norm_image_sub_le_of_norm_deriv_le_segment
  结论: {C : 实数} (hf : DifferentiableOn 实数 f (Icc a b))
  证明: by
  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, norm_image_sub_le_of_norm_deriv_le_segment
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : Real} (hf : DifferentiableOn Real f (Icc a b))
    (bound : forall x in Ico a b, ‖derivWithin f (Icc a b) x‖ <= C) :
    forall x in Icc a b, ‖f x - f a‖ <= C * (x - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt

/--
theorem `norm_image_sub_le_of_norm_deriv_le_segment_01'` / 定理 `norm_image_sub_le_of_norm_deriv_le_segment_01'`

English:
theorem norm_image_sub_le_of_norm_deriv_le_segment_01'
  statement: {f' : Real -> E} {C : Real}
  proof: by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

中文:
定理 norm_image_sub_le_of_norm_deriv_le_segment_01'
  结论: {f' : 实数 -> E} {C : 实数}
  证明: by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

Depends on / 依赖: mul_one, norm_image_sub_le_of_norm_deriv_le_segment, right_mem_Icc, sub_zero, zero_le_one
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : Real -> E} {C : Real}
    (hf : forall x in Icc (0 : Real) 1, HasDerivWithinAt f (f' x) (Icc (0 : Real) 1) x)
    (bound : forall x in Ico (0 : Real) 1, ‖f' x‖ <= C) : ‖f 1 - f 0‖ <= C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/--
theorem `norm_image_sub_le_of_norm_deriv_le_segment_01` / 定理 `norm_image_sub_le_of_norm_deriv_le_segment_01`

English:
theorem norm_image_sub_le_of_norm_deriv_le_segment_01
  statement: {C : Real}
  proof: by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

中文:
定理 norm_image_sub_le_of_norm_deriv_le_segment_01
  结论: {C : 实数}
  证明: by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

Depends on / 依赖: mul_one, norm_image_sub_le_of_norm_deriv_le_segment, right_mem_Icc, sub_zero, zero_le_one
-/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : Real}
    (hf : DifferentiableOn Real f (Icc (0 : Real) 1))
    (bound : forall x in Ico (0 : Real) 1, ‖derivWithin f (Icc (0 : Real) 1) x‖ <= C) : ‖f 1 - f 0‖ <= C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

/--
theorem `constant_of_has_deriv_right_zero` / 定理 `constant_of_has_deriv_right_zero`

English:
theorem constant_of_has_deriv_right_zero
  statement: (hcont : ContinuousOn f (Icc a b))
  proof: by
  have : forall x in Icc a b, ‖f x - f a‖ <= 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this

中文:
定理 constant_of_has_deriv_right_zero
  结论: (hcont : ContinuousOn f (Icc a b))
  证明: by
  have : forall x in Icc a b, ‖f x - f a‖ <= 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this

Depends on / 依赖: hderiv, norm_image_sub_le_of_norm_deriv_right_le_segment, norm_le_zero_iff, norm_zero, norm_zero.le, sub_eq_zero, zero_mul
-/
theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
    (hderiv : forall x in Ico a b, HasDerivWithinAt f 0 (Ici x) x) : forall x in Icc a b, f x = f a := by
  have : forall x in Icc a b, ‖f x - f a‖ <= 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this

/--
theorem `constant_of_derivWithin_zero` / 定理 `constant_of_derivWithin_zero`

English:
theorem constant_of_derivWithin_zero
  statement: (hdiff : DifferentiableOn Real f (Icc a b))
  proof: by
  have H : forall x in Ico a b, ‖derivWithin f (Icc a b) x‖ <= 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx

中文:
定理 constant_of_derivWithin_zero
  结论: (hdiff : DifferentiableOn 实数 f (Icc a b))
  证明: by
  have H : forall x in Ico a b, ‖derivWithin f (Icc a b) x‖ <= 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx

Depends on / 依赖: derivWithin, hderiv, norm_image_sub_le_of_norm_deriv_le_segment, norm_le_zero_iff, sub_eq_zero, zero_mul
-/
theorem constant_of_derivWithin_zero (hdiff : DifferentiableOn Real f (Icc a b))
    (hderiv : forall x in Ico a b, derivWithin f (Icc a b) x = 0) : forall x in Icc a b, f x = f a := by
  have H : forall x in Ico a b, ‖derivWithin f (Icc a b) x‖ <= 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx

variable {f' g : Real -> E}

/--
theorem `eq_of_has_deriv_right_eq` / 定理 `eq_of_has_deriv_right_eq`

English:
theorem eq_of_has_deriv_right_eq
  statement: (derivf : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  proof: by
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using! (derivf y hy).sub (derivg y hy)

中文:
定理 eq_of_has_deriv_right_eq
  结论: (derivf : 对任意 x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  证明: by
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using! (derivf y hy).sub (derivg y hy)

Depends on / 依赖: constant_of_has_deriv_right_zero, derivf, derivg, fcont.sub, sub_eq_zero, sub_self
-/
theorem eq_of_has_deriv_right_eq (derivf : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (derivg : forall x in Ico a b, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
    (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : forall y in Icc a b, f y = g y := by
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using! (derivf y hy).sub (derivg y hy)

/--
theorem `eq_of_derivWithin_eq` / 定理 `eq_of_derivWithin_eq`

English:
theorem eq_of_derivWithin_eq
  statement: (fdiff : DifferentiableOn Real f (Icc a b))
  proof: by
  have A : forall y in Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  have B : forall y in Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y

中文:
定理 eq_of_derivWithin_eq
  结论: (fdiff : DifferentiableOn 实数 f (Icc a b))
  证明: by
  have A : forall y in Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  have B : forall y in Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y

Depends on / 依赖: HasDerivWithinAt, Icc_mem_nhdsGE_of_mem, continuousOn, derivWithin, eq_of_has_deriv_right_eq, fdiff.continuousOn, gdiff.c, hasDerivWithinAt, hasDerivWithinAt.mono_of_mem_nhdsWithin, hderiv, mem_Icc_of_Ico, mono_of_mem_nhdsWithin
-/
theorem eq_of_derivWithin_eq (fdiff : DifferentiableOn Real f (Icc a b))
    (gdiff : DifferentiableOn Real g (Icc a b))
    (hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) :
    forall y in Icc a b, f y = g y := by
  have A : forall y in Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  have B : forall y in Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y := fun y hy =>
    (gdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  exact eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuousOn
    gdiff.continuousOn hi

end

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]` to
achieve this result. For the domain `E` we also assume `[NormedSpace ℝ E]` to have a notion
of a `Convex` set. -/

section

namespace Convex

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f g : E -> G} {C : Real} {s : Set E} {x y : E} {f' g' : E -> E ->L[𝕜] G} {φ : E ->L[𝕜] G}

instance (priority := 100) : PathConnectedSpace 𝕜 := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
theorem `norm_image_sub_le_of_norm_hasFDerivWithin_le` / 定理 `norm_image_sub_le_of_norm_hasFDerivWithin_le`

English:
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real G := .restrictScalars Real 𝕜 G
  /- By composition with `AffineMap.lineMap x y`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We 

中文:
定理 norm_image_sub_le_of_norm_hasFDerivWithin_le
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real G := .restrictScalars Real 𝕜 G
  /- By composition with `AffineMap.lineMap x y`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We 

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, RCLike, rclike, restrictScalars
-/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
    (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖ <= C) (hs : Convex Real s)
    (xs : x in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖ := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real G := .restrictScalars Real 𝕜 G
  /- By composition with `AffineMap.lineMap x y`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We just have to check the differentiability of the composition and bounds on its derivative,
    which is straightforward but tedious for lack of automation. -/
  set g := (AffineMap.lineMap x y : Real -> E)
  have segm : MapsTo g (Icc 0 1 : Set Real) s := hs.mapsTo_lineMap xs ys
  have hD : forall t in Icc (0 : Real) 1,
      HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := fun t ht => by
    simpa using ((hf (g t) (segm ht)).restrictScalars Real).comp_hasDerivWithinAt _
      AffineMap.hasDerivWithinAt_lineMap segm
  have bound : forall t in Ico (0 : Real) 1, ‖f' (g t) (y - x)‖ <= C * ‖y - x‖ := fun t ht =>
    le_of_opNorm_le _ (bound _ <| segm <| Ico_subset_Icc_self ht) _
  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound

/--
theorem `lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` / 定理 `lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`

English:
theorem lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
  statement: {C : Real>=0}
  proof: by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in

中文:
定理 lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
  结论: {C : 实数>=0}
  证明: by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in

Depends on / 依赖: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le, lipschitzOnWith_iff_norm_sub_le, norm_image_sub_le_of_norm_hasFDerivWithin_le, x_in, y_in
-/
theorem lipschitzOnWith_of_nnnorm_hasFDerivWithin_le {C : Real>=0}
    (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖₊ <= C)
    (hs : Convex Real s) : LipschitzOnWith C f s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in

/--
theorem `exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt` / 定理 `exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt`

English:
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
  statement: (hs : Convex Real s)
  proof: by
  obtain ⟨ε, ε0, hε⟩ : exists ε > 0,
      ball x ε inter s subseteq { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K } :=
    mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine ⟨s inter ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ 

中文:
定理 exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
  结论: (hs : Convex 实数 s)
  证明: by
  obtain ⟨ε, ε0, hε⟩ : exists ε > 0,
      ball x ε inter s subseteq { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K } :=
    mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine ⟨s inter ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ 

Depends on / 依赖: HasFDerivWithinAt, ball_mem_nhds, convex_ball, eventually, gt_mem_nhds, hcont.nnnorm.eventually, hder.and, hs.inter, inter_comm, inter_mem_nhdsWithin, inter_subset_left, lipschitzOnWith_of_nnnorm_hasFDerivWithin_le, mem_nhdsWithin_iff, nnnorm, subseteq
-/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Convex Real s)
    {f : E -> G} (hder : forallᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (K : Real>=0) (hK : ‖f' x‖₊ < K) :
    exists t in 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨ε, ε0, hε⟩ : exists ε > 0,
      ball x ε inter s subseteq { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K } :=
    mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine ⟨s inter ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ ε0), ?_⟩
  exact
    (hs.inter (convex_ball _ _)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun y hy => (hε hy).1.mono inter_subset_left) fun y hy => (hε hy).2.le

/--
theorem `exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt` / 定理 `exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt`

English:
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt
  statement: (hs : Convex Real s) {f : E -> G}
  proof: (exists_gt _).imp
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont

中文:
定理 exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt
  结论: (hs : Convex 实数 s) {f : E -> G}
  证明: (exists_gt _).imp
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont

Depends on / 依赖: exists_gt, exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt, hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
-/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex Real s) {f : E -> G}
    (hder : forallᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
    exists K, exists t in 𝓝[s] x, LipschitzOnWith K f t :=
(exists_gt _).imp
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont

/--
theorem `norm_image_sub_le_of_norm_fderivWithin_le` / 定理 `norm_image_sub_le_of_norm_fderivWithin_le`

English:
theorem norm_image_sub_le_of_norm_fderivWithin_le
  statement: (hf : DifferentiableOn 𝕜 f s)
  proof: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

中文:
定理 norm_image_sub_le_of_norm_fderivWithin_le
  结论: (hf : DifferentiableOn 𝕜 f s)
  证明: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

Depends on / 依赖: hasFDerivWithinAt, hs.norm_image_sub_le_of_norm_hasFDerivWithin_le, norm_image_sub_le_of_norm_hasFDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s)
    (bound : forall x in s, ‖fderivWithin 𝕜 f s x‖ <= C) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    ‖f y - f x‖ <= C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

/--
theorem `lipschitzOnWith_of_nnnorm_fderivWithin_le` / 定理 `lipschitzOnWith_of_nnnorm_fderivWithin_le`

English:
theorem lipschitzOnWith_of_nnnorm_fderivWithin_le
  statement: {C : Real>=0} (hf : DifferentiableOn 𝕜 f s)
  proof: hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound

中文:
定理 lipschitzOnWith_of_nnnorm_fderivWithin_le
  结论: {C : 实数>=0} (hf : DifferentiableOn 𝕜 f s)
  证明: hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound

Depends on / 依赖: hasFDerivWithinAt, hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le, lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
-/
theorem lipschitzOnWith_of_nnnorm_fderivWithin_le {C : Real>=0} (hf : DifferentiableOn 𝕜 f s)
    (bound : forall x in s, ‖fderivWithin 𝕜 f s x‖₊ <= C) (hs : Convex Real s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound

/--
theorem `norm_image_sub_le_of_norm_fderiv_le` / 定理 `norm_image_sub_le_of_norm_fderiv_le`

English:
theorem norm_image_sub_le_of_norm_fderiv_le
  statement: (hf : forall x in s, DifferentiableAt 𝕜 f x)
  proof: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

中文:
定理 norm_image_sub_le_of_norm_fderiv_le
  结论: (hf : 对任意 x in s, DifferentiableAt 𝕜 f x)
  证明: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

Depends on / 依赖: hasFDerivAt, hasFDerivAt.hasFDerivWithinAt, hasFDerivWithinAt, hs.norm_image_sub_le_of_norm_hasFDerivWithin_le, norm_image_sub_le_of_norm_hasFDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_fderiv_le (hf : forall x in s, DifferentiableAt 𝕜 f x)
    (bound : forall x in s, ‖fderiv 𝕜 f x‖ <= C) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    ‖f y - f x‖ <= C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/--
theorem `lipschitzOnWith_of_nnnorm_fderiv_le` / 定理 `lipschitzOnWith_of_nnnorm_fderiv_le`

English:
theorem lipschitzOnWith_of_nnnorm_fderiv_le
  statement: {C : Real>=0} (hf : forall x in s, DifferentiableAt 𝕜 f x)
  proof: hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound

中文:
定理 lipschitzOnWith_of_nnnorm_fderiv_le
  结论: {C : 实数>=0} (hf : 对任意 x in s, DifferentiableAt 𝕜 f x)
  证明: hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound

Depends on / 依赖: hasFDerivAt, hasFDerivAt.hasFDerivWithinAt, hasFDerivWithinAt, hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le, lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
-/
theorem lipschitzOnWith_of_nnnorm_fderiv_le {C : Real>=0} (hf : forall x in s, DifferentiableAt 𝕜 f x)
    (bound : forall x in s, ‖fderiv 𝕜 f x‖₊ <= C) (hs : Convex Real s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound

/--
theorem `_root_.lipschitzWith_of_nnnorm_fderiv_le` / 定理 `_root_.lipschitzWith_of_nnnorm_fderiv_le`

English:
theorem _root_.lipschitzWith_of_nnnorm_fderiv_le
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hf x) (fun x _ => bound x) convex_univ

中文:
定理 _root_.lipschitzWith_of_nnnorm_fderiv_le
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hf x) (fun x _ => bound x) convex_univ

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, RCLike, convex_univ, lipschitzOnWith_of_nnnorm_fderiv_le, lipschitzOnWith_univ, rclike, restrictScalars
-/
theorem _root_.lipschitzWith_of_nnnorm_fderiv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E -> G}
    {C : Real>=0} (hf : Differentiable 𝕜 f)
    (bound : forall x, ‖fderiv 𝕜 f x‖₊ <= C) : LipschitzWith C f := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hf x) (fun x _ => bound x) convex_univ

/--
theorem `norm_image_sub_le_of_norm_hasFDerivWithin_le'` / 定理 `norm_image_sub_le_of_norm_hasFDerivWithin_le'`

English:
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le'
  proof: by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g y := f y - φ y
  have hg : f

中文:
定理 norm_image_sub_le_of_norm_hasFDerivWithin_le'
  证明: by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g y := f y - φ y
  have hg : f
-/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x - φ‖ <= C)
    (hs : Convex Real s) (xs : x in s) (ys : y in s) : ‖f y - f x - φ (y - x)‖ <= C * ‖y - x‖ := by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g y := f y - φ y
  have hg : forall x in s, HasFDerivWithinAt g (f' x - φ) s x := fun x xs =>
    (hf x xs).sub φ.hasFDerivWithinAt
  calc
    ‖f y - f x - φ (y - x)‖ = ‖f y - f x - (φ y - φ x)‖ := by simp
    _ = ‖f y - φ y - (f x - φ x)‖ := by congr 1; abel
    _ = ‖g y - g x‖ := by simp [g]
    _ <= C * ‖y - x‖ := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg bound hs xs ys

/--
theorem `norm_image_sub_le_of_norm_fderivWithin_le'` / 定理 `norm_image_sub_le_of_norm_fderivWithin_le'`

English:
theorem norm_image_sub_le_of_norm_fderivWithin_le'
  statement: (hf : DifferentiableOn 𝕜 f s)
  proof: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

中文:
定理 norm_image_sub_le_of_norm_fderivWithin_le'
  结论: (hf : DifferentiableOn 𝕜 f s)
  证明: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

Depends on / 依赖: hasFDerivWithinAt, hs.norm_image_sub_le_of_norm_hasFDerivWithin_le, norm_image_sub_le_of_norm_hasFDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_fderivWithin_le' (hf : DifferentiableOn 𝕜 f s)
    (bound : forall x in s, ‖fderivWithin 𝕜 f s x - φ‖ <= C) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    ‖f y - f x - φ (y - x)‖ <= C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

/--
theorem `norm_image_sub_le_of_norm_fderiv_le'` / 定理 `norm_image_sub_le_of_norm_fderiv_le'`

English:
theorem norm_image_sub_le_of_norm_fderiv_le'
  statement: (hf : forall x in s, DifferentiableAt 𝕜 f x)
  proof: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

中文:
定理 norm_image_sub_le_of_norm_fderiv_le'
  结论: (hf : 对任意 x in s, DifferentiableAt 𝕜 f x)
  证明: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

Depends on / 依赖: hasFDerivAt, hasFDerivAt.hasFDerivWithinAt, hasFDerivWithinAt, hs.norm_image_sub_le_of_norm_hasFDerivWithin_le, norm_image_sub_le_of_norm_hasFDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : forall x in s, DifferentiableAt 𝕜 f x)
    (bound : forall x in s, ‖fderiv 𝕜 f x - φ‖ <= C) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    ‖f y - f x - φ (y - x)‖ <= C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/--
theorem `is_const_of_fderivWithin_eq_zero` / 定理 `is_const_of_fderivWithin_eq_zero`

English:
theorem is_const_of_fderivWithin_eq_zero
  statement: (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s)
  proof: by
  have bound : forall x in s, ‖fderivWithin 𝕜 f s x‖ <= 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy

中文:
定理 is_const_of_fderivWithin_eq_zero
  结论: (hs : Convex 实数 s) (hf : DifferentiableOn 𝕜 f s)
  证明: by
  have bound : forall x in s, ‖fderivWithin 𝕜 f s x‖ <= 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy

Depends on / 依赖: dist_eq_norm, dist_le_zero, eq_comm, fderivWithin, hs.norm_image_sub_le_of_norm_fderivWithin_le, le_rfl, norm_image_sub_le_of_norm_fderivWithin_le, norm_zero, zero_mul
-/
theorem is_const_of_fderivWithin_eq_zero (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : forall x in s, fderivWithin 𝕜 f s x = 0) (hx : x in s) (hy : y in s) : f x = f y := by
  have bound : forall x in s, ‖fderivWithin 𝕜 f s x‖ <= 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy

/--
theorem `_root_.is_const_of_fderiv_eq_zero` / 定理 `_root_.is_const_of_fderiv_eq_zero`

English:
theorem _root_.is_const_of_fderiv_eq_zero
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial

中文:
定理 _root_.is_const_of_fderiv_eq_zero
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, RCLike, convex_univ, convex_univ.is_const_of_fderivWithin_eq_zero, differentiableOn, fderivWithin_univ, hf.differentiableOn, is_const_of_fderivWithin_eq_zero, rclike, restrictScalars
-/
theorem _root_.is_const_of_fderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E -> G}
    (hf : Differentiable 𝕜 f) (hf' : forall x, fderiv 𝕜 f x = 0)
    (x y : E) : f x = f y := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial

/--
theorem `eqOn_of_fderivWithin_eq` / 定理 `eqOn_of_fderivWithin_eq`

English:
theorem eqOn_of_fderivWithin_eq
  statement: (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s)
  proof: fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => ?_) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz)]; rw [sub_eq_zero]; rw [hf' hz]

中文:
定理 eqOn_of_fderivWithin_eq
  结论: (hs : Convex 实数 s) (hf : DifferentiableOn 𝕜 f s)
  证明: fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => ?_) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz)]; rw [sub_eq_zero]; rw [hf' hz]

Depends on / 依赖: eq_comm, fderivWithin_sub, hf.sub, hs.is_const_of_fderivWithin_eq_zero, is_const_of_fderivWithin_eq_zero, sub_eq_zero, sub_self
-/
theorem eqOn_of_fderivWithin_eq (hs : Convex Real s) (hf : DifferentiableOn 𝕜 f s)
    (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDiffOn 𝕜 s)
    (hf' : s.EqOn (fderivWithin 𝕜 f s) (fderivWithin 𝕜 g s)) (hx : x in s) (hfgx : f x = g x) :
    s.EqOn f g := fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => ?_) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz)]; rw [sub_eq_zero]; rw [hf' hz]

-- TODO: change the spelling once we have `IsLocallyConstantOn`.
/--
theorem `_root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero` / 定理 `_root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero`

English:
theorem _root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero
  proof: by
  refine Metric.isOpen_iff.mpr fun y ⟨hy, hy'⟩ => ?_
  obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hs y hy
  refine ⟨r, hr, Set.subset_inter h fun x hx => ?_⟩
  have := (convex_ball y r).is_const_of_fderivWithin_eq_zero (hf.mono h) ?_ hx (mem_ball_self hr)
  · simpa [this]
  · intro z hz
    simpa 

中文:
定理 _root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero
  证明: by
  refine Metric.isOpen_iff.mpr fun y ⟨hy, hy'⟩ => ?_
  obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hs y hy
  refine ⟨r, hr, Set.subset_inter h fun x hx => ?_⟩
  have := (convex_ball y r).is_const_of_fderivWithin_eq_zero (hf.mono h) ?_ hx (mem_ball_self hr)
  · simpa [this]
  · intro z hz
    simpa 

Depends on / 依赖: Metric, Metric.isOpen_ball, Metric.isOpen_iff.mp, Metric.isOpen_iff.mpr, Set.subset_inter, convex_ball, fderivWithin_of_isOpen, hf.mono, isOpen_ball, isOpen_iff, is_const_of_fderivWithin_eq_zero, mem_ball_self, subset_inter
-/
theorem _root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero
    (hs : IsOpen s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) (t : Set G) : IsOpen (s inter f ⁻¹' t) := by
  refine Metric.isOpen_iff.mpr fun y ⟨hy, hy'⟩ => ?_
  obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hs y hy
  refine ⟨r, hr, Set.subset_inter h fun x hx => ?_⟩
  have := (convex_ball y r).is_const_of_fderivWithin_eq_zero (hf.mono h) ?_ hx (mem_ball_self hr)
  · simpa [this]
  · intro z hz
    simpa only [fderivWithin_of_isOpen Metric.isOpen_ball hz] using! hf' (h hz)

/--
theorem `_root_.isLocallyConstant_of_fderiv_eq_zero` / 定理 `_root_.isLocallyConstant_of_fderiv_eq_zero`

English:
theorem _root_.isLocallyConstant_of_fderiv_eq_zero
  statement: (h₁ : Differentiable 𝕜 f)
  proof: by
  simpa using!
    isOpen_univ.isOpen_inter_preimage_of_fderiv_eq_zero h₁.differentiableOn fun _ _ => h₂ _

中文:
定理 _root_.isLocallyConstant_of_fderiv_eq_zero
  结论: (h₁ : Differentiable 𝕜 f)
  证明: by
  simpa using!
    isOpen_univ.isOpen_inter_preimage_of_fderiv_eq_zero h₁.differentiableOn fun _ _ => h₂ _

Depends on / 依赖: differentiableOn, isOpen_inter_preimage_of_fderiv_eq_zero, isOpen_univ, isOpen_univ.isOpen_inter_preimage_of_fderiv_eq_zero
-/
theorem _root_.isLocallyConstant_of_fderiv_eq_zero (h₁ : Differentiable 𝕜 f)
    (h₂ : forall x, fderiv 𝕜 f x = 0) : IsLocallyConstant f := by
  simpa using!
    isOpen_univ.isOpen_inter_preimage_of_fderiv_eq_zero h₁.differentiableOn fun _ _ => h₂ _

/--
theorem `_root_.IsOpen.exists_is_const_of_fderiv_eq_zero` / 定理 `_root_.IsOpen.exists_is_const_of_fderiv_eq_zero`

English:
theorem _root_.IsOpen.exists_is_const_of_fderiv_eq_zero
  proof: by
  obtain (rfl | ⟨y, hy⟩) := s.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  · refine ⟨f y, fun x hx => ?_⟩
    have h₁ := hs.isOpen_inter_preimage_of_fderiv_eq_zero hf hf' {f y}
    have h₂ := hf.continuousOn.comp_continuous continuous_subtype_val (fun x => x.2)
    by_contra h₃
    obtain ⟨t, ht

中文:
定理 _root_.IsOpen.exists_is_const_of_fderiv_eq_zero
  证明: by
  obtain (rfl | ⟨y, hy⟩) := s.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  · refine ⟨f y, fun x hx => ?_⟩
    have h₁ := hs.isOpen_inter_preimage_of_fderiv_eq_zero hf hf' {f y}
    have h₂ := hf.continuousOn.comp_continuous continuous_subtype_val (fun x => x.2)
    by_contra h₃
    obtain ⟨t, ht

Depends on / 依赖: Set.ext_iff, comp_continuous, continuousOn, continuous_subtype_val, eq_empty_or_nonempty, eq_or_ne, ext_iff, hf.continuousOn.comp_continuous, hs.isOpen_inter_preimage_of_fderiv_eq_zero, isClosed_singleton, isOpen_inter_preimage_of_fderiv_eq_zero, preimage, s.eq_empty_or_nonempty
-/
theorem _root_.IsOpen.exists_is_const_of_fderiv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) : exists a, forall x in s, f x = a := by
  obtain (rfl | ⟨y, hy⟩) := s.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  · refine ⟨f y, fun x hx => ?_⟩
    have h₁ := hs.isOpen_inter_preimage_of_fderiv_eq_zero hf hf' {f y}
    have h₂ := hf.continuousOn.comp_continuous continuous_subtype_val (fun x => x.2)
    by_contra h₃
    obtain ⟨t, ht, ht'⟩ := (isClosed_singleton (x := f y)).preimage h₂
    have ht'' : forall a in s, a in t ↔ f a != f y := by simpa [Set.ext_iff] using ht'
    obtain ⟨z, H₁, H₂, H₃⟩ := hs' _ _ h₁ ht (fun x h => by simp [h, ht'', eq_or_ne]) ⟨y, by simpa⟩
      ⟨x, by simp [ht'' _ hx, hx, h₃]⟩
    exact (ht'' _ H₁).mp H₃ H₂.2

/--
theorem `_root_.IsOpen.is_const_of_fderiv_eq_zero` / 定理 `_root_.IsOpen.is_const_of_fderiv_eq_zero`

English:
theorem _root_.IsOpen.is_const_of_fderiv_eq_zero
  proof: by
  obtain ⟨a, ha⟩ := hs.exists_is_const_of_fderiv_eq_zero hs' hf hf'
  rw [ha x hx]; rw [ha y hy]

中文:
定理 _root_.IsOpen.is_const_of_fderiv_eq_zero
  证明: by
  obtain ⟨a, ha⟩ := hs.exists_is_const_of_fderiv_eq_zero hs' hf hf'
  rw [ha x hx]; rw [ha y hy]

Depends on / 依赖: exists_is_const_of_fderiv_eq_zero, hs.exists_is_const_of_fderiv_eq_zero
-/
theorem _root_.IsOpen.is_const_of_fderiv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) {x y : E} (hx : x in s) (hy : y in s) : f x = f y := by
  obtain ⟨a, ha⟩ := hs.exists_is_const_of_fderiv_eq_zero hs' hf hf'
  rw [ha x hx]; rw [ha y hy]

/--
theorem `_root_.IsOpen.exists_eq_add_of_fderiv_eq` / 定理 `_root_.IsOpen.exists_eq_add_of_fderiv_eq`

English:
theorem _root_.IsOpen.exists_eq_add_of_fderiv_eq
  statement: (hs : IsOpen s) (hs' : IsPreconnected s)
  proof: by
  simp_rw [Set.EqOn, ← sub_eq_iff_eq_add']
  refine hs.exists_is_const_of_fderiv_eq_zero hs' (hf.sub hg) fun x hx => ?_
  rw [fderiv_fun_sub (hf.differentiableAt (hs.mem_nhds hx)) (hg.differentiableAt (hs.mem_nhds hx))]; rw [hf' hx]; rw [sub_self]; rw [Pi.zero_apply]

中文:
定理 _root_.IsOpen.exists_eq_add_of_fderiv_eq
  结论: (hs : IsOpen s) (hs' : IsPreconnected s)
  证明: by
  simp_rw [Set.EqOn, ← sub_eq_iff_eq_add']
  refine hs.exists_is_const_of_fderiv_eq_zero hs' (hf.sub hg) fun x hx => ?_
  rw [fderiv_fun_sub (hf.differentiableAt (hs.mem_nhds hx)) (hg.differentiableAt (hs.mem_nhds hx))]; rw [hf' hx]; rw [sub_self]; rw [Pi.zero_apply]

Depends on / 依赖: Pi.zero_apply, Set.EqOn, differentiableAt, exists_is_const_of_fderiv_eq_zero, fderiv_fun_sub, hf.differentiableAt, hf.sub, hg.differentiableAt, hs.exists_is_const_of_fderiv_eq_zero, hs.mem_nhds, mem_nhds, simp_rw, sub_eq_iff_eq_add, sub_self, zero_apply
-/
theorem _root_.IsOpen.exists_eq_add_of_fderiv_eq (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (fderiv 𝕜 f) (fderiv 𝕜 g)) : exists a, s.EqOn f (g · + a) := by
  simp_rw [Set.EqOn, ← sub_eq_iff_eq_add']
  refine hs.exists_is_const_of_fderiv_eq_zero hs' (hf.sub hg) fun x hx => ?_
  rw [fderiv_fun_sub (hf.differentiableAt (hs.mem_nhds hx)) (hg.differentiableAt (hs.mem_nhds hx))]; rw [hf' hx]; rw [sub_self]; rw [Pi.zero_apply]

/--
theorem `_root_.IsOpen.eqOn_of_fderiv_eq` / 定理 `_root_.IsOpen.eqOn_of_fderiv_eq`

English:
theorem _root_.IsOpen.eqOn_of_fderiv_eq
  statement: (hs : IsOpen s) (hs' : IsPreconnected s)
  proof: by
  obtain ⟨a, ha⟩ := hs.exists_eq_add_of_fderiv_eq hs' hf hg hf'
  obtain rfl := left_eq_add.mp (hfgx.symm.trans (ha hx))
  simpa using ha

中文:
定理 _root_.IsOpen.eqOn_of_fderiv_eq
  结论: (hs : IsOpen s) (hs' : IsPreconnected s)
  证明: by
  obtain ⟨a, ha⟩ := hs.exists_eq_add_of_fderiv_eq hs' hf hg hf'
  obtain rfl := left_eq_add.mp (hfgx.symm.trans (ha hx))
  simpa using ha

Depends on / 依赖: exists_eq_add_of_fderiv_eq, hfgx.symm.trans, hs.exists_eq_add_of_fderiv_eq, left_eq_add, left_eq_add.mp
-/
theorem _root_.IsOpen.eqOn_of_fderiv_eq (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : forall x in s, fderiv 𝕜 f x = fderiv 𝕜 g x) (hx : x in s) (hfgx : f x = g x) :
    s.EqOn f g := by
  obtain ⟨a, ha⟩ := hs.exists_eq_add_of_fderiv_eq hs' hf hg hf'
  obtain rfl := left_eq_add.mp (hfgx.symm.trans (ha hx))
  simpa using ha

/--
theorem `_root_.eq_of_fderiv_eq` / 定理 `_root_.eq_of_fderiv_eq`

English:
theorem _root_.eq_of_fderiv_eq
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
suffices Set.univ.EqOn f g from funext fun x => this mem_univ x
  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
    uniqueDiffOn_univ (fun x _ => by simpa

中文:
定理 _root_.eq_of_fderiv_eq
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
suffices Set.univ.EqOn f g from funext fun x => this mem_univ x
  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
    uniqueDiffOn_univ (fun x _ => by simpa

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, RCLike, Set.univ.EqOn, convex_univ, convex_univ.eqOn_of_fderivWithin_eq, differentiableOn, eqOn_of_fderivWithin_eq, hf.differentiableOn, hg.differentiableOn, mem_univ, rclike, restrictScalars, uniqueDiffOn_univ
-/
theorem _root_.eq_of_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : E -> G}
    (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
    (hf' : forall x, fderiv 𝕜 f x = fderiv 𝕜 g x) (x : E) (hfgx : f x = g x) : f = g := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := .restrictScalars Real 𝕜 E
suffices Set.univ.EqOn f g from funext fun x => this mem_univ x
  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
    uniqueDiffOn_univ (fun x _ => by simpa using hf' _) (mem_univ _) hfgx

/--
lemma `isLittleO_pow_succ` / 引理 `isLittleO_pow_succ`

English:
lemma isLittleO_pow_succ
  statement: {x₀ : E} {n : Nat} (hs : Convex Real s) (hx₀s : x₀ in s)
  proof: by
  rw [Asymptotics.isLittleO_iff] at hf' ⊢
  intro c hc
  simp_rw [norm_pow, pow_succ, ← mul_assoc, norm_norm]
  simp_rw [norm_pow, norm_norm] at hf'
  have : forallᶠ x in 𝓝[s] x₀, segment Real x₀ x subseteq s ∧ forall y in segment Real x₀ x, ‖f' y‖ <= c * ‖x - x₀‖ ^ n := by
    have h1 : forallᶠ 

中文:
引理 isLittleO_pow_succ
  结论: {x₀ : E} {n : 自然数} (hs : Convex 实数 s) (hx₀s : x₀ in s)
  证明: by
  rw [Asymptotics.isLittleO_iff] at hf' ⊢
  intro c hc
  simp_rw [norm_pow, pow_succ, ← mul_assoc, norm_norm]
  simp_rw [norm_pow, norm_norm] at hf'
  have : forallᶠ x in 𝓝[s] x₀, segment Real x₀ x subseteq s ∧ forall y in segment Real x₀ x, ‖f' y‖ <= c * ‖x - x₀‖ ^ n := by
    have h1 : forallᶠ 

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff, eventually_mem_nhdsWithin, eventually_nhdsWithin_segment, filter_upwards, hs.eventually_nhdsWithin_segment, hs.segment_subset, isLittleO_iff, mul_assoc, norm_norm, norm_pow, pow_succ, segment, segment_subset, simp_rw, subseteq
-/
lemma isLittleO_pow_succ {x₀ : E} {n : Nat} (hs : Convex Real s) (hx₀s : x₀ in s)
    (hff' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) :
    (fun x => f x - f x₀) =o[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ (n + 1) := by
  rw [Asymptotics.isLittleO_iff] at hf' ⊢
  intro c hc
  simp_rw [norm_pow, pow_succ, ← mul_assoc, norm_norm]
  simp_rw [norm_pow, norm_norm] at hf'
  have : forallᶠ x in 𝓝[s] x₀, segment Real x₀ x subseteq s ∧ forall y in segment Real x₀ x, ‖f' y‖ <= c * ‖x - x₀‖ ^ n := by
    have h1 : forallᶠ x in 𝓝[s] x₀, x in s := eventually_mem_nhdsWithin
    filter_upwards [h1, hs.eventually_nhdsWithin_segment hx₀s (hf' hc)] with x hxs h
    refine ⟨hs.segment_subset hx₀s hxs, fun y hy => (h y hy).trans ?_⟩
    gcongr
    exact norm_sub_le_of_mem_segment hy
  filter_upwards [this] with x ⟨h_segment, h⟩
  convert!
    (convex_segment x₀ x).norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun x => f x - f x₀)
      (y := x) (x := x₀) (s := segment Real x₀ x) ?_ h
      (left_mem_segment Real x₀ x)
      (right_mem_segment Real x₀ x) using 1
  · simp
  · simp only [hasFDerivWithinAt_sub_const_iff]
    exact fun x hx => (hff' x (h_segment hx)).mono h_segment

/--
theorem `isLittleO_pow_succ_real` / 定理 `isLittleO_pow_succ_real`

English:
theorem isLittleO_pow_succ_real
  statement: {f f' : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real}
  proof: by
  have h := hs.isLittleO_pow_succ hx₀s hff' ?_ (n := n)
  · rw [Asymptotics.isLittleO_iff] at h ⊢
    simpa using h
  · rw [Asymptotics.isLittleO_iff] at hf' ⊢
    convert! hf' using 4 with c hc x
    simp

中文:
定理 isLittleO_pow_succ_real
  结论: {f f' : 实数 -> E} {x₀ : 实数} {n : 自然数} {s : Set 实数}
  证明: by
  have h := hs.isLittleO_pow_succ hx₀s hff' ?_ (n := n)
  · rw [Asymptotics.isLittleO_iff] at h ⊢
    simpa using h
  · rw [Asymptotics.isLittleO_iff] at hf' ⊢
    convert! hf' using 4 with c hc x
    simp

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff, convert, hs.isLittleO_pow_succ, isLittleO_iff, isLittleO_pow_succ
-/
theorem isLittleO_pow_succ_real {f f' : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real}
    (hs : Convex Real s) (hx₀s : x₀ in s)
    (hff' : forall x in s, HasDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x => (x - x₀) ^ n) :
    (fun x => f x - f x₀) =o[𝓝[s] x₀] fun x => (x - x₀) ^ (n + 1) := by
  have h := hs.isLittleO_pow_succ hx₀s hff' ?_ (n := n)
  · rw [Asymptotics.isLittleO_iff] at h ⊢
    simpa using h
  · rw [Asymptotics.isLittleO_iff] at hf' ⊢
    convert! hf' using 4 with c hc x
    simp

end Convex

namespace Convex

variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f f' : 𝕜 -> G} {s : Set 𝕜} {x y : 𝕜}

/--
theorem `norm_image_sub_le_of_norm_hasDerivWithin_le` / 定理 `norm_image_sub_le_of_norm_hasDerivWithin_le`

English:
theorem norm_image_sub_le_of_norm_hasDerivWithin_le
  statement: {C : Real}
  proof: Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys

中文:
定理 norm_image_sub_le_of_norm_hasDerivWithin_le
  结论: {C : 实数}
  证明: Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys

Depends on / 依赖: Convex, Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le, hasFDerivWithinAt, le_trans, norm_image_sub_le_of_norm_hasFDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : Real}
    (hf : forall x in s, HasDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖ <= C) (hs : Convex Real s)
    (xs : x in s) (ys : y in s) : ‖f y - f x‖ <= C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys

/--
theorem `lipschitzOnWith_of_nnnorm_hasDerivWithin_le` / 定理 `lipschitzOnWith_of_nnnorm_hasDerivWithin_le`

English:
theorem lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  statement: {C : Real>=0} (hs : Convex Real s)
  proof: Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs

中文:
定理 lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  结论: {C : 实数>=0} (hs : Convex 实数 s)
  证明: Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs

Depends on / 依赖: Convex, Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le, hasFDerivWithinAt, le_trans, lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
-/
theorem lipschitzOnWith_of_nnnorm_hasDerivWithin_le {C : Real>=0} (hs : Convex Real s)
    (hf : forall x in s, HasDerivWithinAt f (f' x) s x) (bound : forall x in s, ‖f' x‖₊ <= C) :
    LipschitzOnWith C f s :=
  Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs

/--
theorem `norm_image_sub_le_of_norm_derivWithin_le` / 定理 `norm_image_sub_le_of_norm_derivWithin_le`

English:
theorem norm_image_sub_le_of_norm_derivWithin_le
  statement: {C : Real} (hf : DifferentiableOn 𝕜 f s)
  proof: hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys

中文:
定理 norm_image_sub_le_of_norm_derivWithin_le
  结论: {C : 实数} (hf : DifferentiableOn 𝕜 f s)
  证明: hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys

Depends on / 依赖: hasDerivWithinAt, hs.norm_image_sub_le_of_norm_hasDerivWithin_le, norm_image_sub_le_of_norm_hasDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_derivWithin_le {C : Real} (hf : DifferentiableOn 𝕜 f s)
    (bound : forall x in s, ‖derivWithin f s x‖ <= C) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    ‖f y - f x‖ <= C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys

/--
theorem `lipschitzOnWith_of_nnnorm_derivWithin_le` / 定理 `lipschitzOnWith_of_nnnorm_derivWithin_le`

English:
theorem lipschitzOnWith_of_nnnorm_derivWithin_le
  statement: {C : Real>=0} (hs : Convex Real s)
  proof: hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound

中文:
定理 lipschitzOnWith_of_nnnorm_derivWithin_le
  结论: {C : 实数>=0} (hs : Convex 实数 s)
  证明: hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound

Depends on / 依赖: hasDerivWithinAt, hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le, lipschitzOnWith_of_nnnorm_hasDerivWithin_le
-/
theorem lipschitzOnWith_of_nnnorm_derivWithin_le {C : Real>=0} (hs : Convex Real s)
    (hf : DifferentiableOn 𝕜 f s) (bound : forall x in s, ‖derivWithin f s x‖₊ <= C) :
    LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound

/--
theorem `norm_image_sub_le_of_norm_deriv_le` / 定理 `norm_image_sub_le_of_norm_deriv_le`

English:
theorem norm_image_sub_le_of_norm_deriv_le
  statement: {C : Real} (hf : forall x in s, DifferentiableAt 𝕜 f x)
  proof: hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys

中文:
定理 norm_image_sub_le_of_norm_deriv_le
  结论: {C : 实数} (hf : 对任意 x in s, DifferentiableAt 𝕜 f x)
  证明: hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys

Depends on / 依赖: hasDerivAt, hasDerivAt.hasDerivWithinAt, hasDerivWithinAt, hs.norm_image_sub_le_of_norm_hasDerivWithin_le, norm_image_sub_le_of_norm_hasDerivWithin_le
-/
theorem norm_image_sub_le_of_norm_deriv_le {C : Real} (hf : forall x in s, DifferentiableAt 𝕜 f x)
    (bound : forall x in s, ‖deriv f x‖ <= C) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    ‖f y - f x‖ <= C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys

/--
theorem `lipschitzOnWith_of_nnnorm_deriv_le` / 定理 `lipschitzOnWith_of_nnnorm_deriv_le`

English:
theorem lipschitzOnWith_of_nnnorm_deriv_le
  statement: {C : Real>=0} (hf : forall x in s, DifferentiableAt 𝕜 f x)
  proof: hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound

中文:
定理 lipschitzOnWith_of_nnnorm_deriv_le
  结论: {C : 实数>=0} (hf : 对任意 x in s, DifferentiableAt 𝕜 f x)
  证明: hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound

Depends on / 依赖: hasDerivAt, hasDerivAt.hasDerivWithinAt, hasDerivWithinAt, hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le, lipschitzOnWith_of_nnnorm_hasDerivWithin_le
-/
theorem lipschitzOnWith_of_nnnorm_deriv_le {C : Real>=0} (hf : forall x in s, DifferentiableAt 𝕜 f x)
    (bound : forall x in s, ‖deriv f x‖₊ <= C) (hs : Convex Real s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound

/--
theorem `_root_.lipschitzWith_of_nnnorm_deriv_le` / 定理 `_root_.lipschitzWith_of_nnnorm_deriv_le`

English:
theorem _root_.lipschitzWith_of_nnnorm_deriv_le
  statement: {C : Real>=0} (hf : Differentiable 𝕜 f)
  proof: lipschitzOnWith_univ.1
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x

中文:
定理 _root_.lipschitzWith_of_nnnorm_deriv_le
  结论: {C : 实数>=0} (hf : Differentiable 𝕜 f)
  证明: lipschitzOnWith_univ.1
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x

Depends on / 依赖: convex_univ, convex_univ.lipschitzOnWith_of_nnnorm_deriv_le, lipschitzOnWith_of_nnnorm_deriv_le, lipschitzOnWith_univ
-/
theorem _root_.lipschitzWith_of_nnnorm_deriv_le {C : Real>=0} (hf : Differentiable 𝕜 f)
    (bound : forall x, ‖deriv f x‖₊ <= C) : LipschitzWith C f :=
lipschitzOnWith_univ.1
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x

/--
theorem `_root_.is_const_of_deriv_eq_zero` / 定理 `_root_.is_const_of_deriv_eq_zero`

English:
theorem _root_.is_const_of_deriv_eq_zero
  statement: (hf : Differentiable 𝕜 f) (hf' : forall x, deriv f x = 0)
  proof: is_const_of_fderiv_eq_zero hf (fun z => by simp [← toSpanSingleton_deriv, hf']) _ _

中文:
定理 _root_.is_const_of_deriv_eq_zero
  结论: (hf : Differentiable 𝕜 f) (hf' : 对任意 x, deriv f x = 0)
  证明: is_const_of_fderiv_eq_zero hf (fun z => by simp [← toSpanSingleton_deriv, hf']) _ _

Depends on / 依赖: is_const_of_fderiv_eq_zero, toSpanSingleton_deriv
-/
theorem _root_.is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : forall x, deriv f x = 0)
    (x y : 𝕜) : f x = f y :=
  is_const_of_fderiv_eq_zero hf (fun z => by simp [← toSpanSingleton_deriv, hf']) _ _

/--
theorem `_root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero` / 定理 `_root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero`

English:
theorem _root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero
  proof: hs.isOpen_inter_preimage_of_fderiv_eq_zero hf
    (fun x hx => by simp [← toSpanSingleton_deriv, hf' hx]) t

中文:
定理 _root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero
  证明: hs.isOpen_inter_preimage_of_fderiv_eq_zero hf
    (fun x hx => by simp [← toSpanSingleton_deriv, hf' hx]) t

Depends on / 依赖: hs.isOpen_inter_preimage_of_fderiv_eq_zero, isOpen_inter_preimage_of_fderiv_eq_zero, toSpanSingleton_deriv
-/
theorem _root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero
    (hs : IsOpen s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) (t : Set G) : IsOpen (s inter f ⁻¹' t) :=
  hs.isOpen_inter_preimage_of_fderiv_eq_zero hf
    (fun x hx => by simp [← toSpanSingleton_deriv, hf' hx]) t

/--
theorem `_root_.IsOpen.exists_is_const_of_deriv_eq_zero` / 定理 `_root_.IsOpen.exists_is_const_of_deriv_eq_zero`

English:
theorem _root_.IsOpen.exists_is_const_of_deriv_eq_zero
  proof: hs.exists_is_const_of_fderiv_eq_zero hs' hf (fun {x} hx => by
    ext; simp [← toSpanSingleton_deriv, hf' hx])

中文:
定理 _root_.IsOpen.exists_is_const_of_deriv_eq_zero
  证明: hs.exists_is_const_of_fderiv_eq_zero hs' hf (fun {x} hx => by
    ext; simp [← toSpanSingleton_deriv, hf' hx])

Depends on / 依赖: exists_is_const_of_fderiv_eq_zero, hs.exists_is_const_of_fderiv_eq_zero, toSpanSingleton_deriv
-/
theorem _root_.IsOpen.exists_is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) : exists a, forall x in s, f x = a :=
  hs.exists_is_const_of_fderiv_eq_zero hs' hf (fun {x} hx => by
    ext; simp [← toSpanSingleton_deriv, hf' hx])

/--
theorem `_root_.IsOpen.is_const_of_deriv_eq_zero` / 定理 `_root_.IsOpen.is_const_of_deriv_eq_zero`

English:
theorem _root_.IsOpen.is_const_of_deriv_eq_zero
  proof: hs.is_const_of_fderiv_eq_zero hs' hf (fun a ha => by
    ext; simp [← toSpanSingleton_deriv, hf' ha]) hx hy

中文:
定理 _root_.IsOpen.is_const_of_deriv_eq_zero
  证明: hs.is_const_of_fderiv_eq_zero hs' hf (fun a ha => by
    ext; simp [← toSpanSingleton_deriv, hf' ha]) hx hy

Depends on / 依赖: hs.is_const_of_fderiv_eq_zero, is_const_of_fderiv_eq_zero, toSpanSingleton_deriv
-/
theorem _root_.IsOpen.is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) {x y : 𝕜} (hx : x in s) (hy : y in s) : f x = f y :=
  hs.is_const_of_fderiv_eq_zero hs' hf (fun a ha => by
    ext; simp [← toSpanSingleton_deriv, hf' ha]) hx hy

/--
theorem `_root_.IsOpen.exists_eq_add_of_deriv_eq` / 定理 `_root_.IsOpen.exists_eq_add_of_deriv_eq`

English:
theorem _root_.IsOpen.exists_eq_add_of_deriv_eq
  statement: {f g : 𝕜 -> G} (hs : IsOpen s)
  proof: hs.exists_eq_add_of_fderiv_eq hs' hf hg (fun x hx => by simp [← toSpanSingleton_deriv, hf' hx])

中文:
定理 _root_.IsOpen.exists_eq_add_of_deriv_eq
  结论: {f g : 𝕜 -> G} (hs : IsOpen s)
  证明: hs.exists_eq_add_of_fderiv_eq hs' hf hg (fun x hx => by simp [← toSpanSingleton_deriv, hf' hx])

Depends on / 依赖: exists_eq_add_of_fderiv_eq, hs.exists_eq_add_of_fderiv_eq, toSpanSingleton_deriv
-/
theorem _root_.IsOpen.exists_eq_add_of_deriv_eq {f g : 𝕜 -> G} (hs : IsOpen s)
    (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (deriv f) (deriv g)) : exists a, s.EqOn f (g · + a) :=
  hs.exists_eq_add_of_fderiv_eq hs' hf hg (fun x hx => by simp [← toSpanSingleton_deriv, hf' hx])

/--
theorem `_root_.IsOpen.eqOn_of_deriv_eq` / 定理 `_root_.IsOpen.eqOn_of_deriv_eq`

English:
theorem _root_.IsOpen.eqOn_of_deriv_eq
  statement: {f g : 𝕜 -> G} (hs : IsOpen s)
  proof: hs.eqOn_of_fderiv_eq hs' hf hg (fun _ hx => ContinuousLinearMap.ext_ring (hf' hx)) hx hfgx

中文:
定理 _root_.IsOpen.eqOn_of_deriv_eq
  结论: {f g : 𝕜 -> G} (hs : IsOpen s)
  证明: hs.eqOn_of_fderiv_eq hs' hf hg (fun _ hx => ContinuousLinearMap.ext_ring (hf' hx)) hx hfgx

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_ring, eqOn_of_fderiv_eq, ext_ring, hs.eqOn_of_fderiv_eq
-/
theorem _root_.IsOpen.eqOn_of_deriv_eq {f g : 𝕜 -> G} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (deriv f) (deriv g)) (hx : x in s) (hfgx : f x = g x) :
    s.EqOn f g :=
  hs.eqOn_of_fderiv_eq hs' hf hg (fun _ hx => ContinuousLinearMap.ext_ring (hf' hx)) hx hfgx

end Convex

end

section RCLike

/-!
### Vector-valued functions `f : E → F`. Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {f : G -> H} {f' : G -> G ->L[𝕜] H} {x : G}

/--
theorem `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` / 定理 `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`

English:
theorem hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
  proof: by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  rw [hasStrictFDerivAt_iff_isLittleO]; rw [isLittleO_iff]
  refine fun c hc => Metric.eventually_nhds_iff_ball.mpr ?_
  -- the correct ε is the modulus of continuity of f'
  rcases Metric.mem_nhds_iff.mp (inter_mem hd

中文:
定理 hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
  证明: by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  rw [hasStrictFDerivAt_iff_isLittleO]; rw [isLittleO_iff]
  refine fun c hc => Metric.eventually_nhds_iff_ball.mpr ?_
  -- the correct ε is the modulus of continuity of f'
  rcases Metric.mem_nhds_iff.mp (inter_mem hd
-/
theorem hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (hder : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictFDerivAt f (f' x) x := by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  rw [hasStrictFDerivAt_iff_isLittleO]; rw [isLittleO_iff]
  refine fun c hc => Metric.eventually_nhds_iff_ball.mpr ?_
  -- the correct ε is the modulus of continuity of f'
  rcases Metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩
  refine ⟨ε, ε0, ?_⟩
  -- simplify formulas involving the product E × E
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same]; rw [prodMk_mem_set_prod_eq] at h
  -- exploit the choice of ε as the modulus of continuity of f'
  have hf' : forall x' in ball x ε, ‖f' x' - f' x‖ <= c := fun x' H' => by
    rw [← dist_eq_norm]
    exact le_of_lt (hε H').2
  -- apply mean value theorem
  let : NormedSpace Real G := .restrictScalars Real 𝕜 G
  refine (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le' ?_ hf' h.2 h.1
  exact fun y hy => (hε hy).1.hasFDerivWithinAt

/--
theorem `hasStrictDerivAt_of_hasDerivAt_of_continuousAt` / 定理 `hasStrictDerivAt_of_hasDerivAt_of_continuousAt`

English:
theorem hasStrictDerivAt_of_hasDerivAt_of_continuousAt
  statement: {f f' : 𝕜 -> G} {x : 𝕜}
  proof: hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt)
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont

中文:
定理 hasStrictDerivAt_of_hasDerivAt_of_continuousAt
  结论: {f f' : 𝕜 -> G} {x : 𝕜}
  证明: hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt)
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont

Depends on / 依赖: continuous, continuous.continuousAt.comp, continuousAt, hasFDerivAt, hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt, hder.mono, hy.hasFDerivAt, smulRightL
-/
theorem hasStrictDerivAt_of_hasDerivAt_of_continuousAt {f f' : 𝕜 -> G} {x : 𝕜}
    (hder : forallᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictDerivAt f (f' x) x :=
hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt)
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont

end RCLike
