/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Order.Filter.Curry

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `hasFDerivAt_of_tendstoLocallyUniformlyOn`.

## Main statements

* `uniformCauchySeqOnFilter_of_fderiv`: If
    1. `f : ℕ → E → G` is a sequence of functions which have derivatives
       `f' : ℕ → E → (E →L[𝕜] G)` on a neighborhood of `x`,
    2. the functions `f` converge at `x`, and
    3. the derivatives `f'` form a Cauchy sequence uniformly on a neighborhood of `x`,
  then the `f` form a Cauchy sequence _uniformly_ on a neighborhood of `x`
* `hasFDerivAt_of_tendstoUniformlyOnFilter` : Suppose (1), (2), and (3) above are true. Let
  `g` (resp. `g'`) be the limiting function of the `f` (resp. `g'`). Then `f'` is the derivative of
  `g` on a neighborhood of `x`
* `hasFDerivAt_of_tendstoUniformlyOn`: An often-easier-to-use version of the above theorem when
  *all* the derivatives exist and functions converge on a common open set and the derivatives
  converge uniformly there.

Each of the above statements also has variations that support `deriv` instead of `fderiv`.

## Implementation notes

Our technique for proving the main result is the famous "`ε / 3` proof." In words, you can find it
explained, for instance, at [this StackExchange post](https://math.stackexchange.com/questions/214218/uniform-convergence-of-derivatives-tao-14-2-7).
The subtlety is that we want to prove that the difference quotients of the `g` converge to the `g'`.
That is, we want to prove something like:

```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

To do so, we will need to introduce a pair of quantifiers

```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

So how do we write this in terms of filters? Well, the initial definition of the derivative is

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

There are two ways we might introduce `n`. We could do:

```lean
∀ᶠ (n : ℕ) in atTop, Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∃ N, ∀ n ≥ N, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`,
which _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is _not_ equivalent to it. On the other hand, we might
try

```lean
Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (atTop ×ˢ 𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∀ ε > 0, ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ y ∈ B_δ(x)`, which
again _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is not equivalent to it.

So to get the quantifier order we want, we need to introduce a new filter construction, which we
call a "curried filter"

```lean
Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (atTop.curry (𝓝 x)) (𝓝 0)
```

Then the above implications are `Filter.Tendsto.curry` and
`Filter.Tendsto.mono_left Filter.curry_le_prod`. We will use both of these deductions as part of
our proof.

We note that if you loosen the assumptions of the main theorem then the proof becomes quite a bit
easier. In particular, if you assume there is a common neighborhood `s` where all of the three
assumptions of `hasFDerivAt_of_tendstoUniformlyOnFilter` hold and that the `f'` are
continuous, then you can avoid the mean value theorem and much of the work around curried filters.

## Tags

uniform convergence, limits of derivatives
-/

public section


open Filter

open scoped uniformity Filter Topology

section LimitsOfDerivatives

variable {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι -> E -> G}
  {g : E -> G} {f' : ι -> E -> E ->L[𝕜] G} {g' : E -> E ->L[𝕜] G} {x : E}

/--
theorem `uniformCauchySeqOnFilter_of_fderiv` / 定理 `uniformCauchySeqOnFilter_of_fderiv`

English:
theorem uniformCauchySeqOnFilter_of_fderiv
  statement: (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hf' ⊢
  suffices
    TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (𝓝 x) ∧
      TendstoUniformlyOnFilter (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0 (l ×ˢ l) (𝓝 x) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero]; rw [add_zero] at this
    apply this.congr (.of_forall (fun x => by simp; abel))
  constructor
  · -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw [Metric.tendstoUniformlyOnFilter_iff] at hf' ⊢
    intro ε hε
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).and this)
    obtain ⟨R, hR, hR'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
    let r := min 1 R
    have hr : 0 < r := by simp [r, hR]
    have hr' : forall ⦃y : E⦄, y in Metric.ball x r -> c y := fun y hy =>
      hR' (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    have hxy : forall y : E, y in Metric.ball x r -> ‖y - x‖ < 1 := by
      intro y hy
      rw [Metric.mem_ball]; rw [dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hxyε : forall y : E, y in Metric.ball x r -> ε * ‖y - x‖ < ε := by
      intro y hy
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy)
    -- With a small ball in hand, apply the mean value theorem
    refine
      eventually_prod_iff.mpr
        ⟨_, b, (· in Metric.ball x r),
          eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
    simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e ⊢
    refine lt_of_le_of_lt ?_ (hxyε y hy)
    exact
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
        (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOnFilter_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    exact
      eventually_prod_iff.mpr
        ⟨fun n : ι × ι => f n.1 x in t ∧ f n.2 x in t,
          eventually_prod_iff.mpr ⟨_, ht, _, ht, fun {n} hn {n'} hn' => ⟨hn, hn'⟩⟩,
          fun _ => True,
          by simp,
          fun {n} hn {y} _ => by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2⟩

中文:
定理 uniformCauchySeqOnFilter_of_fderiv
  结论: (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hf' ⊢
  suffices
    TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (𝓝 x) ∧
      TendstoUniformlyOnFilter (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0 (l ×ˢ l) (𝓝 x) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero]; rw [add_zero] at this
    apply this.congr (.of_forall (fun x => by simp; abel))
  constructor
  · -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw [Metric.tendstoUniformlyOnFilter_iff] at hf' ⊢
    intro ε hε
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).and this)
    obtain ⟨R, hR, hR'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
    let r := min 1 R
    have hr : 0 < r := by simp [r, hR]
    have hr' : forall ⦃y : E⦄, y in Metric.ball x r -> c y := fun y hy =>
      hR' (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    have hxy : forall y : E, y in Metric.ball x r -> ‖y - x‖ < 1 := by
      intro y hy
      rw [Metric.mem_ball]; rw [dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hxyε : forall y : E, y in Metric.ball x r -> ε * ‖y - x‖ < ε := by
      intro y hy
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy)
    -- With a small ball in hand, apply the mean value theorem
    refine
      eventually_prod_iff.mpr
        ⟨_, b, (· in Metric.ball x r),
          eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
    simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e ⊢
    refine lt_of_le_of_lt ?_ (hxyε y hy)
    exact
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
        (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOnFilter_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    exact
      eventually_prod_iff.mpr
        ⟨fun n : ι × ι => f n.1 x in t ∧ f n.2 x in t,
          eventually_prod_iff.mpr ⟨_, ht, _, ht, fun {n} hn {n'} hn' => ⟨hn, hn'⟩⟩,
          fun _ => True,
          by simp,
          fun {n} hn {y} _ => by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2⟩

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, NormedSpace.restrictScalars, RCLike, SeminormedAddGroup, SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero, TendstoUniformlyOnFilter, add_zero, neg.add, neg_zero, rclike, restrictScalars, uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero
-/
theorem uniformCauchySeqOnFilter_of_fderiv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x) := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hf' ⊢
  suffices
    TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (𝓝 x) ∧
      TendstoUniformlyOnFilter (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0 (l ×ˢ l) (𝓝 x) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero]; rw [add_zero] at this
    apply this.congr (.of_forall (fun x => by simp; abel))
  constructor
  · -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw [Metric.tendstoUniformlyOnFilter_iff] at hf' ⊢
    intro ε hε
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).and this)
    obtain ⟨R, hR, hR'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
    let r := min 1 R
    have hr : 0 < r := by simp [r, hR]
    have hr' : forall ⦃y : E⦄, y in Metric.ball x r -> c y := fun y hy =>
      hR' (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    have hxy : forall y : E, y in Metric.ball x r -> ‖y - x‖ < 1 := by
      intro y hy
      rw [Metric.mem_ball]; rw [dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hxyε : forall y : E, y in Metric.ball x r -> ε * ‖y - x‖ < ε := by
      intro y hy
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy)
    -- With a small ball in hand, apply the mean value theorem
    refine
      eventually_prod_iff.mpr
        ⟨_, b, (· in Metric.ball x r),
          eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
    simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e ⊢
    refine lt_of_le_of_lt ?_ (hxyε y hy)
    exact
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
        (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOnFilter_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    exact
      eventually_prod_iff.mpr
        ⟨fun n : ι × ι => f n.1 x in t ∧ f n.2 x in t,
          eventually_prod_iff.mpr ⟨_, ht, _, ht, fun {n} hn {n'} hn' => ⟨hn, hn'⟩⟩,
          fun _ => True,
          by simp,
          fun {n} hn {y} _ => by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2⟩

/--
theorem `uniformCauchySeqOn_ball_of_fderiv` / 定理 `uniformCauchySeqOn_ball_of_fderiv`

English:
theorem uniformCauchySeqOn_ball_of_fderiv
  statement: {r : Real} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  rcases le_or_gt r 0 with (hr | hr)
  · simp only [Metric.ball_eq_empty.2 hr, UniformCauchySeqOn, Set.mem_empty_iff_false,
      IsEmpty.forall_iff, eventually_const, imp_true_iff]
  rw [SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero] at hf' ⊢
  suffices
    TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (Metric.ball x r) ∧
      TendstoUniformlyOn (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0
        (l ×ˢ l) (Metric.ball x r) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero]; rw [add_zero] at this
    refine this.congr ?_
    filter_upwards with n z _ using (by simp; abel)
  constructor
  · -- This inequality follows from the mean value theorem
    rw [Metric.tendstoUniformlyOn_iff] at hf' ⊢
    intro ε hε
    obtain ⟨q, hqpos, hq⟩ : exists q : Real, 0 < q ∧ q * r < ε := by
      simp_rw [mul_comm]
      exact exists_pos_mul_lt hε.lt r
    apply (hf' q hqpos.gt).mono
    intro n hn y hy
    simp_rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, norm_neg_add] at hn ⊢
    have mvt :=
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((hf n.1 z hz).sub (hf n.2 z hz)).hasFDerivWithinAt) (fun z hz => (hn z hz).le)
        (convex_ball x r) (Metric.mem_ball_self hr) hy
    refine lt_of_le_of_lt mvt ?_
    have : q * ‖y - x‖ < q * r :=
      mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using Metric.mem_ball.mp hy) (norm_nonneg _)
        hqpos
    exact this.trans hq
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    rw [eventually_prod_iff]
    refine ⟨fun n => f n x in t, ht, fun n => f n x in t, ht, ?_⟩
    intro n hn n' hn' z _
    rw [dist_eq_norm]; rw [Pi.zero_apply]; rw [zero_sub]; rw [norm_neg]; rw [← dist_eq_norm]
    exact ht' _ hn _ hn'

中文:
定理 uniformCauchySeqOn_ball_of_fderiv
  结论: {r : 实数} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  rcases le_or_gt r 0 with (hr | hr)
  · simp only [Metric.ball_eq_empty.2 hr, UniformCauchySeqOn, Set.mem_empty_iff_false,
      IsEmpty.forall_iff, eventually_const, imp_true_iff]
  rw [SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero] at hf' ⊢
  suffices
    TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (Metric.ball x r) ∧
      TendstoUniformlyOn (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0
        (l ×ˢ l) (Metric.ball x r) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero]; rw [add_zero] at this
    refine this.congr ?_
    filter_upwards with n z _ using (by simp; abel)
  constructor
  · -- This inequality follows from the mean value theorem
    rw [Metric.tendstoUniformlyOn_iff] at hf' ⊢
    intro ε hε
    obtain ⟨q, hqpos, hq⟩ : exists q : Real, 0 < q ∧ q * r < ε := by
      simp_rw [mul_comm]
      exact exists_pos_mul_lt hε.lt r
    apply (hf' q hqpos.gt).mono
    intro n hn y hy
    simp_rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, norm_neg_add] at hn ⊢
    have mvt :=
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((hf n.1 z hz).sub (hf n.2 z hz)).hasFDerivWithinAt) (fun z hz => (hn z hz).le)
        (convex_ball x r) (Metric.mem_ball_self hr) hy
    refine lt_of_le_of_lt mvt ?_
    have : q * ‖y - x‖ < q * r :=
      mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using Metric.mem_ball.mp hy) (norm_nonneg _)
        hqpos
    exact this.trans hq
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    rw [eventually_prod_iff]
    refine ⟨fun n => f n x in t, ht, fun n => f n x in t, ht, ?_⟩
    intro n hn n' hn' z _
    rw [dist_eq_norm]; rw [Pi.zero_apply]; rw [zero_sub]; rw [norm_neg]; rw [← dist_eq_norm]
    exact ht' _ hn _ hn'

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, IsRCLikeNormedField, IsRCLikeNormedField.rclike, Metric, Metric.ball_eq_empty, NormedSpace, NormedSpace.restrictScalars, RCLike, SeminormedAddGroup, SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero, Set.mem_empty_iff_false, TendstoUniformlyOn, UniformCauchySeqOn, ball_eq_empty, cauchy_map_iff, eventually_const, forall_iff, imp_true_iff, le_or_gt
-/
theorem uniformCauchySeqOn_ball_of_fderiv {r : Real} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
    (hf : forall n : ι, forall y : E, y in Metric.ball x r -> HasFDerivAt (f n) (f' n y) y)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOn f l (Metric.ball x r) := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  rcases le_or_gt r 0 with (hr | hr)
  · simp only [Metric.ball_eq_empty.2 hr, UniformCauchySeqOn, Set.mem_empty_iff_false,
      IsEmpty.forall_iff, eventually_const, imp_true_iff]
  rw [SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero] at hf' ⊢
  suffices
    TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (Metric.ball x r) ∧
      TendstoUniformlyOn (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0
        (l ×ˢ l) (Metric.ball x r) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero]; rw [add_zero] at this
    refine this.congr ?_
    filter_upwards with n z _ using (by simp; abel)
  constructor
  · -- This inequality follows from the mean value theorem
    rw [Metric.tendstoUniformlyOn_iff] at hf' ⊢
    intro ε hε
    obtain ⟨q, hqpos, hq⟩ : exists q : Real, 0 < q ∧ q * r < ε := by
      simp_rw [mul_comm]
      exact exists_pos_mul_lt hε.lt r
    apply (hf' q hqpos.gt).mono
    intro n hn y hy
    simp_rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, norm_neg_add] at hn ⊢
    have mvt :=
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((hf n.1 z hz).sub (hf n.2 z hz)).hasFDerivWithinAt) (fun z hz => (hn z hz).le)
        (convex_ball x r) (Metric.mem_ball_self hr) hy
    refine lt_of_le_of_lt mvt ?_
    have : q * ‖y - x‖ < q * r :=
      mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using Metric.mem_ball.mp hy) (norm_nonneg _)
        hqpos
    exact this.trans hq
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    rw [eventually_prod_iff]
    refine ⟨fun n => f n x in t, ht, fun n => f n x in t, ht, ?_⟩
    intro n hn n' hn' z _
    rw [dist_eq_norm]; rw [Pi.zero_apply]; rw [zero_sub]; rw [norm_neg]; rw [← dist_eq_norm]
    exact ht' _ hn _ hn'

/--
theorem `cauchy_map_of_uniformCauchySeqOn_fderiv` / 定理 `cauchy_map_of_uniformCauchySeqOn_fderiv`

English:
theorem cauchy_map_of_uniformCauchySeqOn_fderiv
  statement: {s : Set E} (hs : IsOpen s) (h's : IsPreconnected s)
  proof: by
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  let t := { y | y in s ∧ Cauchy (map (fun n => f n y) l) }
  suffices H : s subseteq t from (H hx).2
  have A : forall x ε, x in t -> Metric.ball x ε subseteq s -> Metric.ball x ε subseteq t := fun x ε xt hx y hy =>
    ⟨hx hy,
      (uniformCauchySeqOn_ball_of_fderiv (hf'.mono hx) (fun n y hy => hf n y (hx hy))
            xt.2).cauchy_map
        hy⟩
  have open_t : IsOpen t := by
    rw [Metric.isOpen_iff]
    intro x hx
    rcases Metric.isOpen_iff.1 hs x hx.1 with ⟨ε, εpos, hε⟩
    exact ⟨ε, εpos, A x ε hx hε⟩
  have st_nonempty : (s inter t).Nonempty := ⟨x₀, hx₀, ⟨hx₀, hfg⟩⟩
  suffices H : closure t inter s subseteq t from h's.subset_of_closure_inter_subset open_t st_nonempty H
  rintro x ⟨xt, xs⟩
  obtain ⟨ε, εpos, hε⟩ : exists (ε : Real), ε > 0 ∧ Metric.ball x ε subseteq s := Metric.isOpen_iff.1 hs x xs
  obtain ⟨y, yt, hxy⟩ : exists (y : E), y in t ∧ dist x y < ε / 2 :=
    Metric.mem_closure_iff.1 xt _ (half_pos εpos)
  have B : Metric.ball y (ε / 2) subseteq Metric.ball x ε := by
    apply Metric.ball_subset_ball'; rw [dist_comm]; linarith
  exact A y (ε / 2) yt (B.trans hε) (Metric.mem_ball.2 hxy)

中文:
定理 cauchy_map_of_uniformCauchySeqOn_fderiv
  结论: {s : 集合 E} (hs : 是开集 s) (h's : 是预连通 s)
  证明: by
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  let t := { y | y in s ∧ Cauchy (map (fun n => f n y) l) }
  suffices H : s subseteq t from (H hx).2
  have A : forall x ε, x in t -> Metric.ball x ε subseteq s -> Metric.ball x ε subseteq t := fun x ε xt hx y hy =>
    ⟨hx hy,
      (uniformCauchySeqOn_ball_of_fderiv (hf'.mono hx) (fun n y hy => hf n y (hx hy))
            xt.2).cauchy_map
        hy⟩
  have open_t : IsOpen t := by
    rw [Metric.isOpen_iff]
    intro x hx
    rcases Metric.isOpen_iff.1 hs x hx.1 with ⟨ε, εpos, hε⟩
    exact ⟨ε, εpos, A x ε hx hε⟩
  have st_nonempty : (s inter t).Nonempty := ⟨x₀, hx₀, ⟨hx₀, hfg⟩⟩
  suffices H : closure t inter s subseteq t from h's.subset_of_closure_inter_subset open_t st_nonempty H
  rintro x ⟨xt, xs⟩
  obtain ⟨ε, εpos, hε⟩ : exists (ε : Real), ε > 0 ∧ Metric.ball x ε subseteq s := Metric.isOpen_iff.1 hs x xs
  obtain ⟨y, yt, hxy⟩ : exists (y : E), y in t ∧ dist x y < ε / 2 :=
    Metric.mem_closure_iff.1 xt _ (half_pos εpos)
  have B : Metric.ball y (ε / 2) subseteq Metric.ball x ε := by
    apply Metric.ball_subset_ball'; rw [dist_comm]; linarith
  exact A y (ε / 2) yt (B.trans hε) (Metric.mem_ball.2 hxy)

Depends on / 依赖: Cauchy, IsOpen, Metric, Metric.ball, Metric.isOpen_iff, cauchy_map, cauchy_map_iff, isOpen_iff, open_t, subseteq, uniformCauchySeqOn_ball_of_fderiv
-/
theorem cauchy_map_of_uniformCauchySeqOn_fderiv {s : Set E} (hs : IsOpen s) (h's : IsPreconnected s)
    (hf' : UniformCauchySeqOn f' l s) (hf : forall n : ι, forall y : E, y in s -> HasFDerivAt (f n) (f' n y) y)
    {x₀ x : E} (hx₀ : x₀ in s) (hx : x in s) (hfg : Cauchy (map (fun n => f n x₀) l)) :
    Cauchy (map (fun n => f n x) l) := by
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  let t := { y | y in s ∧ Cauchy (map (fun n => f n y) l) }
  suffices H : s subseteq t from (H hx).2
  have A : forall x ε, x in t -> Metric.ball x ε subseteq s -> Metric.ball x ε subseteq t := fun x ε xt hx y hy =>
    ⟨hx hy,
      (uniformCauchySeqOn_ball_of_fderiv (hf'.mono hx) (fun n y hy => hf n y (hx hy))
            xt.2).cauchy_map
        hy⟩
  have open_t : IsOpen t := by
    rw [Metric.isOpen_iff]
    intro x hx
    rcases Metric.isOpen_iff.1 hs x hx.1 with ⟨ε, εpos, hε⟩
    exact ⟨ε, εpos, A x ε hx hε⟩
  have st_nonempty : (s inter t).Nonempty := ⟨x₀, hx₀, ⟨hx₀, hfg⟩⟩
  suffices H : closure t inter s subseteq t from h's.subset_of_closure_inter_subset open_t st_nonempty H
  rintro x ⟨xt, xs⟩
  obtain ⟨ε, εpos, hε⟩ : exists (ε : Real), ε > 0 ∧ Metric.ball x ε subseteq s := Metric.isOpen_iff.1 hs x xs
  obtain ⟨y, yt, hxy⟩ : exists (y : E), y in t ∧ dist x y < ε / 2 :=
    Metric.mem_closure_iff.1 xt _ (half_pos εpos)
  have B : Metric.ball y (ε / 2) subseteq Metric.ball x ε := by
    apply Metric.ball_subset_ball'; rw [dist_comm]; linarith
  exact A y (ε / 2) yt (B.trans hε) (Metric.mem_ball.2 hxy)

/--
theorem `difference_quotients_converge_uniformly` / 定理 `difference_quotients_converge_uniformly`

English:
theorem difference_quotients_converge_uniformly
  proof: by
  let A : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  refine
    UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto ?_
      ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy =>
        (hy.1.sub hy.2).const_smul _)
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero]
  rw [Metric.tendstoUniformlyOnFilter_iff]
  have hfg' := hf'.uniformCauchySeqOnFilter
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hfg'
  rw [Metric.tendstoUniformlyOnFilter_iff] at hfg'
  intro ε hε
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε
  specialize hfg' (q : Real) (by simp [hqpos])
  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this)
  obtain ⟨r, hr, hr'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine
    ⟨_, b, (· in Metric.ball x r),
      eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
  simp only [Pi.zero_apply, dist_zero_left]
  rw [norm_neg_add]; rw [← smul_sub]; rw [norm_smul]; rw [norm_inv]; rw [RCLike.norm_coe_norm]
  refine lt_of_le_of_lt ?_ hqε
  by_cases hyz' : x = y; · simp [hyz', hqpos.le]
  have hyz : 0 < ‖y - x‖ := by rw [norm_pos_iff]; intro hy'; exact hyz' (eq_of_sub_eq_zero hy').symm
  rw [inv_mul_le_iff₀ hyz]; rw [mul_comm]; rw [sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e
  refine
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
      (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy

中文:
定理 difference_quotients_converge_uniformly
  证明: by
  let A : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  refine
    UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto ?_
      ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy =>
        (hy.1.sub hy.2).const_smul _)
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero]
  rw [Metric.tendstoUniformlyOnFilter_iff]
  have hfg' := hf'.uniformCauchySeqOnFilter
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hfg'
  rw [Metric.tendstoUniformlyOnFilter_iff] at hfg'
  intro ε hε
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε
  specialize hfg' (q : Real) (by simp [hqpos])
  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this)
  obtain ⟨r, hr, hr'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine
    ⟨_, b, (· in Metric.ball x r),
      eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
  simp only [Pi.zero_apply, dist_zero_left]
  rw [norm_neg_add]; rw [← smul_sub]; rw [norm_smul]; rw [norm_inv]; rw [RCLike.norm_coe_norm]
  refine lt_of_le_of_lt ?_ hqε
  by_cases hyz' : x = y; · simp [hyz', hqpos.le]
  have hyz : 0 < ‖y - x‖ := by rw [norm_pos_iff]; intro hy'; exact hyz' (eq_of_sub_eq_zero hy').symm
  rw [inv_mul_le_iff₀ hyz]; rw [mul_comm]; rw [sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e
  refine
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
      (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy

Depends on / 依赖: Metric, Metric.tendstoUniformlyOnFilter_iff, NormedSpace, NormedSpace.restrictScalars, SeminormedAddGroup, SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero, UniformCauchySeqOnFilter, UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto, const_smul, eventually_const, eventually_const.mpr, hfg.and, hfg.self_of_nhds, restrictScalars, self_of_nhds, tendstoUniformlyOnFilter_iff, tendstoUniformlyOnFilter_of_tendsto, uniformCauchySeqOnFilter, uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero
-/
theorem difference_quotients_converge_uniformly
    {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι -> E -> G}
    {g : E -> G} {f' : ι -> E -> E ->L[𝕜] G} {g' : E -> E ->L[𝕜] G} {x : E}
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : forallᶠ y : E in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) :
    TendstoUniformlyOnFilter (fun n : ι => fun y : E => (‖y - x‖⁻¹ : 𝕜) • (f n y - f n x))
      (fun y : E => (‖y - x‖⁻¹ : 𝕜) • (g y - g x)) l (𝓝 x) := by
  let A : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  refine
    UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto ?_
      ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy =>
        (hy.1.sub hy.2).const_smul _)
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero]
  rw [Metric.tendstoUniformlyOnFilter_iff]
  have hfg' := hf'.uniformCauchySeqOnFilter
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hfg'
  rw [Metric.tendstoUniformlyOnFilter_iff] at hfg'
  intro ε hε
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε
  specialize hfg' (q : Real) (by simp [hqpos])
  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this)
  obtain ⟨r, hr, hr'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine
    ⟨_, b, (· in Metric.ball x r),
      eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
  simp only [Pi.zero_apply, dist_zero_left]
  rw [norm_neg_add]; rw [← smul_sub]; rw [norm_smul]; rw [norm_inv]; rw [RCLike.norm_coe_norm]
  refine lt_of_le_of_lt ?_ hqε
  by_cases hyz' : x = y; · simp [hyz', hqpos.le]
  have hyz : 0 < ‖y - x‖ := by rw [norm_pos_iff]; intro hy'; exact hyz' (eq_of_sub_eq_zero hy').symm
  rw [inv_mul_le_iff₀ hyz]; rw [mul_comm]; rw [sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e
  refine
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
      (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy

/--
theorem `hasFDerivAt_of_tendstoUniformlyOnFilter` / 定理 `hasFDerivAt_of_tendstoUniformlyOnFilter`

English:
theorem hasFDerivAt_of_tendstoUniformlyOnFilter
  statement: [NeBot l]
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- The proof strategy follows several steps:
  -- 1. The quantifiers in the definition of the derivative are
  -- `∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  -- `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x)` which will allow us to introduce the
  -- `f(') n`
  -- 2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  -- the quantifiers using the uniform convergence assumption
  rw [hasFDerivAt_iff_tendsto]
  -- Introduce extra quantifier via curried filters
  suffices
    Tendsto (fun y : ι × E => ‖y.2 - x‖⁻¹ * ‖g y.2 - g x - (g' x) (y.2 - x)‖)
      (l.curry (𝓝 x)) (𝓝 0) by
    rw [Metric.tendsto_nhds] at this ⊢
    intro ε hε
    specialize this ε hε
    rw [eventually_curry_iff] at this
    simp only at this
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const])
  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  -- * The difference functions of the `f n` converge *uniformly* to the difference functions
  -- of the `g n`
  -- * The `f' n` are the derivatives of the `f n`
  -- * The `f' n` converge to `g'` at `x`
  conv =>
    congr
    ext
    rw [← abs_norm]; rw [← abs_inv]; rw [← @RCLike.norm_ofReal 𝕜 _ _]; rw [RCLike.ofReal_inv]; rw [← norm_smul]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have :
    (fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
      ((fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
          fun a : ι × E =>
          (‖a.2 - x‖⁻¹ : 𝕜) • (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x))) +
        fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (f' a.1 x - g' x) (a.2 - x) := by
    ext; simp only [Pi.add_apply]; rw [← smul_add, ← smul_add]; congr
    simp only [map_sub, sub_add_sub_cancel, FunLike.coe_sub, Pi.sub_apply]
    abel
  simp_rw [this]
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0) := by simp only [add_zero]
  rw [this]
  refine Tendsto.add (Tendsto.add ?_ ?_) ?_
  · have := difference_quotients_converge_uniformly hf' hf hfg
    rw [Metric.tendstoUniformlyOnFilter_iff] at this
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((this ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn ⊢
    convert! hn using 2
    module
  · -- (Almost) the definition of the derivatives
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine hf.curry.mono fun n hn => ?_
    have := hn.self_of_nhds
    rw [hasFDerivAt_iff_tendsto]; rw [Metric.tendsto_nhds] at this
    refine (this ε hε).mono fun y hy => ?_
    rw [dist_eq_norm] at hy ⊢
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢
    rw [norm_smul]; rw [norm_inv]; rw [RCLike.norm_coe_norm]
    exact hy
  · -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine Tendsto.mono_left ?_ curry_le_prod
    have h1 : Tendsto (fun n : ι × E => g' n.2 - f' n.1 n.2) (l ×ˢ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendstoUniformlyOnFilter_iff] at hf'
      exact Metric.tendsto_nhds.mpr fun ε hε => by simpa [dist_eq_norm] using hf' ε hε
    have h2 : Tendsto (fun n : ι => g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1 ⊢
      exact fun ε hε => (h1 ε hε).curry.mono fun n hn => hn.self_of_nhds
    refine squeeze_zero_norm ?_
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_fst.comp (h2.prodMap tendsto_id)))
    intro n
    simp_rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    by_cases hx : x = n.2; · simp [hx]
    have hnx : 0 < ‖n.2 - x‖ := by
      rw [norm_pos_iff]; intro hx'; exact hx (eq_of_sub_eq_zero hx').symm
    rw [inv_mul_le_iff₀ hnx]; rw [mul_comm]
    simp only [Function.comp_apply, Prod.map_apply']
    rw [norm_sub_rev]
    exact (f' n.1 x - g' x).le_opNorm (n.2 - x)

中文:
定理 hasFDerivAt_of_tendstoUniformlyOnFilter
  结论: [NeBot l]
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- The proof strategy follows several steps:
  -- 1. The quantifiers in the definition of the derivative are
  -- `∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  -- `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x)` which will allow us to introduce the
  -- `f(') n`
  -- 2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  -- the quantifiers using the uniform convergence assumption
  rw [hasFDerivAt_iff_tendsto]
  -- Introduce extra quantifier via curried filters
  suffices
    Tendsto (fun y : ι × E => ‖y.2 - x‖⁻¹ * ‖g y.2 - g x - (g' x) (y.2 - x)‖)
      (l.curry (𝓝 x)) (𝓝 0) by
    rw [Metric.tendsto_nhds] at this ⊢
    intro ε hε
    specialize this ε hε
    rw [eventually_curry_iff] at this
    simp only at this
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const])
  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  -- * The difference functions of the `f n` converge *uniformly* to the difference functions
  -- of the `g n`
  -- * The `f' n` are the derivatives of the `f n`
  -- * The `f' n` converge to `g'` at `x`
  conv =>
    congr
    ext
    rw [← abs_norm]; rw [← abs_inv]; rw [← @RCLike.norm_ofReal 𝕜 _ _]; rw [RCLike.ofReal_inv]; rw [← norm_smul]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have :
    (fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
      ((fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
          fun a : ι × E =>
          (‖a.2 - x‖⁻¹ : 𝕜) • (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x))) +
        fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (f' a.1 x - g' x) (a.2 - x) := by
    ext; simp only [Pi.add_apply]; rw [← smul_add, ← smul_add]; congr
    simp only [map_sub, sub_add_sub_cancel, FunLike.coe_sub, Pi.sub_apply]
    abel
  simp_rw [this]
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0) := by simp only [add_zero]
  rw [this]
  refine Tendsto.add (Tendsto.add ?_ ?_) ?_
  · have := difference_quotients_converge_uniformly hf' hf hfg
    rw [Metric.tendstoUniformlyOnFilter_iff] at this
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((this ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn ⊢
    convert! hn using 2
    module
  · -- (Almost) the definition of the derivatives
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine hf.curry.mono fun n hn => ?_
    have := hn.self_of_nhds
    rw [hasFDerivAt_iff_tendsto]; rw [Metric.tendsto_nhds] at this
    refine (this ε hε).mono fun y hy => ?_
    rw [dist_eq_norm] at hy ⊢
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢
    rw [norm_smul]; rw [norm_inv]; rw [RCLike.norm_coe_norm]
    exact hy
  · -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine Tendsto.mono_left ?_ curry_le_prod
    have h1 : Tendsto (fun n : ι × E => g' n.2 - f' n.1 n.2) (l ×ˢ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendstoUniformlyOnFilter_iff] at hf'
      exact Metric.tendsto_nhds.mpr fun ε hε => by simpa [dist_eq_norm] using hf' ε hε
    have h2 : Tendsto (fun n : ι => g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1 ⊢
      exact fun ε hε => (h1 ε hε).curry.mono fun n hn => hn.self_of_nhds
    refine squeeze_zero_norm ?_
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_fst.comp (h2.prodMap tendsto_id)))
    intro n
    simp_rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    by_cases hx : x = n.2; · simp [hx]
    have hnx : 0 < ‖n.2 - x‖ := by
      rw [norm_pos_iff]; intro hx'; exact hx (eq_of_sub_eq_zero hx').symm
    rw [inv_mul_le_iff₀ hnx]; rw [mul_comm]
    simp only [Function.comp_apply, Prod.map_apply']
    rw [norm_sub_rev]
    exact (f' n.1 x - g' x).le_opNorm (n.2 - x)

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, RCLike, rclike
-/
theorem hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : forallᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasFDerivAt g (g' x) x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- The proof strategy follows several steps:
  -- 1. The quantifiers in the definition of the derivative are
  -- `∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  -- `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x)` which will allow us to introduce the
  -- `f(') n`
  -- 2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  -- the quantifiers using the uniform convergence assumption
  rw [hasFDerivAt_iff_tendsto]
  -- Introduce extra quantifier via curried filters
  suffices
    Tendsto (fun y : ι × E => ‖y.2 - x‖⁻¹ * ‖g y.2 - g x - (g' x) (y.2 - x)‖)
      (l.curry (𝓝 x)) (𝓝 0) by
    rw [Metric.tendsto_nhds] at this ⊢
    intro ε hε
    specialize this ε hε
    rw [eventually_curry_iff] at this
    simp only at this
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const])
  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  -- * The difference functions of the `f n` converge *uniformly* to the difference functions
  -- of the `g n`
  -- * The `f' n` are the derivatives of the `f n`
  -- * The `f' n` converge to `g'` at `x`
  conv =>
    congr
    ext
    rw [← abs_norm]; rw [← abs_inv]; rw [← @RCLike.norm_ofReal 𝕜 _ _]; rw [RCLike.ofReal_inv]; rw [← norm_smul]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have :
    (fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
      ((fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
          fun a : ι × E =>
          (‖a.2 - x‖⁻¹ : 𝕜) • (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x))) +
        fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (f' a.1 x - g' x) (a.2 - x) := by
    ext; simp only [Pi.add_apply]; rw [← smul_add, ← smul_add]; congr
    simp only [map_sub, sub_add_sub_cancel, FunLike.coe_sub, Pi.sub_apply]
    abel
  simp_rw [this]
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0) := by simp only [add_zero]
  rw [this]
  refine Tendsto.add (Tendsto.add ?_ ?_) ?_
  · have := difference_quotients_converge_uniformly hf' hf hfg
    rw [Metric.tendstoUniformlyOnFilter_iff] at this
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((this ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn ⊢
    convert! hn using 2
    module
  · -- (Almost) the definition of the derivatives
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine hf.curry.mono fun n hn => ?_
    have := hn.self_of_nhds
    rw [hasFDerivAt_iff_tendsto]; rw [Metric.tendsto_nhds] at this
    refine (this ε hε).mono fun y hy => ?_
    rw [dist_eq_norm] at hy ⊢
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢
    rw [norm_smul]; rw [norm_inv]; rw [RCLike.norm_coe_norm]
    exact hy
  · -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine Tendsto.mono_left ?_ curry_le_prod
    have h1 : Tendsto (fun n : ι × E => g' n.2 - f' n.1 n.2) (l ×ˢ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendstoUniformlyOnFilter_iff] at hf'
      exact Metric.tendsto_nhds.mpr fun ε hε => by simpa [dist_eq_norm] using hf' ε hε
    have h2 : Tendsto (fun n : ι => g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1 ⊢
      exact fun ε hε => (h1 ε hε).curry.mono fun n hn => hn.self_of_nhds
    refine squeeze_zero_norm ?_
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_fst.comp (h2.prodMap tendsto_id)))
    intro n
    simp_rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    by_cases hx : x = n.2; · simp [hx]
    have hnx : 0 < ‖n.2 - x‖ := by
      rw [norm_pos_iff]; intro hx'; exact hx (eq_of_sub_eq_zero hx').symm
    rw [inv_mul_le_iff₀ hnx]; rw [mul_comm]
    simp only [Function.comp_apply, Prod.map_apply']
    rw [norm_sub_rev]
    exact (f' n.1 x - g' x).le_opNorm (n.2 - x)

/--
theorem `hasFDerivAt_of_tendstoLocallyUniformlyOn` / 定理 `hasFDerivAt_of_tendstoLocallyUniformlyOn`

English:
theorem hasFDerivAt_of_tendstoLocallyUniformlyOn
  statement: [NeBot l] {s : Set E} (hs : IsOpen s)
  proof: by
  have h1 : s in 𝓝 x := hs.mem_nhds hx
  have h3 : Set.univ ×ˢ s in l ×ˢ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self_iff]
  have h4 : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_of_mem h3 fun ⟨n, z⟩ ⟨_, hz⟩ => hf n z hz
  refine hasFDerivAt_of_tendstoUniformlyOnFilter ?_ h4 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

中文:
定理 hasFDerivAt_of_tendstoLocallyUniformlyOn
  结论: [NeBot l] {s : 集合 E} (hs : 是开集 s)
  证明: by
  have h1 : s in 𝓝 x := hs.mem_nhds hx
  have h3 : Set.univ ×ˢ s in l ×ˢ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self_iff]
  have h4 : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_of_mem h3 fun ⟨n, z⟩ ⟨_, hz⟩ => hf n z hz
  refine hasFDerivAt_of_tendstoUniformlyOnFilter ?_ h4 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

Depends on / 依赖: HasFDerivAt, IsOpen, IsOpen.nhdsWithin_eq, Set.univ, and_self_iff, eventually_of_mem, hasFDerivAt_of_tendstoUniformlyOnFilter, hs.mem_nhds, mem_nhds, nhdsWithin_eq, prod_mem_prod_iff, tendstoLocallyUniformlyOn_iff_filter, tendstoLocallyUniformlyOn_iff_filter.mp, univ_mem
-/
theorem hasFDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s) (hf : forall n, forall x in s, HasFDerivAt (f n) (f' n x) x)
    (hfg : forall x in s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x in s) :
    HasFDerivAt g (g' x) x := by
  have h1 : s in 𝓝 x := hs.mem_nhds hx
  have h3 : Set.univ ×ˢ s in l ×ˢ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self_iff]
  have h4 : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_of_mem h3 fun ⟨n, z⟩ ⟨_, hz⟩ => hf n z hz
  refine hasFDerivAt_of_tendstoUniformlyOnFilter ?_ h4 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/--
theorem `hasFDerivAt_of_tendsto_locally_uniformly_on'` / 定理 `hasFDerivAt_of_tendsto_locally_uniformly_on'`

English:
theorem hasFDerivAt_of_tendsto_locally_uniformly_on'
  statement: [NeBot l] {s : Set E} (hs : IsOpen s)
  proof: by
  refine hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf' (fun n z hz => ?_) hfg hx
  exact ((hf n z hz).differentiableAt (hs.mem_nhds hz)).hasFDerivAt

中文:
定理 hasFDerivAt_of_tendsto_locally_uniformly_on'
  结论: [NeBot l] {s : 集合 E} (hs : 是开集 s)
  证明: by
  refine hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf' (fun n z hz => ?_) hfg hx
  exact ((hf n z hz).differentiableAt (hs.mem_nhds hz)).hasFDerivAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hasFDerivAt_of_tendstoLocallyUniformlyOn, hs.mem_nhds, mem_nhds
-/
theorem hasFDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (fderiv 𝕜 ∘ f) g' l s) (hf : forall n, DifferentiableOn 𝕜 (f n) s)
    (hfg : forall x in s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x in s) :
    HasFDerivAt g (g' x) x := by
  refine hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf' (fun n z hz => ?_) hfg hx
  exact ((hf n z hz).differentiableAt (hs.mem_nhds hz)).hasFDerivAt

/--
theorem `hasFDerivAt_of_tendstoUniformlyOn` / 定理 `hasFDerivAt_of_tendstoUniformlyOn`

English:
theorem hasFDerivAt_of_tendstoUniformlyOn
  statement: [NeBot l] {s : Set E} (hs : IsOpen s)
  proof: hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

中文:
定理 hasFDerivAt_of_tendstoUniformlyOn
  结论: [NeBot l] {s : 集合 E} (hs : 是开集 s)
  证明: hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

Depends on / 依赖: hasFDerivAt_of_tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn
-/
theorem hasFDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoUniformlyOn f' g' l s)
    (hf : forall n : ι, forall x : E, x in s -> HasFDerivAt (f n) (f' n x) x)
    (hfg : forall x : E, x in s -> Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x in s) :
    HasFDerivAt g (g' x) x :=
  hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

/--
theorem `hasFDerivAt_of_tendstoUniformly` / 定理 `hasFDerivAt_of_tendstoUniformly`

English:
theorem hasFDerivAt_of_tendstoUniformly
  statement: [NeBot l] (hf' : TendstoUniformly f' g' l)
  proof: by
  have hf : forall n : ι, forall x : E, x in Set.univ -> HasFDerivAt (f n) (f' n x) x := by simp [hf]
  have hfg : forall x : E, x in Set.univ -> Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

中文:
定理 hasFDerivAt_of_tendstoUniformly
  结论: [NeBot l] (hf' : TendstoUniformly f' g' l)
  证明: by
  have hf : forall n : ι, forall x : E, x in Set.univ -> HasFDerivAt (f n) (f' n x) x := by simp [hf]
  have hfg : forall x : E, x in Set.univ -> Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

Depends on / 依赖: HasFDerivAt, Set.mem_univ, Set.univ, Tendsto, TendstoUniformlyOn, hasFDerivAt_of_tendstoUniformlyOn, isOpen_univ, mem_univ, tendstoUniformlyOn_univ
-/
theorem hasFDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
    (hf : forall n : ι, forall x : E, HasFDerivAt (f n) (f' n x) x)
    (hfg : forall x : E, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : E) : HasFDerivAt g (g' x) x := by
  have hf : forall n : ι, forall x : E, x in Set.univ -> HasFDerivAt (f n) (f' n x) x := by simp [hf]
  have hfg : forall x : E, x in Set.univ -> Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

end LimitsOfDerivatives

section deriv

/-! ### `deriv` versions of above theorems

In this section, we provide `deriv` equivalents of the `fderiv` lemmas in the previous section.
-/


variable {ι : Type*} {l : Filter ι} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {G : Type*} [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f : ι -> 𝕜 -> G} {g : 𝕜 -> G} {f' : ι -> 𝕜 -> G} {g' : 𝕜 -> G} {x : 𝕜}

/--
theorem `UniformCauchySeqOnFilter.one_smulRight` / 定理 `UniformCauchySeqOnFilter.one_smulRight`

English:
theorem UniformCauchySeqOnFilter.one_smulRight
  statement: {l' : Filter 𝕜}
  proof: by
  intro u hu
  simpa using hf' _ ((ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous hu)

中文:
定理 UniformCauchySeqOnFilter.one_smulRight
  结论: {l' : 滤子 𝕜}
  证明: by
  intro u hu
  simpa using hf' _ ((ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous hu)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRightL, smulRightL, uniformContinuous
-/
theorem UniformCauchySeqOnFilter.one_smulRight {l' : Filter 𝕜}
    (hf' : UniformCauchySeqOnFilter f' l l') :
    UniformCauchySeqOnFilter (fun n z => (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)) l l' := by
  intro u hu
  simpa using hf' _ ((ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous hu)

variable [IsRCLikeNormedField 𝕜]

/--
theorem `uniformCauchySeqOnFilter_of_deriv` / 定理 `uniformCauchySeqOnFilter_of_deriv`

English:
theorem uniformCauchySeqOnFilter_of_deriv
  statement: (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
  proof: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  exact uniformCauchySeqOnFilter_of_fderiv hf'.one_smulRight hf hfg

中文:
定理 uniformCauchySeqOnFilter_of_deriv
  结论: (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
  证明: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  exact uniformCauchySeqOnFilter_of_fderiv hf'.one_smulRight hf hfg

Depends on / 依赖: hasDerivAt_iff_hasFDerivAt, one_smulRight, simp_rw, uniformCauchySeqOnFilter_of_fderiv
-/
theorem uniformCauchySeqOnFilter_of_deriv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x) := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  exact uniformCauchySeqOnFilter_of_fderiv hf'.one_smulRight hf hfg

/--
theorem `uniformCauchySeqOn_ball_of_deriv` / 定理 `uniformCauchySeqOn_ball_of_deriv`

English:
theorem uniformCauchySeqOn_ball_of_deriv
  statement: {r : Real} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
  proof: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  have hf' :
    UniformCauchySeqOn (fun n z => (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)) l
      (Metric.ball x r) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_uniformCauchySeqOn hf'
  exact uniformCauchySeqOn_ball_of_fderiv hf' hf hfg

中文:
定理 uniformCauchySeqOn_ball_of_deriv
  结论: {r : 实数} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
  证明: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  have hf' :
    UniformCauchySeqOn (fun n z => (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)) l
      (Metric.ball x r) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_uniformCauchySeqOn hf'
  exact uniformCauchySeqOn_ball_of_fderiv hf' hf hfg

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRightL, Metric, Metric.ball, UniformCauchySeqOn, comp_uniformCauchySeqOn, hasDerivAt_iff_hasFDerivAt, simp_rw, smulRight, smulRightL, uniformCauchySeqOn_ball_of_fderiv, uniformContinuous, uniformContinuous.comp_uniformCauchySeqOn
-/
theorem uniformCauchySeqOn_ball_of_deriv {r : Real} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
    (hf : forall n : ι, forall y : 𝕜, y in Metric.ball x r -> HasDerivAt (f n) (f' n y) y)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOn f l (Metric.ball x r) := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  have hf' :
    UniformCauchySeqOn (fun n z => (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)) l
      (Metric.ball x r) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_uniformCauchySeqOn hf'
  exact uniformCauchySeqOn_ball_of_fderiv hf' hf hfg

/--
theorem `hasDerivAt_of_tendstoUniformlyOnFilter` / 定理 `hasDerivAt_of_tendstoUniformlyOnFilter`

English:
theorem hasDerivAt_of_tendstoUniformlyOnFilter
  statement: [NeBot l]
  proof: by
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `hasFDerivAt_of_tendstoUniformlyOnFilter`
  let F' n z := (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)
  let G' z := (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (g' z)
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf ⊢
  have hf' : TendstoUniformlyOnFilter F' G' l (𝓝 x) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_tendstoUniformlyOnFilter hf'
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hf' hf hfg

中文:
定理 hasDerivAt_of_tendstoUniformlyOnFilter
  结论: [NeBot l]
  证明: by
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `hasFDerivAt_of_tendstoUniformlyOnFilter`
  let F' n z := (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)
  let G' z := (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (g' z)
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf ⊢
  have hf' : TendstoUniformlyOnFilter F' G' l (𝓝 x) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_tendstoUniformlyOnFilter hf'
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hf' hf hfg
-/
theorem hasDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : forallᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasDerivAt g (g' x) x := by
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `hasFDerivAt_of_tendstoUniformlyOnFilter`
  let F' n z := (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (f' n z)
  let G' z := (1 : 𝕜 ->L[𝕜] 𝕜).smulRight (g' z)
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf ⊢
  have hf' : TendstoUniformlyOnFilter F' G' l (𝓝 x) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_tendstoUniformlyOnFilter hf'
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hf' hf hfg

/--
theorem `hasDerivAt_of_tendstoLocallyUniformlyOn` / 定理 `hasDerivAt_of_tendstoLocallyUniformlyOn`

English:
theorem hasDerivAt_of_tendstoLocallyUniformlyOn
  statement: [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
  proof: by
  have h1 : s in 𝓝 x := hs.mem_nhds hx
  have h2 : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_prod_iff.2 ⟨_, hf, fun x => x in s, h1, fun {n} => id⟩
  refine hasDerivAt_of_tendstoUniformlyOnFilter ?_ h2 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

中文:
定理 hasDerivAt_of_tendstoLocallyUniformlyOn
  结论: [NeBot l] {s : 集合 𝕜} (hs : 是开集 s)
  证明: by
  have h1 : s in 𝓝 x := hs.mem_nhds hx
  have h2 : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_prod_iff.2 ⟨_, hf, fun x => x in s, h1, fun {n} => id⟩
  refine hasDerivAt_of_tendstoUniformlyOnFilter ?_ h2 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

Depends on / 依赖: HasDerivAt, IsOpen, IsOpen.nhdsWithin_eq, eventually_of_mem, eventually_prod_iff, hasDerivAt_of_tendstoUniformlyOnFilter, hs.mem_nhds, mem_nhds, nhdsWithin_eq, tendstoLocallyUniformlyOn_iff_filter, tendstoLocallyUniformlyOn_iff_filter.mp
-/
theorem hasDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s)
    (hf : forallᶠ n in l, forall x in s, HasDerivAt (f n) (f' n x) x)
    (hfg : forall x in s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x in s) : HasDerivAt g (g' x) x := by
  have h1 : s in 𝓝 x := hs.mem_nhds hx
  have h2 : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_prod_iff.2 ⟨_, hf, fun x => x in s, h1, fun {n} => id⟩
  refine hasDerivAt_of_tendstoUniformlyOnFilter ?_ h2 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/--
theorem `hasDerivAt_of_tendsto_locally_uniformly_on'` / 定理 `hasDerivAt_of_tendsto_locally_uniformly_on'`

English:
theorem hasDerivAt_of_tendsto_locally_uniformly_on'
  statement: [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
  proof: by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn hs hf' ?_ hfg hx
  filter_upwards [hf] with n h z hz using ((h z hz).differentiableAt (hs.mem_nhds hz)).hasDerivAt

中文:
定理 hasDerivAt_of_tendsto_locally_uniformly_on'
  结论: [NeBot l] {s : 集合 𝕜} (hs : 是开集 s)
  证明: by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn hs hf' ?_ hfg hx
  filter_upwards [hf] with n h z hz using ((h z hz).differentiableAt (hs.mem_nhds hz)).hasDerivAt

Depends on / 依赖: differentiableAt, filter_upwards, hasDerivAt, hasDerivAt_of_tendstoLocallyUniformlyOn, hs.mem_nhds, mem_nhds
-/
theorem hasDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (deriv ∘ f) g' l s)
    (hf : forallᶠ n in l, DifferentiableOn 𝕜 (f n) s)
    (hfg : forall x in s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x in s) : HasDerivAt g (g' x) x := by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn hs hf' ?_ hfg hx
  filter_upwards [hf] with n h z hz using ((h z hz).differentiableAt (hs.mem_nhds hz)).hasDerivAt

/--
theorem `hasDerivAt_of_tendstoUniformlyOn` / 定理 `hasDerivAt_of_tendstoUniformlyOn`

English:
theorem hasDerivAt_of_tendstoUniformlyOn
  statement: [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
  proof: hasDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

中文:
定理 hasDerivAt_of_tendstoUniformlyOn
  结论: [NeBot l] {s : 集合 𝕜} (hs : 是开集 s)
  证明: hasDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

Depends on / 依赖: hasDerivAt_of_tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn
-/
theorem hasDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoUniformlyOn f' g' l s)
    (hf : forallᶠ n in l, forall x : 𝕜, x in s -> HasDerivAt (f n) (f' n x) x)
    (hfg : forall x : 𝕜, x in s -> Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x in s) :
    HasDerivAt g (g' x) x :=
  hasDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

/--
theorem `hasDerivAt_of_tendstoUniformly` / 定理 `hasDerivAt_of_tendstoUniformly`

English:
theorem hasDerivAt_of_tendstoUniformly
  statement: [NeBot l] (hf' : TendstoUniformly f' g' l)
  proof: by
  have hf : forallᶠ n in l, forall x : 𝕜, x in Set.univ -> HasDerivAt (f n) (f' n x) x := by
    filter_upwards [hf] with n h x _ using h x
  have hfg : forall x : 𝕜, x in Set.univ -> Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

中文:
定理 hasDerivAt_of_tendstoUniformly
  结论: [NeBot l] (hf' : TendstoUniformly f' g' l)
  证明: by
  have hf : forallᶠ n in l, forall x : 𝕜, x in Set.univ -> HasDerivAt (f n) (f' n x) x := by
    filter_upwards [hf] with n h x _ using h x
  have hfg : forall x : 𝕜, x in Set.univ -> Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

Depends on / 依赖: HasDerivAt, Set.mem_univ, Set.univ, Tendsto, TendstoUniformlyOn, filter_upwards, hasDerivAt_of_tendstoUniformlyOn, isOpen_univ, mem_univ, tendstoUniformlyOn_univ
-/
theorem hasDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
    (hf : forallᶠ n in l, forall x : 𝕜, HasDerivAt (f n) (f' n x) x)
    (hfg : forall x : 𝕜, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : 𝕜) : HasDerivAt g (g' x) x := by
  have hf : forallᶠ n in l, forall x : 𝕜, x in Set.univ -> HasDerivAt (f n) (f' n x) x := by
    filter_upwards [hf] with n h x _ using h x
  have hfg : forall x : 𝕜, x in Set.univ -> Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

end deriv
