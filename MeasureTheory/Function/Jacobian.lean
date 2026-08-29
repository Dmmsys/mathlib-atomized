/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Change of variables in higher-dimensional integrals

Let `μ` be a Lebesgue measure on a finite-dimensional real vector space `E`.
Let `f : E → E` be a function which is injective and differentiable on a measurable set `s`,
with derivative `f'`. Then we prove that `f '' s` is measurable, and
its measure is given by the formula `μ (f '' s) = ∫⁻ x in s, |(f' x).det| ∂μ` (where `(f' x).det`
is almost everywhere measurable, but not Borel-measurable in general). This formula is proved in
`lintegral_abs_det_fderiv_eq_addHaar_image`. We deduce the change of variables
formula for the Lebesgue and Bochner integrals, in `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
and `integral_image_eq_integral_abs_det_fderiv_smul` respectively.

Specialized versions in one dimension (using the derivative instead of the determinant of the
Fréchet derivative) can be found in the file `Mathlib/MeasureTheory/Function/JacobianOneDim.lean`,
together with versions for monotone and antitone functions.

## Main results

* `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`: if `f` is differentiable on a
  set `s` with zero measure, then `f '' s` also has zero measure.
* `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`: if `f` is differentiable on a set `s`, and
  its derivative is never invertible, then `f '' s` has zero measure (a version of Sard's lemma).
* `aemeasurable_fderivWithin`: if `f` is differentiable on a measurable set `s`, then `f'`
  is almost everywhere measurable on `s`.

For the next statements, `s` is a measurable set and `f` is differentiable on `s`
(with a derivative `f'`) and injective on `s`.

* `measurable_image_of_fderivWithin`: the image `f '' s` is measurable.
* `measurableEmbedding_of_fderivWithin`: the function `s.domRestrict f` is a measurable embedding.
* `lintegral_abs_det_fderiv_eq_addHaar_image`: the image measure is given by
    `μ (f '' s) = ∫⁻ x in s, |(f' x).det| ∂μ`.
* `lintegral_image_eq_lintegral_abs_det_fderiv_mul`: for `g : E → ℝ≥0∞`, one has
    `∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ`.
* `integral_image_eq_integral_abs_det_fderiv_smul`: for `g : E → F`, one has
    `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`.
* `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`: for `g : E → F`, the function `g` is
  integrable on `f '' s` if and only if `|(f' x).det| • g (f x)` is integrable on `s`.

## Implementation

Typical versions of these results in the literature have much stronger assumptions: `s` would
typically be open, and the derivative `f' x` would depend continuously on `x` and be invertible
everywhere, to have the local inverse theorem at our disposal. The proof strategy under our weaker
assumptions is more involved. We follow [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2].

The first remark is that, if `f` is sufficiently well approximated by a linear map `A` on a set
`s`, then `f` expands the volume of `s` by at least `A.det - ε` and at most `A.det + ε`, where
the closeness condition depends on `A` in a non-explicit way (see `addHaar_image_le_mul_of_det_lt`
and `mul_le_addHaar_image_of_lt_det`). This fact holds for balls by a simple inclusion argument,
and follows for general sets using the Besicovitch covering theorem to cover the set by balls with
measures adding up essentially to `μ s`.

When `f` is differentiable on `s`, one may partition `s` into countably many subsets `s ∩ t n`
(where `t n` is measurable), on each of which `f` is well approximated by a linear map, so that the
above results apply. See `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, which
follows from the pointwise differentiability (in a non-completely trivial way, as one should ensure
a form of uniformity on the sets of the partition).

Combining the above two results would give the conclusion, except for two difficulties: it is not
obvious why `f '' s` and `f'` should be measurable, which prevents us from using countable
additivity for the measure and the integral. It turns out that `f '' s` is indeed measurable,
and that `f'` is almost everywhere measurable, which is enough to recover countable additivity.

The measurability of `f '' s` follows from the deep Lusin-Souslin theorem ensuring that, in a
Polish space, a continuous injective image of a measurable set is measurable.

The key point to check the almost everywhere measurability of `f'` is that, if `f` is approximated
up to `δ` by a linear map on a set `s`, then `f'` is within `δ` of `A` on a full measure subset
of `s` (namely, its density points). With the above approximation argument, it follows that `f'`
is the almost everywhere limit of a sequence of measurable functions (which are constant on the
pieces of the good discretization), and is therefore almost everywhere measurable.

## Tags
Change of variables in integrals

## References
[Fremlin, *Measure Theory* (volume 2)][fremlin_vol2]
-/

public section

open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
  TopologicalSpace

open scoped NNReal ENNReal Topology Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] {s : Set E} {f : E -> E} {f' : E -> E ->L[Real] E}

/-!
### Decomposition lemmas

We state lemmas ensuring that a differentiable function can be approximated, on countably many
measurable pieces, by linear maps (with a prescribed precision depending on the linear map).
-/

/--
theorem `exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt` / 定理 `exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt`

English:
theorem exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt
  statement: [SecondCountableTopology F]
  proof: by
  /- Choose countably many linear maps `f' z`. For every such map, if `f` has a derivative at `x`
    close enough to `f' z`, then `f y - f x` is well approximated by `f' z (y - x)` for `y` close
    enough to `x`, say on a ball of radius `r` (or even `u n` for some `n`, where `u` is a fixed
    

中文:
定理 存在_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt
  结论: [第二可数拓扑 F]
  证明: by
  /- Choose countably many linear maps `f' z`. For every such map, if `f` has a derivative at `x`
    close enough to `f' z`, then `f y - f x` is well approximated by `f' z (y - x)` for `y` close
    enough to `x`, say on a ball of radius `r` (or even `u n` for some `n`, where `u` is a fixed
    
-/
theorem exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x)
    (r : (E ->L[Real] F) -> Real>=0) (rpos : forall A, r A != 0) :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] F),
      (forall n, IsClosed (t n)) ∧
        (s subseteq ⋃ n, t n) ∧
          (forall n, ApproximatesLinearOn f (A n) (s inter t n) (r (A n))) ∧
            (s.Nonempty -> forall n, exists y in s, A n = f' y) := by
  /- Choose countably many linear maps `f' z`. For every such map, if `f` has a derivative at `x`
    close enough to `f' z`, then `f y - f x` is well approximated by `f' z (y - x)` for `y` close
    enough to `x`, say on a ball of radius `r` (or even `u n` for some `n`, where `u` is a fixed
    sequence tending to `0`).
    Let `M n z` be the points where this happens. Then this set is relatively closed inside `s`,
    and moreover in every closed ball of radius `u n / 3` inside it the map is well approximated by
    `f' z`. Using countably many closed balls to split `M n z` into small diameter subsets
    `K n z p`, one obtains the desired sets `t q` after reindexing.
    -/
  -- exclude the trivial case where `s` is empty
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · refine ⟨fun _ => ∅, fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> simp
  -- we will use countably many linear maps. Select these from all the derivatives since the
  -- space of linear maps is second-countable
  obtain ⟨T, T_count, hT⟩ :
    exists T : Set s,
      T.Countable ∧ ⋃ x in T, ball (f' (x : E)) (r (f' x)) = ⋃ x : s, ball (f' x) (r (f' x)) :=
    TopologicalSpace.isOpen_iUnion_countable _ fun x => isOpen_ball
  -- fix a sequence `u` of positive reals tending to zero.
  obtain ⟨u, _, u_pos, u_lim⟩ :
    exists u : Nat -> Real, StrictAnti u ∧ (forall n : Nat, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  -- `M n z` is the set of points `x` such that `f y - f x` is close to `f' z (y - x)` for `y`
  -- in the ball of radius `u n` around `x`.
  let M : Nat -> T -> Set E := fun n z =>
    {x | x in s ∧ forall y in s inter ball x (u n), ‖f y - f x - f' z (y - x)‖ <= r (f' z) * ‖y - x‖}
  -- As `f` is differentiable everywhere on `s`, the sets `M n z` cover `s` by design.
  have s_subset : forall x in s, exists (n : Nat) (z : T), x in M n z := by
    intro x xs
    obtain ⟨z, zT, hz⟩ : exists z in T, f' x in ball (f' (z : E)) (r (f' z)) := by
      have : f' x in ⋃ z in T, ball (f' (z : E)) (r (f' z)) := by
        rw [hT]
        refine mem_iUnion.2 ⟨⟨x, xs⟩, ?_⟩
        simpa only [mem_ball, Subtype.coe_mk, dist_self] using! (rpos (f' x)).bot_lt
      rwa [mem_iUnion₂, bex_def] at this
    obtain ⟨ε, εpos, hε⟩ : exists ε : Real, 0 < ε ∧ ‖f' x - f' z‖ + ε <= r (f' z) := by
      refine ⟨r (f' z) - ‖f' x - f' z‖, ?_, le_of_eq (by abel)⟩
      simpa only [sub_pos] using! mem_ball_iff_norm.mp hz
    obtain ⟨δ, δpos, hδ⟩ :
      exists (δ : Real), 0 < δ ∧ ball x δ inter s subseteq {y | ‖f y - f x - (f' x) (y - x)‖ <= ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
    obtain ⟨n, hn⟩ : exists n, u n < δ := ((tendsto_order.1 u_lim).2 _ δpos).exists
    refine ⟨n, ⟨z, zT⟩, ⟨xs, ?_⟩⟩
    intro y hy
    calc
      ‖f y - f x - (f' z) (y - x)‖ = ‖f y - f x - (f' x) (y - x) + (f' x - f' z) (y - x)‖ := by
        congr 1
        simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
        abel
      _ <= ‖f y - f x - (f' x) (y - x)‖ + ‖(f' x - f' z) (y - x)‖ := norm_add_le _ _
      _ <= ε * ‖y - x‖ + ‖f' x - f' z‖ * ‖y - x‖ := by
        refine add_le_add (hδ ?_) (ContinuousLinearMap.le_opNorm _ _)
        rw [inter_comm]
        exact inter_subset_inter_right _ (ball_subset_ball hn.le) hy
      _ <= r (f' z) * ‖y - x‖ := by
        rw [← add_mul]; rw [add_comm]
        gcongr
  -- the sets `M n z` are relatively closed in `s`, as all the conditions defining it are clearly
  -- closed
  have closure_M_subset : forall n z, s inter closure (M n z) subseteq M n z := by
    rintro n z x ⟨xs, hx⟩
    refine ⟨xs, fun y hy => ?_⟩
    obtain ⟨a, aM, a_lim⟩ : exists a : Nat -> E, (forall k, a k in M n z) ∧ Tendsto a atTop (𝓝 x) :=
      mem_closure_iff_seq_limit.1 hx
    have L1 :
      Tendsto (fun k : Nat => ‖f y - f (a k) - (f' z) (y - a k)‖) atTop
        (𝓝 ‖f y - f x - (f' z) (y - x)‖) := by
      apply Tendsto.norm
      have L : Tendsto (fun k => f (a k)) atTop (𝓝 (f x)) := by
        apply (hf' x xs).continuousWithinAt.tendsto.comp
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ a_lim
        exact Eventually.of_forall fun k => (aM k).1
      apply Tendsto.sub (tendsto_const_nhds.sub L)
      exact ((f' z).continuous.tendsto _).comp (tendsto_const_nhds.sub a_lim)
    have L2 : Tendsto (fun k : Nat => (r (f' z) : Real) * ‖y - a k‖) atTop (𝓝 (r (f' z) * ‖y - x‖)) :=
      (tendsto_const_nhds.sub a_lim).norm.const_mul _
    have I : forallᶠ k in atTop, ‖f y - f (a k) - (f' z) (y - a k)‖ <= r (f' z) * ‖y - a k‖ := by
      have L : Tendsto (fun k => dist y (a k)) atTop (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist a_lim
      filter_upwards [(tendsto_order.1 L).2 _ hy.2]
      intro k hk
      exact (aM k).2 y ⟨hy.1, hk⟩
    exact le_of_tendsto_of_tendsto L1 L2 I
  -- choose a dense sequence `d p`
  rcases TopologicalSpace.exists_dense_seq E with ⟨d, hd⟩
  -- split `M n z` into subsets `K n z p` of small diameters by intersecting with the ball
  -- `closedBall (d p) (u n / 3)`.
  let K : Nat -> T -> Nat -> Set E := fun n z p => closure (M n z) inter closedBall (d p) (u n / 3)
  -- on the sets `K n z p`, the map `f` is well approximated by `f' z` by design.
  have K_approx : forall (n) (z : T) (p), ApproximatesLinearOn f (f' z) (s inter K n z p) (r (f' z)) := by
    intro n z p x hx y hy
    have yM : y in M n z := closure_M_subset _ _ ⟨hy.1, hy.2.1⟩
    refine yM.2 _ ⟨hx.1, ?_⟩
    calc
      dist x y <= dist x (d p) + dist y (d p) := dist_triangle_right _ _ _
      _ <= u n / 3 + u n / 3 := add_le_add hx.2.2 hy.2.2
      _ < u n := by linarith [u_pos n]
  -- the sets `K n z p` are also closed, again by design.
  have K_closed : forall (n) (z : T) (p), IsClosed (K n z p) := fun n z p =>
    isClosed_closure.inter isClosed_closedBall
  -- reindex the sets `K n z p`, to let them only depend on an integer parameter `q`.
  obtain ⟨F, hF⟩ : exists F : Nat -> Nat × T × Nat, Function.Surjective F := by
    have : Encodable T := T_count.toEncodable
    have : Nonempty T := by
      rcases hs with ⟨x, xs⟩
      rcases s_subset x xs with ⟨n, z, _⟩
      exact ⟨z⟩
    inhabit ↥T
    exact ⟨_, Encodable.surjective_decode_getD (Nat × T × Nat) default⟩
  -- these sets `t q = K n z p` will do
  refine
    ⟨fun q => K (F q).1 (F q).2.1 (F q).2.2, fun q => f' (F q).2.1, fun n => K_closed _ _ _,
      fun x xs => ?_, fun q => K_approx _ _ _, fun _ q => ⟨(F q).2.1, (F q).2.1.1.2, rfl⟩⟩
  -- the only fact that needs further checking is that they cover `s`.
  -- we already know that any point `x ∈ s` belongs to a set `M n z`.
  obtain ⟨n, z, hnz⟩ : exists (n : Nat) (z : T), x in M n z := s_subset x xs
  -- by density, it also belongs to a ball `closedBall (d p) (u n / 3)`.
  obtain ⟨p, hp⟩ : exists p : Nat, x in closedBall (d p) (u n / 3) := by
    have : Set.Nonempty (ball x (u n / 3)) := by simp only [nonempty_ball]; linarith [u_pos n]
    obtain ⟨p, hp⟩ : exists p : Nat, d p in ball x (u n / 3) := hd.exists_mem_open isOpen_ball this
    exact ⟨p, (mem_ball'.1 hp).le⟩
  -- choose `q` for which `t q = K n z p`.
  obtain ⟨q, hq⟩ : exists q, F q = (n, z, p) := hF _
  -- then `x` belongs to `t q`.
  apply mem_iUnion.2 ⟨q, _⟩
  simp -zeta only [K, hq, mem_inter_iff, hp, and_true]
  exact subset_closure hnz

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

open scoped Function -- required for scoped `on` notation

/--
theorem `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` / 定理 `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`

English:
theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
  statement: [SecondCountableTopology F]
  proof: by
  rcases exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r rpos with
    ⟨t, A, t_closed, st, t_approx, ht⟩
  refine
    ⟨disjointed t, A, disjoint_disjointed _,
      MeasurableSet.disjointed fun n => (t_closed n).measurableSet, ?_, ?_, ht⟩
  · rw [iUnion_disjointed]; ex

中文:
定理 存在_partition_approximatesLinearOn_of_hasFDerivWithinAt
  结论: [第二可数拓扑 F]
  证明: by
  rcases exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r rpos with
    ⟨t, A, t_closed, st, t_approx, ht⟩
  refine
    ⟨disjointed t, A, disjoint_disjointed _,
      MeasurableSet.disjointed fun n => (t_closed n).measurableSet, ?_, ?_, ht⟩
  · rw [iUnion_disjointed]; ex

Depends on / 依赖: MeasurableSet, MeasurableSet.disjointed, disjoint_disjointed, disjointed, disjointed_subset, exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt, iUnion_disjointed, inter_subset_inter_right, measurableSet, mono_set, t_approx, t_closed
-/
theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E -> F) (s : Set E) (f' : E -> E ->L[Real] F) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x)
    (r : (E ->L[Real] F) -> Real>=0) (rpos : forall A, r A != 0) :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] F),
      Pairwise (Disjoint on t) ∧
        (forall n, MeasurableSet (t n)) ∧
          (s subseteq ⋃ n, t n) ∧
            (forall n, ApproximatesLinearOn f (A n) (s inter t n) (r (A n))) ∧
              (s.Nonempty -> forall n, exists y in s, A n = f' y) := by
  rcases exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r rpos with
    ⟨t, A, t_closed, st, t_approx, ht⟩
  refine
    ⟨disjointed t, A, disjoint_disjointed _,
      MeasurableSet.disjointed fun n => (t_closed n).measurableSet, ?_, ?_, ht⟩
  · rw [iUnion_disjointed]; exact st
  · intro n; exact (t_approx n).mono_set (inter_subset_inter_right _ (disjointed_subset _ _))

namespace MeasureTheory

/-!
### Local lemmas

We check that a function which is well enough approximated by a linear map expands the volume
essentially like this linear map, and that its derivative (if it exists) is almost everywhere close
to the approximating linear map.
-/


/--
theorem `addHaar_image_le_mul_of_det_lt` / 定理 `addHaar_image_le_mul_of_det_lt`

English:
theorem addHaar_image_le_mul_of_det_lt
  statement: (A : E ->L[Real] E) {m : Real>=0}
  proof: by
  apply nhdsWithin_le_nhds
  let d := ENNReal.ofReal |A.det|
  -- construct a small neighborhood of `A '' (closedBall 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ :
    exists ε : Real, μ (closedBall 0 ε + A '' closedBall 0 1) < m * μ (closedBall 0 1) ∧ 0 <

中文:
定理 addHaar_image_le_mul_of_det_lt
  结论: (A : E ->L[实数] E) {m : 实数>=0}
  证明: by
  apply nhdsWithin_le_nhds
  let d := ENNReal.ofReal |A.det|
  -- construct a small neighborhood of `A '' (closedBall 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ :
    exists ε : Real, μ (closedBall 0 ε + A '' closedBall 0 1) < m * μ (closedBall 0 1) ∧ 0 <

Depends on / 依赖: A.det, ENNReal, ENNReal.ofReal, nhdsWithin_le_nhds, ofReal
-/
theorem addHaar_image_le_mul_of_det_lt (A : E ->L[Real] E) {m : Real>=0}
    (hm : ENNReal.ofReal |A.det| < m) :
    forallᶠ δ in 𝓝[>] (0 : Real>=0),
      forall (s : Set E) (f : E -> E), ApproximatesLinearOn f A s δ -> μ (f '' s) <= m * μ s := by
  apply nhdsWithin_le_nhds
  let d := ENNReal.ofReal |A.det|
  -- construct a small neighborhood of `A '' (closedBall 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ :
    exists ε : Real, μ (closedBall 0 ε + A '' closedBall 0 1) < m * μ (closedBall 0 1) ∧ 0 < ε := by
    have HC : IsCompact (A '' closedBall 0 1) :=
      (ProperSpace.isCompact_closedBall _ _).image A.continuous
    have L0 :
      Tendsto (fun ε => μ (cthickening ε (A '' closedBall 0 1))) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact tendsto_measure_cthickening_of_isCompact HC
    have L1 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply L0.congr' _
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [← HC.add_closedBall_zero (le_of_lt hr)]; rw [add_comm]
    have L2 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (d * μ (closedBall 0 1))) := by
      convert! L1
      exact (addHaar_image_continuousLinearMap _ _ _).symm
    have I : d * μ (closedBall 0 1) < m * μ (closedBall 0 1) := by
      gcongr; exacts [(measure_closedBall_pos μ _ zero_lt_one).ne', measure_closedBall_lt_top.ne]
    have H :
      forallᶠ b : Real in 𝓝[>] 0, μ (closedBall 0 b + A '' closedBall 0 1) < m * μ (closedBall 0 1) :=
      (tendsto_order.1 L2).2 _ I
    exact (H.and self_mem_nhdsWithin).exists
  have : Iio (.mk ε εpos.le) in 𝓝 (0 : Real>=0) := by apply Iio_mem_nhds; exact εpos
  filter_upwards [this]
  -- fix a function `f` which is close enough to `A`.
  intro δ hδ s f hf
  simp only [mem_Iio, ← NNReal.coe_lt_coe, NNReal.coe_mk] at hδ
  -- This function expands the volume of any ball by at most `m`
  have I : forall x r, x in s -> 0 <= r -> μ (f '' (s inter closedBall x r)) <= m * μ (closedBall x r) := by
    intro x r xs r0
    have K : f '' (s inter closedBall x r) subseteq A '' closedBall 0 r + closedBall (f x) (ε * r) := by
      rintro y ⟨z, ⟨zs, zr⟩, rfl⟩
      rw [mem_closedBall_iff_norm] at zr
      apply Set.mem_add.2 ⟨A (z - x), _, f z - f x - A (z - x) + f x, _, _⟩
      · apply mem_image_of_mem
        simpa only [dist_eq_norm, mem_closedBall, mem_closedBall_zero_iff, sub_zero] using zr
      · rw [mem_closedBall_iff_norm, add_sub_cancel_right]
        calc
          ‖f z - f x - A (z - x)‖ <= δ * ‖z - x‖ := hf _ zs _ xs
          _ <= ε * r := by gcongr
      · simp only [map_sub]
        abel
    have :
      A '' closedBall 0 r + closedBall (f x) (ε * r) =
        {f x} + r • (A '' closedBall 0 1 + closedBall 0 ε) := by
      rw [smul_add]; rw [← add_assoc]; rw [add_comm {f x}]; rw [add_assoc]; rw [smul_closedBall _ _ εpos.le]; rw [smul_zero]; rw [singleton_add_closedBall_zero]; rw [← image_smul_set]; rw [_root_.smul_closedBall _ _ zero_le_one]; rw [smul_zero]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg r0]; rw [mul_one]; rw [mul_comm]
    rw [this] at K
    calc
      μ (f '' (s inter closedBall x r)) <= μ ({f x} + r • (A '' closedBall 0 1 + closedBall 0 ε)) :=
        measure_mono K
      _ = ENNReal.ofReal (r ^ finrank Real E) * μ (A '' closedBall 0 1 + closedBall 0 ε) := by
        simp only [abs_of_nonneg r0, addHaar_smul, image_add_left, abs_pow, singleton_add,
          measure_preimage_add]
      _ <= ENNReal.ofReal (r ^ finrank Real E) * (m * μ (closedBall 0 1)) := by
        rw [add_comm]; gcongr
      _ = m * μ (closedBall x r) := by simp only [addHaar_closedBall' μ _ r0]; ring
  -- covering `s` by closed balls with total measure very close to `μ s`, one deduces that the
  -- measure of `f '' s` is at most `m * (μ s + a)` for any positive `a`.
  have J : forallᶠ a in 𝓝[>] (0 : Real>=0∞), μ (f '' s) <= m * (μ s + a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [mem_Ioi] at ha
    obtain ⟨t, r, t_count, ts, rpos, st, μt⟩ :
      exists (t : Set E) (r : E -> Real),
        t.Countable ∧
          t subseteq s ∧
            (forall x : E, x in t -> 0 < r x) ∧
              (s subseteq ⋃ x in t, closedBall x (r x)) ∧
                (∑' x : ↥t, μ (closedBall (↑x) (r ↑x))) <= μ s + a :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le μ ha.ne' (fun _ => Ioi 0) s
        fun x _ δ δpos => ⟨δ / 2, by simp [half_pos δpos, δpos]⟩
    have : Encodable t := t_count.toEncodable
    calc
      μ (f '' s) <= μ (⋃ x : t, f '' (s inter closedBall x (r x))) := by
        rw [biUnion_eq_iUnion] at st
        apply measure_mono
        rw [← image_iUnion]; rw [← inter_iUnion]
        exact Set.image_mono (subset_inter (Subset.refl _) st)
      _ <= ∑' x : t, μ (f '' (s inter closedBall x (r x))) := measure_iUnion_le _
      _ <= ∑' x : t, m * μ (closedBall x (r x)) :=
        (ENNReal.tsum_le_tsum fun x => I x (r x) (ts x.2) (rpos x x.2).le)
      _ <= m * (μ s + a) := by rw [ENNReal.tsum_mul_left]; gcongr
  -- taking the limit in `a`, one obtains the conclusion
  have L : Tendsto (fun a => (m : Real>=0∞) * (μ s + a)) (𝓝[>] 0) (𝓝 (m * (μ s + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ENNReal.Tendsto.const_mul (tendsto_const_nhds.add tendsto_id)
    simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
  rw [add_zero] at L
  exact ge_of_tendsto L J

/--
theorem `mul_le_addHaar_image_of_lt_det` / 定理 `mul_le_addHaar_image_of_lt_det`

English:
theorem mul_le_addHaar_image_of_lt_det
  statement: (A : E ->L[Real] E) {m : Real>=0}
  proof: by
  apply nhdsWithin_le_nhds
  -- The assumption `hm` implies that `A` is invertible. If `f` is close enough to `A`, it is also
  -- invertible. One can then pass to the inverses, and deduce the estimate from
  -- `addHaar_image_le_mul_of_det_lt` applied to `f⁻¹` and `A⁻¹`.
  -- exclude first the t

中文:
定理 mul_le_addHaar_image_of_lt_det
  结论: (A : E ->L[实数] E) {m : 实数>=0}
  证明: by
  apply nhdsWithin_le_nhds
  -- The assumption `hm` implies that `A` is invertible. If `f` is close enough to `A`, it is also
  -- invertible. One can then pass to the inverses, and deduce the estimate from
  -- `addHaar_image_le_mul_of_det_lt` applied to `f⁻¹` and `A⁻¹`.
  -- exclude first the t

Depends on / 依赖: nhdsWithin_le_nhds
-/
theorem mul_le_addHaar_image_of_lt_det (A : E ->L[Real] E) {m : Real>=0}
    (hm : (m : Real>=0∞) < ENNReal.ofReal |A.det|) :
    forallᶠ δ in 𝓝[>] (0 : Real>=0),
      forall (s : Set E) (f : E -> E), ApproximatesLinearOn f A s δ -> (m : Real>=0∞) * μ s <= μ (f '' s) := by
  apply nhdsWithin_le_nhds
  -- The assumption `hm` implies that `A` is invertible. If `f` is close enough to `A`, it is also
  -- invertible. One can then pass to the inverses, and deduce the estimate from
  -- `addHaar_image_le_mul_of_det_lt` applied to `f⁻¹` and `A⁻¹`.
  -- exclude first the trivial case where `m = 0`.
  rcases eq_zero_or_pos m with (rfl | mpos)
  · filter_upwards
    simp only [forall_const, zero_mul, imp_true_iff, zero_le, ENNReal.coe_zero]
  have hA : A.det != 0 := by
    intro h; simp only [h, ENNReal.not_lt_zero, ENNReal.ofReal_zero, abs_zero] at hm
  -- let `B` be the continuous linear equiv version of `A`.
  let B := A.toContinuousLinearEquivOfDetNeZero hA
  -- the determinant of `B.symm` is bounded by `m⁻¹`
  have I : ENNReal.ofReal |(B.symm : E ->L[Real] E).det| < (m⁻¹ : Real>=0) := by
    simp only [ENNReal.ofReal, abs_inv, Real.toNNReal_inv, ContinuousLinearEquiv.det_coe_symm,
      ENNReal.coe_lt_coe] at hm ⊢
    exact NNReal.inv_lt_inv mpos.ne' hm
  -- therefore, we may apply `addHaar_image_le_mul_of_det_lt` to `B.symm` and `m⁻¹`.
  obtain ⟨δ₀, δ₀pos, hδ₀⟩ :
    exists δ : Real>=0,
      0 < δ ∧
        forall (t : Set E) (g : E -> E),
          ApproximatesLinearOn g (B.symm : E ->L[Real] E) t δ -> μ (g '' t) <= ↑m⁻¹ * μ t := by
    have :
      forallᶠ δ : Real>=0 in 𝓝[>] 0,
        forall (t : Set E) (g : E -> E),
          ApproximatesLinearOn g (B.symm : E ->L[Real] E) t δ -> μ (g '' t) <= ↑m⁻¹ * μ t :=
      addHaar_image_le_mul_of_det_lt μ B.symm I
    rcases (this.and self_mem_nhdsWithin).exists with ⟨δ₀, h, h'⟩
    exact ⟨δ₀, h', h⟩
  -- record smallness conditions for `δ` that will be needed to apply `hδ₀` below.
  have L1 : forallᶠ δ in 𝓝 (0 : Real>=0), Subsingleton E ∨ δ < ‖(B.symm : E ->L[Real] E)‖₊⁻¹ := by
    by_cases h : Subsingleton E
    · simp only [h, true_or, eventually_const]
    simp only [h, false_or]
    apply Iio_mem_nhds
    simpa only [h, false_or, inv_pos] using B.subsingleton_or_nnnorm_symm_pos
  have L2 :
    forallᶠ δ in 𝓝 (0 : Real>=0), ‖(B.symm : E ->L[Real] E)‖₊ * (‖(B.symm : E ->L[Real] E)‖₊⁻¹ - δ)⁻¹ * δ < δ₀ := by
    have :
      Tendsto (fun δ => ‖(B.symm : E ->L[Real] E)‖₊ * (‖(B.symm : E ->L[Real] E)‖₊⁻¹ - δ)⁻¹ * δ) (𝓝 0)
        (𝓝 (‖(B.symm : E ->L[Real] E)‖₊ * (‖(B.symm : E ->L[Real] E)‖₊⁻¹ - 0)⁻¹ * 0)) := by
      rcases eq_or_ne ‖(B.symm : E ->L[Real] E)‖₊ 0 with (H | H)
      · simpa only [H, zero_mul] using tendsto_const_nhds
      refine Tendsto.mul (tendsto_const_nhds.mul ?_) tendsto_id
      refine (Tendsto.sub tendsto_const_nhds tendsto_id).inv₀ ?_
      simpa only [tsub_zero, inv_eq_zero, Ne] using H
    simp only [mul_zero] at this
    exact (tendsto_order.1 this).2 δ₀ δ₀pos
  -- let `δ` be small enough, and `f` approximated by `B` up to `δ`.
  filter_upwards [L1, L2]
  intro δ h1δ h2δ s f hf
  have hf' : ApproximatesLinearOn f (B : E ->L[Real] E) s δ := by convert! hf
  let F := hf'.toPartialEquiv h1δ
  -- the condition to be checked can be reformulated in terms of the inverse maps
  suffices H : μ (F.symm '' F.target) <= (m⁻¹ : Real>=0) * μ F.target by
    change (m : Real>=0∞) * μ F.source <= μ F.target
    rwa [← F.symm_image_target_eq_source, mul_comm, ← ENNReal.le_div_iff_mul_le, div_eq_mul_inv,
      mul_comm, ← ENNReal.coe_inv mpos.ne']
    · apply Or.inl
      simpa only [ENNReal.coe_eq_zero, Ne] using mpos.ne'
    · simp
  -- as `f⁻¹` is well approximated by `B⁻¹`, the conclusion follows from `hδ₀`
  -- and our choice of `δ`.
  exact hδ₀ _ _ ((hf'.to_inv h1δ).mono_num h2δ.le)

/--
theorem `_root_.ApproximatesLinearOn.norm_fderiv_sub_le` / 定理 `_root_.ApproximatesLinearOn.norm_fderiv_sub_le`

English:
theorem _root_.ApproximatesLinearOn.norm_fderiv_sub_le
  statement: {A : E ->L[Real] E} {δ : Real>=0}
  proof: by
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
    At such a point `x`, for any `z` and any `ε > 0` one has for small `r`
    that `{x} + r • closedBall z ε` intersects `s`. At a point `y` in the intersection,
    `f y - f x` is close both to `f' x 

中文:
定理 _root_.ApproximatesLinearOn.norm_fderiv_sub_le
  结论: {A : E ->L[实数] E} {δ : 实数>=0}
  证明: by
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
    At such a point `x`, for any `z` and any `ε > 0` one has for small `r`
    that `{x} + r • closedBall z ε` intersects `s`. At a point `y` in the intersection,
    `f y - f x` is close both to `f' x 
-/
theorem _root_.ApproximatesLinearOn.norm_fderiv_sub_le {A : E ->L[Real] E} {δ : Real>=0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s) (f' : E -> E ->L[Real] E)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) : forallᵐ x ∂μ.restrict s, ‖f' x - A‖₊ <= δ := by
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
    At such a point `x`, for any `z` and any `ε > 0` one has for small `r`
    that `{x} + r • closedBall z ε` intersects `s`. At a point `y` in the intersection,
    `f y - f x` is close both to `f' x (r z)` (by differentiability) and to `A (r z)`
    (by linear approximation), so these two quantities are close, i.e., `(f' x - A) z` is small. -/
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs]
  -- start from a Lebesgue density point `x`, belonging to `s`.
  intro x hx xs
  -- consider an arbitrary vector `z`.
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  -- to show that `‖(f' x - A) z‖ ≤ δ ‖z‖`, it suffices to do it up to some error that vanishes
  -- asymptotically in terms of `ε > 0`.
  suffices H : forall ε, 0 < ε -> ‖(f' x - A) z‖ <= (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have :
      Tendsto (fun ε : Real => ((δ : Real) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at this
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    filter_upwards [self_mem_nhdsWithin]
    exact H
  -- fix a positive `ε`.
  intro ε εpos
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` intersects `s`, as `x` is a
  -- density point
  have B₁ : forallᶠ r in 𝓝[>] (0 : Real), (s inter ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
    exists ρ > 0, ball x ρ inter s subseteq {y : E | ‖f y - f x - (f' x) (y - x)‖ <= ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` is included in the set where
  -- `f y - f x` is well approximated by `f' x (y - x)`.
  have B₂ : forallᶠ r in 𝓝[>] (0 : Real), {x} + r • closedBall z ε subseteq ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  -- fix a small positive `r` satisfying the above properties, as well as a corresponding `y`.
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
    exists r : Real,
      (s inter ({x} + r • closedBall z ε)).Nonempty ∧ {x} + r • closedBall z ε subseteq ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  -- write `y = x + r a` with `a ∈ closedBall z ε`.
  obtain ⟨a, az, ya⟩ : exists a, a in closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ <= ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ <= ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ <= ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  -- use the approximation properties to control `(f' x - A) a`, and then `(f' x - A) z` as `z` is
  -- close to `a`.
  have I : r * ‖(f' x - A) a‖ <= r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
          Pi.sub_apply, map_smul, smul_sub]
      _ <= ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := norm_sub_le _ _
      _ <= δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ <= r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
      congr 1
      simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
      abel
    _ <= ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ <= (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ <= (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr

/-!
### Measure zero of the image, over non-measurable sets

If a set has measure `0`, then its image under a differentiable map has measure zero. This doesn't
require the set to be measurable. In the same way, if `f` is differentiable on a set `s` with
non-invertible derivative everywhere, then `f '' s` has measure `0`, again without measurability
assumptions.
-/


/--
theorem `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` / 定理 `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`

English:
theorem addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  statement: (hf : DifferentiableOn Real f s)
  proof: by
  rw [← nonpos_iff_eq_zero]
  have :
      forall A : E ->L[Real] E, exists δ : Real>=0, 0 < δ ∧
        forall (t : Set E), ApproximatesLinearOn f A t δ ->
          μ (f '' t) <= (Real.toNNReal |A.det| + 1 : Real>=0) * μ t := by
    intro A
    let m : Real>=0 := Real.toNNReal |A.det| + 1
    h

中文:
定理 addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  结论: (hf : DifferentiableOn 实数 f s)
  证明: by
  rw [← nonpos_iff_eq_zero]
  have :
      forall A : E ->L[Real] E, exists δ : Real>=0, 0 < δ ∧
        forall (t : Set E), ApproximatesLinearOn f A t δ ->
          μ (f '' t) <= (Real.toNNReal |A.det| + 1 : Real>=0) * μ t := by
    intro A
    let m : Real>=0 := Real.toNNReal |A.det| + 1
    h

Depends on / 依赖: A.det, ApproximatesLinearOn, ENNReal, ENNReal.coe_lt_coe, ENNReal.ofReal, Real.toNNReal, addHaar_image_le_mul_of_det_lt, coe_lt_coe, lt_add_iff_pos_right, nonpos_iff_eq_zero, ofReal, self_mem_nhdsWithin, toNNReal, zero_lt_one
-/
theorem addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : DifferentiableOn Real f s)
    (hs : μ s = 0) : μ (f '' s) = 0 := by
  rw [← nonpos_iff_eq_zero]
  have :
      forall A : E ->L[Real] E, exists δ : Real>=0, 0 < δ ∧
        forall (t : Set E), ApproximatesLinearOn f A t δ ->
          μ (f '' t) <= (Real.toNNReal |A.det| + 1 : Real>=0) * μ t := by
    intro A
    let m : Real>=0 := Real.toNNReal |A.det| + 1
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, zero_lt_one, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  obtain ⟨t, A, _, _, t_cover, ht, -⟩ :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] E),
      Pairwise (Disjoint on t) ∧
        (forall n : Nat, MeasurableSet (t n)) ∧
          (s subseteq ⋃ n : Nat, t n) ∧
            (forall n : Nat, ApproximatesLinearOn f (A n) (s inter t n) (δ (A n))) ∧
              (s.Nonempty -> forall n, exists y in s, A n = fderivWithin Real f s y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderivWithin Real f s)
      (fun x xs => (hf x xs).hasFDerivWithinAt) δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) <= μ (⋃ n, f '' (s inter t n)) := by
      apply measure_mono
      rw [← image_iUnion]; rw [← inter_iUnion]
      exact Set.image_mono (subset_inter Subset.rfl t_cover)
    _ <= ∑' n, μ (f '' (s inter t n)) := measure_iUnion_le _
    _ <= ∑' n, (Real.toNNReal |(A n).det| + 1 : Real>=0) * μ (s inter t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2
      exact ht n
    _ <= ∑' n, ((Real.toNNReal |(A n).det| + 1 : Real>=0) : Real>=0∞) * 0 := by
      gcongr with n
      exact le_trans (measure_mono inter_subset_left) (le_of_eq hs)
    _ = 0 := by simp only [tsum_zero, mul_zero]

/--
theorem `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux` / 定理 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux`

English:
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | h's); · simp only [measure_empty, zero_le, image_empty]
  have :
      forall A : E ->L[Real] E, exists δ : Real>=0, 0 < δ ∧
        forall (t : Set E), ApproximatesLinearOn f A t δ ->
          μ (f '' t) <= (Real.toNNReal |A.det| + ε : Real>=0) * μ t 

中文:
定理 addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | h's); · simp only [measure_empty, zero_le, image_empty]
  have :
      forall A : E ->L[Real] E, exists δ : Real>=0, 0 < δ ∧
        forall (t : Set E), ApproximatesLinearOn f A t δ ->
          μ (f '' t) <= (Real.toNNReal |A.det| + ε : Real>=0) * μ t 

Depends on / 依赖: A.det, ApproximatesLinearOn, ENNReal, ENNReal.coe_lt_coe, ENNReal.ofReal, Real.toNNReal, addHaar_image_le_mul_of_det_lt, coe_lt_coe, eq_empty_or_nonempty, image_empty, lt_add_iff_pos_right, measure_empty, ofReal, toNNReal, zero_le
-/
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (R : Real) (hs : s subseteq closedBall 0 R) (ε : Real>=0)
    (εpos : 0 < ε) (h'f' : forall x in s, (f' x).det = 0) : μ (f '' s) <= ε * μ (closedBall 0 R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's); · simp only [measure_empty, zero_le, image_empty]
  have :
      forall A : E ->L[Real] E, exists δ : Real>=0, 0 < δ ∧
        forall (t : Set E), ApproximatesLinearOn f A t δ ->
          μ (f '' t) <= (Real.toNNReal |A.det| + ε : Real>=0) * μ t := by
    intro A
    let m : Real>=0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] E),
      Pairwise (Disjoint on t) ∧
        (forall n : Nat, MeasurableSet (t n)) ∧
          (s subseteq ⋃ n : Nat, t n) ∧
            (forall n : Nat, ApproximatesLinearOn f (A n) (s inter t n) (δ (A n))) ∧
              (s.Nonempty -> forall n, exists y in s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) <= μ (⋃ n, f '' (s inter t n)) := by
      rw [← image_iUnion]; rw [← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ <= ∑' n, μ (f '' (s inter t n)) := measure_iUnion_le _
    _ <= ∑' n, (Real.toNNReal |(A n).det| + ε : Real>=0) * μ (s inter t n) := by
      gcongr
      exact (hδ (A _)).2 _ (ht _)
    _ = ∑' n, ε * μ (s inter t n) := by
      congr with n
      rcases Af' h's n with ⟨y, ys, hy⟩
      simp only [hy, h'f' y ys, Real.toNNReal_zero, abs_zero, zero_add]
    _ <= ε * ∑' n, μ (closedBall 0 R inter t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * μ (⋃ n, closedBall 0 R inter t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ <= ε * μ (closedBall 0 R) := by grw [← inter_iUnion, inter_subset_left]

/--
theorem `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` / 定理 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`

English:
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
  proof: by
  suffices H : forall R, μ (f '' (s inter closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero]; rw [← iUnion_inter_closedBall_nat s 0]
    calc
      μ (f '' ⋃ n : Nat, s inter closedBall 0 n) <= ∑' n : Nat, μ (f '' (s inter closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_

中文:
定理 addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
  证明: by
  suffices H : forall R, μ (f '' (s inter closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero]; rw [← iUnion_inter_closedBall_nat s 0]
    calc
      μ (f '' ⋃ n : Nat, s inter closedBall 0 n) <= ∑' n : Nat, μ (f '' (s inter closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_

Depends on / 依赖: addHaar_image_eq_zero_of_det_fderivW, closedBall, iUnion_inter_closedBall_nat, image_iUnion, measure_iUnion_le, nonpos_iff_eq_zero, tsum_zero
-/
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (h'f' : forall x in s, (f' x).det = 0) :
    μ (f '' s) = 0 := by
  suffices H : forall R, μ (f '' (s inter closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero]; rw [← iUnion_inter_closedBall_nat s 0]
    calc
      μ (f '' ⋃ n : Nat, s inter closedBall 0 n) <= ∑' n : Nat, μ (f '' (s inter closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ <= 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
  intro R
  have A : forall (ε : Real>=0), 0 < ε -> μ (f '' (s inter closedBall 0 R)) <= ε * μ (closedBall 0 R) :=
    fun ε εpos =>
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux μ
      (fun x hx => (hf' x hx.1).mono inter_subset_left) R inter_subset_right ε εpos
      fun x hx => h'f' x hx.1
  have B : Tendsto (fun ε : Real>=0 => (ε : Real>=0∞) * μ (closedBall 0 R)) (𝓝[>] 0) (𝓝 0) := by
    have :
      Tendsto (fun ε : Real>=0 => (ε : Real>=0∞) * μ (closedBall 0 R)) (𝓝 0)
        (𝓝 (((0 : Real>=0) : Real>=0∞) * μ (closedBall 0 R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto B
  filter_upwards [self_mem_nhdsWithin]
  exact A

/-!
### Weak measurability statements

We show that the derivative of a function on a set is almost everywhere measurable, and that the
image `f '' s` is measurable if `f` is injective on `s`. The latter statement follows from the
Lusin-Souslin theorem.
-/


/--
theorem `aemeasurable_fderivWithin` / 定理 `aemeasurable_fderivWithin`

English:
theorem aemeasurable_fderivWithin
  statement: (hs : MeasurableSet s)
  proof: by
  /- It suffices to show that `f'` can be uniformly approximated by a measurable function.
    Fix `ε > 0`. Thanks to `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, one
    can find a countable measurable partition of `s` into sets `s ∩ t n` on which `f` is well
    approximated by

中文:
定理 aemeasurable_fderivWithin
  结论: (hs : 可测集 s)
  证明: by
  /- It suffices to show that `f'` can be uniformly approximated by a measurable function.
    Fix `ε > 0`. Thanks to `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, one
    can find a countable measurable partition of `s` into sets `s ∩ t n` on which `f` is well
    approximated by
-/
theorem aemeasurable_fderivWithin (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) : AEMeasurable f' (μ.restrict s) := by
  /- It suffices to show that `f'` can be uniformly approximated by a measurable function.
    Fix `ε > 0`. Thanks to `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, one
    can find a countable measurable partition of `s` into sets `s ∩ t n` on which `f` is well
    approximated by linear maps `A n`. On almost all of `s ∩ t n`, it follows from
    `ApproximatesLinearOn.norm_fderiv_sub_le` that `f'` is uniformly approximated by `A n`, which
    gives the conclusion. -/
  -- fix a precision `ε`
  refine aemeasurable_of_unif_approx fun ε εpos => ?_
  let δ : Real>=0 := ⟨ε, le_of_lt εpos⟩
  have δpos : 0 < δ := εpos
  -- partition `s` into sets `s ∩ t n` on which `f` is approximated by linear maps `A n`.
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, _⟩ :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] E),
      Pairwise (Disjoint on t) ∧
        (forall n : Nat, MeasurableSet (t n)) ∧
          (s subseteq ⋃ n : Nat, t n) ∧
            (forall n : Nat, ApproximatesLinearOn f (A n) (s inter t n) δ) ∧
              (s.Nonempty -> forall n, exists y in s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' (fun _ => δ) fun _ =>
      δpos.ne'
  -- define a measurable function `g` which coincides with `A n` on `t n`.
  obtain ⟨g, g_meas, hg⟩ :
      exists g : E -> E ->L[Real] E, Measurable g ∧ forall (n : Nat) (x : E), x in t n -> g x = A n :=
exists_measurable_piecewise t t_meas (fun n _ => A n) (fun n => measurable_const)
      t_disj.mono fun i j h => by simp only [h.inter_eq, eqOn_empty]
  refine ⟨g, g_meas.aemeasurable, ?_⟩
  -- reduce to checking that `f'` and `g` are close on almost all of `s ∩ t n`, for all `n`.
  suffices H : forallᵐ x : E ∂sum fun n => μ.restrict (s inter t n), dist (g x) (f' x) <= ε by
    have : μ.restrict s <= sum fun n => μ.restrict (s inter t n) := by
      have : s = ⋃ n, s inter t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
      conv_lhs => rw [this]
      exact restrict_iUnion_le
    exact ae_mono this H
  -- fix such an `n`.
  refine ae_sum_iff.2 fun n => ?_
  -- on almost all `s ∩ t n`, `f' x` is close to `A n` thanks to
  -- `ApproximatesLinearOn.norm_fderiv_sub_le`.
  have E₁ : forallᵐ x : E ∂μ.restrict (s inter t n), ‖f' x - A n‖₊ <= δ :=
    (ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
      (hf' x hx.1).mono inter_subset_left
  -- moreover, `g x` is equal to `A n` there.
  have E₂ : forallᵐ x : E ∂μ.restrict (s inter t n), g x = A n := by
    suffices H : forallᵐ x : E ∂μ.restrict (t n), g x = A n from
      ae_mono (restrict_mono inter_subset_right le_rfl) H
    filter_upwards [ae_restrict_mem (t_meas n)]
    exact hg n
  -- putting these two properties together gives the conclusion.
  filter_upwards [E₁, E₂] with x hx1 hx2
  rw [← nndist_eq_nnnorm] at hx1
  rw [hx2]; rw [dist_comm]
  exact hx1

/--
theorem `aemeasurable_ofReal_abs_det_fderivWithin` / 定理 `aemeasurable_ofReal_abs_det_fderivWithin`

English:
theorem aemeasurable_ofReal_abs_det_fderivWithin
  statement: (hs : MeasurableSet s)
  proof: by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

中文:
定理 aemeasurable_of实数_abs_det_fderivWithin
  结论: (hs : 可测集 s)
  证明: by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable, ENNReal, ENNReal.measurable_ofReal.comp_aemeasurable, aemeasurable_fderivWithin, comp_aemeasurable, continuous_abs, continuous_abs.measurable.comp_aemeasurable, continuous_det, measurable, measurable_ofReal
-/
theorem aemeasurable_ofReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => ENNReal.ofReal |(f' x).det|) (μ.restrict s) := by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

/--
theorem `aemeasurable_toNNReal_abs_det_fderivWithin` / 定理 `aemeasurable_toNNReal_abs_det_fderivWithin`

English:
theorem aemeasurable_toNNReal_abs_det_fderivWithin
  statement: (hs : MeasurableSet s)
  proof: by
  apply measurable_real_toNNReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

中文:
定理 aemeasurable_toNN实数_abs_det_fderivWithin
  结论: (hs : 可测集 s)
  证明: by
  apply measurable_real_toNNReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable, aemeasurable_fderivWithin, comp_aemeasurable, continuous_abs, continuous_abs.measurable.comp_aemeasurable, continuous_det, measurable, measurable_real_toNNReal, measurable_real_toNNReal.comp_aemeasurable
-/
theorem aemeasurable_toNNReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => |(f' x).det|.toNNReal) (μ.restrict s) := by
  apply measurable_real_toNNReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'

/--
theorem `measurable_image_of_fderivWithin` / 定理 `measurable_image_of_fderivWithin`

English:
theorem measurable_image_of_fderivWithin
  statement: (hs : MeasurableSet s)
  proof: haveI : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf

中文:
定理 measurable_image_of_fderivWithin
  结论: (hs : 可测集 s)
  证明: haveI : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf

Depends on / 依赖: DifferentiableOn, DifferentiableOn.continuousOn, continuousOn, differentiableWithinAt, hs.image_of_continuousOn_injOn, image_of_continuousOn_injOn
-/
theorem measurable_image_of_fderivWithin (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableSet (f '' s) :=
  haveI : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf

/--
theorem `nullMeasurable_image_of_fderivWithin` / 定理 `nullMeasurable_image_of_fderivWithin`

English:
theorem nullMeasurable_image_of_fderivWithin
  statement: (hs : NullMeasurableSet s μ)
  proof: by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : f '' s =ᵐ[μ] f '' t := by
    have : s = t union (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this]; rw [image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)
    apply addHaar_im

中文:
定理 nullMeasurable_image_of_fderivWithin
  结论: (hs : NullMeasurableSet s μ)
  证明: by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : f '' s =ᵐ[μ] f '' t := by
    have : s = t union (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this]; rw [image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)
    apply addHaar_im

Depends on / 依赖: A.symm, MeasurableSet, MeasurableSet.nullMeas, NullMeasurableSet, NullMeasurableSet.congr, addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero, ae_eq_empty, ae_eq_empty.mpr, ae_eq_set, differentiableWithinAt, differentiableWithinAt.mono, exists_measurable_subset_ae_eq, hs.exists_measurable_subset_ae_eq, image_union, nullMeas, sdiff_subset, t_eq_s, union_ae_eq_left_of_ae_eq_empty, union_eq_self_of_subset_left
-/
theorem nullMeasurable_image_of_fderivWithin (hs : NullMeasurableSet s μ)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    NullMeasurableSet (f '' s) μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : f '' s =ᵐ[μ] f '' t := by
    have : s = t union (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this]; rw [image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun x hx => ?_) (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  apply NullMeasurableSet.congr _ A.symm
  apply MeasurableSet.nullMeasurableSet
  apply measurable_image_of_fderivWithin ht _ (hf.mono ts) (f' := f')
  intro x hx
  exact (hf' x (ts hx)).mono ts

/--
theorem `measurableEmbedding_of_fderivWithin` / 定理 `measurableEmbedding_of_fderivWithin`

English:
theorem measurableEmbedding_of_fderivWithin
  statement: (hs : MeasurableSet s)
  proof: haveI : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
  this.continuousOn.measurableEmbedding hs hf

中文:
定理 measurableEmbedding_of_fderivWithin
  结论: (hs : 可测集 s)
  证明: haveI : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
  this.continuousOn.measurableEmbedding hs hf

Depends on / 依赖: DifferentiableOn, continuousOn, differentiableWithinAt, measurableEmbedding, this.continuousOn.measurableEmbedding
-/
theorem measurableEmbedding_of_fderivWithin (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    MeasurableEmbedding (s.domRestrict f) :=
  haveI : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
  this.continuousOn.measurableEmbedding hs hf



/--
theorem `addHaar_image_le_lintegral_abs_det_fderiv_aux1` / 定理 `addHaar_image_le_lintegral_abs_det_fderiv_aux1`

English:
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux1
  statement: (hs : MeasurableSet s)
  proof: by
  /- To bound `μ (f '' s)`, we cover `s` by sets where `f` is well-approximated by linear maps
    `A n` (and where `f'` is almost everywhere close to `A n`), and then use that `f` expands the
    measure of such a set by at most `(A n).det + ε`. -/
  have :
    forall A : E ->L[Real] E,
      ex

中文:
定理 addHaar_image_le_lintegral_abs_det_fderiv_aux1
  结论: (hs : 可测集 s)
  证明: by
  /- To bound `μ (f '' s)`, we cover `s` by sets where `f` is well-approximated by linear maps
    `A n` (and where `f'` is almost everywhere close to `A n`), and then use that `f` expands the
    measure of such a set by at most `(A n).det + ε`. -/
  have :
    forall A : E ->L[Real] E,
      ex
-/
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux1 (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) {ε : Real>=0} (εpos : 0 < ε) :
    μ (f '' s) <= (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
  /- To bound `μ (f '' s)`, we cover `s` by sets where `f` is well-approximated by linear maps
    `A n` (and where `f'` is almost everywhere close to `A n`), and then use that `f` expands the
    measure of such a set by at most `(A n).det + ε`. -/
  have :
    forall A : E ->L[Real] E,
      exists δ : Real>=0,
        0 < δ ∧
          (forall B : E ->L[Real] E, ‖B - A‖ <= δ -> |B.det - A.det| <= ε) ∧
            forall (t : Set E) (g : E -> E), ApproximatesLinearOn g A t δ ->
              μ (g '' t) <= (ENNReal.ofReal |A.det| + ε) * μ t := by
    intro A
    let m : Real>=0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    obtain ⟨δ', δ'pos, hδ'⟩ : exists (δ' : Real), 0 < δ' ∧ forall B, dist B A < δ' -> dist B.det A.det < ↑ε := by
      refine continuousAt_iff.1 ?_ ε εpos
      exact ContinuousLinearMap.continuous_det.continuousAt
    let δ'' : Real>=0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      calc
        ‖B - A‖ <= (min δ δ'' : Real>=0) := hB
        _ <= δ'' := by simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
        _ < δ' := half_lt_self δ'pos
    · intro t g htg
      exact h t g (htg.mono_num (min_le_left _ _))
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] E),
      Pairwise (Disjoint on t) ∧
        (forall n : Nat, MeasurableSet (t n)) ∧
          (s subseteq ⋃ n : Nat, t n) ∧
            (forall n : Nat, ApproximatesLinearOn f (A n) (s inter t n) (δ (A n))) ∧
              (s.Nonempty -> forall n, exists y in s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) <= μ (⋃ n, f '' (s inter t n)) := by
      apply measure_mono
      rw [← image_iUnion]; rw [← inter_iUnion]
      exact Set.image_mono (subset_inter Subset.rfl t_cover)
    _ <= ∑' n, μ (f '' (s inter t n)) := measure_iUnion_le _
    _ <= ∑' n, (ENNReal.ofReal |(A n).det| + ε) * μ (s inter t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2.2
      exact ht n
    _ = ∑' n, ∫⁻ _ in s inter t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
    _ <= ∑' n, ∫⁻ x in s inter t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have I : |(A n).det| <= |(f' x).det| + ε :=
        calc
          |(A n).det| = |(f' x).det - ((f' x).det - (A n).det)| := by congr 1; abel
          _ <= |(f' x).det| + |(f' x).det - (A n).det| := abs_sub _ _
          _ <= |(f' x).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(A n).det| + ε <= ENNReal.ofReal (|(f' x).det| + ε) + ε := by gcongr
        _ = ENNReal.ofReal |(f' x).det| + 2 * ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, two_mul, add_assoc, NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ x in ⋃ n, s inter t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      have M : forall n : Nat, MeasurableSet (s inter t n) := fun n => hs.inter (t_meas n)
      rw [lintegral_iUnion M]
      exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      rw [← inter_iUnion]; rw [inter_eq_self_of_subset_left t_cover]
    _ = (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
      simp only [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]

/--
theorem `addHaar_image_le_lintegral_abs_det_fderiv_aux2` / 定理 `addHaar_image_le_lintegral_abs_det_fderiv_aux2`

English:
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux2
  statement: (hs : MeasurableSet s) (h's : μ s != ∞)
  proof: by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : Real>=0 => (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * (0 : Real>=0) * μ s)) := by
    apply Tendsto.mono_left _ 

中文:
定理 addHaar_image_le_lintegral_abs_det_fderiv_aux2
  结论: (hs : 可测集 s) (h's : μ s != ∞)
  证明: by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : Real>=0 => (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * (0 : Real>=0) * μ s)) := by
    apply Tendsto.mono_left _ 
-/
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux2 (hs : MeasurableSet s) (h's : μ s != ∞)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) <= ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : Real>=0 => (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * (0 : Real>=0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact addHaar_image_le_lintegral_abs_det_fderiv_aux1 μ hs hf' εpos

/--
theorem `addHaar_image_le_lintegral_abs_det_fderiv` / 定理 `addHaar_image_le_lintegral_abs_det_fderiv`

English:
theorem addHaar_image_le_lintegral_abs_det_fderiv
  statement: (hs : MeasurableSet s)
  proof: by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : forall n, MeasurableSet (u n) := by
    intro n
    apply Me

中文:
定理 addHaar_image_le_lintegral_abs_det_fderiv
  结论: (hs : 可测集 s)
  证明: by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : forall n, MeasurableSet (u n) := by
    intro n
    apply Me
-/
theorem addHaar_image_le_lintegral_abs_det_fderiv (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) <= ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : forall n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s inter u n := by
    rw [← inter_iUnion]; rw [iUnion_disjointed]; rw [iUnion_spanningSets]; rw [inter_univ]
  calc
    μ (f '' s) <= ∑' n, μ (f '' (s inter u n)) := by
      conv_lhs => rw [A, image_iUnion]
      exact measure_iUnion_le _
    _ <= ∑' n, ∫⁻ x in s inter u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        addHaar_image_le_lintegral_abs_det_fderiv_aux2 μ (hs.inter (u_meas n)) _ fun x hx =>
          (hf' x hx.1).mono inter_subset_left
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_rhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right

/--
theorem `lintegral_abs_det_fderiv_le_addHaar_image_aux1` / 定理 `lintegral_abs_det_fderiv_le_addHaar_image_aux1`

English:
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux1
  statement: (hs : MeasurableSet s)
  proof: by
  /- To bound `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ`, we cover `s` by sets where `f` is
    well-approximated by linear maps `A n` (and where `f'` is almost everywhere close to `A n`),
    and then use that `f` expands the measure of such a set by at least `(A n).det - ε`. -/
  have :
    fo

中文:
定理 lintegral_abs_det_fderiv_le_addHaar_image_aux1
  结论: (hs : 可测集 s)
  证明: by
  /- To bound `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ`, we cover `s` by sets where `f` is
    well-approximated by linear maps `A n` (and where `f'` is almost everywhere close to `A n`),
    and then use that `f` expands the measure of such a set by at least `(A n).det - ε`. -/
  have :
    fo
-/
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux1 (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) {ε : Real>=0} (εpos : 0 < ε) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) <= μ (f '' s) + 2 * ε * μ s := by
  /- To bound `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ`, we cover `s` by sets where `f` is
    well-approximated by linear maps `A n` (and where `f'` is almost everywhere close to `A n`),
    and then use that `f` expands the measure of such a set by at least `(A n).det - ε`. -/
  have :
    forall A : E ->L[Real] E,
      exists δ : Real>=0,
        0 < δ ∧
          (forall B : E ->L[Real] E, ‖B - A‖ <= δ -> |B.det - A.det| <= ε) ∧
            forall (t : Set E) (g : E -> E), ApproximatesLinearOn g A t δ ->
              ENNReal.ofReal |A.det| * μ t <= μ (g '' t) + ε * μ t := by
    intro A
    obtain ⟨δ', δ'pos, hδ'⟩ : exists (δ' : Real), 0 < δ' ∧ forall B, dist B A < δ' -> dist B.det A.det < ↑ε := by
      refine continuousAt_iff.1 ?_ ε εpos
      exact ContinuousLinearMap.continuous_det.continuousAt
    let δ'' : Real>=0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    have I'' : forall B : E ->L[Real] E, ‖B - A‖ <= ↑δ'' -> |B.det - A.det| <= ↑ε := by
      intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      exact hB.trans_lt (half_lt_self δ'pos)
    rcases eq_or_ne A.det 0 with (hA | hA)
    · refine ⟨δ'', half_pos δ'pos, I'', ?_⟩
      simp only [hA, forall_const, zero_mul, ENNReal.ofReal_zero, imp_true_iff,
        zero_le, abs_zero]
    let m : Real>=0 := Real.toNNReal |A.det| - ε
    have I : (m : Real>=0∞) < ENNReal.ofReal |A.det| := by
      simp only [m, ENNReal.ofReal, ENNReal.coe_sub]
      apply ENNReal.sub_lt_self ENNReal.coe_ne_top
      · simpa only [abs_nonpos_iff, Real.toNNReal_eq_zero, ENNReal.coe_eq_zero, Ne] using hA
      · simp only [εpos.ne', ENNReal.coe_eq_zero, Ne, not_false_iff]
    rcases ((mul_le_addHaar_image_of_lt_det μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      apply I'' _ (hB.trans _)
      simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
    · intro t g htg
      rcases eq_or_ne (μ t) ∞ with (ht | ht)
      · simp only [ht, εpos.ne', ENNReal.mul_top, ENNReal.coe_eq_zero, le_top, Ne,
          not_false_iff, _root_.add_top]
      have := h t g (htg.mono_num (min_le_left _ _))
      rwa [ENNReal.coe_sub, ENNReal.sub_mul, tsub_le_iff_right] at this
      simp only [ht, imp_true_iff, Ne, not_false_iff]
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    exists (t : Nat -> Set E) (A : Nat -> E ->L[Real] E),
      Pairwise (Disjoint on t) ∧
        (forall n : Nat, MeasurableSet (t n)) ∧
          (s subseteq ⋃ n : Nat, t n) ∧
            (forall n : Nat, ApproximatesLinearOn f (A n) (s inter t n) (δ (A n))) ∧
              (s.Nonempty -> forall n, exists y in s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  have s_eq : s = ⋃ n, s inter t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s inter t n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [s_eq]
      rw [lintegral_iUnion]
      · exact fun n => hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ <= ∑' n, ∫⁻ _ in s inter t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have I : |(f' x).det| <= |(A n).det| + ε :=
        calc
          |(f' x).det| = |(A n).det + ((f' x).det - (A n).det)| := by congr 1; abel
          _ <= |(A n).det| + |(f' x).det - (A n).det| := abs_add_le _ _
          _ <= |(A n).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(f' x).det| <= ENNReal.ofReal (|(A n).det| + ε) :=
          ENNReal.ofReal_le_ofReal I
        _ = ENNReal.ofReal |(A n).det| + ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    _ = ∑' n, (ENNReal.ofReal |(A n).det| * μ (s inter t n) + ε * μ (s inter t n)) := by
      simp only [setLIntegral_const, lintegral_add_right _ measurable_const]
    _ <= ∑' n, (μ (f '' (s inter t n)) + ε * μ (s inter t n) + ε * μ (s inter t n)) := by
      gcongr
      exact (hδ (A _)).2.2 _ _ (ht _)
    _ = μ (f '' s) + 2 * ε * μ s := by
      conv_rhs => rw [s_eq]
      rw [image_iUnion]; rw [measure_iUnion]; rotate_left
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact Disjoint.mono inter_subset_right inter_subset_right (t_disj hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (t_meas i))
            (fun x hx => (hf' x hx.1).mono inter_subset_left)
            (hf.mono inter_subset_left)
      rw [measure_iUnion]; rotate_left
      · exact pairwise_disjoint_mono t_disj fun i => inter_subset_right
      · exact fun i => hs.inter (t_meas i)
      rw [← ENNReal.tsum_mul_left]; rw [← ENNReal.tsum_add]
      congr 1
      ext1 i
      rw [mul_assoc]; rw [two_mul]; rw [add_assoc]

/--
theorem `lintegral_abs_det_fderiv_le_addHaar_image_aux2` / 定理 `lintegral_abs_det_fderiv_le_addHaar_image_aux2`

English:
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux2
  statement: (hs : MeasurableSet s) (h's : μ s != ∞)
  proof: by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : Real>=0 => μ (f '' s) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 (μ (f '' s) + 2 * (0 : Real>=0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine

中文:
定理 lintegral_abs_det_fderiv_le_addHaar_image_aux2
  结论: (hs : 可测集 s) (h's : μ s != ∞)
  证明: by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : Real>=0 => μ (f '' s) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 (μ (f '' s) + 2 * (0 : Real>=0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine
-/
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux2 (hs : MeasurableSet s) (h's : μ s != ∞)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) <= μ (f '' s) := by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : Real>=0 => μ (f '' s) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 (μ (f '' s) + 2 * (0 : Real>=0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact lintegral_abs_det_fderiv_le_addHaar_image_aux1 μ hs hf' hf εpos

/--
theorem `lintegral_abs_det_fderiv_le_addHaar_image` / 定理 `lintegral_abs_det_fderiv_le_addHaar_image`

English:
theorem lintegral_abs_det_fderiv_le_addHaar_image
  statement: (hs : MeasurableSet s)
  proof: by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : forall n, MeasurableSet (u n) := by
    intro n
    apply Me

中文:
定理 lintegral_abs_det_fderiv_le_addHaar_image
  结论: (hs : 可测集 s)
  证明: by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : forall n, MeasurableSet (u n) := by
    intro n
    apply Me
-/
theorem lintegral_abs_det_fderiv_le_addHaar_image (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) <= μ (f '' s) := by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  have u_meas : forall n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s inter u n := by
    rw [← inter_iUnion]; rw [iUnion_disjointed]; rw [iUnion_spanningSets]; rw [inter_univ]
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s inter u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
    _ <= ∑' n, μ (f '' (s inter u n)) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        lintegral_abs_det_fderiv_le_addHaar_image_aux2 μ (hs.inter (u_meas n)) _
          (fun x hx => (hf' x hx.1).mono inter_subset_left) (hf.mono inter_subset_left)
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = μ (f '' s) := by
      conv_rhs => rw [A, image_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact
          Disjoint.mono inter_subset_right inter_subset_right
            (disjoint_disjointed _ hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (u_meas i))
            (fun x hx => (hf' x hx.1).mono inter_subset_left)
            (hf.mono inter_subset_left)

/--
theorem `lintegral_abs_det_fderiv_eq_addHaar_image` / 定理 `lintegral_abs_det_fderiv_eq_addHaar_image`

English:
theorem lintegral_abs_det_fderiv_eq_addHaar_image
  statement: (hs : MeasurableSet s)
  proof: le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')

中文:
定理 lintegral_abs_det_fderiv_eq_addHaar_image
  结论: (hs : 可测集 s)
  证明: le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')

Depends on / 依赖: addHaar_image_le_lintegral_abs_det_fderiv, le_antisymm, lintegral_abs_det_fderiv_le_addHaar_image
-/
theorem lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) :=
  le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')

/--
theorem `lintegral_abs_det_fderiv_eq_addHaar_image₀` / 定理 `lintegral_abs_det_fderiv_eq_addHaar_image₀`

English:
theorem lintegral_abs_det_fderiv_eq_addHaar_image₀
  statement: (hs : NullMeasurableSet s μ)
  proof: by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : μ (f '' s) = μ (f '' t) := by
    apply measure_congr
    have : s = t union (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this]; rw [image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.

中文:
定理 lintegral_abs_det_fderiv_eq_addHaar_image₀
  结论: (hs : NullMeasurableSet s μ)
  证明: by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : μ (f '' s) = μ (f '' t) := by
    apply measure_congr
    have : s = t union (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this]; rw [image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.

Depends on / 依赖: ENNReal, ENNReal.ofReal, addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero, ae_eq_empty, ae_eq_empty.mpr, ae_eq_set, differentiableWithinAt, differentiableWithinAt.mono, exists_measurable_subset_ae_eq, hs.exists_measurable_subset_ae_eq, image_union, measure_congr, ofReal, sdiff_subset, t_eq_s, union_ae_eq_left_of_ae_eq_empty, union_eq_self_of_subset_left
-/
theorem lintegral_abs_det_fderiv_eq_addHaar_image₀ (hs : NullMeasurableSet s μ)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have A : μ (f '' s) = μ (f '' t) := by
    apply measure_congr
    have : s = t union (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [this]; rw [image_union]
    refine union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun x hx => ?_) (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  have B : (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ)
      = (∫⁻ x in t, ENNReal.ofReal |(f' x).det| ∂μ) :=
    setLIntegral_congr t_eq_s.symm
  rw [A]; rw [B]; rw [lintegral_abs_det_fderiv_eq_addHaar_image _ ht _ (hf.mono ts)]
  intro x hx
  exact (hf' x (ts hx)).mono ts

/--
theorem `map_withDensity_abs_det_fderiv_eq_addHaar` / 定理 `map_withDensity_abs_det_fderiv_eq_addHaar`

English:
theorem map_withDensity_abs_det_fderiv_eq_addHaar
  statement: (hs : NullMeasurableSet s μ)
  proof: by
  have h'f : AEMeasurable f (μ.restrict s) := by
    apply ContinuousOn.aemeasurable₀ (fun x hx => ?_) hs
    exact (hf' x hx).differentiableWithinAt.continuousWithinAt
  have h''f : AEMeasurable f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) := by
    apply h'f.mono_ac
    e

中文:
定理 map_withDensity_abs_det_fderiv_eq_addHaar
  结论: (hs : NullMeasurableSet s μ)
  证明: by
  have h'f : AEMeasurable f (μ.restrict s) := by
    apply ContinuousOn.aemeasurable₀ (fun x hx => ?_) hs
    exact (hf' x hx).differentiableWithinAt.continuousWithinAt
  have h''f : AEMeasurable f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) := by
    apply h'f.mono_ac
    e

Depends on / 依赖: AEMeasurable, ContinuousOn, ContinuousOn.aemeasurable, ENNReal, ENNReal.ofReal, Measure, Measure.ext, NullMeasurableSet, continuousWithinAt, differentiableWithinAt, differentiableWithinAt.continuousWithinAt, f.mono_ac, f.nullMeasurableSet_preimage, map_apply_of_aemeasurable, mono_ac, nullMeasurableSet_preimage, ofReal, restrict, withDensit, withDensity
-/
theorem map_withDensity_abs_det_fderiv_eq_addHaar (hs : NullMeasurableSet s μ)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) =
      μ.restrict (f '' s) := by
  have h'f : AEMeasurable f (μ.restrict s) := by
    apply ContinuousOn.aemeasurable₀ (fun x hx => ?_) hs
    exact (hf' x hx).differentiableWithinAt.continuousWithinAt
  have h''f : AEMeasurable f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) := by
    apply h'f.mono_ac
    exact withDensity_absolutelyContinuous _ _
  apply Measure.ext fun t ht => ?_
  have h't : NullMeasurableSet (f ⁻¹' t) (μ.restrict s) := h'f.nullMeasurableSet_preimage ht
  rw [map_apply_of_aemeasurable h''f ht]; rw [withDensity_apply₀ _ h't]; rw [Measure.restrict_apply ht]; rw [restrict_restrict₀ h't]; rw [lintegral_abs_det_fderiv_eq_addHaar_image₀ μ ((nullMeasurableSet_restrict hs).1 h't)
      (fun x hx => (hf' x hx.2).mono inter_subset_right) (hf.mono inter_subset_right)]; rw [image_preimage_inter]

/--
theorem `restrict_map_withDensity_abs_det_fderiv_eq_addHaar` / 定理 `restrict_map_withDensity_abs_det_fderiv_eq_addHaar`

English:
theorem restrict_map_withDensity_abs_det_fderiv_eq_addHaar
  statement: (hs : MeasurableSet s)
  proof: by
  obtain ⟨u, u_meas, uf⟩ : exists u, Measurable u ∧ EqOn u f s := by
    classical
    refine ⟨piecewise s f 0, ?_, piecewise_eqOn _ _ _⟩
    refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn hs
    have : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWi

中文:
定理 restrict_map_withDensity_abs_det_fderiv_eq_addHaar
  结论: (hs : 可测集 s)
  证明: by
  obtain ⟨u, u_meas, uf⟩ : exists u, Measurable u ∧ EqOn u f s := by
    classical
    refine ⟨piecewise s f 0, ?_, piecewise_eqOn _ _ _⟩
    refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn hs
    have : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWi

Depends on / 依赖: ContinuousOn, ContinuousOn.measurable_piecewise, DifferentiableOn, HasFDerivWithinAt, Measurable, Measure, Measure.map, classical, continuousOn, continuous_zero, continuous_zero.continuousOn, differentiableWithinAt, measurable_piecewise, piecewise, piecewise_eqOn, this.continuousOn, u_meas
-/
theorem restrict_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map (s.domRestrict f) (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (f '' s) := by
  obtain ⟨u, u_meas, uf⟩ : exists u, Measurable u ∧ EqOn u f s := by
    classical
    refine ⟨piecewise s f 0, ?_, piecewise_eqOn _ _ _⟩
    refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn hs
    have : DifferentiableOn Real f s := fun x hx => (hf' x hx).differentiableWithinAt
    exact this.continuousOn
  have u' : forall x in s, HasFDerivWithinAt u (f' x) s x := fun x hx =>
    (hf' x hx).congr (fun y hy => uf hy) (uf hx)
  set F : s -> E := u ∘ (↑) with hF
  have A :
    Measure.map F (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (u '' s) := by
    rw [hF]; rw [← Measure.map_map u_meas measurable_subtype_coe]; rw [map_comap_subtype_coe hs]; rw [restrict_withDensity hs]
    exact map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet u' (hf.congr uf.symm)
  rw [uf.image_eq] at A
  have : F = s.domRestrict f := by
    ext x
    exact uf x.2
  rwa [this] at A

/-! ### Change of variable formulas in integrals -/


/--
theorem `lintegral_image_eq_lintegral_abs_det_fderiv_mul` / 定理 `lintegral_image_eq_lintegral_abs_det_fderiv_mul`

English:
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul
  statement: (hs : MeasurableSet s)
  proof: by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).lintegral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map]; rw [map_comap_subtype_coe hs

中文:
定理 lintegral_image_eq_lintegral_abs_det_fderiv_mul
  结论: (hs : 可测集 s)
  证明: by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).lintegral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map]; rw [map_comap_subtype_coe hs

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, Function, Function.comp_apply, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Pi.mul_apply, Set.domRestrict_apply, aemeasurable_ofReal_abs_det_fderivWithin, comp_apply, domRestrict_apply, eventually_true, lintegral_map, map_comap_subtype_coe, measurableEmbedding_of_fderivWithin, mul_apply, ofReal_lt_top, restrict_map_withDensity_abs_det_fderiv_eq_addHaar, subtype_coe
-/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E -> Real>=0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).lintegral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map]; rw [map_comap_subtype_coe hs]; rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · simp only [Pi.mul_apply]
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact aemeasurable_ofReal_abs_det_fderivWithin μ hs hf'

/--
theorem `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` / 定理 `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`

English:
theorem integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
  statement: (hs : MeasurableSet s)
  proof: by
  rw [IntegrableOn]; rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).integrable_map_iff]
  simp only [Set.domRestrict_eq, ← Function.comp_assoc, ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_i

中文:
定理 integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
  结论: (hs : 可测集 s)
  证明: by
  rw [IntegrableOn]; rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).integrable_map_iff]
  simp only [Set.domRestrict_eq, ← Function.comp_assoc, ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_i

Depends on / 依赖: ENNReal, ENNReal.ofReal, Function, Function.comp_apply, Function.comp_assoc, IntegrableOn, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Real.coe_toNNReal, Set.domRestrict_eq, abs_nonneg, coe_toNNReal, comp_apply, comp_assoc, domRestrict_eq, integrable_map_iff, map_comap_subtype_coe, measurableEmbedding_of_fderivWithin, ofReal, restrict_map_withDensity_abs_det_fderiv_eq_addHaar
-/
theorem integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E -> F) :
    IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x => |(f' x).det| • g (f x)) s μ := by
  rw [IntegrableOn]; rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).integrable_map_iff]
  simp only [Set.domRestrict_eq, ← Function.comp_assoc, ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_iff]; rw [map_comap_subtype_coe hs]; rw [restrict_withDensity hs]; rw [integrable_withDensity_iff_integrable_coe_smul₀]
  · simp_rw [IntegrableOn, Real.coe_toNNReal _ (abs_nonneg _), Function.comp_apply]
  · exact aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf'

/--
theorem `integral_image_eq_integral_abs_det_fderiv_smul` / 定理 `integral_image_eq_integral_abs_det_fderiv_smul`

English:
theorem integral_image_eq_integral_abs_det_fderiv_smul
  statement: (hs : MeasurableSet s)
  proof: by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map]; rw [map_comap_

中文:
定理 integral_image_eq_integral_abs_det_fderiv_smul
  结论: (hs : 可测集 s)
  证明: by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map]; rw [map_comap_

Depends on / 依赖: ENNReal, ENNReal.ofReal, Function, Function.comp_apply, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, NNReal, NNReal.smul_def, Real.coe_toNNReal, Set.domRestrict_apply, abs_nonneg, aemeasurable_toNNReal_abs_det_fderivWithin, coe_toNNReal, comp_apply, domRestrict_apply, integral_map, map_comap_subtype_coe, measurableEmbedding_of_fderivWithin, ofReal, restrict_map_withDensity_abs_det_fderiv_eq_addHaar
-/
theorem integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E -> F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf]; rw [(measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map]; rw [map_comap_subtype_coe hs]; rw [setIntegral_withDensity_eq_setIntegral_smul₀
      (aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf') _ hs]
  congr with x
  rw [NNReal.smul_def]; rw [Real.coe_toNNReal _ (abs_nonneg (f' x).det)]

/--
theorem `integral_target_eq_integral_abs_det_fderiv_smul` / 定理 `integral_target_eq_integral_abs_det_fderiv_smul`

English:
theorem integral_target_eq_integral_abs_det_fderiv_smul
  statement: {f : OpenPartialHomeomorph E E}
  proof: by
  have : f '' f.source = f.target := PartialEquiv.image_source_eq_target f.toPartialEquiv
  rw [← this]
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  intro x hx
  exact (hf' x hx).hasFDerivWithinAt

中文:
定理 integral_target_eq_integral_abs_det_fderiv_smul
  结论: {f : OpenPartialHomeomorph E E}
  证明: by
  have : f '' f.source = f.target := PartialEquiv.image_source_eq_target f.toPartialEquiv
  rw [← this]
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  intro x hx
  exact (hf' x hx).hasFDerivWithinAt

Depends on / 依赖: PartialEquiv, PartialEquiv.image_source_eq_target, f.injOn, f.open_source.measurableSet, f.source, f.target, f.toPartialEquiv, hasFDerivWithinAt, image_source_eq_target, integral_image_eq_integral_abs_det_fderiv_smul, measurableSet, open_source, source, target, toPartialEquiv
-/
theorem integral_target_eq_integral_abs_det_fderiv_smul {f : OpenPartialHomeomorph E E}
    (hf' : forall x in f.source, HasFDerivAt f (f' x) x) (g : E -> F) :
    ∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ := by
  have : f '' f.source = f.target := PartialEquiv.image_source_eq_target f.toPartialEquiv
  rw [← this]
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  intro x hx
  exact (hf' x hx).hasFDerivWithinAt

section withDensity

/--
lemma `_root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul` / 引理 `_root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul`

English:
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul
  proof: by
  rw [Measure.comap_apply f hf.injective (fun t ht => hf.measurableSet_image' ht) _ hs]; rw [withDensity_apply _ (hf.measurableSet_image' hs)]; rw [← ofReal_integral_eq_lintegral_ofReal hg_int
      ((ae_restrict_iff' (hf.measurableSet_image' hs)).mpr hg)]; rw [integral_image_eq_integral_abs_det_

中文:
引理 _root_.可测嵌入.withDensity_of实数_comap_apply_eq_integral_abs_det_fderiv_mul
  证明: by
  rw [Measure.comap_apply f hf.injective (fun t ht => hf.measurableSet_image' ht) _ hs]; rw [withDensity_apply _ (hf.measurableSet_image' hs)]; rw [← ofReal_integral_eq_lintegral_ofReal hg_int
      ((ae_restrict_iff' (hf.measurableSet_image' hs)).mpr hg)]; rw [integral_image_eq_integral_abs_det_

Depends on / 依赖: Measure, Measure.comap_apply, ae_restrict_iff, comap_apply, hf.injective, hf.injective.injOn, hf.measurableSet_image, hg_int, injective, integral_image_eq_integral_abs_det_fderiv_smul, measurableSet_image, ofReal_integral_eq_lintegral_ofReal, simp_rw, smul_eq_mul, withDensity_apply
-/
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul
    (hs : MeasurableSet s) (hf : MeasurableEmbedding f)
    {g : E -> Real} (hg : forallᵐ x ∂μ, x in f '' s -> 0 <= g x) (hg_int : IntegrableOn g (f '' s) μ)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) :
    (μ.withDensity (fun x => ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |(f' x).det| * g (f x) ∂μ) := by
  rw [Measure.comap_apply f hf.injective (fun t ht => hf.measurableSet_image' ht) _ hs]; rw [withDensity_apply _ (hf.measurableSet_image' hs)]; rw [← ofReal_integral_eq_lintegral_ofReal hg_int
      ((ae_restrict_iff' (hf.measurableSet_image' hs)).mpr hg)]; rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs hf' hf.injective.injOn]
  simp_rw [smul_eq_mul]

/--
lemma `_root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul` / 引理 `_root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul`

English:
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
  proof: by
  rw [MeasurableEquiv.map_symm]; rw [MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul μ hs
      f.measurableEmbedding hg hg_int hf']

中文:
引理 _root_.可测等价.withDensity_of实数_map_symm_apply_eq_integral_abs_det_fderiv_mul
  证明: by
  rw [MeasurableEquiv.map_symm]; rw [MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul μ hs
      f.measurableEmbedding hg hg_int hf']

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul, MeasurableEquiv, MeasurableEquiv.map_symm, f.measurableEmbedding, hg_int, map_symm, measurableEmbedding, withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul
-/
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
    (hs : MeasurableSet s) (f : E ≃ᵐ E)
    {g : E -> Real} (hg : forallᵐ x ∂μ, x in f '' s -> 0 <= g x) (hg_int : IntegrableOn g (f '' s) μ)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) :
    (μ.withDensity (fun x => ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |(f' x).det| * g (f x) ∂μ) := by
  rw [MeasurableEquiv.map_symm]; rw [MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul μ hs
      f.measurableEmbedding hg hg_int hf']

end withDensity

end MeasureTheory
