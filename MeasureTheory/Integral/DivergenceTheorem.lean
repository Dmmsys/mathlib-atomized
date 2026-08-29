/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Divergence theorem for Bochner integral

In this file we prove the Divergence theorem for Bochner integral on a box in
`ℝⁿ⁺¹ = Fin (n + 1) → ℝ`. More precisely, we prove the following theorem.

Let `E` be a complete normed space. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is
continuous on a rectangular box `[a, b] : Set ℝⁿ⁺¹`, `a ≤ b`, differentiable on its interior with
derivative `f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹`, and the divergence `fun x ↦ ∑ i, f' x eᵢ i`
is integrable on `[a, b]`, where `eᵢ = Pi.single i 1` is the `i`-th basis vector,
then its integral is equal to the sum of integrals of `f` over the faces of `[a, b]`,
taken with appropriate signs. Moreover, the same
is true if the function is not differentiable at countably many points of the interior of `[a, b]`.

Once we prove the general theorem, we deduce corollaries for functions `ℝ → E` and pairs of
functions `(ℝ × ℝ) → E`.

## Notation

We use the following local notation to make the statement more readable. Note that the documentation
website shows the actual terms, not those abbreviated using local notations.

* `ℝⁿ`, `ℝⁿ⁺¹`, `Eⁿ⁺¹`: `Fin n → ℝ`, `Fin (n + 1) → ℝ`, `Fin (n + 1) → E`;
* `face i`: the `i`-th face of the box `[a, b]` as a closed segment in `ℝⁿ`, namely
  `[a ∘ Fin.succAbove i, b ∘ Fin.succAbove i]`;
* `e i` : `i`-th basis vector `Pi.single i 1`;
* `frontFace i`, `backFace i`: embeddings `ℝⁿ → ℝⁿ⁺¹` corresponding to the front face
  `{x | x i = b i}` and back face `{x | x i = a i}` of the box `[a, b]`, respectively.
  They are given by `Fin.insertNth i (b i)` and `Fin.insertNth i (a i)`.

## TODO

* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/

public section


open Set Finset TopologicalSpace Function BoxIntegral MeasureTheory Filter

open scoped Topology Interval

universe u

namespace MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

section

variable {n : Nat}

local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n -> $t)

local macro:arg t:term:max noWs "ⁿ⁺¹" : term => `(Fin (n + 1) -> $t)

local notation "e " i => Pi.single i 1

section

/-!
### Divergence theorem for functions on `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`.

In this section we use the divergence theorem for a Henstock-Kurzweil-like integral
`BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` to prove the divergence
theorem for Bochner integral. The divergence theorem for Bochner integral
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` assumes that the function
itself is continuous on a closed box, differentiable at all but countably many points of its
interior, and the divergence is integrable on the box.

This statement differs from `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt`
in several aspects.

* We use Bochner integral instead of a Henstock-Kurzweil integral. This modification is done in
  `MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁`. As a side effect
  of this change, we need to assume that the divergence is integrable.

* We don't assume differentiability on the boundary of the box. This modification is done in
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_aux₂`. To prove it, we
  choose an increasing sequence of smaller boxes that cover the interior of the original box, then
  apply the previous lemma to these smaller boxes and take the limit of both sides of the equation.

* We assume `a ≤ b` instead of `∀ i, a i < b i`. This is the last step of the proof, and it is done
  in the main theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
-/

/--
theorem `integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁` / 定理 `integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁`

English:
theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁
  statement: (I : Box (Fin (n + 1)))
  proof: by
  wlog hE : CompleteSpace E generalizing
  · simp [integral, hE]
  simp only [← setIntegral_congr_set (Box.coe_ae_eq_Icc _)]
  have A := (Hi.mono_set Box.coe_subset_Icc).hasBoxIntegral ⊥ rfl
  have B :=
    hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I f f' (s inter Box.Icc I)
      (hs.

中文:
定理 integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁
  结论: (I : Box (Fin (n + 1)))
  证明: by
  wlog hE : CompleteSpace E generalizing
  · simp [integral, hE]
  simp only [← setIntegral_congr_set (Box.coe_ae_eq_Icc _)]
  have A := (Hi.mono_set Box.coe_subset_Icc).hasBoxIntegral ⊥ rfl
  have B :=
    hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I f f' (s inter Box.Icc I)
      (hs.
-/
private theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (I : Box (Fin (n + 1)))
    (f : Realⁿ⁺¹ -> Eⁿ⁺¹)
    (f' : Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] Eⁿ⁺¹) (s : Set Realⁿ⁺¹)
    (hs : s.Countable) (Hc : ContinuousOn f (Box.Icc I))
    (Hd : forall x in (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Box.Icc I)) :
    (∫ x in Box.Icc I, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in Box.Icc (I.face i), f (i.insertNth (I.upper i) x) i) -
          ∫ x in Box.Icc (I.face i), f (i.insertNth (I.lower i) x) i) := by
  wlog hE : CompleteSpace E generalizing
  · simp [integral, hE]
  simp only [← setIntegral_congr_set (Box.coe_ae_eq_Icc _)]
  have A := (Hi.mono_set Box.coe_subset_Icc).hasBoxIntegral ⊥ rfl
  have B :=
    hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I f f' (s inter Box.Icc I)
      (hs.mono inter_subset_left) (fun x hx => Hc _ hx.2) fun x hx =>
      Hd _ ⟨hx.1, fun h => hx.2 ⟨h, hx.1⟩⟩
  rw [continuousOn_pi] at Hc
  refine (A.unique B).trans (sum_congr rfl fun i _ => ?_)
  refine congr_arg₂ Sub.sub ?_ ?_
  · have := Box.continuousOn_face_Icc (Hc i) (Set.right_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrableOn_compact (μ := volume) (Box.isCompact_Icc _)).mono_set
      Box.coe_subset_Icc
    exact (this.hasBoxIntegral ⊥ rfl).integral_eq
  · have := Box.continuousOn_face_Icc (Hc i) (Set.left_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrableOn_compact (μ := volume) (Box.isCompact_Icc _)).mono_set
      Box.coe_subset_Icc
    exact (this.hasBoxIntegral ⊥ rfl).integral_eq

/--
theorem `integral_divergence_of_hasFDerivAt_off_countable_aux₂` / 定理 `integral_divergence_of_hasFDerivAt_off_countable_aux₂`

English:
theorem integral_divergence_of_hasFDerivAt_off_countable_aux₂
  statement: (I : Box (Fin (n + 1)))
  proof: by
  /- Choose a monotone sequence `J k` of subboxes that cover the interior of `I` and prove that
    these boxes satisfy the assumptions of the previous lemma. -/
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩
  have hJ_sub' : forall k, Box.Icc (J k) subseteq Box.Icc I := fun k => (

中文:
定理 integral_divergence_of_hasFDerivAt_off_countable_aux₂
  结论: (I : Box (Fin (n + 1)))
  证明: by
  /- Choose a monotone sequence `J k` of subboxes that cover the interior of `I` and prove that
    these boxes satisfy the assumptions of the previous lemma. -/
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩
  have hJ_sub' : forall k, Box.Icc (J k) subseteq Box.Icc I := fun k => (
-/
private theorem integral_divergence_of_hasFDerivAt_off_countable_aux₂ (I : Box (Fin (n + 1)))
    (f : Realⁿ⁺¹ -> Eⁿ⁺¹)
    (f' : Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] Eⁿ⁺¹)
    (s : Set Realⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Box.Icc I))
    (Hd : forall x in Box.Ioo I \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (∑ i, f' · (e i) i) (Box.Icc I)) :
    (∫ x in Box.Icc I, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in Box.Icc (I.face i), f (i.insertNth (I.upper i) x) i) -
          ∫ x in Box.Icc (I.face i), f (i.insertNth (I.lower i) x) i) := by
  /- Choose a monotone sequence `J k` of subboxes that cover the interior of `I` and prove that
    these boxes satisfy the assumptions of the previous lemma. -/
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩
  have hJ_sub' : forall k, Box.Icc (J k) subseteq Box.Icc I := fun k => (hJ_sub k).trans I.Ioo_subset_Icc
  have hJ_le : forall k, J k <= I := fun k => Box.le_iff_Icc.2 (hJ_sub' k)
  have HcJ : forall k, ContinuousOn f (Box.Icc (J k)) := fun k => Hc.mono (hJ_sub' k)
  have HdJ : forall (k), forall x in (Box.Icc (J k)) \ s, HasFDerivWithinAt f (f' x) (Box.Icc (J k)) x :=
    fun k x hx => (Hd x ⟨hJ_sub k hx.1, hx.2⟩).hasFDerivWithinAt
  have HiJ : forall k, IntegrableOn (∑ i, f' · (e i) i) (Box.Icc (J k)) volume := fun k =>
    Hi.mono_set (hJ_sub' k)
  -- Apply the previous lemma to `J k`.
  have HJ_eq := fun k =>
    integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (J k) f f' s hs (HcJ k) (HdJ k)
      (HiJ k)
  -- Note that the LHS of `HJ_eq k` tends to the LHS of the goal as `k → ∞`.
  have hI_tendsto :
    Tendsto (fun k => ∫ x in Box.Icc (J k), ∑ i, f' x (e i) i) atTop
      (𝓝 (∫ x in Box.Icc I, ∑ i, f' x (e i) i)) := by
    simp only [IntegrableOn, ← Measure.restrict_congr_set (Box.Ioo_ae_eq_Icc _)] at Hi ⊢
    rw [← Box.iUnion_Ioo_of_tendsto J.monotone hJl hJu] at Hi ⊢
    exact tendsto_setIntegral_of_monotone (fun k => (J k).measurableSet_Ioo)
      (Box.Ioo.comp J).monotone Hi
  -- Thus it suffices to prove the same about the RHS.
  refine tendsto_nhds_unique_of_eventuallyEq hI_tendsto ?_ (Eventually.of_forall HJ_eq)
  clear hI_tendsto
  rw [tendsto_pi_nhds] at hJl hJu
  /- We'll need to prove a similar statement about the integrals over the front sides and the
    integrals over the back sides. In order to avoid repeating ourselves, we formulate a lemma. -/
  suffices forall (i : Fin (n + 1)) (c : Nat -> Real) (d), (forall k, c k in Icc (I.lower i) (I.upper i)) ->
    Tendsto c atTop (𝓝 d) ->
      Tendsto (fun k => ∫ x in Box.Icc ((J k).face i), f (i.insertNth (c k) x) i) atTop
        (𝓝 <| ∫ x in Box.Icc (I.face i), f (i.insertNth d x) i) by
    rw [Box.Icc_eq_pi] at hJ_sub'
    refine tendsto_finsetSum _ fun i _ => (this _ _ _ ?_ (hJu _)).sub (this _ _ _ ?_ (hJl _))
    exacts [fun k => hJ_sub' k (J k).upper_mem_Icc _ trivial, fun k =>
      hJ_sub' k (J k).lower_mem_Icc _ trivial]
  intro i c d hc hcd
  /- First we prove that the integrals of the restriction of `f` to `{x | x i = d}` over increasing
    boxes `((J k).face i).Icc` tend to the desired limit. The proof mostly repeats the one above. -/
  have hd : d in Icc (I.lower i) (I.upper i) :=
    isClosed_Icc.mem_of_tendsto hcd (Eventually.of_forall hc)
  have Hic : forall k, IntegrableOn (fun x => f (i.insertNth (c k) x) i) (Box.Icc (I.face i)) := fun k =>
    (Box.continuousOn_face_Icc ((continuous_apply i).comp_continuousOn Hc) (hc k)).integrableOn_Icc
  have Hid : IntegrableOn (fun x => f (i.insertNth d x) i) (Box.Icc (I.face i)) :=
    (Box.continuousOn_face_Icc ((continuous_apply i).comp_continuousOn Hc) hd).integrableOn_Icc
  have H :
    Tendsto (fun k => ∫ x in Box.Icc ((J k).face i), f (i.insertNth d x) i) atTop
      (𝓝 <| ∫ x in Box.Icc (I.face i), f (i.insertNth d x) i) := by
    have hIoo : (⋃ k, Box.Ioo ((J k).face i)) = Box.Ioo (I.face i) :=
      Box.iUnion_Ioo_of_tendsto ((Box.monotone_face i).comp J.monotone)
        (tendsto_pi_nhds.2 fun _ => hJl _) (tendsto_pi_nhds.2 fun _ => hJu _)
    simp only [IntegrableOn, ← Measure.restrict_congr_set (Box.Ioo_ae_eq_Icc _), ← hIoo] at Hid ⊢
    exact tendsto_setIntegral_of_monotone (fun k => ((J k).face i).measurableSet_Ioo)
      (Box.Ioo.monotone.comp ((Box.monotone_face i).comp J.monotone)) Hid
  /- Thus it suffices to show that the distance between the integrals of the restrictions of `f` to
    `{x | x i = c k}` and `{x | x i = d}` over `((J k).face i).Icc` tends to zero as `k → ∞`. Choose
    `ε > 0`. -/
  refine H.congr_dist (Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε εpos => ?_)
  have hvol_pos : forall J : Box (Fin n), 0 < ∏ j, (J.upper j - J.lower j) := fun J =>
prod_pos fun j hj => sub_pos.2 J.lower_lt_upper _
  /- Choose `δ > 0` such that for any `x y ∈ I.Icc` at distance at most `δ`, the distance between
    `f x` and `f y` is at most `ε / volume (I.face i).Icc`, then the distance between the integrals
    is at most `(ε / volume (I.face i).Icc) * volume ((J k).face i).Icc ≤ ε`. -/
  rcases Metric.uniformContinuousOn_iff_le.1 (I.isCompact_Icc.uniformContinuousOn_of_continuous Hc)
      (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) (div_pos εpos (hvol_pos (I.face i)))
    with ⟨δ, δpos, hδ⟩
  refine (hcd.eventually (Metric.ball_mem_nhds _ δpos)).mono fun k hk => ?_
  have Hsub : Box.Icc ((J k).face i) subseteq Box.Icc (I.face i) :=
    Box.le_iff_Icc.1 (Box.face_mono (hJ_le _) i)
  rw [mem_closedBall_zero_iff]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg dist_nonneg]; rw [dist_eq_norm]; rw [← integral_sub (Hid.mono_set Hsub) ((Hic _).mono_set Hsub)]
  calc
    ‖∫ x in Box.Icc ((J k).face i), f (i.insertNth d x) i - f (i.insertNth (c k) x) i‖ <=
        (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) *
          (volume (Box.Icc ((J k).face i))).toReal := by
      refine norm_setIntegral_le_of_norm_le_const (((J k).face i).measure_Icc_lt_top _)
        fun x hx => ?_
      rw [← dist_eq_norm]
      calc
        dist (f (i.insertNth d x) i) (f (i.insertNth (c k) x) i) <=
            dist (f (i.insertNth d x)) (f (i.insertNth (c k) x)) :=
          dist_le_pi_dist (f (i.insertNth d x)) (f (i.insertNth (c k) x)) i
        _ <= ε / ∏ j, ((I.face i).upper j - (I.face i).lower j) :=
          hδ _ (I.mapsTo_insertNth_face_Icc hd <| Hsub hx) _
            (I.mapsTo_insertNth_face_Icc (hc _) <| Hsub hx) ?_
      rw [Fin.dist_insertNth_insertNth]; rw [dist_self]; rw [dist_comm]
      exact max_le hk.le δpos.lt.le
    _ <= ε := by
      rw [Box.Icc_def]; rw [Real.volume_Icc_pi_toReal ((J k).face i).lower_le_upper]; rw [← le_div_iff₀ (hvol_pos _)]
      gcongr
      exacts [hvol_pos _, fun _ _ => sub_nonneg.2 (Box.lower_le_upper _ _),
        (hJ_sub' _ (J _).upper_mem_Icc).2 _, (hJ_sub' _ (J _).lower_mem_Icc).1 _]

variable (a b : Fin (n + 1) -> Real)

local notation "face " i => Set.Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i)
local notation:max "frontFace " i:arg => Fin.insertNth i (b i)
local notation:max "backFace " i:arg => Fin.insertNth i (a i)

/--
theorem `integral_divergence_of_hasFDerivAt_off_countable` / 定理 `integral_divergence_of_hasFDerivAt_off_countable`

English:
theorem integral_divergence_of_hasFDerivAt_off_countable
  statement: (hle : a <= b)
  proof: by
  rcases em (exists i, a i = b i) with (⟨i, hi⟩ | hne)
  · -- First we sort out the trivial case `∃ i, a i = b i`.
    rw [volume_pi]; rw [← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc]
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt
    have : (pi Set.univ fun j => Ioc (a j)

中文:
定理 integral_divergence_of_hasFDerivAt_off_countable
  结论: (hle : a <= b)
  证明: by
  rcases em (exists i, a i = b i) with (⟨i, hi⟩ | hne)
  · -- First we sort out the trivial case `∃ i, a i = b i`.
    rw [volume_pi]; rw [← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc]
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt
    have : (pi Set.univ fun j => Ioc (a j)

Depends on / 依赖: Fin.exists_succAbove_eq, Ioc_eq_empty, Measure, Measure.univ_pi_Ioc_ae_eq_Icc, Set.univ, eq_or_ne, exists_succAbove_eq, hi.not_lt, not_lt, setIntegral_congr_set, setIntegral_empty, sum_eq_zero, univ_pi_Ioc_ae_eq_Icc, univ_pi_eq_empty, volume_pi
-/
theorem integral_divergence_of_hasFDerivAt_off_countable (hle : a <= b)
    (f : Realⁿ⁺¹ -> Eⁿ⁺¹) (f' : Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] Eⁿ⁺¹)
    (s : Set Realⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : forall x in (Set.pi univ fun i => Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in face i, f (frontFace i x) i) - ∫ x in face i, f (backFace i x) i) := by
  rcases em (exists i, a i = b i) with (⟨i, hi⟩ | hne)
  · -- First we sort out the trivial case `∃ i, a i = b i`.
    rw [volume_pi]; rw [← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc]
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt
    have : (pi Set.univ fun j => Ioc (a j) (b j)) = ∅ := univ_pi_eq_empty hi'
    rw [this]; rw [setIntegral_empty]; rw [sum_eq_zero]
    rintro j -
    rcases eq_or_ne i j with (rfl | hne)
    · simp [hi]
    · rcases Fin.exists_succAbove_eq hne with ⟨i, rfl⟩
      have : Icc (a ∘ j.succAbove) (b ∘ j.succAbove) =ᵐ[volume] (∅ : Set Realⁿ) := by
        rw [ae_eq_empty]; rw [Real.volume_Icc_pi]; rw [prod_eq_zero (Finset.mem_univ i)]
        simp [hi]
      rw [setIntegral_congr_set this]; rw [setIntegral_congr_set this]; rw [setIntegral_empty]; rw [setIntegral_empty]; rw [sub_self]
  · -- In the non-trivial case `∀ i, a i < b i`, we apply a lemma we proved above.
    have hlt : forall i, a i < b i := fun i => (hle i).lt_of_ne fun hi => hne ⟨i, hi⟩
    exact integral_divergence_of_hasFDerivAt_off_countable_aux₂ ⟨a, b, hlt⟩ f f' s hs Hc Hd Hi

/--
theorem `integral_divergence_of_hasFDerivAt_off_countable'` / 定理 `integral_divergence_of_hasFDerivAt_off_countable'`

English:
theorem integral_divergence_of_hasFDerivAt_off_countable'
  statement: (hle : a <= b)
  proof: integral_divergence_of_hasFDerivAt_off_countable a b hle (fun x i => f i x)
    (fun x => ContinuousLinearMap.pi fun i => f' i x) s hs (continuousOn_pi.2 Hc)
    (fun x hx => hasFDerivAt_pi.2 (Hd x hx)) Hi

中文:
定理 integral_divergence_of_hasFDerivAt_off_countable'
  结论: (hle : a <= b)
  证明: integral_divergence_of_hasFDerivAt_off_countable a b hle (fun x i => f i x)
    (fun x => ContinuousLinearMap.pi fun i => f' i x) s hs (continuousOn_pi.2 Hc)
    (fun x hx => hasFDerivAt_pi.2 (Hd x hx)) Hi

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.pi, continuousOn_pi, hasFDerivAt_pi, integral_divergence_of_hasFDerivAt_off_countable
-/
theorem integral_divergence_of_hasFDerivAt_off_countable' (hle : a <= b)
    (f : Fin (n + 1) -> Realⁿ⁺¹ -> E)
    (f' : Fin (n + 1) -> Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] E) (s : Set Realⁿ⁺¹)
    (hs : s.Countable) (Hc : forall i, ContinuousOn (f i) (Icc a b))
    (Hd : forall x in (pi Set.univ fun i => Ioo (a i) (b i)) \ s, forall (i), HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' i x (e i)) =
      ∑ i : Fin (n + 1), ((∫ x in face i, f i (frontFace i x)) -
        ∫ x in face i, f i (backFace i x)) :=
  integral_divergence_of_hasFDerivAt_off_countable a b hle (fun x i => f i x)
    (fun x => ContinuousLinearMap.pi fun i => f' i x) s hs (continuousOn_pi.2 Hc)
    (fun x hx => hasFDerivAt_pi.2 (Hd x hx)) Hi

end

/--
theorem `integral_divergence_of_hasFDerivAt_off_countable_of_equiv` / 定理 `integral_divergence_of_hasFDerivAt_off_countable_of_equiv`

English:
theorem integral_divergence_of_hasFDerivAt_off_countable_of_equiv
  statement: {F : Type*}
  proof: have he_emb : MeasurableEmbedding eL := eL.toHomeomorph.measurableEmbedding
  have hIcc : eL ⁻¹' Icc (eL a) (eL b) = Icc a b := by
    ext1 x; simp only [Set.mem_preimage, Set.mem_Icc, he_ord]
  have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' Icc a b := by rw [← hIcc, eL.symm_preimage_preimage]
  calc


中文:
定理 integral_divergence_of_hasFDerivAt_off_countable_of_equiv
  结论: {F : 类型}
  证明: have he_emb : MeasurableEmbedding eL := eL.toHomeomorph.measurableEmbedding
  have hIcc : eL ⁻¹' Icc (eL a) (eL b) = Icc a b := by
    ext1 x; simp only [Set.mem_preimage, Set.mem_Icc, he_ord]
  have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' Icc a b := by rw [← hIcc, eL.symm_preimage_preimage]
  calc


Depends on / 依赖: MeasurableEmbedding, Set.mem_Icc, Set.mem_preimage, eL.symm, eL.symm_preimage_preimage, eL.toHomeomorph.measurableEmbedding, he_emb, he_ord, he_vol, he_vol.setIntegral_preimage_emb, measurableEmbedding, mem_Icc, mem_preimage, setIntegral_preimage_emb, symm_preimage_preimage, toHomeomorph
-/
theorem integral_divergence_of_hasFDerivAt_off_countable_of_equiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace Real F] [Preorder F] [MeasureSpace F] [BorelSpace F]
    (eL : F ≃L[Real] Realⁿ⁺¹) (he_ord : forall x y, eL x <= eL y ↔ x <= y)
    (he_vol : MeasurePreserving eL volume volume) (f : Fin (n + 1) -> F -> E)
    (f' : Fin (n + 1) -> F -> F ->L[Real] E) (s : Set F) (hs : s.Countable) (a b : F) (hle : a <= b)
    (Hc : forall i, ContinuousOn (f i) (Icc a b))
    (Hd : forall x in interior (Icc a b) \ s, forall (i), HasFDerivAt (f i) (f' i x) x) (DF : F -> E)
    (hDF : forall x, DF x = ∑ i, f' i x (eL.symm <| e i)) (Hi : IntegrableOn DF (Icc a b)) :
    ∫ x in Icc a b, DF x =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL b i) x)) -
          ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL a i) x)) :=
  have he_emb : MeasurableEmbedding eL := eL.toHomeomorph.measurableEmbedding
  have hIcc : eL ⁻¹' Icc (eL a) (eL b) = Icc a b := by
    ext1 x; simp only [Set.mem_preimage, Set.mem_Icc, he_ord]
  have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' Icc a b := by rw [← hIcc, eL.symm_preimage_preimage]
  calc
    ∫ x in Icc a b, DF x = ∫ x in Icc a b, ∑ i, f' i x (eL.symm <| e i) := by simp only [hDF]
    _ = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm <| e i) := by
      rw [← he_vol.setIntegral_preimage_emb he_emb]
      simp only [hIcc, eL.symm_apply_apply]
    _ = ∑ i : Fin (n + 1),
          ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL b i) x)) -
            ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL a i) x)) := by
      refine integral_divergence_of_hasFDerivAt_off_countable' (eL a) (eL b)
        ((he_ord _ _).2 hle) (fun i x => f i (eL.symm x))
        (fun i x => f' i (eL.symm x) ∘L (eL.symm : Realⁿ⁺¹ ->L[Real] F)) (eL.symm ⁻¹' s)
        (hs.preimage eL.symm.injective) ?_ ?_ ?_
      · exact fun i => (Hc i).comp eL.symm.continuousOn hIcc'.subset
      · refine fun x hx i => (Hd (eL.symm x) ⟨?_, hx.2⟩ i).comp x eL.symm.hasFDerivAt
        rw [← hIcc]
        refine preimage_interior_subset_interior_preimage eL.continuous ?_
        simpa only [Set.mem_preimage, eL.apply_symm_apply, ← pi_univ_Icc,
          interior_pi_set (@finite_univ (Fin _) _), interior_Icc] using hx.1
      · rw [← he_vol.integrableOn_comp_preimage he_emb, hIcc]
        simp [← hDF, Function.comp_def, Hi]

end

open scoped Interval

open ContinuousLinearMap (smulRight)


local macro:arg t:term:max noWs "¹" : term => `(Fin 1 -> $t)
local macro:arg t:term:max noWs "²" : term => `(Fin 2 -> $t)

/--
theorem `integral_eq_of_hasDerivAt_off_countable_of_le` / 定理 `integral_eq_of_hasDerivAt_off_countable_of_le`

English:
theorem integral_eq_of_hasDerivAt_off_countable_of_le
  statement: [CompleteSpace E] (f f' : Real -> E)
  proof: by
  set e : Real ≃L[Real] Real¹ := (ContinuousLinearEquiv.funUnique (Fin 1) Real Real).symm
  set F' : Real -> Real ->L[Real] E := fun x => smulRight (1 : Real ->L[Real] Real) (f' x)
  calc
    ∫ x in a..b, f' x = ∫ x in Icc a b, f' x := by
      rw [intervalIntegral.integral_of_le hle]; rw [setInt

中文:
定理 integral_eq_of_hasDerivAt_off_countable_of_le
  结论: [CompleteSpace E] (f f' : 实数 -> E)
  证明: by
  set e : Real ≃L[Real] Real¹ := (ContinuousLinearEquiv.funUnique (Fin 1) Real Real).symm
  set F' : Real -> Real ->L[Real] E := fun x => smulRight (1 : Real ->L[Real] Real) (f' x)
  calc
    ∫ x in a..b, f' x = ∫ x in Icc a b, f' x := by
      rw [intervalIntegral.integral_of_le hle]; rw [setInt

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.funUnique, Ioc_ae_eq_Icc, e.symm, funUnique, i.insertNt, i.insertNth, i.succAbove, insertNt, insertNth, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, setIntegral_congr_set, smulRight, succAbove
-/
theorem integral_eq_of_hasDerivAt_off_countable_of_le [CompleteSpace E] (f f' : Real -> E)
    {a b : Real} (hle : a <= b) {s : Set Real} (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : forall x in Ioo a b \ s, HasDerivAt f (f' x) x) (Hi : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  set e : Real ≃L[Real] Real¹ := (ContinuousLinearEquiv.funUnique (Fin 1) Real Real).symm
  set F' : Real -> Real ->L[Real] E := fun x => smulRight (1 : Real ->L[Real] Real) (f' x)
  calc
    ∫ x in a..b, f' x = ∫ x in Icc a b, f' x := by
      rw [intervalIntegral.integral_of_le hle]; rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∑ i : Fin 1,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e a i) x)) := by
      simp only [← interior_Icc] at Hd
      refine
        integral_divergence_of_hasFDerivAt_off_countable_of_equiv e ?_ ?_ (fun _ => f)
          (fun _ => F') s hs a b hle (fun _ => Hc) (fun x hx _ => Hd x hx) _ ?_ ?_
      · exact fun x y => (OrderIso.funUnique (Fin 1) Real).symm.le_iff_le
      · exact (volume_preserving_funUnique (Fin 1) Real).symm _
      · simp [F', e]
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at Hi
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm
    _ = f b - f a := by
      simp [e, Subsingleton.elim (const (Fin 0) _) isEmptyElim, volume_pi,
        Measure.pi_of_empty fun _ : Fin 0 => _]

/--
theorem `integral_eq_of_hasDerivAt_off_countable` / 定理 `integral_eq_of_hasDerivAt_off_countable`

English:
theorem integral_eq_of_hasDerivAt_off_countable
  statement: [CompleteSpace E] (f f' : Real -> E) {a b : Real}
  proof: by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
    exact integral_eq_of_hasDerivAt_off_countable_of_le f f' hab hs Hc Hd Hi
  · simp only [uIcc_of_ge hab, min_eq_right hab, max_eq_left hab] at *
    rw [intervalIntegral.integral_symm]; 

中文:
定理 integral_eq_of_hasDerivAt_off_countable
  结论: [CompleteSpace E] (f f' : 实数 -> E) {a b : 实数}
  证明: by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
    exact integral_eq_of_hasDerivAt_off_countable_of_le f f' hab hs Hc Hd Hi
  · simp only [uIcc_of_ge hab, min_eq_right hab, max_eq_left hab] at *
    rw [intervalIntegral.integral_symm]; 

Depends on / 依赖: Hi.symm, integral_eq_of_hasDerivAt_off_countable_of_le, integral_symm, intervalIntegral, intervalIntegral.integral_symm, le_total, max_eq_left, max_eq_right, min_eq_left, min_eq_right, neg_eq_iff_eq_neg, neg_sub, uIcc_of_ge, uIcc_of_le
-/
theorem integral_eq_of_hasDerivAt_off_countable [CompleteSpace E] (f f' : Real -> E) {a b : Real}
    {s : Set Real} (hs : s.Countable) (Hc : ContinuousOn f [[a, b]])
    (Hd : forall x in Ioo (min a b) (max a b) \ s, HasDerivAt f (f' x) x)
    (Hi : IntervalIntegrable f' volume a b) : ∫ x in a..b, f' x = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
    exact integral_eq_of_hasDerivAt_off_countable_of_le f f' hab hs Hc Hd Hi
  · simp only [uIcc_of_ge hab, min_eq_right hab, max_eq_left hab] at *
    rw [intervalIntegral.integral_symm]; rw [neg_eq_iff_eq_neg]; rw [neg_sub]
    exact integral_eq_of_hasDerivAt_off_countable_of_le f f' hab hs Hc Hd Hi.symm

/--
theorem `integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le` / 定理 `integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`

English:
theorem integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
  statement: (f g : Real × Real -> E)
  proof: let e : (Real × Real) ≃L[Real] Real² := (ContinuousLinearEquiv.finTwoArrow Real Real).symm
  calc
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
        ∑ i : Fin 2,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e b i) x)) -
      

中文:
定理 integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
  结论: (f g : 实数 × 实数 -> E)
  证明: let e : (Real × Real) ≃L[Real] Real² := (ContinuousLinearEquiv.finTwoArrow Real Real).symm
  calc
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
        ∑ i : Fin 2,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e b i) x)) -
      

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.finTwoArrow, e.symm, finTwoArrow, i.insertNth, i.succAbove, insertNth, integral_divergence_of_hasFDerivAt_off_countable_of_equiv, succAbove
-/
theorem integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (f g : Real × Real -> E)
    (f' g' : Real × Real -> Real × Real ->L[Real] E) (a b : Real × Real) (hle : a <= b) (s : Set (Real × Real)) (hs : s.Countable)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (Hdg : forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) -
        ∫ y in a.2..b.2, f (a.1, y) :=
  let e : (Real × Real) ≃L[Real] Real² := (ContinuousLinearEquiv.finTwoArrow Real Real).symm
  calc
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
        ∑ i : Fin 2,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e a i) x)) := by
      refine integral_divergence_of_hasFDerivAt_off_countable_of_equiv e ?_ ?_ ![f, g]
        ![f', g'] s hs a b hle ?_ (fun x hx => ?_) _ ?_ Hi
      · exact fun x y => (OrderIso.finTwoArrowIso Real).symm.le_iff_le
      · exact (volume_preserving_finTwoArrow Real).symm _
      · exact Fin.forall_fin_two.2 ⟨Hcf, Hcg⟩
      · rw [Icc_prod_eq, interior_prod_eq, interior_Icc, interior_Icc] at hx
        exact Fin.forall_fin_two.2 ⟨Hdf x hx, Hdg x hx⟩
      · intro x; rw [Fin.sum_univ_two]; rfl
    _ = ((∫ y in Icc a.2 b.2, f (b.1, y)) - ∫ y in Icc a.2 b.2, f (a.1, y)) +
          ((∫ x in Icc a.1 b.1, g (x, b.2)) - ∫ x in Icc a.1 b.1, g (x, a.2)) := by
      have : forall (a b : Real¹) (f : Real¹ -> E),
          ∫ x in Icc a b, f x = ∫ x in Icc (a 0) (b 0), f fun _ => x := fun a b f => by
        convert!
          (((volume_preserving_funUnique (Fin 1) Real).symm _).setIntegral_preimage_emb
              (MeasurableEquiv.measurableEmbedding _) f _).symm
        exact ((OrderIso.funUnique (Fin 1) Real).symm.preimage_Icc a b).symm
      simp only [Fin.sum_univ_two, this]
      rfl
    _ = (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
            ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) := by
      simp only [intervalIntegral.integral_of_le hle.1, intervalIntegral.integral_of_le hle.2,
        setIntegral_congr_set (Ioc_ae_eq_Icc (α := Real) (μ := volume))]
      abel

/--
theorem `integral_divergence_prod_Icc_of_hasFDerivAt_of_le` / 定理 `integral_divergence_prod_Icc_of_hasFDerivAt_of_le`

English:
theorem integral_divergence_prod_Icc_of_hasFDerivAt_of_le
  statement: (f g : Real × Real -> E)
  proof: integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le f g f' g' a b hle ∅
    (by simp) Hcf Hcg (by simpa only [sdiff_empty]) (by simpa only [sdiff_empty]) Hi

中文:
定理 integral_divergence_prod_Icc_of_hasFDerivAt_of_le
  结论: (f g : 实数 × 实数 -> E)
  证明: integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le f g f' g' a b hle ∅
    (by simp) Hcf Hcg (by simpa only [sdiff_empty]) (by simpa only [sdiff_empty]) Hi

Depends on / 依赖: integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le, sdiff_empty
-/
theorem integral_divergence_prod_Icc_of_hasFDerivAt_of_le (f g : Real × Real -> E)
    (f' g' : Real × Real -> Real × Real ->L[Real] E) (a b : Real × Real) (hle : a <= b)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt f (f' x) x)
    (Hdg : forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :=
  integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le f g f' g' a b hle ∅
    (by simp) Hcf Hcg (by simpa only [sdiff_empty]) (by simpa only [sdiff_empty]) Hi

/--
theorem `integral2_divergence_prod_of_hasFDerivAt_off_countable` / 定理 `integral2_divergence_prod_of_hasFDerivAt_off_countable`

English:
theorem integral2_divergence_prod_of_hasFDerivAt_off_countable
  statement: (f g : Real × Real -> E)
  proof: by
  wlog h₁ : a₁ <= b₁ generalizing a₁ b₁
  · specialize this b₁ a₁
    rw [uIcc_comm b₁ a₁]; rw [min_comm b₁ a₁]; rw [max_comm b₁ a₁] at this
    simp only [intervalIntegral.integral_symm b₁ a₁]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_ge h₁))).trans ?_; abel
  wlog h₂ : a

中文:
定理 integral2_divergence_prod_of_hasFDerivAt_off_countable
  结论: (f g : 实数 × 实数 -> E)
  证明: by
  wlog h₁ : a₁ <= b₁ generalizing a₁ b₁
  · specialize this b₁ a₁
    rw [uIcc_comm b₁ a₁]; rw [min_comm b₁ a₁]; rw [max_comm b₁ a₁] at this
    simp only [intervalIntegral.integral_symm b₁ a₁]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_ge h₁))).trans ?_; abel
  wlog h₂ : a

Depends on / 依赖: Neg.neg, congr_ar, congr_arg, generalizing, integral_neg, integral_symm, intervalIntegral, intervalIntegral.integral_neg, intervalIntegral.integral_symm, le_of_not_ge, max_comm, min_comm, specialize, uIcc_comm
-/
theorem integral2_divergence_prod_of_hasFDerivAt_off_countable (f g : Real × Real -> E)
    (f' g' : Real × Real -> Real × Real ->L[Real] E) (a₁ a₂ b₁ b₂ : Real) (s : Set (Real × Real)) (hs : s.Countable)
    (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hdf : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
      HasFDerivAt f (f' x) x)
    (Hdg : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
      HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) := by
  wlog h₁ : a₁ <= b₁ generalizing a₁ b₁
  · specialize this b₁ a₁
    rw [uIcc_comm b₁ a₁]; rw [min_comm b₁ a₁]; rw [max_comm b₁ a₁] at this
    simp only [intervalIntegral.integral_symm b₁ a₁]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_ge h₁))).trans ?_; abel
  wlog h₂ : a₂ <= b₂ generalizing a₂ b₂
  · specialize this b₂ a₂
    rw [uIcc_comm b₂ a₂]; rw [min_comm b₂ a₂]; rw [max_comm b₂ a₂] at this
    simp only [intervalIntegral.integral_symm b₂ a₂, intervalIntegral.integral_neg]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_ge h₂))).trans ?_; abel
  simp only [uIcc_of_le h₁, uIcc_of_le h₂, min_eq_left, max_eq_right, h₁, h₂] at Hcf Hcg Hdf Hdg Hi
  calc
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
        ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) := by
      simp only [intervalIntegral.integral_of_le, h₁, h₂,
        setIntegral_congr_set (Ioc_ae_eq_Icc (α := Real) (μ := volume))]
    _ = ∫ x in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f' x (1, 0) + g' x (0, 1) := (setIntegral_prod _ Hi).symm
    _ = (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
          ∫ y in a₂..b₂, f (a₁, y) := by
      rw [Icc_prod_Icc] at *
      apply integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le f g f' g'
        (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩ s <;> assumption

/--
theorem `integral2_divergence_prod_of_hasFDerivAt` / 定理 `integral2_divergence_prod_of_hasFDerivAt`

English:
theorem integral2_divergence_prod_of_hasFDerivAt
  statement: (f g : Real × Real -> E)
  proof: integral2_divergence_prod_of_hasFDerivAt_off_countable f g f' g' a₁ a₂ b₁ b₂ ∅ countable_empty
    Hcf Hcg (fun x hx => Hdf x hx.1) (fun x hx => Hdg x hx.1) Hi

中文:
定理 integral2_divergence_prod_of_hasFDerivAt
  结论: (f g : 实数 × 实数 -> E)
  证明: integral2_divergence_prod_of_hasFDerivAt_off_countable f g f' g' a₁ a₂ b₁ b₂ ∅ countable_empty
    Hcf Hcg (fun x hx => Hdf x hx.1) (fun x hx => Hdg x hx.1) Hi

Depends on / 依赖: countable_empty, integral2_divergence_prod_of_hasFDerivAt_off_countable
-/
theorem integral2_divergence_prod_of_hasFDerivAt (f g : Real × Real -> E)
    (f' g' : Real × Real -> Real × Real ->L[Real] E) (a₁ a₂ b₁ b₂ : Real)
    (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hdf : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt f (f' x) x)
    (Hdg : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) :=
  integral2_divergence_prod_of_hasFDerivAt_off_countable f g f' g' a₁ a₂ b₁ b₂ ∅ countable_empty
    Hcf Hcg (fun x hx => Hdf x hx.1) (fun x hx => Hdg x hx.1) Hi

end MeasureTheory
