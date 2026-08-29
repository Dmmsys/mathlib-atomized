/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Volume of balls

Let `E` be a finite-dimensional normed `ℝ`-vector space equipped with a Haar measure `μ`. We
prove that
`μ (Metric.ball 0 1) = (∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)`
for any real number `p` with `0 < p`, see `MeasureTheory.measure_unitBall_eq_integral_div_gamma`. We
also prove the corresponding result to compute `μ {x : E | g x < 1}` where `g : E → ℝ` is a function
defining a norm on `E`, see `MeasureTheory.measure_lt_one_eq_integral_div_gamma`.

Using these formulas, we compute the volume of the unit balls in several cases.

* `MeasureTheory.volume_sum_rpow_lt` / `MeasureTheory.volume_sum_rpow_le`: volume of the open and
  closed balls for the norm `Lp` over a real finite-dimensional vector space with `1 ≤ p`. These
  are computed as `volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r}` and
  `volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r}` since the spaces `PiLp` do not have a
  `MeasureSpace` instance.

* `Complex.volume_sum_rpow_lt_one` / `Complex.volume_sum_rpow_lt`: same as above but for complex
  finite-dimensional vector space.

* `EuclideanSpace.volume_ball` / `EuclideanSpace.volume_closedBall` : volume of open and closed
  balls in a finite-dimensional Euclidean space.

* `InnerProductSpace.volume_ball` / `InnerProductSpace.volume_closedBall`: volume of open and closed
  balls in a finite-dimensional real inner product space.

* `Complex.volume_ball` / `Complex.volume_closedBall`: volume of open and closed balls in `ℂ`.
-/

public section

section general_case

open MeasureTheory MeasureTheory.Measure Module ENNReal

/--
theorem `MeasureTheory.measure_unitBall_eq_integral_div_gamma` / 定理 `MeasureTheory.measure_unitBall_eq_integral_div_gamma`

English:
theorem MeasureTheory.measure_unitBall_eq_integral_div_gamma
  statement: {E : Type*} {p : Real}
  proof: by
  obtain hE | hE := subsingleton_or_nontrivial E
  · rw [(Metric.nonempty_ball.mpr zero_lt_one).eq_zero, ← setIntegral_univ,
      Set.univ_nonempty.eq_zero, integral_singleton, finrank_zero_of_subsingleton, Nat.cast_zero,
      zero_div, zero_add, Real.Gamma_one, div_one, norm_zero, Real.zero_rp

中文:
定理 测度论.measure_unitBall_eq_integral_div_gamma
  结论: {E : 类型} {p : 实数}
  证明: by
  obtain hE | hE := subsingleton_or_nontrivial E
  · rw [(Metric.nonempty_ball.mpr zero_lt_one).eq_zero, ← setIntegral_univ,
      Set.univ_nonempty.eq_zero, integral_singleton, finrank_zero_of_subsingleton, Nat.cast_zero,
      zero_div, zero_add, Real.Gamma_one, div_one, norm_zero, Real.zero_rp

Depends on / 依赖: Gamma_one, Metric, Metric.nonempty_ball.mpr, Nat.cast_pos.mpr, Nat.cast_zero, Real.Gamma_one, Real.exp_zero, Real.zero_rpow, Set.Ioi, Set.univ_nonempty.eq_zero, cast_pos, cast_zero, div_one, eq_zero, exp_zero, finrank, finrank_pos, finrank_zero_of_subsingleton, hp.ne, integral_singleton
-/
theorem MeasureTheory.measure_unitBall_eq_integral_div_gamma {E : Type*} {p : Real}
    [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (hp : 0 < p) :
    μ (Metric.ball 0 1) =
      .ofReal ((∫ (x : E), Real.exp (-‖x‖ ^ p) ∂μ) / Real.Gamma (finrank Real E / p + 1)) := by
  obtain hE | hE := subsingleton_or_nontrivial E
  · rw [(Metric.nonempty_ball.mpr zero_lt_one).eq_zero, ← setIntegral_univ,
      Set.univ_nonempty.eq_zero, integral_singleton, finrank_zero_of_subsingleton, Nat.cast_zero,
      zero_div, zero_add, Real.Gamma_one, div_one, norm_zero, Real.zero_rpow hp.ne', neg_zero,
      Real.exp_zero, smul_eq_mul, mul_one, measureReal_def, ofReal_toReal (measure_ne_top μ {0})]
  · have : (0 : Real) < finrank Real E := Nat.cast_pos.mpr finrank_pos
    have : ((∫ y in Set.Ioi (0 : Real), y ^ (finrank Real E - 1) • Real.exp (-y ^ p)) /
        Real.Gamma ((finrank Real E) / p + 1)) * (finrank Real E) = 1 := by
      simp_rw [← Real.rpow_natCast _ (finrank Real E - 1), smul_eq_mul, Nat.cast_sub finrank_pos,
        Nat.cast_one]
      rw [integral_rpow_mul_exp_neg_rpow hp (by linarith)]; rw [sub_add_cancel]; rw [Real.Gamma_add_one (ne_of_gt (by positivity))]
      field
    rw [integral_fun_norm_addHaar μ (fun x => Real.exp (-x ^ p))]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [mul_div_assoc]; rw [mul_div_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [this]; rw [mul_one]; rw [ofReal_measureReal _]
    exact ne_of_lt measure_ball_lt_top

variable {E : Type*} [AddCommGroup E] [Module Real E] [FiniteDimensional Real E] [mE : MeasurableSpace E]
  [tE : TopologicalSpace E] [IsTopologicalAddGroup E] [BorelSpace E] [T2Space E]
  [ContinuousSMul Real E] (μ : Measure E) [IsAddHaarMeasure μ] {g : E -> Real} (h1 : g 0 = 0)
  (h2 : forall x, g (-x) = g x) (h3 : forall x y, g (x + y) <= g x + g y) (h4 : forall {x}, g x = 0 -> x = 0)
  (h5 : forall r x, g (r • x) <= |r| * (g x))
include h1 h2 h3 h4 h5

/--
theorem `MeasureTheory.measure_lt_one_eq_integral_div_gamma` / 定理 `MeasureTheory.measure_lt_one_eq_integral_div_gamma`

English:
theorem MeasureTheory.measure_lt_one_eq_integral_div_gamma
  given: {p : Real} (hp : 0 < p)
  proof: by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx => h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace Real F := { norm_smul_le := fun _ _ => h5 

中文:
定理 测度论.measure_lt_one_eq_integral_div_gamma
  条件: {p : 实数} (hp : 0 < p)
  证明: by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx => h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace Real F := { norm_smul_le := fun _ _ => h5 
-/
theorem MeasureTheory.measure_lt_one_eq_integral_div_gamma {p : Real} (hp : 0 < p) :
    μ {x : E | g x < 1} =
      .ofReal ((∫ (x : E), Real.exp (-(g x) ^ p) ∂μ) / Real.Gamma (finrank Real E / p + 1)) := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx => h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace Real F := { norm_smul_le := fun _ _ => h5 _ _ }
  -- We put the new topology on F
  let : TopologicalSpace F := UniformSpace.toTopologicalSpace
  let : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv Real _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl Real E : E ≃ₗ[Real] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify the topology of E
  let ν : Measure F := @Measure.map E F mE _ φ μ
  convert! (measure_unitBall_eq_integral_div_gamma ν hp) using 1
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr!
      simp_rw [Metric.ball, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous Real Real _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · -- The map between `E` and `F` as a measurable equivalence
    let ψ := @Homeomorph.toMeasurableEquiv E F tE mE _ _ _ _
      (@ContinuousLinearEquiv.toHomeomorph Real Real _ _ _ _ _ _ E tE _ F _ _ _ _ φ)
    -- The map `ψ` is measure preserving by construction
    have : @MeasurePreserving E F mE _ ψ μ ν :=
      @Measurable.measurePreserving E F mE _ ψ (@MeasurableEquiv.measurable E F mE _ ψ) _
    rw [← this.integral_comp']
    rfl

/--
theorem `MeasureTheory.measure_le_eq_lt` / 定理 `MeasureTheory.measure_le_eq_lt`

English:
theorem MeasureTheory.measure_le_eq_lt
  given: [Nontrivial E] (r : Real)
  proof: by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx => h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace Real F := { norm_smul_le := fun _ _ => h5 

中文:
定理 测度论.measure_le_eq_lt
  条件: [非平凡 E] (r : 实数)
  证明: by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx => h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace Real F := { norm_smul_le := fun _ _ => h5 
-/
theorem MeasureTheory.measure_le_eq_lt [Nontrivial E] (r : Real) :
    μ {x : E | g x <= r} = μ {x : E | g x < r} := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx => h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace Real F := { norm_smul_le := fun _ _ => h5 _ _ }
  -- We put the new topology on F
  let : TopologicalSpace F := UniformSpace.toTopologicalSpace
  let : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv Real _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl Real E : E ≃ₗ[Real] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify the topology of E
  let ν : Measure F := @Measure.map E F mE _ φ μ
  convert! addHaar_closedBall_eq_addHaar_ball ν 0 r using 1
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_closedBall]
    · congr!
      simp_rw [Metric.closedBall, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous Real Real _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr!
      simp_rw [Metric.ball, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous Real Real _ _ _ _ _ _ E tE _ F _ _ _ _ φ

end general_case

section LpSpace

open Real Fintype ENNReal Module MeasureTheory MeasureTheory.Measure WithLp

variable (ι : Type*) [Fintype ι] {p : Real}

/--
theorem `MeasureTheory.volume_sum_rpow_lt_one` / 定理 `MeasureTheory.volume_sum_rpow_lt_one`

English:
theorem MeasureTheory.volume_sum_rpow_lt_one
  given: (hp : 1 <= p)
  proof: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : forall x : ι -> Real, 0 <= ∑ i, |x i| ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (abs_nonneg _) _) _
  -- We collect facts about `Lp

中文:
定理 测度论.volume_sum_rpow_lt_one
  条件: (hp : 1 <= p)
  证明: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : forall x : ι -> Real, 0 <= ∑ i, |x i| ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (abs_nonneg _) _) _
  -- We collect facts about `Lp

Depends on / 依赖: ENNReal, ENNReal.ofReal, Finset, Finset.sum_nonneg, abs_nonneg, le_of_lt, ofReal, rpow_nonneg, sum_nonneg, toReal, toReal_ofReal
-/
theorem MeasureTheory.volume_sum_rpow_lt_one (hp : 1 <= p) :
    volume {x : ι -> Real | ∑ i, |x i| ^ p < 1} =
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : forall x : ι -> Real, 0 <= ∑ i, |x i| ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (abs_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι -> Real) : ‖toLp (.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 <= ENNReal.ofReal p) := fact_iff.mpr (ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι -> Real)‖ = 0 := norm_zero
  have eq_zero (x : ι -> Real) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι -> Real => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι -> Real => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : Real) (x : ι -> Real) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => Real)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm,
    norm_eq_abs] at eq_zero nm_zero nm_neg nm_add nm_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert!
    (measure_lt_one_eq_integral_div_gamma (volume : Measure (ι -> Real)) (g := fun x =>
      (∑ i, |x i| ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp (fun r x => nm_smul r x)
      (by linarith : 0 < p)) using 4
  · rw [rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg (abs_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel₀ _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, exp_sum]
    rw [integral_fintype_prod_volume_eq_pow fun x : Real => exp (- |x| ^ p)]; rw [integral_comp_abs
      (f := fun x => exp (- x ^ p))]; rw [integral_exp_neg_rpow h₁]
  · rw [finrank_fintype_fun_eq_card]

/--
theorem `MeasureTheory.volume_sum_rpow_lt` / 定理 `MeasureTheory.volume_sum_rpow_lt`

English:
theorem MeasureTheory.volume_sum_rpow_lt
  given: [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real)
  proof: by
  have h₁ (x : ι -> Real) : 0 <= ∑ i, |x i| ^ p := by positivity
  have h₂ : forall x : ι -> Real, 0 <= (∑ i, |x i| ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun 

中文:
定理 测度论.volume_sum_rpow_lt
  条件: [非空 ι] {p : 实数} (hp : 1 <= p) (r : 实数)
  证明: by
  have h₁ (x : ι -> Real) : 0 <= ∑ i, |x i| ^ p := by positivity
  have h₂ : forall x : ι -> Real, 0 <= (∑ i, |x i| ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun 

Depends on / 依赖: Fin.pos, Set.mem_ofPred.mp, hx.elim, le_or_gt, lt_of_lt_of_le, measure_empty, mem_ofPred, not_le, not_le.mpr, rpow_nonneg, volume_sum_rp, zero_eq_ofReal, zero_eq_ofReal.mpr, zero_mul, zero_pow
-/
theorem MeasureTheory.volume_sum_rpow_lt [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real) :
    volume {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) < r} = (.ofReal r) ^ card ι *
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ (x : ι -> Real) : 0 <= ∑ i, |x i| ^ p := by positivity
  have h₂ : forall x : ι -> Real, 0 <= (∑ i, |x i| ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact not_le.mpr (lt_of_lt_of_le (Set.mem_ofPred.mp hx) hr) (h₂ x)
    rw [this]; rw [measure_empty]; rw [← zero_eq_ofReal.mpr hr]; rw [zero_pow Fin.pos'.ne']; rw [zero_mul]
  · rw [← volume_sum_rpow_lt_one _ hp, ← ofReal_pow (le_of_lt hr), ← finrank_pi Real]
    convert! addHaar_smul_of_nonneg volume (le_of_lt hr) {x : ι -> Real | ∑ i, |x i| ^ p < 1} using 2
    simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_ofPred_eq, Pi.smul_apply,
      smul_eq_mul, abs_mul, mul_rpow (abs_nonneg _) (abs_nonneg _), abs_inv,
      inv_rpow (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr),
      inv_mul_lt_iff₀ (rpow_pos_of_pos hr _), mul_one, ← rpow_lt_rpow_iff
      (rpow_nonneg (h₁ _) _) (le_of_lt hr) (by linarith : 0 < p), ← rpow_mul
      (h₁ _), div_mul_cancel₀ _ (ne_of_gt (by linarith) : p != 0), Real.rpow_one]

/--
theorem `MeasureTheory.volume_sum_rpow_le` / 定理 `MeasureTheory.volume_sum_rpow_le`

English:
theorem MeasureTheory.volume_sum_rpow_le
  given: [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real)
  proof: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_le_one_eq_lt_one`
  have eq_norm (x : ι -> Real) : ‖toLp (.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
    simp [PiLp.nor

中文:
定理 测度论.volume_sum_rpow_le
  条件: [非空 ι] {p : 实数} (hp : 1 <= p) (r : 实数)
  证明: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_le_one_eq_lt_one`
  have eq_norm (x : ι -> Real) : ‖toLp (.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
    simp [PiLp.nor

Depends on / 依赖: ENNReal, ENNReal.ofReal, le_of_lt, ofReal, toReal, toReal_ofReal
-/
theorem MeasureTheory.volume_sum_rpow_le [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real) :
    volume {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) <= r} = (.ofReal r) ^ card ι *
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_le_one_eq_lt_one`
  have eq_norm (x : ι -> Real) : ‖toLp (.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 <= ENNReal.ofReal p) := fact_iff.mpr (ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι -> Real)‖ = 0 := norm_zero
  have eq_zero (x : ι -> Real) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι -> Real => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι -> Real => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : Real) (x : ι -> Real) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => Real)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm,
    norm_eq_abs] at eq_zero nm_zero nm_neg nm_add nm_smul
  rw [measure_le_eq_lt _ nm_zero (fun x => nm_neg x) (fun x y => nm_add x y) (eq_zero _).mp
    (fun r x => nm_smul r x)]; rw [volume_sum_rpow_lt _ hp]

/--
theorem `Complex.volume_sum_rpow_lt_one` / 定理 `Complex.volume_sum_rpow_lt_one`

English:
theorem Complex.volume_sum_rpow_lt_one
  given: {p : Real} (hp : 1 <= p)
  proof: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : forall x : ι -> Complex, 0 <= ∑ i, ‖x i‖ ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (norm_nonneg _) _) _
  -- We collect facts about

中文:
定理 复形.volume_sum_rpow_lt_one
  条件: {p : 实数} (hp : 1 <= p)
  证明: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : forall x : ι -> Complex, 0 <= ∑ i, ‖x i‖ ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (norm_nonneg _) _) _
  -- We collect facts about

Depends on / 依赖: ENNReal, ENNReal.ofReal, Finset, Finset.sum_nonneg, le_of_lt, norm_nonneg, ofReal, rpow_nonneg, sum_nonneg, toReal, toReal_ofReal
-/
theorem Complex.volume_sum_rpow_lt_one {p : Real} (hp : 1 <= p) :
    volume {x : ι -> Complex | ∑ i, ‖x i‖ ^ p < 1} =
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : forall x : ι -> Complex, 0 <= ∑ i, ‖x i‖ ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (norm_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι -> Complex) : ‖toLp (.ofReal p) x‖ = (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 <= ENNReal.ofReal p) := fact_iff.mpr (ENNReal.ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι -> Complex)‖ = 0 := norm_zero
  have eq_zero (x : ι -> Complex) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι -> Complex => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι -> Complex => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : Real) (x : ι -> Complex) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => Complex)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm] at eq_zero nm_zero nm_neg nm_add nm_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert!
    measure_lt_one_eq_integral_div_gamma (volume : Measure (ι -> Complex)) (g := fun x =>
      (∑ i, ‖x i‖ ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp (fun r x => nm_smul r x)
      (by linarith : 0 < p) using 4
  · rw [rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg (norm_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel₀ _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [integral_fintype_prod_volume_eq_pow fun x : Complex => Real.exp (- ‖x‖ ^ p)]; rw [Complex.integral_exp_neg_rpow hp]
  · rw [finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat, Fintype.card, mul_comm]

/--
theorem `Complex.volume_sum_rpow_lt` / 定理 `Complex.volume_sum_rpow_lt`

English:
theorem Complex.volume_sum_rpow_lt
  given: [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real)
  proof: by
  have h₁ (x : ι -> Complex) : 0 <= ∑ i, ‖x i‖ ^ p := by positivity
  have h₂ : forall x : ι -> Complex, 0 <= (∑ i, ‖x i‖ ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      ref

中文:
定理 复形.volume_sum_rpow_lt
  条件: [非空 ι] {p : 实数} (hp : 1 <= p) (r : 实数)
  证明: by
  have h₁ (x : ι -> Complex) : 0 <= ∑ i, ‖x i‖ ^ p := by positivity
  have h₂ : forall x : ι -> Complex, 0 <= (∑ i, ‖x i‖ ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      ref

Depends on / 依赖: Fin.pos, Set.mem_ofPred.mp, hx.elim, le_or_gt, lt_of_lt_of_le, measure_empty, mem_ofPred, not_le, not_le.mpr, rpow_nonneg, zero_eq_ofReal, zero_eq_ofReal.mpr, zero_mul, zero_pow
-/
theorem Complex.volume_sum_rpow_lt [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real) :
    volume {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = (.ofReal r) ^ (2 * card ι) *
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ (x : ι -> Complex) : 0 <= ∑ i, ‖x i‖ ^ p := by positivity
  have h₂ : forall x : ι -> Complex, 0 <= (∑ i, ‖x i‖ ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact not_le.mpr (lt_of_lt_of_le (Set.mem_ofPred.mp hx) hr) (h₂ x)
    rw [this]; rw [measure_empty]; rw [← zero_eq_ofReal.mpr hr]; rw [zero_pow Fin.pos'.ne']; rw [zero_mul]
  · rw [← Complex.volume_sum_rpow_lt_one _ hp, ← ENNReal.ofReal_pow (le_of_lt hr)]
    convert! addHaar_smul_of_nonneg volume (le_of_lt hr) {x : ι -> Complex | ∑ i, ‖x i‖ ^ p < 1} using 2
    · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_ofPred_eq, Pi.smul_apply,
        norm_smul, mul_rpow (norm_nonneg _) (norm_nonneg _), Real.norm_eq_abs, abs_inv, inv_rpow
        (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr), inv_mul_lt_iff₀
        (rpow_pos_of_pos hr _), mul_one, ← rpow_lt_rpow_iff (rpow_nonneg (h₁ _) _)
        (le_of_lt hr) (by linarith : 0 < p), ← rpow_mul (h₁ _), div_mul_cancel₀ _
        (ne_of_gt (by linarith) : p != 0), Real.rpow_one]
    · simp_rw [finrank_pi_fintype Real, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
        mul_comm, Fintype.card]

/--
theorem `Complex.volume_sum_rpow_le` / 定理 `Complex.volume_sum_rpow_le`

English:
theorem Complex.volume_sum_rpow_le
  given: [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real)
  proof: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι -> Complex) : ‖toLp (.ofReal p) x‖ = (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
   

中文:
定理 复形.volume_sum_rpow_le
  条件: [非空 ι] {p : 实数} (hp : 1 <= p) (r : 实数)
  证明: by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι -> Complex) : ‖toLp (.ofReal p) x‖ = (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
   

Depends on / 依赖: ENNReal, ENNReal.ofReal, le_of_lt, ofReal, toReal, toReal_ofReal
-/
theorem Complex.volume_sum_rpow_le [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real) :
    volume {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) <= r} = (.ofReal r) ^ (2 * card ι) *
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι -> Complex) : ‖toLp (.ofReal p) x‖ = (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 <= ENNReal.ofReal p) := fact_iff.mpr (ENNReal.ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι -> Complex)‖ = 0 := norm_zero
  have eq_zero (x : ι -> Complex) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι -> Complex => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι -> Complex => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : Real) (x : ι -> Complex) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => Complex)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm] at eq_zero nm_zero nm_neg nm_add nm_smul
  rw [measure_le_eq_lt _ nm_zero (fun x => nm_neg x) (fun x y => nm_add x y) (eq_zero _).mp
    (fun r x => nm_smul r x)]; rw [Complex.volume_sum_rpow_lt _ hp]

end LpSpace

namespace EuclideanSpace

variable (ι : Type*) [Nonempty ι] [Fintype ι]

open Fintype Real MeasureTheory MeasureTheory.Measure ENNReal

/--
theorem `volume_ball` / 定理 `volume_ball`

English:
theorem volume_ball
  given: (x : EuclideanSpace Real ι) (r : Real)
  proof: by
  obtain hr | hr := le_total r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow card_ne_zero,
      zero_mul]
  · suffices volume (Metric.ball (0 : EuclideanSpace Real ι) 1) =
        .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) by
      rw [Measure.addHaa

中文:
定理 volume_ball
  条件: (x : EuclideanSpace 实数 ι) (r : 实数)
  证明: by
  obtain hr | hr := le_total r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow card_ne_zero,
      zero_mul]
  · suffices volume (Metric.ball (0 : EuclideanSpace Real ι) 1) =
        .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) by
      rw [Measure.addHaa

Depends on / 依赖: EuclideanSpace, Measure, Measure.addHaar_ball, Metric, Metric.ball, Metric.ball_eq_empty.mpr, PiLp.volume_preserving_toLp, Set.preimage, addHaar_ball, ball_eq_empty, ball_zero_eq, card_ne_zero, finrank_euclideanSpace, le_total, measurableSet_ball, measurableSet_ball.nullMeasurableSet, measure_empty, measure_preimage, nullMeasurableSet, ofReal
-/
theorem volume_ball (x : EuclideanSpace Real ι) (r : Real) :
    volume (Metric.ball x r) = (.ofReal r) ^ card ι *
      .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) := by
  obtain hr | hr := le_total r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow card_ne_zero,
      zero_mul]
  · suffices volume (Metric.ball (0 : EuclideanSpace Real ι) 1) =
        .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) by
      rw [Measure.addHaar_ball _ _ hr]; rw [this]; rw [ofReal_pow hr]; rw [finrank_euclideanSpace]
    rw [← (PiLp.volume_preserving_toLp ι).measure_preimage
      measurableSet_ball.nullMeasurableSet]
    simp only [Set.preimage, ball_zero_eq _ zero_le_one, one_pow, Set.mem_ofPred_eq]
    convert! volume_sum_rpow_lt_one ι one_le_two using 4
    · simp [sq_abs]
    · rw [Gamma_add_one (by simp), Gamma_one_half_eq, ← mul_assoc, mul_div_cancel₀ _
        two_ne_zero, one_mul]

/--
theorem `volume_closedBall` / 定理 `volume_closedBall`

English:
theorem volume_closedBall
  given: (x : EuclideanSpace Real ι) (r : Real)
  proof: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [EuclideanSpace.volume_ball]

中文:
定理 volume_closedBall
  条件: (x : EuclideanSpace 实数 ι) (r : 实数)
  证明: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [EuclideanSpace.volume_ball]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.volume_ball, addHaar_closedBall_eq_addHaar_ball, volume_ball
-/
theorem volume_closedBall (x : EuclideanSpace Real ι) (r : Real) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ card ι *
      .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [EuclideanSpace.volume_ball]

end EuclideanSpace

namespace InnerProductSpace

open scoped Nat
open MeasureTheory MeasureTheory.Measure ENNReal Real Module Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

section Nontrivial

variable [Nontrivial E]

/--
theorem `volume_ball` / 定理 `volume_ball`

English:
theorem volume_ball
  given: (x : E) (r : Real)
  proof: by
  rw [← ((stdOrthonormalBasis Real E).measurePreserving_repr_symm).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  have : Nonempty (Fin (finrank Real E)) := Fin.pos_iff_nonempty.mp finrank_pos
  have := EuclideanSpace.volume_ball (Fin (finrank Real E)) ((stdOrthonormalBasis Real E)

中文:
定理 volume_ball
  条件: (x : E) (r : 实数)
  证明: by
  rw [← ((stdOrthonormalBasis Real E).measurePreserving_repr_symm).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  have : Nonempty (Fin (finrank Real E)) := Fin.pos_iff_nonempty.mp finrank_pos
  have := EuclideanSpace.volume_ball (Fin (finrank Real E)) ((stdOrthonormalBasis Real E)

Depends on / 依赖: EuclideanSpace, EuclideanSpace.volume_ball, Fin.pos_iff_nonempty.mp, Fintype, Fintype.card_fin, LinearIsometryEquiv, LinearIsometryEquiv.preimage_ball, LinearIsometryEquiv.symm_symm, Nonempty, card_fin, convert, finrank, finrank_pos, measurableSet_ball, measurableSet_ball.nullMeasurableSet, measurePreserving_repr_symm, measure_preimage, nullMeasurableSet, pos_iff_nonempty, preimage_ball
-/
theorem volume_ball (x : E) (r : Real) :
    volume (Metric.ball x r) = (.ofReal r) ^ finrank Real E *
      .ofReal (√π ^ finrank Real E / Gamma (finrank Real E / 2 + 1)) := by
  rw [← ((stdOrthonormalBasis Real E).measurePreserving_repr_symm).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  have : Nonempty (Fin (finrank Real E)) := Fin.pos_iff_nonempty.mp finrank_pos
  have := EuclideanSpace.volume_ball (Fin (finrank Real E)) ((stdOrthonormalBasis Real E).repr x) r
  simp_rw [Fintype.card_fin] at this
  convert! this
  simp only [LinearIsometryEquiv.preimage_ball, LinearIsometryEquiv.symm_symm]

/--
theorem `volume_closedBall` / 定理 `volume_closedBall`

English:
theorem volume_closedBall
  given: (x : E) (r : Real)
  proof: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [InnerProductSpace.volume_ball _]

中文:
定理 volume_closedBall
  条件: (x : E) (r : 实数)
  证明: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [InnerProductSpace.volume_ball _]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.volume_ball, addHaar_closedBall_eq_addHaar_ball, volume_ball
-/
theorem volume_closedBall (x : E) (r : Real) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ finrank Real E *
      .ofReal (√π ^ finrank Real E / Gamma (finrank Real E / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [InnerProductSpace.volume_ball _]

/--
lemma `volume_ball_of_dim_even` / 引理 `volume_ball_of_dim_even`

English:
lemma volume_ball_of_dim_even
  given: {k : Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real)
  proof: by
  rw [volume_ball]; rw [hk]; rw [pow_mul]; rw [pow_mul]; rw [sq_sqrt pi_nonneg]
  congr
  simp [Gamma_nat_eq_factorial]

中文:
引理 volume_ball_of_dim_even
  条件: {k : 自然数} (hk : finrank 实数 E = 2 * k) (x : E) (r : 实数)
  证明: by
  rw [volume_ball]; rw [hk]; rw [pow_mul]; rw [pow_mul]; rw [sq_sqrt pi_nonneg]
  congr
  simp [Gamma_nat_eq_factorial]

Depends on / 依赖: Gamma_nat_eq_factorial, pi_nonneg, pow_mul, sq_sqrt, volume_ball
-/
lemma volume_ball_of_dim_even {k : Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real) :
    volume (ball x r) = .ofReal r ^ finrank Real E * .ofReal (π ^ k / (k : Nat)!) := by
  rw [volume_ball]; rw [hk]; rw [pow_mul]; rw [pow_mul]; rw [sq_sqrt pi_nonneg]
  congr
  simp [Gamma_nat_eq_factorial]

/--
lemma `volume_closedBall_of_dim_even` / 引理 `volume_closedBall_of_dim_even`

English:
lemma volume_closedBall_of_dim_even
  given: {k : Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real)
  proof: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_of_dim_even hk x]

中文:
引理 volume_closedBall_of_dim_even
  条件: {k : 自然数} (hk : finrank 实数 E = 2 * k) (x : E) (r : 实数)
  证明: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_of_dim_even hk x]

Depends on / 依赖: addHaar_closedBall_eq_addHaar_ball, volume_ball_of_dim_even
-/
lemma volume_closedBall_of_dim_even {k : Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real) :
    volume (closedBall x r) = .ofReal r ^ finrank Real E * .ofReal (π ^ k / (k : Nat)!) := by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_of_dim_even hk x]

end Nontrivial

/--
lemma `volume_ball_of_dim_odd` / 引理 `volume_ball_of_dim_odd`

English:
lemma volume_ball_of_dim_odd
  given: {k : Nat} (hk : finrank Real E = 2 * k + 1) (x : E) (r : Real)
  proof: by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real) (hk ▸ (2 * k).succ_pos)
  rw [volume_ball]; rw [hk]; rw [pow_succ (√π)]; rw [pow_mul]; rw [sq_sqrt pi_nonneg]; rw [mul_div_assoc]; rw [mul_div_assoc]
  congr 3
  suffices √π / (↑(2 * k + 1)‼ * √π / 2 ^ (k + 1)) = 2 ^ (k + 1) / 

中文:
引理 volume_ball_of_dim_odd
  条件: {k : 自然数} (hk : finrank 实数 E = 2 * k + 1) (x : E) (r : 实数)
  证明: by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real) (hk ▸ (2 * k).succ_pos)
  rw [volume_ball]; rw [hk]; rw [pow_succ (√π)]; rw [pow_mul]; rw [sq_sqrt pi_nonneg]; rw [mul_div_assoc]; rw [mul_div_assoc]
  congr 3
  suffices √π / (↑(2 * k + 1)‼ * √π / 2 ^ (k + 1)) = 2 ^ (k + 1) / 

Depends on / 依赖: Gamma_nat_add_one_add_half, Module, Module.nontrivial_of_finrank_pos, Nontrivial, add_div, add_right_comm, mul_div_assoc, nontrivial_of_finrank_pos, one_div, pi_nonneg, pow_mul, pow_succ, sq_sqrt, succ_pos, volume_ball
-/
lemma volume_ball_of_dim_odd {k : Nat} (hk : finrank Real E = 2 * k + 1) (x : E) (r : Real) :
    volume (ball x r) =
      .ofReal r ^ finrank Real E * .ofReal (π ^ k * 2 ^ (k + 1) / (finrank Real E : Nat)‼) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real) (hk ▸ (2 * k).succ_pos)
  rw [volume_ball]; rw [hk]; rw [pow_succ (√π)]; rw [pow_mul]; rw [sq_sqrt pi_nonneg]; rw [mul_div_assoc]; rw [mul_div_assoc]
  congr 3
  suffices √π / (↑(2 * k + 1)‼ * √π / 2 ^ (k + 1)) = 2 ^ (k + 1) / ↑(2 * k + 1)‼ by
    simpa [add_div, add_right_comm, -one_div, Gamma_nat_add_one_add_half]
  field

/--
lemma `volume_closedBall_of_dim_odd` / 引理 `volume_closedBall_of_dim_odd`

English:
lemma volume_closedBall_of_dim_odd
  given: {k : Nat} (hk : finrank Real E = 2 * k + 1) (x : E) (r : Real)
  proof: by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real) (hk ▸ (2 * k).succ_pos)
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_of_dim_odd hk x r]

中文:
引理 volume_closedBall_of_dim_odd
  条件: {k : 自然数} (hk : finrank 实数 E = 2 * k + 1) (x : E) (r : 实数)
  证明: by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real) (hk ▸ (2 * k).succ_pos)
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_of_dim_odd hk x r]

Depends on / 依赖: Module, Module.nontrivial_of_finrank_pos, Nontrivial, addHaar_closedBall_eq_addHaar_ball, nontrivial_of_finrank_pos, succ_pos, volume_ball_of_dim_odd
-/
lemma volume_closedBall_of_dim_odd {k : Nat} (hk : finrank Real E = 2 * k + 1) (x : E) (r : Real) :
    volume (closedBall x r) =
      .ofReal r ^ finrank Real E * .ofReal (π ^ k * 2 ^ (k + 1) / (finrank Real E : Nat)‼) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real) (hk ▸ (2 * k).succ_pos)
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_of_dim_odd hk x r]

end InnerProductSpace

namespace EuclideanSpace

open Real MeasureTheory MeasureTheory.Measure ENNReal Metric

@[simp]
/--
lemma `volume_ball_fin_two` / 引理 `volume_ball_fin_two`

English:
lemma volume_ball_fin_two
  given: (x : EuclideanSpace Real (Fin 2)) (r : Real)
  proof: by
  norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) x]

@[simp]

中文:
引理 volume_ball_fin_two
  条件: (x : EuclideanSpace 实数 (有限集 2)) (r : 实数)
  证明: by
  norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) x]

@[simp]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.volume_ball_of_dim_even, volume_ball_of_dim_even
-/
lemma volume_ball_fin_two (x : EuclideanSpace Real (Fin 2)) (r : Real) :
    volume (ball x r) = .ofReal r ^ 2 * .ofReal π := by
  norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) x]

@[simp]
/--
lemma `volume_closedBall_fin_two` / 引理 `volume_closedBall_fin_two`

English:
lemma volume_closedBall_fin_two
  given: (x : EuclideanSpace Real (Fin 2)) (r : Real)
  proof: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_fin_two x r]

@[simp]

中文:
引理 volume_closedBall_fin_two
  条件: (x : EuclideanSpace 实数 (有限集 2)) (r : 实数)
  证明: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_fin_two x r]

@[simp]

Depends on / 依赖: addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_two
-/
lemma volume_closedBall_fin_two (x : EuclideanSpace Real (Fin 2)) (r : Real) :
    volume (closedBall x r) = .ofReal r ^ 2 * .ofReal π := by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_fin_two x r]

@[simp]
/--
lemma `volume_ball_fin_three` / 引理 `volume_ball_fin_three`

English:
lemma volume_ball_fin_three
  given: (x : EuclideanSpace Real (Fin 3)) (r : Real)
  proof: by
  norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp) x]

@[simp]

中文:
引理 volume_ball_fin_three
  条件: (x : EuclideanSpace 实数 (有限集 3)) (r : 实数)
  证明: by
  norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp) x]

@[simp]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.volume_ball_of_dim_odd, volume_ball_of_dim_odd
-/
lemma volume_ball_fin_three (x : EuclideanSpace Real (Fin 3)) (r : Real) :
    volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp) x]

@[simp]
/--
lemma `volume_closedBall_fin_three` / 引理 `volume_closedBall_fin_three`

English:
lemma volume_closedBall_fin_three
  given: (x : EuclideanSpace Real (Fin 3)) (r : Real)
  proof: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_fin_three x]

中文:
引理 volume_closedBall_fin_three
  条件: (x : EuclideanSpace 实数 (有限集 3)) (r : 实数)
  证明: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_fin_three x]

Depends on / 依赖: addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_three
-/
lemma volume_closedBall_fin_three (x : EuclideanSpace Real (Fin 3)) (r : Real) :
    volume (closedBall x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [volume_ball_fin_three x]

end EuclideanSpace

section Complex

open MeasureTheory MeasureTheory.Measure ENNReal

@[simp]
/--
theorem `Complex.volume_ball` / 定理 `Complex.volume_ball`

English:
theorem Complex.volume_ball
  given: (a : Complex) (r : Real)
  proof: by
  simp [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) a,
    ← NNReal.coe_real_pi, ofReal_coe_nnreal]

@[simp]

中文:
定理 复形.volume_ball
  条件: (a : 复形) (r : 实数)
  证明: by
  simp [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) a,
    ← NNReal.coe_real_pi, ofReal_coe_nnreal]

@[simp]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.volume_ball_of_dim_even, NNReal, NNReal.coe_real_pi, coe_real_pi, ofReal_coe_nnreal, volume_ball_of_dim_even
-/
theorem Complex.volume_ball (a : Complex) (r : Real) :
    volume (Metric.ball a r) = .ofReal r ^ 2 * NNReal.pi := by
  simp [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) a,
    ← NNReal.coe_real_pi, ofReal_coe_nnreal]

@[simp]
/--
theorem `Complex.volume_closedBall` / 定理 `Complex.volume_closedBall`

English:
theorem Complex.volume_closedBall
  given: (a : Complex) (r : Real)
  proof: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [Complex.volume_ball]

中文:
定理 复形.volume_closedBall
  条件: (a : 复形) (r : 实数)
  证明: by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [Complex.volume_ball]

Depends on / 依赖: Complex.volume_ball, addHaar_closedBall_eq_addHaar_ball, volume_ball
-/
theorem Complex.volume_closedBall (a : Complex) (r : Real) :
    volume (Metric.closedBall a r) = .ofReal r ^ 2 * NNReal.pi := by
  rw [addHaar_closedBall_eq_addHaar_ball]; rw [Complex.volume_ball]

end Complex
