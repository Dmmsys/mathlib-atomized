/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Basic properties of Haar measures on real vector spaces

-/

public section

noncomputable section

open Function Filter Inv MeasureTheory.Measure Module Set TopologicalSpace
open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

/-- The instance `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` applies in particular
to show that an additive Haar measure on a nontrivial finite-dimensional real vector space has no
atom. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [Nontrivial E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] :
    NullSingletonClass μ := by
  infer_instance

section LinearEquiv

variable {𝕜 G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [NontriviallyNormedField 𝕜]
  [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [Module 𝕜 G] [Module 𝕜 H] (μ : Measure G)
  [IsAddHaarMeasure μ] [BorelSpace G] [BorelSpace H]
  [CompleteSpace 𝕜] [T2Space G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]
  [ContinuousSMul 𝕜 H] [T2Space H]

/--
Instance `MapLinearEquiv.isAddHaarMeasure` / 实例 `MapLinearEquiv.isAddHaarMeasure`

English:
instance MapLinearEquiv.isAddHaarMeasure
  signature: (e : G ≃ₗ[𝕜] H)
  body: e.toContinuousLinearEquiv.isAddHaarMeasure_map _

中文:
实例 MapLinearEquiv.isAddHaarMeasure
  签名: (e : G ≃ₗ[𝕜] H)
  定义体: e.toContinuousLinearEquiv.isAddHaarMeasure_map _

Depends on / 依赖: e.toContinuousLinearEquiv.isAddHaarMeasure_map, isAddHaarMeasure_map, toContinuousLinearEquiv
-/
instance MapLinearEquiv.isAddHaarMeasure (e : G ≃ₗ[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  e.toContinuousLinearEquiv.isAddHaarMeasure_map _

end LinearEquiv

section SeminormedGroup
variable {G H : Type*} [MeasurableSpace G] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G]
  [MeasurableSpace H] [SeminormedGroup H] [OpensMeasurableSpace H]

-- TODO: This could be streamlined by proving that inner regular measures always exist
open Metric Bornology in
@[to_additive]
/--
lemma `_root_.MonoidHom.exists_nhds_isBounded` / 引理 `_root_.MonoidHom.exists_nhds_isBounded`

English:
lemma _root_.MonoidHom.exists_nhds_isBounded
  given: (f : G ->* H) (hf : Measurable f) (x : G)
  proof: by
  let K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨n, hn⟩ : exists n : Nat, 0 < haar (interior K inter f ⁻¹' ball 1 n) := by
    by_contra!
    simp_rw [nonpos_iff_eq_zero, ← measure_iUnion_null_iff, ← inter_iUnion, ← preimage_iUnion,
      iUnion_ball_nat, preimage_univ, inter_univ]

中文:
引理 _root_.幺半群态射.存在_nhds_isBounded
  条件: (f : G ->* H) (hf : 可测 f) (x : G)
  证明: by
  let K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨n, hn⟩ : exists n : Nat, 0 < haar (interior K inter f ⁻¹' ball 1 n) := by
    by_contra!
    simp_rw [nonpos_iff_eq_zero, ← measure_iUnion_null_iff, ← inter_iUnion, ← preimage_iUnion,
      iUnion_ball_nat, preimage_univ, inter_univ]

Depends on / 依赖: Classical, Classical.arbitrary, K.interior_nonempty, PositiveCompacts, arbitrary, div_mem_nhds_one_of_haar_pos_ne_top, iUnion_ball_nat, inter_iUnion, inter_univ, interior, interior_nonempty, isOpen_interior, isOpen_interior.measurableSe, isOpen_interior.measure_pos, measurableSe, measure_iUnion_null_iff, measure_pos, mul_one, nonpos_iff_eq_zero, not_gt
-/
lemma _root_.MonoidHom.exists_nhds_isBounded (f : G ->* H) (hf : Measurable f) (x : G) :
    exists s in 𝓝 x, IsBounded (f '' s) := by
  let K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨n, hn⟩ : exists n : Nat, 0 < haar (interior K inter f ⁻¹' ball 1 n) := by
    by_contra!
    simp_rw [nonpos_iff_eq_zero, ← measure_iUnion_null_iff, ← inter_iUnion, ← preimage_iUnion,
      iUnion_ball_nat, preimage_univ, inter_univ] at this
exact this.not_gt isOpen_interior.measure_pos _ K.interior_nonempty
  rw [← mul_one x]; rw [← smul_eq_mul]
refine ⟨_, smul_mem_nhds_smul _ div_mem_nhds_one_of_haar_pos_ne_top haar _
(isOpen_interior.measurableSet.inter <| hf measurableSet_ball) hn
      mt (measure_mono_top <| inter_subset_left.trans interior_subset) K.isCompact.measure_ne_top,
    ?_⟩
  have : Bornology.IsBounded (f '' (interior K inter f ⁻¹' ball 1 n)) :=
isBounded_ball.subset (image_mono inter_subset_right).trans image_preimage_subset _ _
  rw [image_smul_distrib]; rw [image_div]
  exact (this.div this).smul _

end SeminormedGroup

/--
lemma `AddMonoidHom.continuous_of_measurable` / 引理 `AddMonoidHom.continuous_of_measurable`

English:
lemma AddMonoidHom.continuous_of_measurable
  statement: {G H : Type*}
  proof: let ⟨_s, hs, hbdd⟩ := f.exists_nhds_isBounded hf 0; f.continuous_of_isBounded_nhds_zero hs hbdd

中文:
引理 加法幺半群态射.continuous_of_measurable
  结论: {G H : 类型}
  证明: let ⟨_s, hs, hbdd⟩ := f.exists_nhds_isBounded hf 0; f.continuous_of_isBounded_nhds_zero hs hbdd

Depends on / 依赖: continuous_of_isBounded_nhds_zero, exists_nhds_isBounded, f.continuous_of_isBounded_nhds_zero, f.exists_nhds_isBounded
-/
lemma AddMonoidHom.continuous_of_measurable {G H : Type*}
    [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SeminormedAddCommGroup H] [MeasurableSpace H] [OpensMeasurableSpace H] [NormedSpace Real H]
    (f : G ->+ H) (hf : Measurable f) : Continuous f :=
  let ⟨_s, hs, hbdd⟩ := f.exists_nhds_isBounded hf 0; f.continuous_of_isBounded_nhds_zero hs hbdd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional Real E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace Real F]

/--
theorem `integral_comp_smul` / 定理 `integral_comp_smul`

English:
theorem integral_comp_smul
  given: (f : E -> F) (R : Real)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank Real E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun _ => f 0 := by ext 

中文:
定理 integral_comp_smul
  条件: (f : E -> F) (R : 实数)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank Real E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun _ => f 0 := by ext 

Depends on / 依赖: CompleteSpace, Nat.eq_zero_or_pos, Nontrivial, Subsingleton, Subsingleton.elim, abs_one, conv_rhs, eq_or_ne, eq_zero_or_pos, finrank, finrank_pos_iff, finrank_zero_iff, hE.ne, integral, integral_const, inv_one, measure_univ_of_isAddLeftInvaria, one_smul, pow_zero, zero_pow
-/
theorem integral_comp_smul (f : E -> F) (R : Real) :
    ∫ x, f (R • x) ∂μ = |(R ^ finrank Real E)⁻¹| • ∫ x, f x ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank Real E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun _ => f 0 := by ext x; rw [Subsingleton.elim x 0]
      conv_rhs => rw [this]
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const]
    · have : Nontrivial E := finrank_pos_iff.1 hE
      simp [zero_pow hE.ne', measure_univ_of_isAddLeftInvariant, measureReal_def]
  · calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂Measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hR).unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank Real E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]

/--
theorem `integral_comp_smul_of_nonneg` / 定理 `integral_comp_smul_of_nonneg`

English:
theorem integral_comp_smul_of_nonneg
  given: (f : E -> F) (R : Real) {hR : 0 <= R}
  proof: by
  rw [integral_comp_smul μ f R]; rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]

中文:
定理 integral_comp_smul_of_nonneg
  条件: (f : E -> F) (R : 实数) {hR : 0 <= R}
  证明: by
  rw [integral_comp_smul μ f R]; rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]

Depends on / 依赖: abs_of_nonneg, integral_comp_smul, inv_nonneg, pow_nonneg
-/
theorem integral_comp_smul_of_nonneg (f : E -> F) (R : Real) {hR : 0 <= R} :
    ∫ x, f (R • x) ∂μ = (R ^ finrank Real E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R]; rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]

/--
theorem `integral_comp_inv_smul` / 定理 `integral_comp_inv_smul`

English:
theorem integral_comp_inv_smul
  given: (f : E -> F) (R : Real)
  proof: by
  rw [integral_comp_smul μ f R⁻¹]; rw [inv_pow]; rw [inv_inv]

中文:
定理 integral_comp_inv_smul
  条件: (f : E -> F) (R : 实数)
  证明: by
  rw [integral_comp_smul μ f R⁻¹]; rw [inv_pow]; rw [inv_inv]

Depends on / 依赖: integral_comp_smul, inv_inv, inv_pow
-/
theorem integral_comp_inv_smul (f : E -> F) (R : Real) :
    ∫ x, f (R⁻¹ • x) ∂μ = |R ^ finrank Real E| • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R⁻¹]; rw [inv_pow]; rw [inv_inv]

/--
theorem `integral_comp_inv_smul_of_nonneg` / 定理 `integral_comp_inv_smul_of_nonneg`

English:
theorem integral_comp_inv_smul_of_nonneg
  given: (f : E -> F) {R : Real} (hR : 0 <= R)
  proof: by
  rw [integral_comp_inv_smul μ f R]; rw [abs_of_nonneg (pow_nonneg hR _)]

中文:
定理 integral_comp_inv_smul_of_nonneg
  条件: (f : E -> F) {R : 实数} (hR : 0 <= R)
  证明: by
  rw [integral_comp_inv_smul μ f R]; rw [abs_of_nonneg (pow_nonneg hR _)]

Depends on / 依赖: abs_of_nonneg, integral_comp_inv_smul, pow_nonneg
-/
theorem integral_comp_inv_smul_of_nonneg (f : E -> F) {R : Real} (hR : 0 <= R) :
    ∫ x, f (R⁻¹ • x) ∂μ = R ^ finrank Real E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R]; rw [abs_of_nonneg (pow_nonneg hR _)]

/--
theorem `setIntegral_comp_smul` / 定理 `setIntegral_comp_smul`

English:
theorem setIntegral_comp_smul
  given: (f : E -> F) {R : Real} (s : Set E) (hR : R != 0)
  proof: by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 R hR)).toMeasurableEquiv
  calc
  ∫ x in s, f (R • x) ∂μ
    = ∫ x in e ⁻¹' e.symm ⁻¹' s, f (e x) ∂μ := by simp [← preimage_comp]; rfl
  _ = ∫ y in e.symm ⁻¹' s, f y ∂map (fun x => R • x) μ := (setIntegral_map_equiv _ _ _).symm
  _ = |(R ^ finrank R

中文:
定理 set整数egral_comp_smul
  条件: (f : E -> F) {R : 实数} (s : 集合 E) (hR : R != 0)
  证明: by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 R hR)).toMeasurableEquiv
  calc
  ∫ x in s, f (R • x) ∂μ
    = ∫ x in e ⁻¹' e.symm ⁻¹' s, f (e x) ∂μ := by simp [← preimage_comp]; rfl
  _ = ∫ y in e.symm ⁻¹' s, f y ∂map (fun x => R • x) μ := (setIntegral_map_equiv _ _ _).symm
  _ = |(R ^ finrank R

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Homeomorph, Homeomorph.smul, Units.mk0, abs_nonneg, e.symm, finrank, integral_smul_measure, map_addHaar_smul, mem_s, preimage_comp, setIntegral_map_equiv, toMeasurableEquiv, toReal_ofReal
-/
theorem setIntegral_comp_smul (f : E -> F) {R : Real} (s : Set E) (hR : R != 0) :
    ∫ x in s, f (R • x) ∂μ = |(R ^ finrank Real E)⁻¹| • ∫ x in R • s, f x ∂μ := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 R hR)).toMeasurableEquiv
  calc
  ∫ x in s, f (R • x) ∂μ
    = ∫ x in e ⁻¹' e.symm ⁻¹' s, f (e x) ∂μ := by simp [← preimage_comp]; rfl
  _ = ∫ y in e.symm ⁻¹' s, f y ∂map (fun x => R • x) μ := (setIntegral_map_equiv _ _ _).symm
  _ = |(R ^ finrank Real E)⁻¹| • ∫ y in e.symm ⁻¹' s, f y ∂μ := by
    simp [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]
  _ = |(R ^ finrank Real E)⁻¹| • ∫ x in R • s, f x ∂μ := by
    congr 3
    ext y
    rw [mem_smul_set_iff_inv_smul_mem₀ hR]
    rfl

/--
theorem `setIntegral_comp_smul_of_pos` / 定理 `setIntegral_comp_smul_of_pos`

English:
theorem setIntegral_comp_smul_of_pos
  given: (f : E -> F) {R : Real} (s : Set E) (hR : 0 < R)
  proof: by
  rw [setIntegral_comp_smul μ f s hR.ne']; rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]

中文:
定理 set整数egral_comp_smul_of_pos
  条件: (f : E -> F) {R : 实数} (s : 集合 E) (hR : 0 < R)
  证明: by
  rw [setIntegral_comp_smul μ f s hR.ne']; rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]

Depends on / 依赖: abs_of_nonneg, hR.le, hR.ne, inv_nonneg, pow_nonneg, setIntegral_comp_smul
-/
theorem setIntegral_comp_smul_of_pos (f : E -> F) {R : Real} (s : Set E) (hR : 0 < R) :
    ∫ x in s, f (R • x) ∂μ = (R ^ finrank Real E)⁻¹ • ∫ x in R • s, f x ∂μ := by
  rw [setIntegral_comp_smul μ f s hR.ne']; rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]

/--
theorem `integral_comp_mul_left` / 定理 `integral_comp_mul_left`

English:
theorem integral_comp_mul_left
  given: (g : Real -> F) (a : Real)
  proof: by
  simp_rw [← smul_eq_mul, Measure.integral_comp_smul, Module.finrank_self, pow_one]

中文:
定理 integral_comp_mul_left
  条件: (g : 实数 -> F) (a : 实数)
  证明: by
  simp_rw [← smul_eq_mul, Measure.integral_comp_smul, Module.finrank_self, pow_one]

Depends on / 依赖: Measure, Measure.integral_comp_smul, Module, Module.finrank_self, finrank_self, integral_comp_smul, pow_one, simp_rw, smul_eq_mul
-/
theorem integral_comp_mul_left (g : Real -> F) (a : Real) :
    (∫ x : Real, g (a * x)) = |a⁻¹| • ∫ y : Real, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_smul, Module.finrank_self, pow_one]

/--
theorem `integral_comp_inv_mul_left` / 定理 `integral_comp_inv_mul_left`

English:
theorem integral_comp_inv_mul_left
  given: (g : Real -> F) (a : Real)
  proof: by
  simp_rw [← smul_eq_mul, Measure.integral_comp_inv_smul, Module.finrank_self, pow_one]

中文:
定理 integral_comp_inv_mul_left
  条件: (g : 实数 -> F) (a : 实数)
  证明: by
  simp_rw [← smul_eq_mul, Measure.integral_comp_inv_smul, Module.finrank_self, pow_one]

Depends on / 依赖: Measure, Measure.integral_comp_inv_smul, Module, Module.finrank_self, finrank_self, integral_comp_inv_smul, pow_one, simp_rw, smul_eq_mul
-/
theorem integral_comp_inv_mul_left (g : Real -> F) (a : Real) :
    (∫ x : Real, g (a⁻¹ * x)) = |a| • ∫ y : Real, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_inv_smul, Module.finrank_self, pow_one]

/--
theorem `integral_comp_mul_right` / 定理 `integral_comp_mul_right`

English:
theorem integral_comp_mul_right
  given: (g : Real -> F) (a : Real)
  proof: by
  simpa only [mul_comm] using integral_comp_mul_left g a

中文:
定理 integral_comp_mul_right
  条件: (g : 实数 -> F) (a : 实数)
  证明: by
  simpa only [mul_comm] using integral_comp_mul_left g a

Depends on / 依赖: integral_comp_mul_left, mul_comm
-/
theorem integral_comp_mul_right (g : Real -> F) (a : Real) :
    (∫ x : Real, g (x * a)) = |a⁻¹| • ∫ y : Real, g y := by
  simpa only [mul_comm] using integral_comp_mul_left g a

/--
theorem `integral_comp_inv_mul_right` / 定理 `integral_comp_inv_mul_right`

English:
theorem integral_comp_inv_mul_right
  given: (g : Real -> F) (a : Real)
  proof: by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a

中文:
定理 integral_comp_inv_mul_right
  条件: (g : 实数 -> F) (a : 实数)
  证明: by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a

Depends on / 依赖: integral_comp_inv_mul_left, mul_comm
-/
theorem integral_comp_inv_mul_right (g : Real -> F) (a : Real) :
    (∫ x : Real, g (x * a⁻¹)) = |a| • ∫ y : Real, g y := by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a

/--
theorem `integral_comp_div` / 定理 `integral_comp_div`

English:
theorem integral_comp_div
  given: (g : Real -> F) (a : Real)
  statement: (∫ x : Real, g (x / a)) = |a| • ∫ y : Real, g y
  proof: integral_comp_inv_mul_right g a

中文:
定理 integral_comp_div
  条件: (g : 实数 -> F) (a : 实数)
  结论: (∫ x : 实数, g (x / a)) = |a| • ∫ y : 实数, g y
  证明: integral_comp_inv_mul_right g a

Depends on / 依赖: integral_comp_inv_mul_right
-/
theorem integral_comp_div (g : Real -> F) (a : Real) : (∫ x : Real, g (x / a)) = |a| • ∫ y : Real, g y :=
  integral_comp_inv_mul_right g a

end Measure

variable {F : Type*} [NormedAddCommGroup F]

/--
theorem `integrable_comp_smul_iff` / 定理 `integrable_comp_smul_iff`

English:
theorem integrable_comp_smul_iff
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  -- reduce to one-way implication
  suffices
    forall {g : E -> F} (_ : Integrable g μ) {S : Real} (_ : S != 0), Integrable (fun x => g (S • x)) μ by
    refine ⟨fun hf => ?_, fun hf => this hf hR⟩
    convert! this hf (inv_ne_zero hR)
    rw [← mul_smul]; rw [mul_inv_cancel₀ hR]; rw [one_smul

中文:
定理 integrable_comp_smul_iff
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  -- reduce to one-way implication
  suffices
    forall {g : E -> F} (_ : Integrable g μ) {S : Real} (_ : S != 0), Integrable (fun x => g (S • x)) μ by
    refine ⟨fun hf => ?_, fun hf => this hf hR⟩
    convert! this hf (inv_ne_zero hR)
    rw [← mul_smul]; rw [mul_inv_cancel₀ hR]; rw [one_smul
-/
theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E -> F) {R : Real} (hR : R != 0) : Integrable (fun x => f (R • x)) μ ↔ Integrable f μ := by
  -- reduce to one-way implication
  suffices
    forall {g : E -> F} (_ : Integrable g μ) {S : Real} (_ : S != 0), Integrable (fun x => g (S • x)) μ by
    refine ⟨fun hf => ?_, fun hf => this hf hR⟩
    convert! this hf (inv_ne_zero hR)
    rw [← mul_smul]; rw [mul_inv_cancel₀ hR]; rw [one_smul]
  -- now prove
  intro g hg S hS
  let t := ((Homeomorph.smul (isUnit_iff_ne_zero.2 hS).unit).toMeasurableEquiv : E ≃ᵐ E)
  refine (integrable_map_equiv t g).mp (?_ : Integrable g (map (S • ·) μ))
  rwa [map_addHaar_smul μ hS, integrable_smul_measure _ ENNReal.ofReal_ne_top]
  simpa only [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos] using inv_ne_zero (pow_ne_zero _ hS)

/--
theorem `Integrable.comp_smul` / 定理 `Integrable.comp_smul`

English:
theorem Integrable.comp_smul
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: (integrable_comp_smul_iff μ f hR).2 hf

中文:
定理 可积.comp_smul
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: (integrable_comp_smul_iff μ f hR).2 hf

Depends on / 依赖: integrable_comp_smul_iff
-/
theorem Integrable.comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] {μ : Measure E} [IsAddHaarMeasure μ]
    {f : E -> F} (hf : Integrable f μ) {R : Real} (hR : R != 0) : Integrable (fun x => f (R • x)) μ :=
  (integrable_comp_smul_iff μ f hR).2 hf

/--
theorem `integrable_comp_mul_left_iff` / 定理 `integrable_comp_mul_left_iff`

English:
theorem integrable_comp_mul_left_iff
  given: (g : Real -> F) {R : Real} (hR : R != 0)
  proof: by
  simpa only [smul_eq_mul] using integrable_comp_smul_iff volume g hR

中文:
定理 integrable_comp_mul_left_iff
  条件: (g : 实数 -> F) {R : 实数} (hR : R != 0)
  证明: by
  simpa only [smul_eq_mul] using integrable_comp_smul_iff volume g hR

Depends on / 依赖: integrable_comp_smul_iff, smul_eq_mul, volume
-/
theorem integrable_comp_mul_left_iff (g : Real -> F) {R : Real} (hR : R != 0) :
    (Integrable fun x => g (R * x)) ↔ Integrable g := by
  simpa only [smul_eq_mul] using integrable_comp_smul_iff volume g hR

/--
theorem `Integrable.comp_mul_left'` / 定理 `Integrable.comp_mul_left'`

English:
theorem Integrable.comp_mul_left'
  given: {g : Real -> F} (hg : Integrable g) {R : Real} (hR : R != 0)
  proof: (integrable_comp_mul_left_iff g hR).2 hg

中文:
定理 可积.comp_mul_left'
  条件: {g : 实数 -> F} (hg : 可积 g) {R : 实数} (hR : R != 0)
  证明: (integrable_comp_mul_left_iff g hR).2 hg

Depends on / 依赖: integrable_comp_mul_left_iff
-/
theorem Integrable.comp_mul_left' {g : Real -> F} (hg : Integrable g) {R : Real} (hR : R != 0) :
    Integrable fun x => g (R * x) :=
  (integrable_comp_mul_left_iff g hR).2 hg

/--
theorem `integrable_comp_mul_right_iff` / 定理 `integrable_comp_mul_right_iff`

English:
theorem integrable_comp_mul_right_iff
  given: (g : Real -> F) {R : Real} (hR : R != 0)
  proof: by
  simpa only [mul_comm] using integrable_comp_mul_left_iff g hR

中文:
定理 integrable_comp_mul_right_iff
  条件: (g : 实数 -> F) {R : 实数} (hR : R != 0)
  证明: by
  simpa only [mul_comm] using integrable_comp_mul_left_iff g hR

Depends on / 依赖: integrable_comp_mul_left_iff, mul_comm
-/
theorem integrable_comp_mul_right_iff (g : Real -> F) {R : Real} (hR : R != 0) :
    (Integrable fun x => g (x * R)) ↔ Integrable g := by
  simpa only [mul_comm] using integrable_comp_mul_left_iff g hR

/--
theorem `Integrable.comp_mul_right'` / 定理 `Integrable.comp_mul_right'`

English:
theorem Integrable.comp_mul_right'
  given: {g : Real -> F} (hg : Integrable g) {R : Real} (hR : R != 0)
  proof: (integrable_comp_mul_right_iff g hR).2 hg

中文:
定理 可积.comp_mul_right'
  条件: {g : 实数 -> F} (hg : 可积 g) {R : 实数} (hR : R != 0)
  证明: (integrable_comp_mul_right_iff g hR).2 hg

Depends on / 依赖: integrable_comp_mul_right_iff
-/
theorem Integrable.comp_mul_right' {g : Real -> F} (hg : Integrable g) {R : Real} (hR : R != 0) :
    Integrable fun x => g (x * R) :=
  (integrable_comp_mul_right_iff g hR).2 hg

/--
theorem `integrable_comp_div_iff` / 定理 `integrable_comp_div_iff`

English:
theorem integrable_comp_div_iff
  given: (g : Real -> F) {R : Real} (hR : R != 0)
  proof: integrable_comp_mul_right_iff g (inv_ne_zero hR)

中文:
定理 integrable_comp_div_iff
  条件: (g : 实数 -> F) {R : 实数} (hR : R != 0)
  证明: integrable_comp_mul_right_iff g (inv_ne_zero hR)

Depends on / 依赖: integrable_comp_mul_right_iff, inv_ne_zero
-/
theorem integrable_comp_div_iff (g : Real -> F) {R : Real} (hR : R != 0) :
    (Integrable fun x => g (x / R)) ↔ Integrable g :=
  integrable_comp_mul_right_iff g (inv_ne_zero hR)

/--
theorem `Integrable.comp_div` / 定理 `Integrable.comp_div`

English:
theorem Integrable.comp_div
  given: {g : Real -> F} (hg : Integrable g) {R : Real} (hR : R != 0)
  proof: (integrable_comp_div_iff g hR).2 hg

中文:
定理 可积.comp_div
  条件: {g : 实数 -> F} (hg : 可积 g) {R : 实数} (hR : R != 0)
  证明: (integrable_comp_div_iff g hR).2 hg

Depends on / 依赖: integrable_comp_div_iff
-/
theorem Integrable.comp_div {g : Real -> F} (hg : Integrable g) {R : Real} (hR : R != 0) :
    Integrable fun x => g (x / R) :=
  (integrable_comp_div_iff g hR).2 hg

section InnerProductSpace

variable {E' F' A : Type*}
variable [NormedAddCommGroup E'] [InnerProductSpace Real E'] [FiniteDimensional Real E']
  [MeasurableSpace E'] [BorelSpace E']
variable [NormedAddCommGroup F'] [InnerProductSpace Real F'] [FiniteDimensional Real F']
  [MeasurableSpace F'] [BorelSpace F']

variable (f : E' ≃ₗᵢ[Real] F')
variable [NormedAddCommGroup A]

/--
theorem `integrable_comp` / 定理 `integrable_comp`

English:
theorem integrable_comp
  given: (g : F' -> A)
  statement: Integrable (g ∘ f) ↔ Integrable g
  proof: f.measurePreserving.integrable_comp_emb f.toMeasurableEquiv.measurableEmbedding

中文:
定理 integrable_comp
  条件: (g : F' -> A)
  结论: 可积 (g ∘ f) ↔ 可积 g
  证明: f.measurePreserving.integrable_comp_emb f.toMeasurableEquiv.measurableEmbedding

Depends on / 依赖: f.measurePreserving.integrable_comp_emb, f.toMeasurableEquiv.measurableEmbedding, integrable_comp_emb, measurableEmbedding, measurePreserving, toMeasurableEquiv
-/
theorem integrable_comp (g : F' -> A) : Integrable (g ∘ f) ↔ Integrable g :=
  f.measurePreserving.integrable_comp_emb f.toMeasurableEquiv.measurableEmbedding

/--
theorem `integral_comp` / 定理 `integral_comp`

English:
theorem integral_comp
  given: [NormedSpace Real A] (g : F' -> A)
  statement: ∫ (x : E'), g (f x) = ∫ (y : F'), g y
  proof: f.measurePreserving.integral_comp' (f := f.toMeasurableEquiv) g

中文:
定理 integral_comp
  条件: [赋范空间 实数 A] (g : F' -> A)
  结论: ∫ (x : E'), g (f x) = ∫ (y : F'), g y
  证明: f.measurePreserving.integral_comp' (f := f.toMeasurableEquiv) g

Depends on / 依赖: f.measurePreserving.integral_comp, f.toMeasurableEquiv, integral_comp, measurePreserving, toMeasurableEquiv
-/
theorem integral_comp [NormedSpace Real A] (g : F' -> A) : ∫ (x : E'), g (f x) = ∫ (y : F'), g y :=
  f.measurePreserving.integral_comp' (f := f.toMeasurableEquiv) g

end InnerProductSpace

end MeasureTheory
