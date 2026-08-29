/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The Mellin transform

We define the Mellin transform of a locally integrable function on `Ioi 0`, and show it is
differentiable in a suitable vertical strip.

## Main statements

- `mellin` : the Mellin transform `∫ (t : ℝ) in Ioi 0, t ^ (s - 1) • f t`,
  where `s` is a complex number.
- `HasMellin`: shorthand asserting that the Mellin transform exists and has a given value
  (analogous to `HasSum`).
- `mellin_differentiableAt_of_isBigO_rpow` : if `f` is `O(x ^ (-a))` at infinity, and
  `O(x ^ (-b))` at 0, then `mellin f` is holomorphic on the domain `b < re s < a`.

-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics TopologicalSpace

open Real

open Complex hiding exp log

open scoped Topology

noncomputable section

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
Definition of `MellinConvergent` / `MellinConvergent` 的定义

English:
definition MellinConvergent
  signature: (f : Real -> E) (s : Complex)
  body: IntegrableOn (fun t : Real => (t : Complex) ^ (s - 1) • f t) (Ioi 0)

中文:
定义 MellinConvergent
  签名: (f : 实数 -> E) (s : Complex)
  定义体: IntegrableOn (fun t : Real => (t : Complex) ^ (s - 1) • f t) (Ioi 0)

Depends on / 依赖: IntegrableOn
-/
def MellinConvergent (f : Real -> E) (s : Complex) : Prop :=
  IntegrableOn (fun t : Real => (t : Complex) ^ (s - 1) • f t) (Ioi 0)

/--
theorem `MellinConvergent.const_smul` / 定理 `MellinConvergent.const_smul`

English:
theorem MellinConvergent.const_smul
  statement: {f : Real -> E} {s : Complex} (hf : MellinConvergent f s) {𝕜 : Type*}
  proof: by
  simpa only [MellinConvergent, smul_comm] using! hf.smul c

中文:
定理 MellinConvergent.const_smul
  结论: {f : 实数 -> E} {s : Complex} (hf : MellinConvergent f s) {𝕜 : 类型}
  证明: by
  simpa only [MellinConvergent, smul_comm] using! hf.smul c

Depends on / 依赖: MellinConvergent, hf.smul, smul_comm
-/
theorem MellinConvergent.const_smul {f : Real -> E} {s : Complex} (hf : MellinConvergent f s) {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass Complex 𝕜 E] (c : 𝕜) :
    MellinConvergent (fun t => c • f t) s := by
  simpa only [MellinConvergent, smul_comm] using! hf.smul c

/--
theorem `MellinConvergent.cpow_smul` / 定理 `MellinConvergent.cpow_smul`

English:
theorem MellinConvergent.cpow_smul
  given: {f : Real -> E} {s a : Complex}
  proof: by
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

nonrec theorem MellinConvergent.div_const {f : Real -> Complex} {s : Complex} (hf : MellinConvergent f s) (a : Complex) :
    MellinConver

中文:
定理 MellinConvergent.cpow_smul
  条件: {f : 实数 -> E} {s a : Complex}
  证明: by
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

nonrec theorem MellinConvergent.div_const {f : Real -> Complex} {s : Complex} (hf : MellinConvergent f s) (a : Complex) :
    MellinConver

Depends on / 依赖: cpow_add, integrableOn_congr_fun, measurableSet_Ioi, mul_smul, ne_of_gt, ofReal_ne_zero, simp_rw, sub_add_eq_add_sub
-/
theorem MellinConvergent.cpow_smul {f : Real -> E} {s a : Complex} :
    MellinConvergent (fun t => (t : Complex) ^ a • f t) s ↔ MellinConvergent f (s + a) := by
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

nonrec theorem MellinConvergent.div_const {f : Real -> Complex} {s : Complex} (hf : MellinConvergent f s) (a : Complex) :
    MellinConvergent (fun t => f t / a) s := by
  simpa only [MellinConvergent, smul_eq_mul, ← mul_div_assoc] using! hf.div_const a

/--
theorem `MellinConvergent.comp_mul_left` / 定理 `MellinConvergent.comp_mul_left`

English:
theorem MellinConvergent.comp_mul_left
  given: {f : Real -> E} {s : Complex} {a : Real} (ha : 0 < a)
  proof: by
  have := integrableOn_Ioi_comp_mul_left_iff (fun t : Real => (t : Complex) ^ (s - 1) • f t) 0 ha
  rw [mul_zero] at this
  have h1 : EqOn (fun t : Real => (↑(a * t) : Complex) ^ (s - 1) • f (a * t))
      ((a : Complex) ^ (s - 1) • fun t : Real => (t : Complex) ^ (s - 1) • f (a * t)) (Ioi 0) := 

中文:
定理 MellinConvergent.comp_mul_left
  条件: {f : 实数 -> E} {s : Complex} {a : 实数} (ha : 0 < a)
  证明: by
  have := integrableOn_Ioi_comp_mul_left_iff (fun t : Real => (t : Complex) ^ (s - 1) • f t) 0 ha
  rw [mul_zero] at this
  have h1 : EqOn (fun t : Real => (↑(a * t) : Complex) ^ (s - 1) • f (a * t))
      ((a : Complex) ^ (s - 1) • fun t : Real => (t : Complex) ^ (s - 1) • f (a * t)) (Ioi 0) := 

Depends on / 依赖: Pi.smul_apply, cpow_eq_zero_iff, ha.le, integrableOn_Ioi_comp_mul_left_iff, le_of_lt, mul_cpow_ofReal_nonneg, mul_smul, mul_zero, not_and_or, ofReal_, ofReal_mul, smul_apply
-/
theorem MellinConvergent.comp_mul_left {f : Real -> E} {s : Complex} {a : Real} (ha : 0 < a) :
    MellinConvergent (fun t => f (a * t)) s ↔ MellinConvergent f s := by
  have := integrableOn_Ioi_comp_mul_left_iff (fun t : Real => (t : Complex) ^ (s - 1) • f t) 0 ha
  rw [mul_zero] at this
  have h1 : EqOn (fun t : Real => (↑(a * t) : Complex) ^ (s - 1) • f (a * t))
      ((a : Complex) ^ (s - 1) • fun t : Real => (t : Complex) ^ (s - 1) • f (a * t)) (Ioi 0) := fun t ht => by
    simp only [ofReal_mul, mul_cpow_ofReal_nonneg ha.le (le_of_lt ht), mul_smul, Pi.smul_apply]
  have h2 : (a : Complex) ^ (s - 1) != 0 := by
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]; rw [ofReal_eq_zero]
    exact Or.inl ha.ne'
  rw [MellinConvergent]; rw [MellinConvergent]; rw [← this]; rw [integrableOn_congr_fun h1 measurableSet_Ioi]; rw [IntegrableOn]; rw [IntegrableOn]; rw [integrable_smul_iff h2]

/--
theorem `MellinConvergent.comp_rpow` / 定理 `MellinConvergent.comp_rpow`

English:
theorem MellinConvergent.comp_rpow
  given: {f : Real -> E} {s : Complex} {a : Real} (ha : a != 0)
  proof: by
  refine Iff.trans ?_ (integrableOn_Ioi_comp_rpow_iff' _ ha)
  rw [MellinConvergent]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [← Complex.coe_smul (t ^ (a - 1))]; rw [← mul_smul]; rw [← cpow_mul_ofReal_nonneg (le_of_lt ht)]; rw [ofReal_cpow (le_of_lt ht)]; rw [← cpow

中文:
定理 MellinConvergent.comp_rpow
  条件: {f : 实数 -> E} {s : Complex} {a : 实数} (ha : a != 0)
  证明: by
  refine Iff.trans ?_ (integrableOn_Ioi_comp_rpow_iff' _ ha)
  rw [MellinConvergent]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [← Complex.coe_smul (t ^ (a - 1))]; rw [← mul_smul]; rw [← cpow_mul_ofReal_nonneg (le_of_lt ht)]; rw [ofReal_cpow (le_of_lt ht)]; rw [← cpow

Depends on / 依赖: Complex.coe_smul, Iff.trans, MellinConvergent, add_comm, add_sub_assoc, coe_smul, cpow_add, cpow_mul_ofReal_nonneg, integrableOn_Ioi_comp_rpow_iff, integrableOn_congr_fun, le_of_lt, measurableSet_Ioi, mul_one, mul_smul, mul_sub, ne_of_gt, ofReal_cpow, ofReal_ne_zero, ofReal_ne_zero.mpr, ofReal_one
-/
theorem MellinConvergent.comp_rpow {f : Real -> E} {s : Complex} {a : Real} (ha : a != 0) :
    MellinConvergent (fun t => f (t ^ a)) s ↔ MellinConvergent f (s / a) := by
  refine Iff.trans ?_ (integrableOn_Ioi_comp_rpow_iff' _ ha)
  rw [MellinConvergent]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [← Complex.coe_smul (t ^ (a - 1))]; rw [← mul_smul]; rw [← cpow_mul_ofReal_nonneg (le_of_lt ht)]; rw [ofReal_cpow (le_of_lt ht)]; rw [← cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht))]; rw [ofReal_sub]; rw [ofReal_one]; rw [mul_sub]; rw [mul_div_cancel₀ _ (ofReal_ne_zero.mpr ha)]; rw [mul_one]; rw [add_comm]; rw [←
    add_sub_assoc]; rw [sub_add_cancel]

/--
Definition of `Complex.VerticalIntegrable` / `Complex.VerticalIntegrable` 的定义

English:
definition Complex.VerticalIntegrable
  signature: (f : Complex -> E) (σ : Real) (μ : Measure Real := by volume_tac)
  body: Integrable (fun (y : Real) => f (σ + y * I)) μ

中文:
定义 Complex.VerticalIntegrable
  签名: (f : Complex -> E) (σ : 实数) (μ : Measure 实数 := by volume_tac)
  定义体: Integrable (fun (y : Real) => f (σ + y * I)) μ

Depends on / 依赖: Integrable, volume_tac
-/
def Complex.VerticalIntegrable (f : Complex -> E) (σ : Real) (μ : Measure Real := by volume_tac) : Prop :=
  Integrable (fun (y : Real) => f (σ + y * I)) μ

/--
Definition of `mellin` / `mellin` 的定义

English:
definition mellin
  signature: (f : Real -> E) (s : Complex)
  body: ∫ t : Real in Ioi 0, (t : Complex) ^ (s - 1) • f t

中文:
定义 mellin
  签名: (f : 实数 -> E) (s : Complex)
  定义体: ∫ t : Real in Ioi 0, (t : Complex) ^ (s - 1) • f t
-/
def mellin (f : Real -> E) (s : Complex) : E :=
  ∫ t : Real in Ioi 0, (t : Complex) ^ (s - 1) • f t

/--
Definition of `mellinInv` / `mellinInv` 的定义

English:
definition mellinInv
  signature: (σ : Real) (f : Complex -> E) (x : Real)
  body: (1 / (2 * π)) • ∫ y : Real, (x : Complex) ^ (-(σ + y * I)) • f (σ + y * I)

中文:
定义 mellinInv
  签名: (σ : 实数) (f : Complex -> E) (x : 实数)
  定义体: (1 / (2 * π)) • ∫ y : Real, (x : Complex) ^ (-(σ + y * I)) • f (σ + y * I)
-/
def mellinInv (σ : Real) (f : Complex -> E) (x : Real) : E :=
  (1 / (2 * π)) • ∫ y : Real, (x : Complex) ^ (-(σ + y * I)) • f (σ + y * I)

-- next few lemmas don't require convergence of the Mellin transform (they are just 0 = 0 otherwise)
/--
theorem `mellin_cpow_smul` / 定理 `mellin_cpow_smul`

English:
theorem mellin_cpow_smul
  given: (f : Real -> E) (s a : Complex)
  proof: by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

中文:
定理 mellin_cpow_smul
  条件: (f : 实数 -> E) (s a : Complex)
  证明: by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

Depends on / 依赖: cpow_add, measurableSet_Ioi, mul_smul, ne_of_gt, ofReal_ne_zero, setIntegral_congr_fun, simp_rw, sub_add_eq_add_sub
-/
theorem mellin_cpow_smul (f : Real -> E) (s a : Complex) :
    mellin (fun t => (t : Complex) ^ a • f t) s = mellin f (s + a) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

/--
theorem `mellin_const_smul` / 定理 `mellin_const_smul`

English:
theorem mellin_const_smul
  statement: (f : Real -> E) (s : Complex) {𝕜 : Type*}
  proof: by
  simp only [mellin, smul_comm, integral_smul]

中文:
定理 mellin_const_smul
  结论: (f : 实数 -> E) (s : Complex) {𝕜 : 类型}
  证明: by
  simp only [mellin, smul_comm, integral_smul]

Depends on / 依赖: integral_smul, mellin, smul_comm
-/
theorem mellin_const_smul (f : Real -> E) (s : Complex) {𝕜 : Type*}
    [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass Complex 𝕜 E] (c : 𝕜) :
    mellin (fun t => c • f t) s = c • mellin f s := by
  simp only [mellin, smul_comm, integral_smul]

/--
theorem `mellin_div_const` / 定理 `mellin_div_const`

English:
theorem mellin_div_const
  given: (f : Real -> Complex) (s a : Complex)
  statement: mellin (fun t => f t / a) s = mellin f s / a
  proof: by
  simp_rw [mellin, smul_eq_mul, ← mul_div_assoc, integral_div]

中文:
定理 mellin_div_const
  条件: (f : 实数 -> Complex) (s a : Complex)
  结论: mellin (fun t => f t / a) s = mellin f s / a
  证明: by
  simp_rw [mellin, smul_eq_mul, ← mul_div_assoc, integral_div]

Depends on / 依赖: integral_div, mellin, mul_div_assoc, simp_rw, smul_eq_mul
-/
theorem mellin_div_const (f : Real -> Complex) (s a : Complex) : mellin (fun t => f t / a) s = mellin f s / a := by
  simp_rw [mellin, smul_eq_mul, ← mul_div_assoc, integral_div]

/--
theorem `mellin_comp_rpow` / 定理 `mellin_comp_rpow`

English:
theorem mellin_comp_rpow
  given: (f : Real -> E) (s : Complex) (a : Real)
  proof: by
  /- This is true for `a = 0` as all sides are undefined but turn out to vanish thanks to our
  convention. The interesting case is `a ≠ 0` -/
  rcases eq_or_ne a 0 with rfl | ha
  · by_cases hE : CompleteSpace E
    · simp [integral_smul_const, mellin, setIntegral_Ioi_zero_cpow]
    · simp [inte

中文:
定理 mellin_comp_rpow
  条件: (f : 实数 -> E) (s : Complex) (a : 实数)
  证明: by
  /- This is true for `a = 0` as all sides are undefined but turn out to vanish thanks to our
  convention. The interesting case is `a ≠ 0` -/
  rcases eq_or_ne a 0 with rfl | ha
  · by_cases hE : CompleteSpace E
    · simp [integral_smul_const, mellin, setIntegral_Ioi_zero_cpow]
    · simp [inte
-/
theorem mellin_comp_rpow (f : Real -> E) (s : Complex) (a : Real) :
    mellin (fun t => f (t ^ a)) s = |a|⁻¹ • mellin f (s / a) := by
  /- This is true for `a = 0` as all sides are undefined but turn out to vanish thanks to our
  convention. The interesting case is `a ≠ 0` -/
  rcases eq_or_ne a 0 with rfl | ha
  · by_cases hE : CompleteSpace E
    · simp [integral_smul_const, mellin, setIntegral_Ioi_zero_cpow]
    · simp [integral, mellin, hE]
  simp_rw [mellin]
  conv_rhs => rw [← integral_comp_rpow_Ioi _ ha, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [← mul_smul]; rw [← mul_assoc]; rw [inv_mul_cancel₀ (mt abs_eq_zero.1 ha)]; rw [one_mul]; rw [← smul_assoc]; rw [real_smul]
  rw [ofReal_cpow (le_of_lt ht)]; rw [← cpow_mul_ofReal_nonneg (le_of_lt ht)]; rw [←
    cpow_add _ _ (ofReal_ne_zero.mpr <| ne_of_gt ht)]; rw [ofReal_sub]; rw [ofReal_one]; rw [mul_sub]; rw [mul_div_cancel₀ _ (ofReal_ne_zero.mpr ha)]; rw [add_comm]; rw [← add_sub_assoc]; rw [mul_one]; rw [sub_add_cancel]

/--
theorem `mellin_comp_mul_left` / 定理 `mellin_comp_mul_left`

English:
theorem mellin_comp_mul_left
  given: (f : Real -> E) (s : Complex) {a : Real} (ha : 0 < a)
  proof: by
  simp_rw [mellin]
  have : EqOn (fun t : Real => (t : Complex) ^ (s - 1) • f (a * t))
      (fun t : Real => (a : Complex) ^ (1 - s) • (fun u : Real => (u : Complex) ^ (s - 1) • f u) (a * t))
        (Ioi 0) := fun t ht => by
    dsimp only
    rw [ofReal_mul]; rw [mul_cpow_ofReal_nonneg ha.le (

中文:
定理 mellin_comp_mul_left
  条件: (f : 实数 -> E) (s : Complex) {a : 实数} (ha : 0 < a)
  证明: by
  simp_rw [mellin]
  have : EqOn (fun t : Real => (t : Complex) ^ (s - 1) • f (a * t))
      (fun t : Real => (a : Complex) ^ (1 - s) • (fun u : Real => (u : Complex) ^ (s - 1) • f u) (a * t))
        (Ioi 0) := fun t ht => by
    dsimp only
    rw [ofReal_mul]; rw [mul_cpow_ofReal_nonneg ha.le (

Depends on / 依赖: Or.inl, cpow_eq_zero_iff, cpow_neg, ha.le, ha.ne, le_of_lt, mellin, mul_cpow_ofReal_nonneg, mul_smul, not_and_or, ofReal_eq_zero, ofReal_mul, setIntegral_congr_fun, simp_rw
-/
theorem mellin_comp_mul_left (f : Real -> E) (s : Complex) {a : Real} (ha : 0 < a) :
    mellin (fun t => f (a * t)) s = (a : Complex) ^ (-s) • mellin f s := by
  simp_rw [mellin]
  have : EqOn (fun t : Real => (t : Complex) ^ (s - 1) • f (a * t))
      (fun t : Real => (a : Complex) ^ (1 - s) • (fun u : Real => (u : Complex) ^ (s - 1) • f u) (a * t))
        (Ioi 0) := fun t ht => by
    dsimp only
    rw [ofReal_mul]; rw [mul_cpow_ofReal_nonneg ha.le (le_of_lt ht)]; rw [← mul_smul]; rw [(by ring : 1 - s = -(s - 1))]; rw [cpow_neg]; rw [inv_mul_cancel_left₀]
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [ofReal_eq_zero]; rw [not_and_or]
    exact Or.inl ha.ne'
  rw [setIntegral_congr_fun measurableSet_Ioi this]; rw [integral_smul]; rw [integral_comp_mul_left_Ioi (fun u => (u : Complex) ^ (s - 1) • f u) _ ha]; rw [mul_zero]; rw [← Complex.coe_smul]; rw [← mul_smul]; rw [sub_eq_add_neg]; rw [cpow_add _ _ (ofReal_ne_zero.mpr ha.ne')]; rw [cpow_one]; rw [ofReal_inv]; rw [mul_assoc]; rw [mul_comm]; rw [inv_mul_cancel_right₀ (ofReal_ne_zero.mpr ha.ne')]

/--
theorem `mellin_comp_mul_right` / 定理 `mellin_comp_mul_right`

English:
theorem mellin_comp_mul_right
  given: (f : Real -> E) (s : Complex) {a : Real} (ha : 0 < a)
  proof: by
  simpa only [mul_comm] using mellin_comp_mul_left f s ha

中文:
定理 mellin_comp_mul_right
  条件: (f : 实数 -> E) (s : Complex) {a : 实数} (ha : 0 < a)
  证明: by
  simpa only [mul_comm] using mellin_comp_mul_left f s ha

Depends on / 依赖: mellin_comp_mul_left, mul_comm
-/
theorem mellin_comp_mul_right (f : Real -> E) (s : Complex) {a : Real} (ha : 0 < a) :
    mellin (fun t => f (t * a)) s = (a : Complex) ^ (-s) • mellin f s := by
  simpa only [mul_comm] using mellin_comp_mul_left f s ha

/--
theorem `mellin_comp_inv` / 定理 `mellin_comp_inv`

English:
theorem mellin_comp_inv
  given: (f : Real -> E) (s : Complex)
  statement: mellin (fun t => f t⁻¹) s = mellin f (-s)
  proof: by
  simp_rw [← rpow_neg_one, mellin_comp_rpow _ _ _, abs_neg, abs_one,
    inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one]

中文:
定理 mellin_comp_inv
  条件: (f : 实数 -> E) (s : Complex)
  结论: mellin (fun t => f t⁻¹) s = mellin f (-s)
  证明: by
  simp_rw [← rpow_neg_one, mellin_comp_rpow _ _ _, abs_neg, abs_one,
    inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one]

Depends on / 依赖: abs_neg, abs_one, div_neg, div_one, inv_one, mellin_comp_rpow, ofReal_neg, ofReal_one, one_smul, rpow_neg_one, simp_rw
-/
theorem mellin_comp_inv (f : Real -> E) (s : Complex) : mellin (fun t => f t⁻¹) s = mellin f (-s) := by
  simp_rw [← rpow_neg_one, mellin_comp_rpow _ _ _, abs_neg, abs_one,
    inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one]

/--
Definition of `HasMellin` / `HasMellin` 的定义

English:
definition HasMellin
  signature: (f : Real -> E) (s : Complex) (m : E)
  body: MellinConvergent f s ∧ mellin f s = m

中文:
定义 HasMellin
  签名: (f : 实数 -> E) (s : Complex) (m : E)
  定义体: MellinConvergent f s ∧ mellin f s = m

Depends on / 依赖: MellinConvergent, mellin
-/
def HasMellin (f : Real -> E) (s : Complex) (m : E) : Prop :=
  MellinConvergent f s ∧ mellin f s = m

/--
theorem `hasMellin_add` / 定理 `hasMellin_add`

English:
theorem hasMellin_add
  statement: {f g : Real -> E} {s : Complex} (hf : MellinConvergent f s)
  proof: ⟨by simpa only [MellinConvergent, smul_add] using! hf.add hg, by
    simpa only [mellin, smul_add] using! integral_add hf hg⟩

中文:
定理 hasMellin_add
  结论: {f g : 实数 -> E} {s : Complex} (hf : MellinConvergent f s)
  证明: ⟨by simpa only [MellinConvergent, smul_add] using! hf.add hg, by
    simpa only [mellin, smul_add] using! integral_add hf hg⟩

Depends on / 依赖: MellinConvergent, hf.add, integral_add, mellin, smul_add
-/
theorem hasMellin_add {f g : Real -> E} {s : Complex} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : HasMellin (fun t => f t + g t) s (mellin f s + mellin g s) :=
  ⟨by simpa only [MellinConvergent, smul_add] using! hf.add hg, by
    simpa only [mellin, smul_add] using! integral_add hf hg⟩

/--
theorem `hasMellin_sub` / 定理 `hasMellin_sub`

English:
theorem hasMellin_sub
  statement: {f g : Real -> E} {s : Complex} (hf : MellinConvergent f s)
  proof: ⟨by simpa only [MellinConvergent, smul_sub] using! hf.sub hg, by
    simpa only [mellin, smul_sub] using! integral_sub hf hg⟩

中文:
定理 hasMellin_sub
  结论: {f g : 实数 -> E} {s : Complex} (hf : MellinConvergent f s)
  证明: ⟨by simpa only [MellinConvergent, smul_sub] using! hf.sub hg, by
    simpa only [mellin, smul_sub] using! integral_sub hf hg⟩

Depends on / 依赖: MellinConvergent, hf.sub, integral_sub, mellin, smul_sub
-/
theorem hasMellin_sub {f g : Real -> E} {s : Complex} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : HasMellin (fun t => f t - g t) s (mellin f s - mellin g s) :=
  ⟨by simpa only [MellinConvergent, smul_sub] using! hf.sub hg, by
    simpa only [mellin, smul_sub] using! integral_sub hf hg⟩

/--
theorem `hasMellin_const_smul` / 定理 `hasMellin_const_smul`

English:
theorem hasMellin_const_smul
  statement: {f : Real -> E} {s : Complex} (hf : MellinConvergent f s)
  proof: ⟨hf.const_smul c, by simp [mellin, smul_comm, hf.integral_smul]⟩

中文:
定理 hasMellin_const_smul
  结论: {f : 实数 -> E} {s : Complex} (hf : MellinConvergent f s)
  证明: ⟨hf.const_smul c, by simp [mellin, smul_comm, hf.integral_smul]⟩

Depends on / 依赖: const_smul, hf.const_smul, hf.integral_smul, integral_smul, mellin, smul_comm
-/
theorem hasMellin_const_smul {f : Real -> E} {s : Complex} (hf : MellinConvergent f s)
    {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass Complex R E] (c : R) :
    HasMellin (fun t => c • f t) s (c • mellin f s) :=
  ⟨hf.const_smul c, by simp [mellin, smul_comm, hf.integral_smul]⟩

end Defs

variable {E : Type*} [NormedAddCommGroup E]

section MellinConvergent

/-! ## Convergence of Mellin transform integrals -/

/--
theorem `mellin_convergent_iff_norm` / 定理 `mellin_convergent_iff_norm`

English:
theorem mellin_convergent_iff_norm
  statement: [NormedSpace Complex E] {f : Real -> E} {T : Set Real} (hT : T subseteq Ioi 0)
  proof: by
  have : AEStronglyMeasurable (fun t : Real => (t : Complex) ^ (s - 1) • f t) (volume.restrict T) := by
    refine ((continuousOn_of_forall_continuousAt ?_).aestronglyMeasurable hT').smul
      (hfc.mono_set hT)
    exact fun t ht => continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt (hT ht))

中文:
定理 mellin_convergent_iff_norm
  结论: [NormedSpace Complex E] {f : 实数 -> E} {T : Set 实数} (hT : T subseteq Ioi 0)
  证明: by
  have : AEStronglyMeasurable (fun t : Real => (t : Complex) ^ (s - 1) • f t) (volume.restrict T) := by
    refine ((continuousOn_of_forall_continuousAt ?_).aestronglyMeasurable hT').smul
      (hfc.mono_set hT)
    exact fun t ht => continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt (hT ht))

Depends on / 依赖: AEStronglyMeasurable, IntegrableOn, Or.inr, aestronglyMeasurable, continuousAt_ofReal_cpow_const, continuousOn_of_forall_continuousAt, hfc.mono_set, integrableOn_congr_fun, integrable_norm_iff, mono_set, ne_of_gt, norm_cpow_eq_rpow_re_of_pos, norm_smul, one_re, restrict, simp_rw, sub_re, volume, volume.restrict
-/
theorem mellin_convergent_iff_norm [NormedSpace Complex E] {f : Real -> E} {T : Set Real} (hT : T subseteq Ioi 0)
    (hT' : MeasurableSet T) (hfc : AEStronglyMeasurable f <| volume.restrict <| Ioi 0) {s : Complex} :
    IntegrableOn (fun t : Real => (t : Complex) ^ (s - 1) • f t) T ↔
      IntegrableOn (fun t : Real => t ^ (s.re - 1) * ‖f t‖) T := by
  have : AEStronglyMeasurable (fun t : Real => (t : Complex) ^ (s - 1) • f t) (volume.restrict T) := by
    refine ((continuousOn_of_forall_continuousAt ?_).aestronglyMeasurable hT').smul
      (hfc.mono_set hT)
    exact fun t ht => continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt (hT ht))
  rw [IntegrableOn]; rw [← integrable_norm_iff this]; rw [← IntegrableOn]
  refine integrableOn_congr_fun (fun t ht => ?_) hT'
  simp_rw [norm_smul, norm_cpow_eq_rpow_re_of_pos (hT ht), sub_re, one_re]

/--
theorem `mellin_convergent_top_of_isBigO` / 定理 `mellin_convergent_top_of_isBigO`

English:
theorem mellin_convergent_top_of_isBigO
  statement: {f : Real -> Real}
  proof: by
  obtain ⟨d, hd'⟩ := hf.isBigOWith
  simp_rw [IsBigOWith, eventually_atTop] at hd'
  obtain ⟨e, he⟩ := hd'
  have he' : 0 < max e 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨max e 1, he', ?_, ?_⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set (Ioi_subset_Ioi he'.le))
    refine (

中文:
定理 mellin_convergent_top_of_isBigO
  结论: {f : 实数 -> 实数}
  证明: by
  obtain ⟨d, hd'⟩ := hf.isBigOWith
  simp_rw [IsBigOWith, eventually_atTop] at hd'
  obtain ⟨e, he⟩ := hd'
  have he' : 0 < max e 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨max e 1, he', ?_, ?_⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set (Ioi_subset_Ioi he'.le))
    refine (

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mul, Ioi_subset_Ioi, IsBigOWith, Or.inl, aestronglyMeasurable, continuousAt_rpow_const, continuousOn_of_forall_continuousAt, eventually_atTop, hf.isBigOWith, hfc.mono_set, isBigOWith, le_max_right, measurableSet_Ioi, mono_set, restrict, simp_rw, trans_le, volume, volume.restrict
-/
theorem mellin_convergent_top_of_isBigO {f : Real -> Real}
    (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0)) {a s : Real}
    (hf : f =O[atTop] (· ^ (-a))) (hs : s < a) :
    exists c : Real, 0 < c ∧ IntegrableOn (fun t : Real => t ^ (s - 1) * f t) (Ioi c) := by
  obtain ⟨d, hd'⟩ := hf.isBigOWith
  simp_rw [IsBigOWith, eventually_atTop] at hd'
  obtain ⟨e, he⟩ := hd'
  have he' : 0 < max e 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨max e 1, he', ?_, ?_⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set (Ioi_subset_Ioi he'.le))
    refine (continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact continuousAt_rpow_const _ _ (Or.inl <| (he'.trans ht).ne')
  · have : forallᵐ t : Real ∂volume.restrict (Ioi <| max e 1),
        ‖t ^ (s - 1) * f t‖ <= t ^ (s - 1 + -a) * d := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht' : 0 < t := he'.trans ht
      rw [norm_mul]; rw [rpow_add ht']; rw [← norm_of_nonneg (rpow_nonneg ht'.le (-a))]; rw [mul_assoc]; rw [mul_comm _ d]; rw [norm_of_nonneg (rpow_nonneg ht'.le _)]
      gcongr
      exact he t ((le_max_left e 1).trans_lt ht).le
    refine (HasFiniteIntegral.mul_const ?_ _).mono' this
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) he').hasFiniteIntegral

/--
theorem `mellin_convergent_zero_of_isBigO` / 定理 `mellin_convergent_zero_of_isBigO`

English:
theorem mellin_convergent_zero_of_isBigO
  statement: {b : Real} {f : Real -> Real}
  proof: by
  obtain ⟨d, _, hd'⟩ := hf.exists_pos
  simp_rw [IsBigOWith, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, gt_iff_lt] at hd'
  obtain ⟨ε, hε, hε'⟩ := hd'
  refine ⟨ε, hε, Iff.mpr integrableOn_Ioc_iff_integrableOn_Ioo ⟨?_, ?_⟩⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set Ioo_subs

中文:
定理 mellin_convergent_zero_of_isBigO
  结论: {b : 实数} {f : 实数 -> 实数}
  证明: by
  obtain ⟨d, _, hd'⟩ := hf.exists_pos
  simp_rw [IsBigOWith, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, gt_iff_lt] at hd'
  obtain ⟨ε, hε, hε'⟩ := hd'
  refine ⟨ε, hε, Iff.mpr integrableOn_Ioc_iff_integrableOn_Ioo ⟨?_, ?_⟩⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set Ioo_subs

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mul, HasFiniteIntegral, HasFiniteIntegral.mono, Iff.mpr, Ioo_subset_Ioi_self, IsBigOWith, Metric, Metric.eventually_nhds_iff, Or.inl, aestronglyMeasurable, continuousAt_rpow_const, continuousOn_of_forall_continuousAt, eventually_nhdsWithin_iff, eventually_nhds_iff, exists_pos, gt_iff_lt, hf.exists_pos, hfc.mono_set, integrableOn_Ioc_iff_integrableOn_Ioo
-/
theorem mellin_convergent_zero_of_isBigO {b : Real} {f : Real -> Real}
    (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0))
    (hf : f =O[𝓝[>] 0] (· ^ (-b))) {s : Real} (hs : b < s) :
    exists c : Real, 0 < c ∧ IntegrableOn (fun t : Real => t ^ (s - 1) * f t) (Ioc 0 c) := by
  obtain ⟨d, _, hd'⟩ := hf.exists_pos
  simp_rw [IsBigOWith, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, gt_iff_lt] at hd'
  obtain ⟨ε, hε, hε'⟩ := hd'
  refine ⟨ε, hε, Iff.mpr integrableOn_Ioc_iff_integrableOn_Ioo ⟨?_, ?_⟩⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set Ioo_subset_Ioi_self)
    refine (continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioo
    exact continuousAt_rpow_const _ _ (Or.inl ht.1.ne')
  · apply HasFiniteIntegral.mono' (g := fun t => d * t ^ (s - b - 1))
    · refine (Integrable.hasFiniteIntegral ?_).const_mul _
      rw [← IntegrableOn]; rw [← integrableOn_Ioc_iff_integrableOn_Ioo]; rw [←
        intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
      rw [mul_comm]; rw [norm_mul]
      specialize hε' _ ht.1
      · rw [dist_eq_norm, sub_zero, norm_of_nonneg ht.1.le]
        exact ht.2
      · calc _ <= d * ‖t ^ (-b)‖ * ‖t ^ (s - 1)‖ := by gcongr
          _ = d * t ^ (s - b - 1) := ?_
        simp_rw [norm_of_nonneg (rpow_nonneg ht.1.le _), mul_assoc]
        rw [← rpow_add ht.1]
        congr 2
        abel

/--
theorem `mellin_convergent_of_isBigO_scalar` / 定理 `mellin_convergent_of_isBigO_scalar`

English:
theorem mellin_convergent_of_isBigO_scalar
  statement: {a b : Real} {f : Real -> Real} {s : Real}
  proof: by
  obtain ⟨c1, hc1, hc1'⟩ := mellin_convergent_top_of_isBigO hfc.aestronglyMeasurable hf_top hs_top
  obtain ⟨c2, hc2, hc2'⟩ :=
    mellin_convergent_zero_of_isBigO hfc.aestronglyMeasurable hf_bot hs_bot
  have : Ioi 0 = Ioc 0 c2 union Ioc c2 c1 union Ioi c1 := by
    rw [union_assoc]; rw [Ioc_uni

中文:
定理 mellin_convergent_of_isBigO_scalar
  结论: {a b : 实数} {f : 实数 -> 实数} {s : 实数}
  证明: by
  obtain ⟨c1, hc1, hc1'⟩ := mellin_convergent_top_of_isBigO hfc.aestronglyMeasurable hf_top hs_top
  obtain ⟨c2, hc2, hc2'⟩ :=
    mellin_convergent_zero_of_isBigO hfc.aestronglyMeasurable hf_bot hs_bot
  have : Ioi 0 = Ioc 0 c2 union Ioc c2 c1 union Ioi c1 := by
    rw [union_assoc]; rw [Ioc_uni

Depends on / 依赖: Iff.mp, Ioc_union_Ioi, aestronglyMeasurable, hf_bot, hf_top, hfc.aestronglyMeasurable, hs_bot, hs_top, integrableOn_union, le_max_right, lt_min, mellin_convergent_top_of_isBigO, mellin_convergent_zero_of_isBigO, min_eq_left, min_le_left, union_assoc
-/
theorem mellin_convergent_of_isBigO_scalar {a b : Real} {f : Real -> Real} {s : Real}
    (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s) :
    IntegrableOn (fun t : Real => t ^ (s - 1) * f t) (Ioi 0) := by
  obtain ⟨c1, hc1, hc1'⟩ := mellin_convergent_top_of_isBigO hfc.aestronglyMeasurable hf_top hs_top
  obtain ⟨c2, hc2, hc2'⟩ :=
    mellin_convergent_zero_of_isBigO hfc.aestronglyMeasurable hf_bot hs_bot
  have : Ioi 0 = Ioc 0 c2 union Ioc c2 c1 union Ioi c1 := by
    rw [union_assoc]; rw [Ioc_union_Ioi (le_max_right _ _)]; rw [Ioc_union_Ioi ((min_le_left _ _).trans (le_max_right _ _))]; rw [min_eq_left (lt_min hc2 hc1).le]
  rw [this]; rw [integrableOn_union]; rw [integrableOn_union]
  refine ⟨⟨hc2', Iff.mp integrableOn_Icc_iff_integrableOn_Ioc ?_⟩, hc1'⟩
  refine
    (hfc.continuousOn_mul ?_ isOpen_Ioi.isLocallyClosed).integrableOn_compact_subset
      (fun t ht => (hc2.trans_le ht.1 : 0 < t)) isCompact_Icc
  exact continuousOn_of_forall_continuousAt
fun t ht => continuousAt_rpow_const _ _ Or.inl ne_of_gt ht

/--
theorem `mellinConvergent_of_isBigO_rpow` / 定理 `mellinConvergent_of_isBigO_rpow`

English:
theorem mellinConvergent_of_isBigO_rpow
  statement: [NormedSpace Complex E] {a b : Real} {f : Real -> E} {s : Complex}
  proof: by
  rw [MellinConvergent]; rw [mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hfc.aestronglyMeasurable]
  exact mellin_convergent_of_isBigO_scalar hfc.norm hf_top.norm_left hs_top hf_bot.norm_left hs_bot

中文:
定理 mellinConvergent_of_isBigO_rpow
  结论: [NormedSpace Complex E] {a b : 实数} {f : 实数 -> E} {s : Complex}
  证明: by
  rw [MellinConvergent]; rw [mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hfc.aestronglyMeasurable]
  exact mellin_convergent_of_isBigO_scalar hfc.norm hf_top.norm_left hs_top hf_bot.norm_left hs_bot

Depends on / 依赖: MellinConvergent, Subset, Subset.rfl, aestronglyMeasurable, hf_bot, hf_bot.norm_left, hf_top, hf_top.norm_left, hfc.aestronglyMeasurable, hfc.norm, hs_bot, hs_top, measurableSet_Ioi, mellin_convergent_iff_norm, mellin_convergent_of_isBigO_scalar, norm_left
-/
theorem mellinConvergent_of_isBigO_rpow [NormedSpace Complex E] {a b : Real} {f : Real -> E} {s : Complex}
    (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    MellinConvergent f s := by
  rw [MellinConvergent]; rw [mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hfc.aestronglyMeasurable]
  exact mellin_convergent_of_isBigO_scalar hfc.norm hf_top.norm_left hs_top hf_bot.norm_left hs_bot

end MellinConvergent

section MellinDiff

/--
theorem `isBigO_rpow_top_log_smul` / 定理 `isBigO_rpow_top_log_smul`

English:
theorem isBigO_rpow_top_log_smul
  statement: [NormedSpace Real E] {a b : Real} {f : Real -> E} (hab : b < a)
  proof: by
  refine
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).isBigO.smul hf).congr'
      (Eventually.of_forall fun t => by rfl)
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun t ht => ?_))
  simp only
  rw [smul_eq_mul]; rw [← rpow_add ht]; rw [← sub_eq_add_neg]; rw [sub_eq_add_neg a];

中文:
定理 isBigO_rpow_top_log_smul
  结论: [NormedSpace 实数 E] {a b : 实数} {f : 实数 -> E} (hab : b < a)
  证明: by
  refine
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).isBigO.smul hf).congr'
      (Eventually.of_forall fun t => by rfl)
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun t ht => ?_))
  simp only
  rw [smul_eq_mul]; rw [← rpow_add ht]; rw [← sub_eq_add_neg]; rw [sub_eq_add_neg a];

Depends on / 依赖: Eventually, Eventually.of_forall, add_sub_cancel_left, eventually_gt_atTop, isBigO, isBigO.smul, isLittleO_log_rpow_atTop, of_forall, rpow_add, smul_eq_mul, sub_eq_add_neg, sub_pos, sub_pos.mpr
-/
theorem isBigO_rpow_top_log_smul [NormedSpace Real E] {a b : Real} {f : Real -> E} (hab : b < a)
    (hf : f =O[atTop] (· ^ (-a))) :
    (fun t : Real => log t • f t) =O[atTop] (· ^ (-b)) := by
  refine
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).isBigO.smul hf).congr'
      (Eventually.of_forall fun t => by rfl)
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun t ht => ?_))
  simp only
  rw [smul_eq_mul]; rw [← rpow_add ht]; rw [← sub_eq_add_neg]; rw [sub_eq_add_neg a]; rw [add_sub_cancel_left]

/--
theorem `isBigO_rpow_zero_log_smul` / 定理 `isBigO_rpow_zero_log_smul`

English:
theorem isBigO_rpow_zero_log_smul
  statement: [NormedSpace Real E] {a b : Real} {f : Real -> E} (hab : a < b)
  proof: by
  have : log =o[𝓝[>] 0] fun t : Real => t ^ (a - b) := by
    refine ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).neg_left.comp_tendsto
          tendsto_inv_nhdsGT_zero).congr'
      (.of_forall fun t => ?_)
      (eventually_mem_nhdsWithin.mono fun t ht => ?_)
    · simp
    · simp_rw [Functio

中文:
定理 isBigO_rpow_zero_log_smul
  结论: [NormedSpace 实数 E] {a b : 实数} {f : 实数 -> E} (hab : a < b)
  证明: by
  have : log =o[𝓝[>] 0] fun t : Real => t ^ (a - b) := by
    refine ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).neg_left.comp_tendsto
          tendsto_inv_nhdsGT_zero).congr'
      (.of_forall fun t => ?_)
      (eventually_mem_nhdsWithin.mono fun t ht => ?_)
    · simp
    · simp_rw [Functio

Depends on / 依赖: Eventually, Eventually.of_forall, Function, Function.comp_apply, comp_apply, comp_tendsto, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mpr, inv_rpow, isBigO, isLittleO_log_rpow_atTop, le_of_lt, neg_left, neg_left.comp_tendsto, neg_sub, of_forall, rpow_neg, simp_rw
-/
theorem isBigO_rpow_zero_log_smul [NormedSpace Real E] {a b : Real} {f : Real -> E} (hab : a < b)
    (hf : f =O[𝓝[>] 0] (· ^ (-a))) :
    (fun t : Real => log t • f t) =O[𝓝[>] 0] (· ^ (-b)) := by
  have : log =o[𝓝[>] 0] fun t : Real => t ^ (a - b) := by
    refine ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).neg_left.comp_tendsto
          tendsto_inv_nhdsGT_zero).congr'
      (.of_forall fun t => ?_)
      (eventually_mem_nhdsWithin.mono fun t ht => ?_)
    · simp
    · simp_rw [Function.comp_apply, inv_rpow (le_of_lt ht), ← rpow_neg (le_of_lt ht), neg_sub]
  refine (this.isBigO.smul hf).congr' (Eventually.of_forall fun t => by rfl)
      (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ?_))
  simp_rw [smul_eq_mul, ← rpow_add ht]
  congr 1
  abel

/--
theorem `mellin_hasDerivAt_of_isBigO_rpow` / 定理 `mellin_hasDerivAt_of_isBigO_rpow`

English:
theorem mellin_hasDerivAt_of_isBigO_rpow
  statement: [NormedSpace Complex E] {a b : Real}
  proof: by
  set F : Complex -> Real -> E := fun (z : Complex) (t : Real) => (t : Complex) ^ (z - 1) • f t
  set F' : Complex -> Real -> E := fun (z : Complex) (t : Real) => ((t : Complex) ^ (z - 1) * log t) • f t
  -- A convenient radius of ball within which we can uniformly bound the derivative.
  obtain 

中文:
定理 mellin_hasDerivAt_of_isBigO_rpow
  结论: [NormedSpace Complex E] {a b : 实数}
  证明: by
  set F : Complex -> Real -> E := fun (z : Complex) (t : Real) => (t : Complex) ^ (z - 1) • f t
  set F' : Complex -> Real -> E := fun (z : Complex) (t : Real) => ((t : Complex) ^ (z - 1) * log t) • f t
  -- A convenient radius of ball within which we can uniformly bound the derivative.
  obtain 
-/
theorem mellin_hasDerivAt_of_isBigO_rpow [NormedSpace Complex E] {a b : Real}
    {f : Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f (Ioi 0)) (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    MellinConvergent (fun t => log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t => log t • f t) s) s := by
  set F : Complex -> Real -> E := fun (z : Complex) (t : Real) => (t : Complex) ^ (z - 1) • f t
  set F' : Complex -> Real -> E := fun (z : Complex) (t : Real) => ((t : Complex) ^ (z - 1) * log t) • f t
  -- A convenient radius of ball within which we can uniformly bound the derivative.
  obtain ⟨v, hv0, hv1, hv2⟩ : exists v : Real, 0 < v ∧ v < s.re - b ∧ v < a - s.re := by
    obtain ⟨w, hw1, hw2⟩ := exists_between (sub_pos.mpr hs_top)
    obtain ⟨w', hw1', hw2'⟩ := exists_between (sub_pos.mpr hs_bot)
    exact
      ⟨min w w', lt_min hw1 hw1', (min_le_right _ _).trans_lt hw2', (min_le_left _ _).trans_lt hw2⟩
  let bound : Real -> Real := fun t : Real => (t ^ (s.re + v - 1) + t ^ (s.re - v - 1)) * |log t| * ‖f t‖
  have h1 : forallᶠ z : Complex in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict <| Ioi 0) := by
    refine Eventually.of_forall fun z => AEStronglyMeasurable.smul ?_ hfc.aestronglyMeasurable
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
  have h2 : IntegrableOn (F s) (Ioi (0 : Real)) := by
    exact mellinConvergent_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot
  have h3 : AEStronglyMeasurable (F' s) (volume.restrict <| Ioi 0) := by
    apply LocallyIntegrableOn.aestronglyMeasurable
    refine hfc.continuousOn_smul isOpen_Ioi.isLocallyClosed
      ((continuousOn_of_forall_continuousAt fun t ht => ?_).mul ?_)
    · exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
    · refine continuous_ofReal.comp_continuousOn ?_
      exact continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi)
  have h4 : forallᵐ t : Real ∂volume.restrict (Ioi 0),
      forall z : Complex, z in Metric.ball s v -> ‖F' z t‖ <= bound t := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    simp_rw [F', bound, norm_smul, norm_mul, norm_real, mul_assoc, norm_eq_abs]
    gcongr
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    rcases le_or_gt 1 t with h | h
    · refine le_add_of_le_of_nonneg (rpow_le_rpow_of_exponent_le h ?_)
        (by positivity)
      rw [sub_re]; rw [one_re]; rw [sub_le_sub_iff_right]
      rw [mem_ball_iff_norm] at hz
      have hz' := (re_le_norm _).trans hz.le
      rwa [sub_re, sub_le_iff_le_add'] at hz'
    · refine
        le_add_of_nonneg_of_le (rpow_pos_of_pos ht _).le (rpow_le_rpow_of_exponent_ge ht h.le ?_)
      rw [sub_re]; rw [one_re]; rw [sub_le_iff_le_add]; rw [sub_add_cancel]
      rw [mem_ball_iff_norm'] at hz
      have hz' := (re_le_norm _).trans hz.le
      rwa [sub_re, sub_le_iff_le_add, ← sub_le_iff_le_add'] at hz'
  have h5 : IntegrableOn bound (Ioi 0) := by
    simp_rw [bound, add_mul, mul_assoc]
    suffices forall {j : Real}, b < j -> j < a ->
        IntegrableOn (fun t : Real => t ^ (j - 1) * (|log t| * ‖f t‖)) (Ioi 0) volume by
      refine Integrable.add (this ?_ ?_) (this ?_ ?_)
      all_goals linarith
    · intro j hj hj'
      obtain ⟨w, hw1, hw2⟩ := exists_between hj
      obtain ⟨w', hw1', hw2'⟩ := exists_between hj'
      refine mellin_convergent_of_isBigO_scalar ?_ ?_ hw1' ?_ hw2
      · simp_rw [mul_comm]
        refine hfc.norm.mul_continuousOn ?_ isOpen_Ioi.isLocallyClosed
        refine Continuous.comp_continuousOn _root_.continuous_abs (continuousOn_log.mono ?_)
        exact subset_compl_singleton_iff.mpr self_notMem_Ioi
      · refine (isBigO_rpow_top_log_smul hw2' hf_top).norm_left.congr_left fun t => ?_
        simp only [norm_smul, Real.norm_eq_abs]
      · refine (isBigO_rpow_zero_log_smul hw1 hf_bot).norm_left.congr_left fun t => ?_
        simp only [norm_smul, Real.norm_eq_abs]
  have h6 : forallᵐ t : Real ∂volume.restrict (Ioi 0),
      forall y : Complex, y in Metric.ball s v -> HasDerivAt (fun z : Complex => F z t) (F' y t) y := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht y _ => ?_
    have ht' : (t : Complex) != 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have u1 : HasDerivAt (fun z : Complex => (t : Complex) ^ (z - 1)) (t ^ (y - 1) * log t) y := by
      convert! ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [ofReal_log (le_of_lt ht)]
      ring
    exact u1.smul_const (f t)
  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hv0) h1 h2 h3 h4 h5 h6
  simpa only [F', mul_smul] using! main

/--
theorem `mellin_differentiableAt_of_isBigO_rpow` / 定理 `mellin_differentiableAt_of_isBigO_rpow`

English:
theorem mellin_differentiableAt_of_isBigO_rpow
  statement: [NormedSpace Complex E] {a b : Real}
  proof: (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot).2.differentiableAt

中文:
定理 mellin_differentiableAt_of_isBigO_rpow
  结论: [NormedSpace Complex E] {a b : 实数}
  证明: (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot).2.differentiableAt

Depends on / 依赖: differentiableAt, hf_bot, hf_top, hs_bot, hs_top, mellin_hasDerivAt_of_isBigO_rpow
-/
theorem mellin_differentiableAt_of_isBigO_rpow [NormedSpace Complex E] {a b : Real}
    {f : Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f <| Ioi 0)
    (hf_top : f =O[atTop] (· ^ (-a))) (hs_top : s.re < a)
    (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    DifferentiableAt Complex (mellin f) s :=
  (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot).2.differentiableAt

end MellinDiff

section ExpDecay

/--
theorem `mellinConvergent_of_isBigO_rpow_exp` / 定理 `mellinConvergent_of_isBigO_rpow_exp`

English:
theorem mellinConvergent_of_isBigO_rpow_exp
  statement: [NormedSpace Complex E] {a b : Real} (ha : 0 < a) {f : Real -> E}
  proof: mellinConvergent_of_isBigO_rpow hfc (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO)
    (lt_add_one _) hf_bot hs_bot

中文:
定理 mellinConvergent_of_isBigO_rpow_exp
  结论: [NormedSpace Complex E] {a b : 实数} (ha : 0 < a) {f : 实数 -> E}
  证明: mellinConvergent_of_isBigO_rpow hfc (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO)
    (lt_add_one _) hf_bot hs_bot

Depends on / 依赖: hf_bot, hf_top, hf_top.trans, hs_bot, isBigO, isLittleO_exp_neg_mul_rpow_atTop, lt_add_one, mellinConvergent_of_isBigO_rpow
-/
theorem mellinConvergent_of_isBigO_rpow_exp [NormedSpace Complex E] {a b : Real} (ha : 0 < a) {f : Real -> E}
    {s : Complex} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] fun t => exp (-a * t))
    (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) : MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow hfc (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO)
    (lt_add_one _) hf_bot hs_bot

/--
theorem `mellin_differentiableAt_of_isBigO_rpow_exp` / 定理 `mellin_differentiableAt_of_isBigO_rpow_exp`

English:
theorem mellin_differentiableAt_of_isBigO_rpow_exp
  statement: [NormedSpace Complex E] {a b : Real}
  proof: mellin_differentiableAt_of_isBigO_rpow hfc
    (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO) (lt_add_one _) hf_bot hs_bot

中文:
定理 mellin_differentiableAt_of_isBigO_rpow_exp
  结论: [NormedSpace Complex E] {a b : 实数}
  证明: mellin_differentiableAt_of_isBigO_rpow hfc
    (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO) (lt_add_one _) hf_bot hs_bot

Depends on / 依赖: hf_bot, hf_top, hf_top.trans, hs_bot, isBigO, isLittleO_exp_neg_mul_rpow_atTop, lt_add_one, mellin_differentiableAt_of_isBigO_rpow
-/
theorem mellin_differentiableAt_of_isBigO_rpow_exp [NormedSpace Complex E] {a b : Real}
    (ha : 0 < a) {f : Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f <| Ioi 0)
    (hf_top : f =O[atTop] fun t => exp (-a * t)) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b)))
    (hs_bot : b < s.re) : DifferentiableAt Complex (mellin f) s :=
  mellin_differentiableAt_of_isBigO_rpow hfc
    (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO) (lt_add_one _) hf_bot hs_bot

end ExpDecay

section MellinIoc

/-!
## Mellin transforms of functions on `Ioc 0 1`
-/

/--
theorem `hasMellin_one_Ioc` / 定理 `hasMellin_one_Ioc`

English:
theorem hasMellin_one_Ioc
  given: {s : Complex} (hs : 0 < re s)
  proof: by
  have aux1 : -1 < (s - 1).re := by
    simpa only [sub_re, one_re, sub_eq_add_neg] using! lt_add_of_pos_left _ hs
  have aux2 : s != 0 := by contrapose! hs; rw [hs, zero_re]
  have aux3 : MeasurableSet (Ioc (0 : Real) 1) := measurableSet_Ioc
  simp_rw [HasMellin, mellin, MellinConvergent, ← indi

中文:
定理 hasMellin_one_Ioc
  条件: {s : Complex} (hs : 0 < re s)
  证明: by
  have aux1 : -1 < (s - 1).re := by
    simpa only [sub_re, one_re, sub_eq_add_neg] using! lt_add_of_pos_left _ hs
  have aux2 : s != 0 := by contrapose! hs; rw [hs, zero_re]
  have aux3 : MeasurableSet (Ioc (0 : Real) 1) := measurableSet_Ioc
  simp_rw [HasMellin, mellin, MellinConvergent, ← indi

Depends on / 依赖: HasMellin, IntegrableOn, Ioc_subset_Ioi_self, MeasurableSet, Measure, Measure.restrict_restrict_of_subset, MellinConvergent, contrapose, indicator_smul, integrable_indicator_iff, integral_indicator, intervalIn, lt_add_of_pos_left, measurableSet_Ioc, mellin, mul_one, one_re, restrict_restrict_of_subset, simp_rw, smul_eq_mul
-/
theorem hasMellin_one_Ioc {s : Complex} (hs : 0 < re s) :
    HasMellin (indicator (Ioc 0 1) (fun _ => 1 : Real -> Complex)) s (1 / s) := by
  have aux1 : -1 < (s - 1).re := by
    simpa only [sub_re, one_re, sub_eq_add_neg] using! lt_add_of_pos_left _ hs
  have aux2 : s != 0 := by contrapose! hs; rw [hs, zero_re]
  have aux3 : MeasurableSet (Ioc (0 : Real) 1) := measurableSet_Ioc
  simp_rw [HasMellin, mellin, MellinConvergent, ← indicator_smul, IntegrableOn,
    integrable_indicator_iff aux3, smul_eq_mul, integral_indicator aux3, mul_one, IntegrableOn,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  rw [← IntegrableOn]; rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine ⟨intervalIntegral.intervalIntegrable_cpow' aux1, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one]; rw [integral_cpow (Or.inl aux1)]; rw [sub_add_cancel]; rw [ofReal_zero]; rw [ofReal_one]; rw [one_cpow]; rw [zero_cpow aux2]; rw [sub_zero]

/--
theorem `hasMellin_cpow_Ioc` / 定理 `hasMellin_cpow_Ioc`

English:
theorem hasMellin_cpow_Ioc
  given: (a : Complex) {s : Complex} (hs : 0 < re s + re a)
  proof: by
  have := hasMellin_one_Ioc (by rwa [add_re] : 0 < (s + a).re)
  simp_rw [HasMellin, ← MellinConvergent.cpow_smul, ← mellin_cpow_smul, ← indicator_smul,
    smul_eq_mul, mul_one] at this
  exact this

中文:
定理 hasMellin_cpow_Ioc
  条件: (a : Complex) {s : Complex} (hs : 0 < re s + re a)
  证明: by
  have := hasMellin_one_Ioc (by rwa [add_re] : 0 < (s + a).re)
  simp_rw [HasMellin, ← MellinConvergent.cpow_smul, ← mellin_cpow_smul, ← indicator_smul,
    smul_eq_mul, mul_one] at this
  exact this

Depends on / 依赖: HasMellin, MellinConvergent, MellinConvergent.cpow_smul, add_re, cpow_smul, hasMellin_one_Ioc, indicator_smul, mellin_cpow_smul, mul_one, simp_rw, smul_eq_mul
-/
theorem hasMellin_cpow_Ioc (a : Complex) {s : Complex} (hs : 0 < re s + re a) :
    HasMellin (indicator (Ioc 0 1) (fun t => ↑t ^ a : Real -> Complex)) s (1 / (s + a)) := by
  have := hasMellin_one_Ioc (by rwa [add_re] : 0 < (s + a).re)
  simp_rw [HasMellin, ← MellinConvergent.cpow_smul, ← mellin_cpow_smul, ← indicator_smul,
    smul_eq_mul, mul_one] at this
  exact this

end MellinIoc
