/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integral transform

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.

These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/

@[expose] public section


open Set MeasureTheory Metric Filter Function

open scoped Interval Real

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] (R : Real) (z w : Complex)

namespace Complex

/--
Definition of `circleTransform` / `circleTransform` 的定义

English:
definition circleTransform
  signature: (f : Complex -> E) (θ : Real)
  body: (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)

中文:
定义 circleTransform
  签名: (f : 复形 -> E) (θ : 实数)
  定义体: (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)

Depends on / 依赖: circleMap
-/
def circleTransform (f : Complex -> E) (θ : Real) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)

/--
Definition of `circleTransformDeriv` / `circleTransformDeriv` 的定义

English:
definition circleTransformDeriv
  signature: (f : Complex -> E) (θ : Real)
  body: (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)

中文:
定义 circleTransformDeriv
  签名: (f : 复形 -> E) (θ : 实数)
  定义体: (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)

Depends on / 依赖: circleMap
-/
def circleTransformDeriv (f : Complex -> E) (θ : Real) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)

/--
theorem `circleTransformDeriv_periodic` / 定理 `circleTransformDeriv_periodic`

English:
theorem circleTransformDeriv_periodic
  given: (f : Complex -> E)
  proof: by
  simp [circleTransformDeriv, periodic_circleMap z R _, periodic_circleMap 0 R _]

中文:
定理 circleTransformDeriv_periodic
  条件: (f : 复形 -> E)
  证明: by
  simp [circleTransformDeriv, periodic_circleMap z R _, periodic_circleMap 0 R _]

Depends on / 依赖: circleTransformDeriv, periodic_circleMap
-/
theorem circleTransformDeriv_periodic (f : Complex -> E) :
    Periodic (circleTransformDeriv R z w f) (2 * π) := by
  simp [circleTransformDeriv, periodic_circleMap z R _, periodic_circleMap 0 R _]

/--
theorem `circleTransformDeriv_eq` / 定理 `circleTransformDeriv_eq`

English:
theorem circleTransformDeriv_eq
  given: (f : Complex -> E)
  statement: circleTransformDeriv R z w f =
  proof: by
  ext
  simp_rw [circleTransformDeriv, circleTransform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring

中文:
定理 circleTransformDeriv_eq
  条件: (f : 复形 -> E)
  结论: circleTransformDeriv R z w f =
  证明: by
  ext
  simp_rw [circleTransformDeriv, circleTransform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring

Depends on / 依赖: circleTransform, circleTransformDeriv, inv_pow, mul_assoc, mul_smul, ring_nf, simp_rw
-/
theorem circleTransformDeriv_eq (f : Complex -> E) : circleTransformDeriv R z w f =
    fun θ => (circleMap z R θ - w)⁻¹ • circleTransform R z w f θ := by
  ext
  simp_rw [circleTransformDeriv, circleTransform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring

/--
theorem `integral_circleTransform` / 定理 `integral_circleTransform`

English:
theorem integral_circleTransform
  given: (f : Complex -> E)
  proof: by
  simp_rw [circleTransform, circleIntegral, deriv_circleMap, circleMap]
  simp

中文:
定理 integral_circleTransform
  条件: (f : 复形 -> E)
  证明: by
  simp_rw [circleTransform, circleIntegral, deriv_circleMap, circleMap]
  simp

Depends on / 依赖: circleIntegral, circleMap, circleTransform, deriv_circleMap, simp_rw
-/
theorem integral_circleTransform (f : Complex -> E) :
    (∫ θ : Real in 0..2 * π, circleTransform R z w f θ) =
      (2 * ↑π * I)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z := by
  simp_rw [circleTransform, circleIntegral, deriv_circleMap, circleMap]
  simp

/--
theorem `continuous_circleTransform` / 定理 `continuous_circleTransform`

English:
theorem continuous_circleTransform
  statement: {R : Real} (hR : 0 < R) {f : Complex -> E} {z w : Complex}
  proof: by
  apply_rules [Continuous.smul, continuous_const]
  · rw [funext <| deriv_circleMap _ _]
    fun_prop
  · exact continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _

中文:
定理 continuous_circleTransform
  结论: {R : 实数} (hR : 0 < R) {f : 复形 -> E} {z w : 复形}
  证明: by
  apply_rules [Continuous.smul, continuous_const]
  · rw [funext <| deriv_circleMap _ _]
    fun_prop
  · exact continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _

Depends on / 依赖: Continuous, Continuous.smul, ContinuousOn, ContinuousOn.comp_continuous, apply_rules, circleMap_mem_sphere, comp_continuous, continuous_circleMap, continuous_circleMap_inv, continuous_const, deriv_circleMap, fun_prop, hR.le
-/
theorem continuous_circleTransform {R : Real} (hR : 0 < R) {f : Complex -> E} {z w : Complex}
    (hf : ContinuousOn f <| sphere z R) (hw : w in ball z R) :
    Continuous (circleTransform R z w f) := by
  apply_rules [Continuous.smul, continuous_const]
  · rw [funext <| deriv_circleMap _ _]
    fun_prop
  · exact continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _

/--
theorem `continuous_circleTransformDeriv` / 定理 `continuous_circleTransformDeriv`

English:
theorem continuous_circleTransformDeriv
  statement: {R : Real} (hR : 0 < R) {f : Complex -> E} {z w : Complex}
  proof: by
  rw [circleTransformDeriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circleTransform hR hf hw)

中文:
定理 continuous_circleTransformDeriv
  结论: {R : 实数} (hR : 0 < R) {f : 复形 -> E} {z w : 复形}
  证明: by
  rw [circleTransformDeriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circleTransform hR hf hw)

Depends on / 依赖: circleTransformDeriv_eq, continuous_circleMap_inv, continuous_circleTransform
-/
theorem continuous_circleTransformDeriv {R : Real} (hR : 0 < R) {f : Complex -> E} {z w : Complex}
    (hf : ContinuousOn f (sphere z R)) (hw : w in ball z R) :
    Continuous (circleTransformDeriv R z w f) := by
  rw [circleTransformDeriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circleTransform hR hf hw)

/--
Definition of `circleTransformBoundingFunction` / `circleTransformBoundingFunction` 的定义

English:
definition circleTransformBoundingFunction
  signature: (R : Real) (z : Complex) (w : Complex × Real)
  body: circleTransformDeriv R z w.1 (fun _ => 1) w.2

中文:
定义 circleTransformBoundingFunction
  签名: (R : 实数) (z : 复形) (w : 复形 × 实数)
  定义体: circleTransformDeriv R z w.1 (fun _ => 1) w.2

Depends on / 依赖: circleTransformDeriv
-/
def circleTransformBoundingFunction (R : Real) (z : Complex) (w : Complex × Real) : Complex :=
  circleTransformDeriv R z w.1 (fun _ => 1) w.2

/--
theorem `continuousOn_prod_circle_transform_function` / 定理 `continuousOn_prod_circle_transform_function`

English:
theorem continuousOn_prod_circle_transform_function
  given: {R r : Real} (hr : r < R) {z : Complex}
  proof: by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuousOn_const]
  · exact ((continuous_circleMap z R).comp_continuousOn continuousOn_snd).sub continuousOn_fst
  · rintro ⟨a, b⟩ ⟨ha, -⟩
    have ha2 : a in ball z R := closedBall_subset_ball hr ha
    exact sub_ne_zero.

中文:
定理 continuousOn_prod_circle_transform_function
  条件: {R r : 实数} (hr : r < R) {z : 复形}
  证明: by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuousOn_const]
  · exact ((continuous_circleMap z R).comp_continuousOn continuousOn_snd).sub continuousOn_fst
  · rintro ⟨a, b⟩ ⟨ha, -⟩
    have ha2 : a in ball z R := closedBall_subset_ball hr ha
    exact sub_ne_zero.

Depends on / 依赖: ContinuousOn, ContinuousOn.div, ContinuousOn.pow, apply_rules, circleMap_ne_mem_ball, closedBall_subset_ball, comp_continuousOn, continuousOn_const, continuousOn_fst, continuousOn_snd, continuous_circleMap, one_div, simp_rw, sub_ne_zero
-/
theorem continuousOn_prod_circle_transform_function {R r : Real} (hr : r < R) {z : Complex} :
    ContinuousOn (fun w : Complex × Real => (circleMap z R w.snd - w.fst)⁻¹ ^ 2)
      (closedBall z r ×ˢ univ) := by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuousOn_const]
  · exact ((continuous_circleMap z R).comp_continuousOn continuousOn_snd).sub continuousOn_fst
  · rintro ⟨a, b⟩ ⟨ha, -⟩
    have ha2 : a in ball z R := closedBall_subset_ball hr ha
    exact sub_ne_zero.2 (circleMap_ne_mem_ball ha2 b)

/--
theorem `continuousOn_norm_circleTransformBoundingFunction` / 定理 `continuousOn_norm_circleTransformBoundingFunction`

English:
theorem continuousOn_norm_circleTransformBoundingFunction
  given: {R r : Real} (hr : r < R) (z : Complex)
  proof: by
  have : ContinuousOn (circleTransformBoundingFunction R z) (closedBall z r ×ˢ univ) := by
    apply_rules [ContinuousOn.fun_smul, continuousOn_const]
    · simp only [deriv_circleMap]
      apply_rules [ContinuousOn.mul, (continuous_circleMap 0 R).comp_continuousOn continuousOn_snd,
        cont

中文:
定理 continuousOn_norm_circleTransformBoundingFunction
  条件: {R r : 实数} (hr : r < R) (z : 复形)
  证明: by
  have : ContinuousOn (circleTransformBoundingFunction R z) (closedBall z r ×ˢ univ) := by
    apply_rules [ContinuousOn.fun_smul, continuousOn_const]
    · simp only [deriv_circleMap]
      apply_rules [ContinuousOn.mul, (continuous_circleMap 0 R).comp_continuousOn continuousOn_snd,
        cont

Depends on / 依赖: ContinuousOn, ContinuousOn.fun_smul, ContinuousOn.mul, apply_rules, circleTransformBoundingFunction, closedBall, comp_continuousOn, continuousOn_const, continuousOn_prod_circle_transform_function, continuousOn_snd, continuous_circleMap, deriv_circleMap, fun_smul, inv_pow, this.norm
-/
theorem continuousOn_norm_circleTransformBoundingFunction {R r : Real} (hr : r < R) (z : Complex) :
    ContinuousOn ((‖·‖) ∘ circleTransformBoundingFunction R z) (closedBall z r ×ˢ univ) := by
  have : ContinuousOn (circleTransformBoundingFunction R z) (closedBall z r ×ˢ univ) := by
    apply_rules [ContinuousOn.fun_smul, continuousOn_const]
    · simp only [deriv_circleMap]
      apply_rules [ContinuousOn.mul, (continuous_circleMap 0 R).comp_continuousOn continuousOn_snd,
        continuousOn_const]
    · simpa only [inv_pow] using continuousOn_prod_circle_transform_function hr
  exact this.norm

/--
theorem `norm_circleTransformBoundingFunction_le` / 定理 `norm_circleTransformBoundingFunction_le`

English:
theorem norm_circleTransformBoundingFunction_le
  given: {R r : Real} (hr : r < R) (hr' : 0 <= r) (z : Complex)
  proof: by
  have cts := continuousOn_norm_circleTransformBoundingFunction hr z
  have comp : IsCompact (closedBall z r ×ˢ [[0, 2 * π]]) := by
    apply_rules [IsCompact.prod, ProperSpace.isCompact_closedBall z r, isCompact_uIcc]
  have none : (closedBall z r ×ˢ [[0, 2 * π]]).Nonempty :=
    (nonempty_close

中文:
定理 norm_circleTransformBoundingFunction_le
  条件: {R r : 实数} (hr : r < R) (hr' : 0 <= r) (z : 复形)
  证明: by
  have cts := continuousOn_norm_circleTransformBoundingFunction hr z
  have comp : IsCompact (closedBall z r ×ˢ [[0, 2 * π]]) := by
    apply_rules [IsCompact.prod, ProperSpace.isCompact_closedBall z r, isCompact_uIcc]
  have none : (closedBall z r ×ˢ [[0, 2 * π]]).Nonempty :=
    (nonempty_close

Depends on / 依赖: IsCompact, IsCompact.exists_isMaxOn, IsCompact.prod, Nonempty, ProperSpace, ProperSpace.isCompact_closedBall, apply_rules, closedBall, continuousOn_norm_circleTransformBoundingFunction, cts.mono, exists_isMaxOn, isCompact_closedBall, isCompact_uIcc, isMaxOn_iff, nonempty_closedBall, nonempty_uIcc, prod_mono_right, subset_univ
-/
theorem norm_circleTransformBoundingFunction_le {R r : Real} (hr : r < R) (hr' : 0 <= r) (z : Complex) :
    exists x : closedBall z r ×ˢ [[0, 2 * π]], forall y : closedBall z r ×ˢ [[0, 2 * π]],
    ‖circleTransformBoundingFunction R z y‖ <= ‖circleTransformBoundingFunction R z x‖ := by
  have cts := continuousOn_norm_circleTransformBoundingFunction hr z
  have comp : IsCompact (closedBall z r ×ˢ [[0, 2 * π]]) := by
    apply_rules [IsCompact.prod, ProperSpace.isCompact_closedBall z r, isCompact_uIcc]
  have none : (closedBall z r ×ˢ [[0, 2 * π]]).Nonempty :=
    (nonempty_closedBall.2 hr').prod nonempty_uIcc
  have := IsCompact.exists_isMaxOn comp none (cts.mono <| prod_mono_right (subset_univ _))
  simpa [isMaxOn_iff] using this

/--
theorem `circleTransformDeriv_bound` / 定理 `circleTransformDeriv_bound`

English:
theorem circleTransformDeriv_bound
  statement: {R : Real} (hR : 0 < R) {z x : Complex} {f : Complex -> Complex} (hx : x in ball z R)
  proof: by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    norm_circleTransformBoundingFunction_le hr (pos_of_mem_ball hrx).le z
  let V : Real -> Complex -> Complex := fun θ w => circleTransformDeriv R

中文:
定理 circleTransformDeriv_bound
  结论: {R : 实数} (hR : 0 < R) {z x : 复形} {f : 复形 -> 复形} (hx : x in ball z R)
  证明: by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    norm_circleTransformBoundingFunction_le hr (pos_of_mem_ball hrx).le z
  let V : Real -> Complex -> Complex := fun θ w => circleTransformDeriv R

Depends on / 依赖: H.trans, NormedSpace, NormedSpace.sphere_nonempty, ball_subset_ball, circleTransformDeriv, exists_ball_subset_ball, exists_isMaxOn, exists_lt_mem_ball_of_mem_ball, hR.le, hf.norm, hr.le, isCompact_sphere, norm_circleTransformBoundingFunction_le, pos_of_mem_ball, sphere_nonempty
-/
theorem circleTransformDeriv_bound {R : Real} (hR : 0 < R) {z x : Complex} {f : Complex -> Complex} (hx : x in ball z R)
    (hf : ContinuousOn f (sphere z R)) : exists B ε : Real, 0 < ε ∧
      ball x ε subseteq ball z R ∧ forall (t : Real), forall y in ball x ε, ‖circleTransformDeriv R z y f t‖ <= B := by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    norm_circleTransformBoundingFunction_le hr (pos_of_mem_ball hrx).le z
  let V : Real -> Complex -> Complex := fun θ w => circleTransformDeriv R z w (fun _ => 1) θ
  obtain ⟨X, -, HX2⟩ := (isCompact_sphere z R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hR.le) hf.norm
  refine ⟨‖V b a‖ * ‖f X‖, ε', hε', H.trans (ball_subset_ball hr.le), fun y v hv => ?_⟩
  obtain ⟨y1, hy1, hfun⟩ :=
    Periodic.exists_mem_Ico₀ (circleTransformDeriv_periodic R z v f) Real.two_pi_pos y
have hy2 : y1 in [[0, 2 * π]] := Icc_subset_uIcc Ico_subset_Icc_self hy1
  simp only [isMaxOn_iff, mem_sphere_iff_norm] at HX2
  have := mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closedBall (H hv), hy2⟩⟩)
    (HX2 (circleMap z R y1) (mem_sphere_iff_norm.1 (circleMap_mem_sphere z hR.le y1)))
    (norm_nonneg _) (norm_nonneg _)
  rw [hfun]
  simpa [V, circleTransformBoundingFunction, circleTransformDeriv, mul_assoc] using this

end Complex
