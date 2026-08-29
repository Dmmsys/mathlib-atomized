/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Meromorphic.RCLike
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Canonical Decomposition

If a function `f` is meromorphic on a compact set `U`, then it has only finitely many zeros and
poles on the disk, and the theorem `MeromorphicOn.extract_zeros_poles` can be used to re-write `f`
as `(∏ᶠ u, (· - u) ^ divisor f U u) • g`, where `g` is analytic without zeros on `U`. In case where
`U` is a disk, one consider a similar decomposition, called *Finite Canonical Decomposition* or
*Finite Blaschke Product* that replaces the factors `(· - u)` by canonical factors that take only
values of norm one on the boundary of the disk. This file introduces the canonical factors and
provides API for the canonical decomposition.

This file also formulates an extended version of the canonical decomposition that takes zeros on
poles on the boundary of the ball into account.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

@[expose] public section

namespace Complex

open ComplexConjugate Filter Function MeromorphicOn Metric Real Set Topology

variable {R : Real} {w : Complex}

/-!
## Canonical Factors

Given `R : ℝ` and `w : ℂ`, the canonical factor `canonical R w : ℂ → ℂ` is meromorphic function in
normal form that has a single pole at `w`, no zeros, and takes values of norm one on the circle of
radius `R`.
-/

/--
Definition of `canonicalFactor` / `canonicalFactor` 的定义

English:
definition canonicalFactor
  signature: (R : Real) (w : Complex)
  body: fun z => (R ^ 2 - (conj w) * z) / (R * (z - w))

中文:
定义 canonicalFactor
  签名: (R : 实数) (w : 复形)
  定义体: fun z => (R ^ 2 - (conj w) * z) / (R * (z - w))
-/
noncomputable def canonicalFactor (R : Real) (w : Complex) : Complex -> Complex :=
  fun z => (R ^ 2 - (conj w) * z) / (R * (z - w))

/--
lemma `canonicalFactor_def` / 引理 `canonicalFactor_def`

English:
lemma canonicalFactor_def
  given: (R : Real) (w : Complex)
  proof: rfl

中文:
引理 canonicalFactor_def
  条件: (R : 实数) (w : 复形)
  证明: rfl
-/
lemma canonicalFactor_def (R : Real) (w : Complex) :
    canonicalFactor R w = fun z => (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

/--
lemma `canonicalFactor_apply` / 引理 `canonicalFactor_apply`

English:
lemma canonicalFactor_apply
  given: (R : Real) (w z : Complex)
  proof: rfl

@[simp]

中文:
引理 canonicalFactor_apply
  条件: (R : 实数) (w z : 复形)
  证明: rfl

@[simp]
-/
lemma canonicalFactor_apply (R : Real) (w z : Complex) :
    canonicalFactor R w z = (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

@[simp]
/--
lemma `canonicalFactor_apply_self` / 引理 `canonicalFactor_apply_self`

English:
lemma canonicalFactor_apply_self
  given: (R : Real) (w : Complex)
  proof: by
  simp [canonicalFactor_apply]

中文:
引理 canonicalFactor_apply_self
  条件: (R : 实数) (w : 复形)
  证明: by
  simp [canonicalFactor_apply]

Depends on / 依赖: canonicalFactor_apply
-/
lemma canonicalFactor_apply_self (R : Real) (w : Complex) :
    canonicalFactor R w w = 0 := by
  simp [canonicalFactor_apply]

/-!
### Regularity properties
-/

variable (R w) in
/--
theorem `meromorphic_canonicalFactor` / 定理 `meromorphic_canonicalFactor`

English:
theorem meromorphic_canonicalFactor
  statement: Meromorphic (canonicalFactor R w)
  proof: by
  intro x
  unfold canonicalFactor
  fun_prop

中文:
定理 meromorphic_canonicalFactor
  结论: 亚纯 (canonicalFactor R w)
  证明: by
  intro x
  unfold canonicalFactor
  fun_prop
-/
@[fun_prop] theorem meromorphic_canonicalFactor : Meromorphic (canonicalFactor R w) := by
  intro x
  unfold canonicalFactor
  fun_prop

open scoped ComplexOrder in
variable (R w) in
/--
theorem `analyticOnNhd_canonicalFactor` / 定理 `analyticOnNhd_canonicalFactor`

English:
theorem analyticOnNhd_canonicalFactor
  statement: AnalyticOnNhd Complex (canonicalFactor R w) {w}ᶜ
  proof: by
  intro x hx
  rw [canonicalFactor_def]
  obtain (rfl | h) := eq_or_ne R 0
  · simpa using analyticAt_const
  have : x - w != 0 := by grind
  fun_prop (disch := positivity)

中文:
定理 analyticOnNhd_canonicalFactor
  结论: AnalyticOnNhd 复形 (canonicalFactor R w) {w}ᶜ
  证明: by
  intro x hx
  rw [canonicalFactor_def]
  obtain (rfl | h) := eq_or_ne R 0
  · simpa using analyticAt_const
  have : x - w != 0 := by grind
  fun_prop (disch := positivity)

Depends on / 依赖: analyticAt_const, canonicalFactor_def, eq_or_ne, fun_prop
-/
theorem analyticOnNhd_canonicalFactor : AnalyticOnNhd Complex (canonicalFactor R w) {w}ᶜ := by
  intro x hx
  rw [canonicalFactor_def]
  obtain (rfl | h) := eq_or_ne R 0
  · simpa using analyticAt_const
  have : x - w != 0 := by grind
  fun_prop (disch := positivity)

/--
theorem `meromorphicOrderAt_canonicalFactor` / 定理 `meromorphicOrderAt_canonicalFactor`

English:
theorem meromorphicOrderAt_canonicalFactor
  given: (h : w in ball 0 R)
  proof: by
  unfold canonicalFactor
  rw [fun_meromorphicOrderAt_div (by fun_prop) (by fun_prop)]; rw [fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]
  have : meromorphicOrderAt (fun z => ↑R ^ 2 - (starRingEnd Complex) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).2 ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero, ne_eq, ← ofReal_pow,
        ofReal_inj, sq_eq_sq₀ (pos_of_mem_ball h).le (norm_nonneg w)]
      rw [mem_ball_iff_norm]; rw [sub_zero] at h
      grind
  simp [this, meromorphicOrderAt_const, (pos_of_mem_ball h).ne',
    meromorphicOrderAt_id_sub_const]

中文:
定理 meromorphicOrderAt_canonicalFactor
  条件: (h : w in ball 0 R)
  证明: by
  unfold canonicalFactor
  rw [fun_meromorphicOrderAt_div (by fun_prop) (by fun_prop)]; rw [fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]
  have : meromorphicOrderAt (fun z => ↑R ^ 2 - (starRingEnd Complex) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).2 ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero, ne_eq, ← ofReal_pow,
        ofReal_inj, sq_eq_sq₀ (pos_of_mem_ball h).le (norm_nonneg w)]
      rw [mem_ball_iff_norm]; rw [sub_zero] at h
      grind
  simp [this, meromorphicOrderAt_const, (pos_of_mem_ball h).ne',
    meromorphicOrderAt_id_sub_const]

Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicNFAt, MeromorphicNFAt, MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, canonicalFactor, fun_meromorphicOrderAt_div, fun_meromorphicOrderAt_mul, fun_prop, mem_b, meromorphicNFAt, meromorphicOrderAt, meromorphicOrderAt_eq_zero_iff, ne_eq, normSq_eq_conj_mul_self, normSq_eq_norm_sq, norm_nonneg, ofReal_inj, ofReal_pow, pos_of_mem_ball, starRingEnd
-/
theorem meromorphicOrderAt_canonicalFactor (h : w in ball 0 R) :
    meromorphicOrderAt (canonicalFactor R w) w = -1 := by
  unfold canonicalFactor
  rw [fun_meromorphicOrderAt_div (by fun_prop) (by fun_prop)]; rw [fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]
  have : meromorphicOrderAt (fun z => ↑R ^ 2 - (starRingEnd Complex) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).2 ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero, ne_eq, ← ofReal_pow,
        ofReal_inj, sq_eq_sq₀ (pos_of_mem_ball h).le (norm_nonneg w)]
      rw [mem_ball_iff_norm]; rw [sub_zero] at h
      grind
  simp [this, meromorphicOrderAt_const, (pos_of_mem_ball h).ne',
    meromorphicOrderAt_id_sub_const]

/--
theorem `meromorphicNFOn_canonicalFactor` / 定理 `meromorphicNFOn_canonicalFactor`

English:
theorem meromorphicNFOn_canonicalFactor
  given: (h : w in ball 0 R)
  proof: by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphic_canonicalFactor R z z, ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

中文:
定理 meromorphicNFOn_canonicalFactor
  条件: (h : w in ball 0 R)
  证明: by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphic_canonicalFactor R z z, ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

Depends on / 依赖: WithTop, WithTop.coe_lt_zero.mpr, analyticOnNhd_canonicalFactor, coe_lt_zero, eq_or_ne, meromorphicNFAt, meromorphicNFAt_iff_analyticAt_or, meromorphicOrderAt_canonicalFactor, meromorphic_canonicalFactor
-/
theorem meromorphicNFOn_canonicalFactor (h : w in ball 0 R) :
    MeromorphicNFOn (canonicalFactor R w) Set.univ := by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphic_canonicalFactor R z z, ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

/-!
### Values of Canonical Factors
-/

open scoped ComplexOrder in
/--
theorem `canonicalFactor_ne_zero` / 定理 `canonicalFactor_ne_zero`

English:
theorem canonicalFactor_ne_zero
  statement: {z : Complex} (hw : w in ball 0 R) (h₁z : z in closedBall 0 R)
  proof: by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w != 0 := by grind [mem_ball_zero_iff, norm_nonneg]
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw h₁z
  have h_num_ne_zero : R ^ 2 - conj w * z != 0 := by
    suffices ‖conj w * z‖ < ‖(R : Complex) ^ 2‖ by grind
    suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
    grw [h₁z]
    gcongr
  rw [canonicalFactor_apply]
  positivity

中文:
定理 canonicalFactor_ne_zero
  结论: {z : 复形} (hw : w in ball 0 R) (h₁z : z in closedBall 0 R)
  证明: by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w != 0 := by grind [mem_ball_zero_iff, norm_nonneg]
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw h₁z
  have h_num_ne_zero : R ^ 2 - conj w * z != 0 := by
    suffices ‖conj w * z‖ < ‖(R : Complex) ^ 2‖ by grind
    suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
    grw [h₁z]
    gcongr
  rw [canonicalFactor_apply]
  positivity

Depends on / 依赖: canonicalFactor_apply, dist_zero_right, h_num_ne_zero, mem_ball, mem_ball_zero_iff, mem_closedBall, norm_nonneg
-/
theorem canonicalFactor_ne_zero {z : Complex} (hw : w in ball 0 R) (h₁z : z in closedBall 0 R)
    (h₂z : z != w) :
    canonicalFactor R w z != 0 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w != 0 := by grind [mem_ball_zero_iff, norm_nonneg]
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw h₁z
  have h_num_ne_zero : R ^ 2 - conj w * z != 0 := by
    suffices ‖conj w * z‖ < ‖(R : Complex) ^ 2‖ by grind
    suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
    grw [h₁z]
    gcongr
  rw [canonicalFactor_apply]
  positivity

/--
theorem `canonicalFactor_eq_zero_iff` / 定理 `canonicalFactor_eq_zero_iff`

English:
theorem canonicalFactor_eq_zero_iff
  given: {z : Complex} (hw : w in ball 0 R) (hz : z in ball 0 R)
  proof: by
  constructor
  · contrapose
    exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz)
  · simp_all

中文:
定理 canonicalFactor_eq_zero_iff
  条件: {z : 复形} (hw : w in ball 0 R) (hz : z in ball 0 R)
  证明: by
  constructor
  · contrapose
    exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz)
  · simp_all

Depends on / 依赖: ball_subset_closedBall, canonicalFactor_ne_zero, contrapose
-/
theorem canonicalFactor_eq_zero_iff {z : Complex} (hw : w in ball 0 R) (hz : z in ball 0 R) :
    canonicalFactor R w z = 0 ↔ z = w := by
  constructor
  · contrapose
    exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz)
  · simp_all

open scoped ComplexOrder in
/--
theorem `norm_canonicalFactor_eval_circle_eq_one` / 定理 `norm_canonicalFactor_eval_circle_eq_one`

English:
theorem norm_canonicalFactor_eval_circle_eq_one
  given: {z : Complex} (hw : w in ball 0 R) (hz : z in sphere 0 R)
  proof: by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w != 0 := by
    grind [mem_ball_zero_iff, norm_nonneg, mem_sphere_zero_iff_norm]
  rw [canonicalFactor]; rw [norm_div]; rw [div_eq_iff (by rw [ne_eq]; rw [norm_eq_zero]; positivity), one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow]; rw [← normSq_eq_norm_sq]; rw [normSq_eq_conj_mul_self]; rw [← sub_mul]; rw [mul_comm _ z]
  simp [← map_sub]

中文:
定理 norm_canonicalFactor_eval_circle_eq_one
  条件: {z : 复形} (hw : w in ball 0 R) (hz : z in sphere 0 R)
  证明: by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w != 0 := by
    grind [mem_ball_zero_iff, norm_nonneg, mem_sphere_zero_iff_norm]
  rw [canonicalFactor]; rw [norm_div]; rw [div_eq_iff (by rw [ne_eq]; rw [norm_eq_zero]; positivity), one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow]; rw [← normSq_eq_norm_sq]; rw [normSq_eq_conj_mul_self]; rw [← sub_mul]; rw [mul_comm _ z]
  simp [← map_sub]

Depends on / 依赖: canonicalFactor, div_eq_iff, map_sub, mem_ball_zero_iff, mem_sphere_zero_iff_norm, mul_comm, ne_eq, normSq_eq_conj_mul_self, normSq_eq_norm_sq, norm_div, norm_eq_zero, norm_nonneg, ofReal_pow, one_mul, sub_mul
-/
theorem norm_canonicalFactor_eval_circle_eq_one {z : Complex} (hw : w in ball 0 R) (hz : z in sphere 0 R) :
    ‖canonicalFactor R w z‖ = 1 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w != 0 := by
    grind [mem_ball_zero_iff, norm_nonneg, mem_sphere_zero_iff_norm]
  rw [canonicalFactor]; rw [norm_div]; rw [div_eq_iff (by rw [ne_eq]; rw [norm_eq_zero]; positivity), one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow]; rw [← normSq_eq_norm_sq]; rw [normSq_eq_conj_mul_self]; rw [← sub_mul]; rw [mul_comm _ z]
  simp [← map_sub]

/-!
### Orders and Divisors
-/

/--
theorem `meromorphicOrderAt_canonicalFactor_ne_top` / 定理 `meromorphicOrderAt_canonicalFactor_ne_top`

English:
theorem meromorphicOrderAt_canonicalFactor_ne_top
  given: {z : Complex} {R : Real} (w : Complex) (hR : 0 < R)
  proof: by
  apply (meromorphic_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall.1
  use 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  suffices meromorphicOrderAt (canonicalFactor R w) 0 = 0 by simp_all
  rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
  · simp_all [canonicalFactor, ne_of_gt hR]
  · apply AnalyticAt.meromorphicNFAt
    apply analyticOnNhd_canonicalFactor
    grind

中文:
定理 meromorphicOrderAt_canonicalFactor_ne_top
  条件: {z : 复形} {R : 实数} (w : 复形) (hR : 0 < R)
  证明: by
  apply (meromorphic_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall.1
  use 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  suffices meromorphicOrderAt (canonicalFactor R w) 0 = 0 by simp_all
  rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
  · simp_all [canonicalFactor, ne_of_gt hR]
  · apply AnalyticAt.meromorphicNFAt
    apply analyticOnNhd_canonicalFactor
    grind

Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicNFAt, MeromorphicNFAt, MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, analyticOnNhd_canonicalFactor, canonicalFactor, exists_meromorphicOrderAt_ne_top_iff_forall, mem_ball_self, meromorphicNFAt, meromorphicOrderAt, meromorphicOrderAt_canonicalFactor, meromorphicOrderAt_eq_zero_iff, meromorphic_canonicalFactor, ne_of_gt
-/
theorem meromorphicOrderAt_canonicalFactor_ne_top {z : Complex} {R : Real} (w : Complex) (hR : 0 < R) :
    meromorphicOrderAt (canonicalFactor R w) z != ⊤ := by
  apply (meromorphic_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall.1
  use 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  suffices meromorphicOrderAt (canonicalFactor R w) 0 = 0 by simp_all
  rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
  · simp_all [canonicalFactor, ne_of_gt hR]
  · apply AnalyticAt.meromorphicNFAt
    apply analyticOnNhd_canonicalFactor
    grind

/--
theorem `divisor_canonicalFactor` / 定理 `divisor_canonicalFactor`

English:
theorem divisor_canonicalFactor
  given: (hw : w in ball 0 R)
  proof: by
  ext z
  by_cases hz : z in ball 0 R
  · rw [MeromorphicOn.divisor_apply
      (fun z hz => meromorphic_canonicalFactor R w z) hz]
    obtain (rfl | h₂z) := eq_or_ne z w
    · rw [meromorphicOrderAt_canonicalFactor hz]
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (canonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

中文:
定理 divisor_canonicalFactor
  条件: (hw : w in ball 0 R)
  证明: by
  ext z
  by_cases hz : z in ball 0 R
  · rw [MeromorphicOn.divisor_apply
      (fun z hz => meromorphic_canonicalFactor R w z) hz]
    obtain (rfl | h₂z) := eq_or_ne z w
    · rw [meromorphicOrderAt_canonicalFactor hz]
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (canonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

Depends on / 依赖: Functio, Function, Function.locallyFinsuppWithin.restrict_apply, MeromorphicOn, MeromorphicOn.divisor_apply, Set.mem_univ, ball_subset_closedBall, canonicalFactor, canonicalFactor_ne_zero, divisor_apply, eq_or_ne, locallyFinsuppWithin, mem_univ, meromorphicNFOn_canonicalFactor, meromorphicOrderAt, meromorphicOrderAt_canonicalFactor, meromorphicOrderAt_eq_zero_iff, meromorphic_canonicalFactor, restrict_apply
-/
theorem divisor_canonicalFactor (hw : w in ball 0 R) :
    MeromorphicOn.divisor (canonicalFactor R w) (ball 0 R)
      = -(Function.locallyFinsuppWithin.single w 1).restrict (Set.subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z in ball 0 R
  · rw [MeromorphicOn.divisor_apply
      (fun z hz => meromorphic_canonicalFactor R w z) hz]
    obtain (rfl | h₂z) := eq_or_ne z w
    · rw [meromorphicOrderAt_canonicalFactor hz]
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (canonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

/-!
## Canonical Decomposition

The canonical decomposition theorem shows that a meromorphic function `f` on a disk is equal, up to
modification over a discrete set, to a product of canonical factors and a meromorphic function `g`
without zeros or poles in the interior of the disk.

To simplify notation and avoid repetition, we introduce a structure, `CanonicalDecomp`, that bundles
the conclusions of the decomposition theorem.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {R : Real} {c w : Complex}
  {f g : Complex -> E}

/--
Definition of `CanonicalDecomp` / `CanonicalDecomp` 的定义

English:
structure CanonicalDecomp
  parameters: (f g : Complex -> E) (R : Real)
  axioms and operations (4):
    - meromorphicOn : MeromorphicOn f (closedBall 0 R)
    - meromorphicNFOn : MeromorphicNFOn g (closedBall 0 R)
    - ne_zero : forall u in (ball 0 R), g u != 0
    - eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-MeromorphicOn.divisor f (ball 0 R) u)) • g

中文:
结构 CanonicalDecomp
  参数: (f g : 复形 -> E) (R : 实数)
  公理与运算 (4 个):
    - meromorphicOn : MeromorphicOn f (closedBall 0 R)
    - meromorphicNFOn : MeromorphicNFOn g (closedBall 0 R)
    - ne_zero : 对任意 u in (ball 0 R), g u != 0
    - eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-MeromorphicOn.divisor f (ball 0 R) u)) • g

Depends on / 依赖: analyticOnNhd_const, analyticOnNhd_const.meromorphicNFOn, apply_eq_zero_of_notMem, canonicalFactor_eq_zero_iff, eq_zero_of_zpow_eq_zero, locallyFinsuppWithin, locallyFinsuppWithin.apply_eq_zero_of_notMem, meromorphicNFOn, meromorphicNFOn_canonicalFactor, meromorphicNFOn_finprod, not_false_eq_true, zpow_zero
-/
structure CanonicalDecomp (f g : Complex -> E) (R : Real) : Prop where
  /-- A proof that `f` is meromorphic on `closedBall 0 R`. -/
  meromorphicOn : MeromorphicOn f (closedBall 0 R)
  /-- A proof that `g` is meromorphic in normal form on `closedBall 0 R`. -/
  meromorphicNFOn : MeromorphicNFOn g (closedBall 0 R)
  /-- A proof that `g` does not vanish in the interior of the ball. -/
  ne_zero : forall u in (ball 0 R), g u != 0
  /--
  A proof that `f` is equal, up to modification over a discrete set, to a product of `g` and
  canonical factors prescribed by the divisor of `f`.
  -/
  eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)]
    (∏ᶠ u, (canonicalFactor R u) ^ (-MeromorphicOn.divisor f (ball 0 R) u)) • g

-- Auxiliary lemma for the proof of the canonical decomposition theorem: The factor in the canonical
-- decomposition is meromorphic in normal form.
/--
lemma `canonicalDecomposition_aux₁` / 引理 `canonicalDecomposition_aux₁`

English:
lemma canonicalDecomposition_aux₁
  given: (F : locallyFinsuppWithin (ball (0 : Complex) R) Int)
  proof: by
  refine meromorphicNFOn_finprod (fun w => ?_) fun z hz a ha b hb => ?_
  · by_cases hw : w in ball 0 R
    · exact fun _ _ => (meromorphicNFOn_canonicalFactor hw).zpow (by trivial)
    · simp only [hw, not_false_eq_true, locallyFinsuppWithin.apply_eq_zero_of_notMem, zpow_zero]
      exact analyticOnNhd_const.meromorphicNFOn
  · have ⟨h₂a, h₂b⟩ : a in ball 0 R ∧ b in ball 0 R := by constructor <;> (by_contra; aesop)
    grind [eq_zero_of_zpow_eq_zero hb, eq_zero_of_zpow_eq_zero ha,
      canonicalFactor_eq_zero_iff h₂b hz, canonicalFactor_eq_zero_iff h₂a hz]

中文:
引理 canonicalDecomposition_aux₁
  条件: (F : locallyFinsuppWithin (ball (0 : 复形) R) 整数)
  证明: by
  refine meromorphicNFOn_finprod (fun w => ?_) fun z hz a ha b hb => ?_
  · by_cases hw : w in ball 0 R
    · exact fun _ _ => (meromorphicNFOn_canonicalFactor hw).zpow (by trivial)
    · simp only [hw, not_false_eq_true, locallyFinsuppWithin.apply_eq_zero_of_notMem, zpow_zero]
      exact analyticOnNhd_const.meromorphicNFOn
  · have ⟨h₂a, h₂b⟩ : a in ball 0 R ∧ b in ball 0 R := by constructor <;> (by_contra; aesop)
    grind [eq_zero_of_zpow_eq_zero hb, eq_zero_of_zpow_eq_zero ha,
      canonicalFactor_eq_zero_iff h₂b hz, canonicalFactor_eq_zero_iff h₂a hz]
-/
private lemma canonicalDecomposition_aux₁ (F : locallyFinsuppWithin (ball (0 : Complex) R) Int) :
    MeromorphicNFOn (∏ᶠ u, (canonicalFactor R u) ^ (F u)) (ball (0 : Complex) R) := by
  refine meromorphicNFOn_finprod (fun w => ?_) fun z hz a ha b hb => ?_
  · by_cases hw : w in ball 0 R
    · exact fun _ _ => (meromorphicNFOn_canonicalFactor hw).zpow (by trivial)
    · simp only [hw, not_false_eq_true, locallyFinsuppWithin.apply_eq_zero_of_notMem, zpow_zero]
      exact analyticOnNhd_const.meromorphicNFOn
  · have ⟨h₂a, h₂b⟩ : a in ball 0 R ∧ b in ball 0 R := by constructor <;> (by_contra; aesop)
    grind [eq_zero_of_zpow_eq_zero hb, eq_zero_of_zpow_eq_zero ha,
      canonicalFactor_eq_zero_iff h₂b hz, canonicalFactor_eq_zero_iff h₂a hz]

-- Auxiliary lemma for the proof of the canonical decomposition theorem: Write a function with
-- finite support as a linear combination of singleton indicator functions.
open Function.locallyFinsuppWithin in
/--
lemma `sum_apply_smul_single_eq_self` / 引理 `sum_apply_smul_single_eq_self`

English:
lemma sum_apply_smul_single_eq_self
  proof: by
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp only [coe_sum, coe_zsmul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, Function.locallyFinsuppWithin.restrict_apply]
  by_cases hz : z in F.support
  · rw [← Finset.add_sum_erase _ _ (by aesop : z in h.toFinset), Finset.sum_eq_zero (by aesop)]
    aesop
  · aesop

中文:
引理 sum_apply_smul_single_eq_self
  证明: by
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp only [coe_sum, coe_zsmul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, Function.locallyFinsuppWithin.restrict_apply]
  by_cases hz : z in F.support
  · rw [← Finset.add_sum_erase _ _ (by aesop : z in h.toFinset), Finset.sum_eq_zero (by aesop)]
    aesop
  · aesop
-/
private lemma sum_apply_smul_single_eq_self
    {X : Type*} [TopologicalSpace X] [DecidableEq X] {U : Set X}
    {F : Function.locallyFinsuppWithin U Int} (h : F.support.Finite) :
    ∑ x in h.toFinset, (F x) • ((single x (1 : Int)).restrict (subset_univ U)) = F := by
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp only [coe_sum, coe_zsmul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, Function.locallyFinsuppWithin.restrict_apply]
  by_cases hz : z in F.support
  · rw [← Finset.add_sum_erase _ _ (by aesop : z in h.toFinset), Finset.sum_eq_zero (by aesop)]
    aesop
  · aesop

-- Auxiliary lemma for the proof of the canonical decomposition theorem: Exhibit the divisor of the
-- factor in the canonical decomposition as the negative of the divisor of `f`.
/--
lemma `canonicalDecomposition_aux₂` / 引理 `canonicalDecomposition_aux₂`

English:
lemma canonicalDecomposition_aux₂
  given: (h₁f : MeromorphicOn f (closedBall 0 R))
  proof: by
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]; rw [divisor_prod]
  · simp_rw [divisor_zpow (fun z hz => meromorphic_canonicalFactor R _ z)]
    conv_rhs => rw [← sum_apply_smul_single_eq_self η₀]
    apply Finset.sum_congr rfl fun x hx => ?_
    rw [divisor_canonicalFactor]; rw [smul_neg]; rw [locallyFinsuppWithin.coe_neg]; rw [Pi.neg_apply]; rw [neg_smul]
    by_contra
    simp_all
  · intro z hz
    apply zpow (fun x hx => meromorphic_canonicalFactor R z x)
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R z x)]
    lift (meromorphicOrderAt (canonicalFactor R z) x) to Int using
      (meromorphicOrderAt_canonicalFactor_ne_top z (pos_of_mem_ball hx)) with ℓ
    simp [← WithTop.coe_mul]

中文:
引理 canonicalDecomposition_aux₂
  条件: (h₁f : MeromorphicOn f (closedBall 0 R))
  证明: by
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]; rw [divisor_prod]
  · simp_rw [divisor_zpow (fun z hz => meromorphic_canonicalFactor R _ z)]
    conv_rhs => rw [← sum_apply_smul_single_eq_self η₀]
    apply Finset.sum_congr rfl fun x hx => ?_
    rw [divisor_canonicalFactor]; rw [smul_neg]; rw [locallyFinsuppWithin.coe_neg]; rw [Pi.neg_apply]; rw [neg_smul]
    by_contra
    simp_all
  · intro z hz
    apply zpow (fun x hx => meromorphic_canonicalFactor R z x)
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R z x)]
    lift (meromorphicOrderAt (canonicalFactor R z) x) to Int using
      (meromorphicOrderAt_canonicalFactor_ne_top z (pos_of_mem_ball hx)) with ℓ
    simp [← WithTop.coe_mul]
-/
private lemma canonicalDecomposition_aux₂ (h₁f : MeromorphicOn f (closedBall 0 R)) :
    divisor (∏ᶠ u, (canonicalFactor R u) ^ (divisor f (ball 0 R) u)) (ball 0 R)
      = -(divisor f (ball 0 R)) := by
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]; rw [divisor_prod]
  · simp_rw [divisor_zpow (fun z hz => meromorphic_canonicalFactor R _ z)]
    conv_rhs => rw [← sum_apply_smul_single_eq_self η₀]
    apply Finset.sum_congr rfl fun x hx => ?_
    rw [divisor_canonicalFactor]; rw [smul_neg]; rw [locallyFinsuppWithin.coe_neg]; rw [Pi.neg_apply]; rw [neg_smul]
    by_contra
    simp_all
  · intro z hz
    apply zpow (fun x hx => meromorphic_canonicalFactor R z x)
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R z x)]
    lift (meromorphicOrderAt (canonicalFactor R z) x) to Int using
      (meromorphicOrderAt_canonicalFactor_ne_top z (pos_of_mem_ball hx)) with ℓ
    simp [← WithTop.coe_mul]

-- Auxiliary lemma for the proof of the canonical decomposition theorem: The (inverse of the) factor
-- in the canonical decomposition does not vanish identically.
/--
lemma `canonicalDecomposition_aux₃` / 引理 `canonicalDecomposition_aux₃`

English:
lemma canonicalDecomposition_aux₃
  given: {z : Complex} (hR : 0 < R)
  proof: by
  apply meromorphicOrderAt_finprod_ne_top
    (fun _ => MeromorphicAt.zpow (meromorphic_canonicalFactor _ _ _) _)
  intro c
  rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R c z)]
  lift meromorphicOrderAt (canonicalFactor R c) z to Int using
    (meromorphicOrderAt_canonicalFactor_ne_top c hR) with ℓ
  simp [← WithTop.coe_mul]

中文:
引理 canonicalDecomposition_aux₃
  条件: {z : 复形} (hR : 0 < R)
  证明: by
  apply meromorphicOrderAt_finprod_ne_top
    (fun _ => MeromorphicAt.zpow (meromorphic_canonicalFactor _ _ _) _)
  intro c
  rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R c z)]
  lift meromorphicOrderAt (canonicalFactor R c) z to Int using
    (meromorphicOrderAt_canonicalFactor_ne_top c hR) with ℓ
  simp [← WithTop.coe_mul]
-/
private lemma canonicalDecomposition_aux₃ {z : Complex} (hR : 0 < R) :
    meromorphicOrderAt (∏ᶠ (c : Complex), canonicalFactor R c ^ (divisor f (ball 0 R)) c) z != ⊤ := by
  apply meromorphicOrderAt_finprod_ne_top
    (fun _ => MeromorphicAt.zpow (meromorphic_canonicalFactor _ _ _) _)
  intro c
  rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R c z)]
  lift meromorphicOrderAt (canonicalFactor R c) z to Int using
    (meromorphicOrderAt_canonicalFactor_ne_top c hR) with ℓ
  simp [← WithTop.coe_mul]

/--
theorem `_root_.MeromorphicOn.exists_canonicalDecomp` / 定理 `_root_.MeromorphicOn.exists_canonicalDecomp`

English:
theorem _root_.MeromorphicOn.exists_canonicalDecomp
  proof: by
  -- Trivial case: If `R` is non-positive, then the ball is empty.
  by_cases hR : R <= 0
  · use fun _ => f 0
    exact {
      meromorphicOn := h₁f
      meromorphicNFOn := fun z hz => AnalyticAt.meromorphicNFAt analyticAt_const
      ne_zero := by simp [ball_eq_empty.2 hR]
      eventuallyEq := by
        filter_upwards [self_mem_codiscreteWithin (closedBall 0 R)] with a ha
        have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
        aesop
    }
  rw [not_le] at hR
  -- General case: The requirement that `f =ᶠ[…] (something) • g` implies that `g` must equal
  -- `(something)⁻¹ • g`, converted to a meromorphic function in normal form. The next lines define
  -- `g` in this way and establish basic properties.
  let φ := (∏ᶠ c, canonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply smul (MeromorphicOn.finprod _) h₁f
    exact fun z => zpow (fun z₁ hz₁ => meromorphic_canonicalFactor _ _ _) _
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin_mono ball_subset_closedBall)) isOpen_ball]; rw [divisor_smul _ (fun x hx => h₁f x (ball_subset_closedBall hx))
        (fun z _ => canonicalDecomposition_aux₃ hR)
        (fun z hz => h₂f ⟨z]; rw [ball_subset_closedBall hz⟩)]; rw [canonicalDecomposition_aux₂ h₁f]; rw [neg_add_cancel]
    apply (canonicalDecomposition_aux₁ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g {z : Complex} (hz : z in closedBall 0 R) : meromorphicOrderAt g z != ⊤ := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ hz]; rw [meromorphicOrderAt_smul _ (h₁f z hz)]
    · simpa [h₂f ⟨z, hz⟩] using canonicalDecomposition_aux₃ hR
    · apply MeromorphicAt.finprod (fun x => (meromorphic_canonicalFactor R x z).zpow _)
  -- Use the function `g` defined above and establish the required properties
  use g
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  exact {
    meromorphicOn := h₁f
    meromorphicNFOn := meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
    ne_zero := by
      intro z hz
      rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (h₂g (ball_subset_closedBall hz))]
      have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
      rw [divisor_apply (fun x hx => (h₂g (ball_subset_closedBall hx)).meromorphicAt) hz] at this
      simpa [h₄g (ball_subset_closedBall hz)] using this
    eventuallyEq := by
      trans (∏ i in η₀.toFinset, canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
      · unfold φ
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        · filter_upwards [codiscreteWithin_mono (by tauto) η₀.compl_mem_codiscrete,
            self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
          simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
          rw [← smul_assoc]; rw [← Finset.prod_smul]; rw [Finset.prod_eq_one]; rw [one_smul]
          intro x hx
          rw [smul_eq_mul]; rw [← zpow_add']; rw [neg_add_cancel]; rw [zpow_zero]
          simp_all only [ne_eq, Subtype.forall, mem_closedBall, dist_zero_right,
            locallyFinsuppWithin.support_neg, mem_compl_iff, mem_support, Decidable.not_not,
            Finite.mem_toFinset, neg_add_cancel, not_true_eq_false, neg_eq_zero, and_self, or_self,
            or_false]
          apply canonicalFactor_ne_zero _ (by simp_all) (by grind)
          by_contra h
          simp_all
      · rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] using by simp_all [g]
  }

中文:
定理 _root_.MeromorphicOn.存在_canonicalDecomp
  证明: by
  -- Trivial case: If `R` is non-positive, then the ball is empty.
  by_cases hR : R <= 0
  · use fun _ => f 0
    exact {
      meromorphicOn := h₁f
      meromorphicNFOn := fun z hz => AnalyticAt.meromorphicNFAt analyticAt_const
      ne_zero := by simp [ball_eq_empty.2 hR]
      eventuallyEq := by
        filter_upwards [self_mem_codiscreteWithin (closedBall 0 R)] with a ha
        have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
        aesop
    }
  rw [not_le] at hR
  -- General case: The requirement that `f =ᶠ[…] (something) • g` implies that `g` must equal
  -- `(something)⁻¹ • g`, converted to a meromorphic function in normal form. The next lines define
  -- `g` in this way and establish basic properties.
  let φ := (∏ᶠ c, canonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply smul (MeromorphicOn.finprod _) h₁f
    exact fun z => zpow (fun z₁ hz₁ => meromorphic_canonicalFactor _ _ _) _
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin_mono ball_subset_closedBall)) isOpen_ball]; rw [divisor_smul _ (fun x hx => h₁f x (ball_subset_closedBall hx))
        (fun z _ => canonicalDecomposition_aux₃ hR)
        (fun z hz => h₂f ⟨z]; rw [ball_subset_closedBall hz⟩)]; rw [canonicalDecomposition_aux₂ h₁f]; rw [neg_add_cancel]
    apply (canonicalDecomposition_aux₁ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g {z : Complex} (hz : z in closedBall 0 R) : meromorphicOrderAt g z != ⊤ := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ hz]; rw [meromorphicOrderAt_smul _ (h₁f z hz)]
    · simpa [h₂f ⟨z, hz⟩] using canonicalDecomposition_aux₃ hR
    · apply MeromorphicAt.finprod (fun x => (meromorphic_canonicalFactor R x z).zpow _)
  -- Use the function `g` defined above and establish the required properties
  use g
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  exact {
    meromorphicOn := h₁f
    meromorphicNFOn := meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
    ne_zero := by
      intro z hz
      rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (h₂g (ball_subset_closedBall hz))]
      have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
      rw [divisor_apply (fun x hx => (h₂g (ball_subset_closedBall hx)).meromorphicAt) hz] at this
      simpa [h₄g (ball_subset_closedBall hz)] using this
    eventuallyEq := by
      trans (∏ i in η₀.toFinset, canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
      · unfold φ
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        · filter_upwards [codiscreteWithin_mono (by tauto) η₀.compl_mem_codiscrete,
            self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
          simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
          rw [← smul_assoc]; rw [← Finset.prod_smul]; rw [Finset.prod_eq_one]; rw [one_smul]
          intro x hx
          rw [smul_eq_mul]; rw [← zpow_add']; rw [neg_add_cancel]; rw [zpow_zero]
          simp_all only [ne_eq, Subtype.forall, mem_closedBall, dist_zero_right,
            locallyFinsuppWithin.support_neg, mem_compl_iff, mem_support, Decidable.not_not,
            Finite.mem_toFinset, neg_add_cancel, not_true_eq_false, neg_eq_zero, and_self, or_self,
            or_false]
          apply canonicalFactor_ne_zero _ (by simp_all) (by grind)
          by_contra h
          simp_all
      · rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] using by simp_all [g]
  }
-/
theorem _root_.MeromorphicOn.exists_canonicalDecomp
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : forall u : (closedBall (0 : Complex) R), meromorphicOrderAt f u != ⊤) :
    exists g : Complex -> E, CanonicalDecomp f g R := by
  -- Trivial case: If `R` is non-positive, then the ball is empty.
  by_cases hR : R <= 0
  · use fun _ => f 0
    exact {
      meromorphicOn := h₁f
      meromorphicNFOn := fun z hz => AnalyticAt.meromorphicNFAt analyticAt_const
      ne_zero := by simp [ball_eq_empty.2 hR]
      eventuallyEq := by
        filter_upwards [self_mem_codiscreteWithin (closedBall 0 R)] with a ha
        have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
        aesop
    }
  rw [not_le] at hR
  -- General case: The requirement that `f =ᶠ[…] (something) • g` implies that `g` must equal
  -- `(something)⁻¹ • g`, converted to a meromorphic function in normal form. The next lines define
  -- `g` in this way and establish basic properties.
  let φ := (∏ᶠ c, canonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply smul (MeromorphicOn.finprod _) h₁f
    exact fun z => zpow (fun z₁ hz₁ => meromorphic_canonicalFactor _ _ _) _
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin_mono ball_subset_closedBall)) isOpen_ball]; rw [divisor_smul _ (fun x hx => h₁f x (ball_subset_closedBall hx))
        (fun z _ => canonicalDecomposition_aux₃ hR)
        (fun z hz => h₂f ⟨z]; rw [ball_subset_closedBall hz⟩)]; rw [canonicalDecomposition_aux₂ h₁f]; rw [neg_add_cancel]
    apply (canonicalDecomposition_aux₁ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g {z : Complex} (hz : z in closedBall 0 R) : meromorphicOrderAt g z != ⊤ := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ hz]; rw [meromorphicOrderAt_smul _ (h₁f z hz)]
    · simpa [h₂f ⟨z, hz⟩] using canonicalDecomposition_aux₃ hR
    · apply MeromorphicAt.finprod (fun x => (meromorphic_canonicalFactor R x z).zpow _)
  -- Use the function `g` defined above and establish the required properties
  use g
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  exact {
    meromorphicOn := h₁f
    meromorphicNFOn := meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
    ne_zero := by
      intro z hz
      rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (h₂g (ball_subset_closedBall hz))]
      have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
      rw [divisor_apply (fun x hx => (h₂g (ball_subset_closedBall hx)).meromorphicAt) hz] at this
      simpa [h₄g (ball_subset_closedBall hz)] using this
    eventuallyEq := by
      trans (∏ i in η₀.toFinset, canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
      · unfold φ
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        · filter_upwards [codiscreteWithin_mono (by tauto) η₀.compl_mem_codiscrete,
            self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
          simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
          rw [← smul_assoc]; rw [← Finset.prod_smul]; rw [Finset.prod_eq_one]; rw [one_smul]
          intro x hx
          rw [smul_eq_mul]; rw [← zpow_add']; rw [neg_add_cancel]; rw [zpow_zero]
          simp_all only [ne_eq, Subtype.forall, mem_closedBall, dist_zero_right,
            locallyFinsuppWithin.support_neg, mem_compl_iff, mem_support, Decidable.not_not,
            Finite.mem_toFinset, neg_add_cancel, not_true_eq_false, neg_eq_zero, and_self, or_self,
            or_false]
          apply canonicalFactor_ne_zero _ (by simp_all) (by grind)
          by_contra h
          simp_all
      · rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] using by simp_all [g]
  }

/--
theorem `CanonicalDecomp.divisor_eq_divisor` / 定理 `CanonicalDecomp.divisor_eq_divisor`

English:
theorem CanonicalDecomp.divisor_eq_divisor
  given: {x : Complex} (D : CanonicalDecomp f g R) (hR : 0 < R)
  proof: by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · -- The case where `x` is contained in `ball 0 R`. There, the divisor of `g` vanishes because `g`
    -- does not have zeros or poles. The divisor of `f` vanishes because `x` is not contained in the
    -- sphere.
    have : x ∉ sphere (0 : Complex) R := by aesop
    have := (D.meromorphicNFOn (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2
      (D.ne_zero x (by aesop))
    rw [divisor_apply D.meromorphicNFOn.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · -- The case where `x` is contained in `sphere 0 R`. There, the orders of `f` and `g` agree
    -- because the canonical factors are analytic and do not vanish.
    have η₁ : AnalyticAt Complex (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      refine analyticAt_finprod fun a => ?_
      by_cases ha : a in ball 0 R
      · exact (analyticOnNhd_canonicalFactor _ _ _ (by aesop)).zpow
          (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all only [mem_ball, dist_zero_right, not_lt,
          locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
        exact analyticAt_const
    have η₀ : f =ᶠ[𝓝[!=] x] (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      refine MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := closedBall 0 R) (D.meromorphicOn x (by aesop))
        (η₁.meromorphicAt.smul (D.meromorphicNFOn.meromorphicOn x (by aesop))) (by aesop) ?_
        D.eventuallyEq
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2
    have : meromorphicOrderAt (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      refine η₁.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (finprod_apply_ne_zero fun a => ?_)
      by_cases ha : a in ball 0 R
      · exact zpow_ne_zero _ (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all
    rw [divisor_apply (D.meromorphicOn.mono_set sphere_subset_closedBall) (by aesop)]; rw [divisor_apply D.meromorphicNFOn.meromorphicOn (by aesop)]; rw [meromorphicOrderAt_congr η₀]; rw [meromorphicOrderAt_smul η₁.meromorphicAt (D.meromorphicNFOn (by aesop)).meromorphicAt]
    simp_all
  · -- Trivial case: `x` is outside `closedBall 0 R`, so both divisors evaluate to zero.
    have : x ∉ sphere (0 : Complex) R := by aesop
    simp_all

中文:
定理 CanonicalDecomp.divisor_eq_divisor
  条件: {x : 复形} (D : CanonicalDecomp f g R) (hR : 0 < R)
  证明: by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · -- The case where `x` is contained in `ball 0 R`. There, the divisor of `g` vanishes because `g`
    -- does not have zeros or poles. The divisor of `f` vanishes because `x` is not contained in the
    -- sphere.
    have : x ∉ sphere (0 : Complex) R := by aesop
    have := (D.meromorphicNFOn (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2
      (D.ne_zero x (by aesop))
    rw [divisor_apply D.meromorphicNFOn.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · -- The case where `x` is contained in `sphere 0 R`. There, the orders of `f` and `g` agree
    -- because the canonical factors are analytic and do not vanish.
    have η₁ : AnalyticAt Complex (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      refine analyticAt_finprod fun a => ?_
      by_cases ha : a in ball 0 R
      · exact (analyticOnNhd_canonicalFactor _ _ _ (by aesop)).zpow
          (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all only [mem_ball, dist_zero_right, not_lt,
          locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
        exact analyticAt_const
    have η₀ : f =ᶠ[𝓝[!=] x] (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      refine MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := closedBall 0 R) (D.meromorphicOn x (by aesop))
        (η₁.meromorphicAt.smul (D.meromorphicNFOn.meromorphicOn x (by aesop))) (by aesop) ?_
        D.eventuallyEq
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2
    have : meromorphicOrderAt (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      refine η₁.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (finprod_apply_ne_zero fun a => ?_)
      by_cases ha : a in ball 0 R
      · exact zpow_ne_zero _ (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all
    rw [divisor_apply (D.meromorphicOn.mono_set sphere_subset_closedBall) (by aesop)]; rw [divisor_apply D.meromorphicNFOn.meromorphicOn (by aesop)]; rw [meromorphicOrderAt_congr η₀]; rw [meromorphicOrderAt_smul η₁.meromorphicAt (D.meromorphicNFOn (by aesop)).meromorphicAt]
    simp_all
  · -- Trivial case: `x` is outside `closedBall 0 R`, so both divisors evaluate to zero.
    have : x ∉ sphere (0 : Complex) R := by aesop
    simp_all

Depends on / 依赖: because, contained, divisor, lt_trichotomy, vanishes
-/
theorem CanonicalDecomp.divisor_eq_divisor {x : Complex} (D : CanonicalDecomp f g R) (hR : 0 < R) :
    divisor g (closedBall (0 : Complex) R) x = divisor f (sphere 0 R) x := by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · -- The case where `x` is contained in `ball 0 R`. There, the divisor of `g` vanishes because `g`
    -- does not have zeros or poles. The divisor of `f` vanishes because `x` is not contained in the
    -- sphere.
    have : x ∉ sphere (0 : Complex) R := by aesop
    have := (D.meromorphicNFOn (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2
      (D.ne_zero x (by aesop))
    rw [divisor_apply D.meromorphicNFOn.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · -- The case where `x` is contained in `sphere 0 R`. There, the orders of `f` and `g` agree
    -- because the canonical factors are analytic and do not vanish.
    have η₁ : AnalyticAt Complex (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      refine analyticAt_finprod fun a => ?_
      by_cases ha : a in ball 0 R
      · exact (analyticOnNhd_canonicalFactor _ _ _ (by aesop)).zpow
          (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all only [mem_ball, dist_zero_right, not_lt,
          locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
        exact analyticAt_const
    have η₀ : f =ᶠ[𝓝[!=] x] (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      refine MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := closedBall 0 R) (D.meromorphicOn x (by aesop))
        (η₁.meromorphicAt.smul (D.meromorphicNFOn.meromorphicOn x (by aesop))) (by aesop) ?_
        D.eventuallyEq
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2
    have : meromorphicOrderAt (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      refine η₁.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (finprod_apply_ne_zero fun a => ?_)
      by_cases ha : a in ball 0 R
      · exact zpow_ne_zero _ (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all
    rw [divisor_apply (D.meromorphicOn.mono_set sphere_subset_closedBall) (by aesop)]; rw [divisor_apply D.meromorphicNFOn.meromorphicOn (by aesop)]; rw [meromorphicOrderAt_congr η₀]; rw [meromorphicOrderAt_smul η₁.meromorphicAt (D.meromorphicNFOn (by aesop)).meromorphicAt]
    simp_all
  · -- Trivial case: `x` is outside `closedBall 0 R`, so both divisors evaluate to zero.
    have : x ∉ sphere (0 : Complex) R := by aesop
    simp_all

/-!
## Extended Canonical Decomposition

The extended canonical decomposition theorem shows that a meromorphic function `f` on a closed disk
is equal, up to modification over a discrete set, to a product of a non-vanishing analytic function,
canonical factors and meromorphic functions of the form `(x - const) ^ n` where `const` is on the
circumference of the disk.

To simplify notation and avoid repetition, we introduce a structure, `ECanonicalDecomp`, that
bundles the conclusions of the extended canonical decomposition theorem.
-/

/--
Definition of `ECanonicalDecomp` / `ECanonicalDecomp` 的定义

English:
structure ECanonicalDecomp
  parameters: (f g : Complex -> E) (R : Real)
  axioms and operations (4):
    - meromorphicOn : MeromorphicOn f (closedBall 0 R)
    - analyticOnNhd : AnalyticOnNhd Complex g (closedBall 0 R)
    - ne_zero : forall u in (closedBall 0 R), g u != 0
    - eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)] ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) * (∏ᶠ v, (· - v) ^ (divisor f (sphere 0 R)) v)) • g

中文:
结构 ECanonicalDecomp
  参数: (f g : 复形 -> E) (R : 实数)
  公理与运算 (4 个):
    - meromorphicOn : MeromorphicOn f (closedBall 0 R)
    - analyticOnNhd : AnalyticOnNhd 复形 g (closedBall 0 R)
    - ne_zero : 对任意 u in (closedBall 0 R), g u != 0
    - eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)] ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) * (∏ᶠ v, (· - v) ^ (divisor f (sphere 0 R)) v)) • g
-/
structure ECanonicalDecomp (f g : Complex -> E) (R : Real) where
  /-- A proof that `f` is meromorphic on `closedBall 0 R`. -/
  meromorphicOn : MeromorphicOn f (closedBall 0 R)
  /-- A proof that `g` is analytic in a neighborhood of `closedBall 0 R`. -/
  analyticOnNhd : AnalyticOnNhd Complex g (closedBall 0 R)
  /-- A proof that `g` does not vanish on the closed ball. -/
  ne_zero : forall u in (closedBall 0 R), g u != 0
  /--
  A proof that `f` is equal, up to modification over a discrete set, to a product of `g`, canonical
  factors prescribed by the divisor of `f`, and a factorized rational function with poles and zeros
  only on the boundary of the ball.
  -/
  eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)]
    ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
    * (∏ᶠ v, (· - v) ^ (divisor f (sphere 0 R)) v)) • g

/--
theorem `_root_.MeromorphicOn.exists_ecanonicalDecomp` / 定理 `_root_.MeromorphicOn.exists_ecanonicalDecomp`

English:
theorem _root_.MeromorphicOn.exists_ecanonicalDecomp
  statement: (h₁f : MeromorphicOn f (closedBall 0 R))
  proof: by
  rcases gt_trichotomy 0 R with hR | hR | hR
  · use fun _ => f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd := by simp_all
      ne_zero := by simp_all
      eventuallyEq := by
        simp_all only [closedBall_of_neg]
        filter_upwards [Filter.self_mem_codiscreteWithin ∅] with a ha
        tauto
    }
  · use fun _ => meromorphicTrailingCoeffAt f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd _ _ := by fun_prop
      ne_zero := by
        simp only [hR.symm, closedBall_zero, mem_singleton_iff, ne_eq, forall_eq]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁f 0 _) _
        <;> simp_all
      eventuallyEq := by
        simp only [hR.symm, closedBall_zero]
        apply subsingleton_singleton.mem_codiscreteWithin
    }
  obtain ⟨g, D⟩ := h₁f.exists_canonicalDecomp h₂f
  have h₄g : forall (u : closedBall (0 : Complex) R), meromorphicOrderAt g u != ⊤ := by
    rw [← D.meromorphicNFOn.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)]
    have s₁ : (0 : Complex) in closedBall 0 R := by simp [hR.le]
    use ⟨0, s₁⟩
    simp [(D.meromorphicNFOn s₁).meromorphicOrderAt_eq_zero_iff.2 (D.ne_zero 0 (by simp [hR]))]
obtain ⟨h, h₁h, h₂h, h₃h⟩ := D.meromorphicNFOn.meromorphicOn.extract_zeros_poles h₄g
(divisor g (closedBall 0 R)).finiteSupport isCompact_closedBall 0 R
  use h
  exact {
    meromorphicOn := h₁f
    analyticOnNhd := h₁h
    ne_zero := (h₂h ⟨·, ·⟩)
    eventuallyEq := by
      filter_upwards [D.eventuallyEq, h₃h] with a h₁a h₂a
      simp_rw [← D.divisor_eq_divisor hR]
      simp_all [← smul_assoc]
    }

中文:
定理 _root_.MeromorphicOn.存在_ecanonicalDecomp
  结论: (h₁f : MeromorphicOn f (closedBall 0 R))
  证明: by
  rcases gt_trichotomy 0 R with hR | hR | hR
  · use fun _ => f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd := by simp_all
      ne_zero := by simp_all
      eventuallyEq := by
        simp_all only [closedBall_of_neg]
        filter_upwards [Filter.self_mem_codiscreteWithin ∅] with a ha
        tauto
    }
  · use fun _ => meromorphicTrailingCoeffAt f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd _ _ := by fun_prop
      ne_zero := by
        simp only [hR.symm, closedBall_zero, mem_singleton_iff, ne_eq, forall_eq]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁f 0 _) _
        <;> simp_all
      eventuallyEq := by
        simp only [hR.symm, closedBall_zero]
        apply subsingleton_singleton.mem_codiscreteWithin
    }
  obtain ⟨g, D⟩ := h₁f.exists_canonicalDecomp h₂f
  have h₄g : forall (u : closedBall (0 : Complex) R), meromorphicOrderAt g u != ⊤ := by
    rw [← D.meromorphicNFOn.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)]
    have s₁ : (0 : Complex) in closedBall 0 R := by simp [hR.le]
    use ⟨0, s₁⟩
    simp [(D.meromorphicNFOn s₁).meromorphicOrderAt_eq_zero_iff.2 (D.ne_zero 0 (by simp [hR]))]
obtain ⟨h, h₁h, h₂h, h₃h⟩ := D.meromorphicNFOn.meromorphicOn.extract_zeros_poles h₄g
(divisor g (closedBall 0 R)).finiteSupport isCompact_closedBall 0 R
  use h
  exact {
    meromorphicOn := h₁f
    analyticOnNhd := h₁h
    ne_zero := (h₂h ⟨·, ·⟩)
    eventuallyEq := by
      filter_upwards [D.eventuallyEq, h₃h] with a h₁a h₂a
      simp_rw [← D.divisor_eq_divisor hR]
      simp_all [← smul_assoc]
    }

Depends on / 依赖: Filter, Filter.self_mem_codiscreteWithin, MeromorphicAt, analyticOnNhd, closedBall_of_neg, closedBall_zero, eventuallyEq, filter_upwards, forall_eq, fun_prop, gt_trichotomy, hR.symm, mem_singleton_iff, meromorphicOn, meromorphicTrailingCoeffAt, ne_eq, ne_zero, self_mem_codiscreteWithin
-/
theorem _root_.MeromorphicOn.exists_ecanonicalDecomp (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : forall u : (closedBall (0 : Complex) R), meromorphicOrderAt f u != ⊤) :
    exists h, ECanonicalDecomp f h R := by
  rcases gt_trichotomy 0 R with hR | hR | hR
  · use fun _ => f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd := by simp_all
      ne_zero := by simp_all
      eventuallyEq := by
        simp_all only [closedBall_of_neg]
        filter_upwards [Filter.self_mem_codiscreteWithin ∅] with a ha
        tauto
    }
  · use fun _ => meromorphicTrailingCoeffAt f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd _ _ := by fun_prop
      ne_zero := by
        simp only [hR.symm, closedBall_zero, mem_singleton_iff, ne_eq, forall_eq]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁f 0 _) _
        <;> simp_all
      eventuallyEq := by
        simp only [hR.symm, closedBall_zero]
        apply subsingleton_singleton.mem_codiscreteWithin
    }
  obtain ⟨g, D⟩ := h₁f.exists_canonicalDecomp h₂f
  have h₄g : forall (u : closedBall (0 : Complex) R), meromorphicOrderAt g u != ⊤ := by
    rw [← D.meromorphicNFOn.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)]
    have s₁ : (0 : Complex) in closedBall 0 R := by simp [hR.le]
    use ⟨0, s₁⟩
    simp [(D.meromorphicNFOn s₁).meromorphicOrderAt_eq_zero_iff.2 (D.ne_zero 0 (by simp [hR]))]
obtain ⟨h, h₁h, h₂h, h₃h⟩ := D.meromorphicNFOn.meromorphicOn.extract_zeros_poles h₄g
(divisor g (closedBall 0 R)).finiteSupport isCompact_closedBall 0 R
  use h
  exact {
    meromorphicOn := h₁f
    analyticOnNhd := h₁h
    ne_zero := (h₂h ⟨·, ·⟩)
    eventuallyEq := by
      filter_upwards [D.eventuallyEq, h₃h] with a h₁a h₂a
      simp_rw [← D.divisor_eq_divisor hR]
      simp_all [← smul_assoc]
    }

/--
lemma `mulSupport_pow_subset_support` / 引理 `mulSupport_pow_subset_support`

English:
lemma mulSupport_pow_subset_support
  statement: {α β : Type*} [DivInvMonoid α] (f : β -> α)
  proof: by
  simp only [mulSupport_subset_iff, ne_eq, mem_support]
  intro
  contrapose!
  simp +contextual

中文:
引理 mulSupport_pow_subset_support
  结论: {α β : 类型} [除逆幺半群 α] (f : β -> α)
  证明: by
  simp only [mulSupport_subset_iff, ne_eq, mem_support]
  intro
  contrapose!
  simp +contextual
-/
private lemma mulSupport_pow_subset_support {α β : Type*} [DivInvMonoid α] (f : β -> α)
    (g : β -> Int) : (fun x => f x ^ g x).mulSupport subseteq g.support := by
  simp only [mulSupport_subset_iff, ne_eq, mem_support]
  intro
  contrapose!
  simp +contextual

/--
lemma `ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt` / 引理 `ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt`

English:
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt
  proof: by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : Complex) R
  let S₀R := sphere (0 : Complex) R
  lift (divisor f S₀R).support to Finset Complex using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset Complex using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  have := (D.analyticOnNhd w hw).meromorphicAt
  rw [Eq.comm]
  -- Proof body: Substitute `f` using `h₁f` and compute
  calc ((∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt f w
    _ = ((∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ᶠ (u : Complex), canonicalFactor R u ^ (-(divisor f B₀R) u))
        * ∏ᶠ (v : Complex), (· - v) ^ (divisor f S₀R) v) • h) w := by
      rw [meromorphicTrailingCoeffAt_congr_nhdsNE
        ((D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (by fun_prop) hw ?η₁ D.eventuallyEq)]
      case η₁ =>
        rw [← closure_ball _ hR.ne']
        exact isOpen_ball.perfect_closure.2
    _ = ((∏ i in t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i in t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ i in t₂, canonicalFactor R i ^ (-(divisor f B₀R) i))
        * ∏ i in t₁, (· - i) ^ (divisor f S₀R) i) • h) w := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ((∏ i in t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i in t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • ((∏ n in t₂, meromorphicTrailingCoeffAt (canonicalFactor R n ^ (-(divisor f B₀R) n)) w)
        * ∏ n in t₁, meromorphicTrailingCoeffAt ((· - n) ^ (divisor f S₀R) n) w)
      • h w := by
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
        (D.analyticOnNhd w hw).meromorphicAt]; rw [MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop)]; rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]; rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]; rw [(D.analyticOnNhd w hw).meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw)]
    _ = h w := by
      rw [smul_smul]; rw [mul_mul_mul_comm]; rw [← Finset.prod_mul_distrib]; rw [← Finset.prod_mul_distrib]; rw [Finset.prod_eq_one ?η₁]; rw [Finset.prod_eq_one ?η₂]; rw [mul_one]; rw [one_smul]
      case η₁ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]; rw [← zpow_add₀]; rw [add_neg_cancel]; rw [zpow_zero]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
          (meromorphicOrderAt_canonicalFactor_ne_top x hR)
      case η₂ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]; rw [← zpow_add₀]; rw [locallyFinsuppWithin.coe_neg]; rw [Pi.neg_apply]; rw [neg_add_cancel]; rw [zpow_zero]
        rw [meromorphicTrailingCoeffAt_id_sub_const]
        grind

中文:
引理 ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt
  证明: by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : Complex) R
  let S₀R := sphere (0 : Complex) R
  lift (divisor f S₀R).support to Finset Complex using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset Complex using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  have := (D.analyticOnNhd w hw).meromorphicAt
  rw [Eq.comm]
  -- Proof body: Substitute `f` using `h₁f` and compute
  calc ((∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt f w
    _ = ((∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ᶠ (u : Complex), canonicalFactor R u ^ (-(divisor f B₀R) u))
        * ∏ᶠ (v : Complex), (· - v) ^ (divisor f S₀R) v) • h) w := by
      rw [meromorphicTrailingCoeffAt_congr_nhdsNE
        ((D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (by fun_prop) hw ?η₁ D.eventuallyEq)]
      case η₁ =>
        rw [← closure_ball _ hR.ne']
        exact isOpen_ball.perfect_closure.2
    _ = ((∏ i in t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i in t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ i in t₂, canonicalFactor R i ^ (-(divisor f B₀R) i))
        * ∏ i in t₁, (· - i) ^ (divisor f S₀R) i) • h) w := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ((∏ i in t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i in t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • ((∏ n in t₂, meromorphicTrailingCoeffAt (canonicalFactor R n ^ (-(divisor f B₀R) n)) w)
        * ∏ n in t₁, meromorphicTrailingCoeffAt ((· - n) ^ (divisor f S₀R) n) w)
      • h w := by
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
        (D.analyticOnNhd w hw).meromorphicAt]; rw [MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop)]; rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]; rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]; rw [(D.analyticOnNhd w hw).meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw)]
    _ = h w := by
      rw [smul_smul]; rw [mul_mul_mul_comm]; rw [← Finset.prod_mul_distrib]; rw [← Finset.prod_mul_distrib]; rw [Finset.prod_eq_one ?η₁]; rw [Finset.prod_eq_one ?η₂]; rw [mul_one]; rw [one_smul]
      case η₁ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]; rw [← zpow_add₀]; rw [add_neg_cancel]; rw [zpow_zero]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
          (meromorphicOrderAt_canonicalFactor_ne_top x hR)
      case η₂ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]; rw [← zpow_add₀]; rw [locallyFinsuppWithin.coe_neg]; rw [Pi.neg_apply]; rw [neg_add_cancel]; rw [zpow_zero]
        rw [meromorphicTrailingCoeffAt_id_sub_const]
        grind
-/
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt
    {f h : Complex -> E} (D : ECanonicalDecomp f h R) (hw : w in closedBall 0 R) (hR : 0 < R) :
    h w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : Complex) R
  let S₀R := sphere (0 : Complex) R
  lift (divisor f S₀R).support to Finset Complex using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset Complex using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  have := (D.analyticOnNhd w hw).meromorphicAt
  rw [Eq.comm]
  -- Proof body: Substitute `f` using `h₁f` and compute
  calc ((∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt f w
    _ = ((∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : Complex), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ᶠ (u : Complex), canonicalFactor R u ^ (-(divisor f B₀R) u))
        * ∏ᶠ (v : Complex), (· - v) ^ (divisor f S₀R) v) • h) w := by
      rw [meromorphicTrailingCoeffAt_congr_nhdsNE
        ((D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (by fun_prop) hw ?η₁ D.eventuallyEq)]
      case η₁ =>
        rw [← closure_ball _ hR.ne']
        exact isOpen_ball.perfect_closure.2
    _ = ((∏ i in t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i in t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ i in t₂, canonicalFactor R i ^ (-(divisor f B₀R) i))
        * ∏ i in t₁, (· - i) ^ (divisor f S₀R) i) • h) w := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ((∏ i in t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i in t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • ((∏ n in t₂, meromorphicTrailingCoeffAt (canonicalFactor R n ^ (-(divisor f B₀R) n)) w)
        * ∏ n in t₁, meromorphicTrailingCoeffAt ((· - n) ^ (divisor f S₀R) n) w)
      • h w := by
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
        (D.analyticOnNhd w hw).meromorphicAt]; rw [MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop)]; rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]; rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]; rw [(D.analyticOnNhd w hw).meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw)]
    _ = h w := by
      rw [smul_smul]; rw [mul_mul_mul_comm]; rw [← Finset.prod_mul_distrib]; rw [← Finset.prod_mul_distrib]; rw [Finset.prod_eq_one ?η₁]; rw [Finset.prod_eq_one ?η₂]; rw [mul_one]; rw [one_smul]
      case η₁ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]; rw [← zpow_add₀]; rw [add_neg_cancel]; rw [zpow_zero]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
          (meromorphicOrderAt_canonicalFactor_ne_top x hR)
      case η₂ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]; rw [← zpow_add₀]; rw [locallyFinsuppWithin.coe_neg]; rw [Pi.neg_apply]; rw [neg_add_cancel]; rw [zpow_zero]
        rw [meromorphicTrailingCoeffAt_id_sub_const]
        grind

/--
lemma `ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt` / 引理 `ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt`

English:
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
  proof: by
  rw [D.eq_smul_meromorphicTrailingCoeffAt h₁w hR]
  congr! 4 with x x
  · by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp [h₃x]
    have h₁x : x in ball 0 R := (divisor f (ball 0 R)).supportWithinDomain h₃x
    have h₂x : w != x := by
      rintro rfl
      exact h₃x (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁x, h₂w])
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w h₂x)
      (Complex.canonicalFactor_ne_zero h₁x h₁w h₂x)]
  · by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]

中文:
引理 ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
  证明: by
  rw [D.eq_smul_meromorphicTrailingCoeffAt h₁w hR]
  congr! 4 with x x
  · by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp [h₃x]
    have h₁x : x in ball 0 R := (divisor f (ball 0 R)).supportWithinDomain h₃x
    have h₂x : w != x := by
      rintro rfl
      exact h₃x (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁x, h₂w])
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w h₂x)
      (Complex.canonicalFactor_ne_zero h₁x h₁w h₂x)]
  · by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]

Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero, Complex.analyticOnNhd_canonicalFactor, Complex.canonicalFactor_ne_zero, D.eq_smul_meromorphicTrailingCoeffAt, D.meromorphicOn.mono_set, analyticOnNhd_canonicalFactor, ball_subset_closedBall, canonicalFactor_ne_zero, divisor, divisor_apply, eq_smul_meromorphicTrailingCoeffAt, meromorphicOn, meromorphicTrailingCoeffAt_of_ne_zero, mono_set, supportWithinDomain
-/
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
    {f h : Complex -> E} (D : ECanonicalDecomp f h R) (h₁w : w in closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0) (hR : 0 < R) :
    h w = ((∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  rw [D.eq_smul_meromorphicTrailingCoeffAt h₁w hR]
  congr! 4 with x x
  · by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp [h₃x]
    have h₁x : x in ball 0 R := (divisor f (ball 0 R)).supportWithinDomain h₃x
    have h₂x : w != x := by
      rintro rfl
      exact h₃x (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁x, h₂w])
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w h₂x)
      (Complex.canonicalFactor_ne_zero h₁x h₁w h₂x)]
  · by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]

/--
lemma `ECanonicalDecomp.log_norm_eq` / 引理 `ECanonicalDecomp.log_norm_eq`

English:
lemma ECanonicalDecomp.log_norm_eq
  proof: by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : Complex) R
  let S₀R := sphere (0 : Complex) R
  lift (divisor f S₀R).support to Finset Complex using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset Complex using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  calc Real.log ‖h w‖
    _ = log ‖((∏ᶠ (i : Complex), canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ᶠ (i : Complex), (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        h₁w h₂w hR]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ (by aesop)]
    _ = log ‖((∏ i in t₂, canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ i in t₁, (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ∑ i in t₂, log (‖canonicalFactor R i w‖ ^ (divisor f B₀R) i)
        + ∑ i in t₁, log (‖w - i‖ ^ (-divisor f S₀R) i) + log ‖meromorphicTrailingCoeffAt f w‖ := by
      have η₀ (x) (hx : x in t₁) : ‖w - x‖ ^ (-divisor f S₀R) x != 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]; rw [sub_ne_zero]
        rintro rfl
        simp_all [divisor_def, ← Finset.mem_coe]
      have η₁ (x) (hx : x in t₂) : ‖canonicalFactor R x w‖ ^ (divisor f B₀R) x != 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]
        have h₁x : x in ball 0 R := (divisor f B₀R).supportWithinDomain (ht₂ ▸ hx)
        refine canonicalFactor_ne_zero h₁x h₁w fun _ => ?_
        simp_all [divisor_def, ← Finset.mem_coe]
      simp_rw [norm_smul, norm_mul, norm_prod, norm_zpow]
      rw [Real.log_mul (mul_ne_zero_iff.2 ⟨Finset.prod_ne_zero_iff.2 η₁]; rw [Finset.prod_ne_zero_iff.2 η₀⟩) ?_]; rw [Real.log_mul (Finset.prod_ne_zero_iff.2 η₁)
        (Finset.prod_ne_zero_iff.2 η₀)]; rw [Real.log_prod η₁]; rw [Real.log_prod η₀]
      simpa using (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
    _ = ((∑ᶠ i, (divisor f B₀R i) * Real.log ‖canonicalFactor R i w‖)
        - (∑ᶠ i, (divisor f S₀R i) * Real.log ‖w - i‖))
        + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [finsum_eq_sum_of_support_subset (s := t₂) _ ?η₀]; rw [finsum_eq_sum_of_support_subset (s := t₁) _ ?η₁]
      case η₀ | η₁ => intro _ _; simp_all [S₀R, B₀R]
      rw [sub_eq_add_neg]; rw [← Finset.sum_neg_distrib]
      congr! 3 with i hi i hi <;> simp

中文:
引理 ECanonicalDecomp.log_norm_eq
  证明: by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : Complex) R
  let S₀R := sphere (0 : Complex) R
  lift (divisor f S₀R).support to Finset Complex using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset Complex using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  calc Real.log ‖h w‖
    _ = log ‖((∏ᶠ (i : Complex), canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ᶠ (i : Complex), (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        h₁w h₂w hR]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ (by aesop)]
    _ = log ‖((∏ i in t₂, canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ i in t₁, (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ∑ i in t₂, log (‖canonicalFactor R i w‖ ^ (divisor f B₀R) i)
        + ∑ i in t₁, log (‖w - i‖ ^ (-divisor f S₀R) i) + log ‖meromorphicTrailingCoeffAt f w‖ := by
      have η₀ (x) (hx : x in t₁) : ‖w - x‖ ^ (-divisor f S₀R) x != 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]; rw [sub_ne_zero]
        rintro rfl
        simp_all [divisor_def, ← Finset.mem_coe]
      have η₁ (x) (hx : x in t₂) : ‖canonicalFactor R x w‖ ^ (divisor f B₀R) x != 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]
        have h₁x : x in ball 0 R := (divisor f B₀R).supportWithinDomain (ht₂ ▸ hx)
        refine canonicalFactor_ne_zero h₁x h₁w fun _ => ?_
        simp_all [divisor_def, ← Finset.mem_coe]
      simp_rw [norm_smul, norm_mul, norm_prod, norm_zpow]
      rw [Real.log_mul (mul_ne_zero_iff.2 ⟨Finset.prod_ne_zero_iff.2 η₁]; rw [Finset.prod_ne_zero_iff.2 η₀⟩) ?_]; rw [Real.log_mul (Finset.prod_ne_zero_iff.2 η₁)
        (Finset.prod_ne_zero_iff.2 η₀)]; rw [Real.log_prod η₁]; rw [Real.log_prod η₀]
      simpa using (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
    _ = ((∑ᶠ i, (divisor f B₀R i) * Real.log ‖canonicalFactor R i w‖)
        - (∑ᶠ i, (divisor f S₀R i) * Real.log ‖w - i‖))
        + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [finsum_eq_sum_of_support_subset (s := t₂) _ ?η₀]; rw [finsum_eq_sum_of_support_subset (s := t₁) _ ?η₁]
      case η₀ | η₁ => intro _ _; simp_all [S₀R, B₀R]
      rw [sub_eq_add_neg]; rw [← Finset.sum_neg_distrib]
      congr! 3 with i hi i hi <;> simp
-/
lemma ECanonicalDecomp.log_norm_eq
    {f h : Complex -> E} (D : ECanonicalDecomp f h R) (h₁w : w in closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    Real.log ‖h w‖ = ((∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖)
          - (∑ᶠ i, (divisor f (sphere 0 R) i) * Real.log ‖w - i‖))
          + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : Complex) R
  let S₀R := sphere (0 : Complex) R
  lift (divisor f S₀R).support to Finset Complex using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset Complex using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  calc Real.log ‖h w‖
    _ = log ‖((∏ᶠ (i : Complex), canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ᶠ (i : Complex), (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        h₁w h₂w hR]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ (by aesop)]
    _ = log ‖((∏ i in t₂, canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ i in t₁, (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _]; rw [finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ∑ i in t₂, log (‖canonicalFactor R i w‖ ^ (divisor f B₀R) i)
        + ∑ i in t₁, log (‖w - i‖ ^ (-divisor f S₀R) i) + log ‖meromorphicTrailingCoeffAt f w‖ := by
      have η₀ (x) (hx : x in t₁) : ‖w - x‖ ^ (-divisor f S₀R) x != 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]; rw [sub_ne_zero]
        rintro rfl
        simp_all [divisor_def, ← Finset.mem_coe]
      have η₁ (x) (hx : x in t₂) : ‖canonicalFactor R x w‖ ^ (divisor f B₀R) x != 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]
        have h₁x : x in ball 0 R := (divisor f B₀R).supportWithinDomain (ht₂ ▸ hx)
        refine canonicalFactor_ne_zero h₁x h₁w fun _ => ?_
        simp_all [divisor_def, ← Finset.mem_coe]
      simp_rw [norm_smul, norm_mul, norm_prod, norm_zpow]
      rw [Real.log_mul (mul_ne_zero_iff.2 ⟨Finset.prod_ne_zero_iff.2 η₁]; rw [Finset.prod_ne_zero_iff.2 η₀⟩) ?_]; rw [Real.log_mul (Finset.prod_ne_zero_iff.2 η₁)
        (Finset.prod_ne_zero_iff.2 η₀)]; rw [Real.log_prod η₁]; rw [Real.log_prod η₀]
      simpa using (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
    _ = ((∑ᶠ i, (divisor f B₀R i) * Real.log ‖canonicalFactor R i w‖)
        - (∑ᶠ i, (divisor f S₀R i) * Real.log ‖w - i‖))
        + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [finsum_eq_sum_of_support_subset (s := t₂) _ ?η₀]; rw [finsum_eq_sum_of_support_subset (s := t₁) _ ?η₁]
      case η₀ | η₁ => intro _ _; simp_all [S₀R, B₀R]
      rw [sub_eq_add_neg]; rw [← Finset.sum_neg_distrib]
      congr! 3 with i hi i hi <;> simp

end Complex
