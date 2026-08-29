/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# The Logarithmic Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`. Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The logarithmic counting function of a meromorphic function `f` is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole or zero-divisor of a meromorphic function.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the
  logarithmic counting function for arbitrary normed fields.

## TODO

- Discuss the logarithmic counting function for rational functions, add a forward reference to the
  upcoming converse, formulated in terms of the Nevanlinna height.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/--
Definition of `toClosedBall` / `toClosedBall` 的定义

English:
definition toClosedBall
  signature: (r : Real)
  body: by
  apply restrictMonoidHom
  tauto

中文:
定义 toClosedBall
  签名: (r : 实数)
  定义体: by
  apply restrictMonoidHom
  tauto

Depends on / 依赖: restrictMonoidHom
-/
noncomputable def toClosedBall (r : Real) :
    locallyFinsupp E Int ->+ locallyFinsuppWithin (closedBall (0 : E) |r|) Int := by
  apply restrictMonoidHom
  tauto

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `toClosedBall_eval_within` / 引理 `toClosedBall_eval_within`

English:
lemma toClosedBall_eval_within
  statement: {r : Real} {z : E} (f : locallyFinsupp E Int)
  proof: by
  unfold toClosedBall
  simp_all [restrict_apply]

中文:
引理 toClosedBall_eval_within
  结论: {r : 实数} {z : E} (f : locallyFinsupp E 整数)
  证明: by
  unfold toClosedBall
  simp_all [restrict_apply]

Depends on / 依赖: inner_eq_zero_symm, restrict_apply, toClosedBall
-/
lemma toClosedBall_eval_within {r : Real} {z : E} (f : locallyFinsupp E Int)
    (ha : z in closedBall 0 |r|) :
    toClosedBall r f z = f z := by
  unfold toClosedBall
  simp_all [restrict_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `toClosedBall_divisor` / 引理 `toClosedBall_divisor`

English:
lemma toClosedBall_divisor
  given: {r : Real} {f : Complex -> Complex} (h : Meromorphic f)
  proof: by
  simp_all [locallyFinsuppWithin.toClosedBall]

中文:
引理 toClosedBall_divisor
  条件: {r : 实数} {f : 复形 -> 复形} (h : 亚纯 f)
  证明: by
  simp_all [locallyFinsuppWithin.toClosedBall]

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.toClosedBall, toClosedBall
-/
lemma toClosedBall_divisor {r : Real} {f : Complex -> Complex} (h : Meromorphic f) :
    (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ) := by
  simp_all [locallyFinsuppWithin.toClosedBall]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toClosedBall_support_subset_closedBall` / 引理 `toClosedBall_support_subset_closedBall`

English:
lemma toClosedBall_support_subset_closedBall
  statement: {E : Type*} [NormedAddCommGroup E] {r : Real}
  proof: by
  simp_all [toClosedBall, restrict_apply]

中文:
引理 toClosedBall_support_subset_closedBall
  结论: {E : 类型} [赋范交换加群 E] {r : 实数}
  证明: by
  simp_all [toClosedBall, restrict_apply]

Depends on / 依赖: restrict_apply, toClosedBall
-/
lemma toClosedBall_support_subset_closedBall {E : Type*} [NormedAddCommGroup E] {r : Real}
    (f : locallyFinsupp E Int) :
    (toClosedBall r f).support subseteq closedBall 0 |r| := by
  simp_all [toClosedBall, restrict_apply]

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of `logCounting` / `logCounting` 的定义

English:
definition logCounting
  signature: {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  body: fun r => ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : Real} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply]; rw [this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support union (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

中文:
定义 logCounting
  签名: {E : 类型} [赋范交换加群 E] [真空间 E]
  定义体: fun r => ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : Real} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply]; rw [this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support union (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

Depends on / 依赖: D.toClosedBall, toClosedBall
-/
noncomputable def logCounting {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    locallyFinsupp E Int ->+ (Real -> Real) where
  toFun D := fun r => ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : Real} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply]; rw [this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support union (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

/--
lemma `logCounting_eval_zero` / 引理 `logCounting_eval_zero`

English:
lemma logCounting_eval_zero
  statement: {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  proof: by
  simp [logCounting]

中文:
引理 logCounting_eval_zero
  结论: {E : 类型} [赋范交换加群 E] [真空间 E]
  证明: by
  simp [logCounting]
-/
@[simp] lemma logCounting_eval_zero {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E Int) :
    logCounting D 0 = 0 := by
  simp [logCounting]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `logCounting_single_eq_log_sub_const` / 引理 `logCounting_single_eq_log_sub_const`

English:
lemma logCounting_single_eq_log_sub_const
  statement: [DecidableEq E] [ProperSpace E] {e : E} {r : Real}
  proof: by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall]; rw [restrict_apply]; rw [single_apply])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_apply]
  · simp only [single_apply, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    grind

中文:
引理 logCounting_single_eq_log_sub_const
  结论: [DecidableEq E] [真空间 E] {e : E} {r : 实数}
  证明: by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall]; rw [restrict_apply]; rw [single_apply])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_apply]
  · simp only [single_apply, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    grind
-/
@[simp] lemma logCounting_single_eq_log_sub_const [DecidableEq E] [ProperSpace E] {e : E} {r : Real}
    {n : Int} (hr : ‖e‖ <= r) :
    logCounting (single e n) r = n * (log r - log ‖e‖) := by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall]; rw [restrict_apply]; rw [single_apply])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_apply]
  · simp only [single_apply, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    grind

/-!
### Elementary Properties of Logarithmic Counting Functions
-/

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `logCounting_even` / 引理 `logCounting_even`

English:
lemma logCounting_even
  given: [ProperSpace E] (D : locallyFinsupp E Int)
  proof: fun r => by simp [logCounting, toClosedBall, restrict_apply]

中文:
引理 logCounting_even
  条件: [真空间 E] (D : locallyFinsupp E 整数)
  证明: fun r => by simp [logCounting, toClosedBall, restrict_apply]

Depends on / 依赖: logCounting, restrict_apply, toClosedBall
-/
lemma logCounting_even [ProperSpace E] (D : locallyFinsupp E Int) :
    (logCounting D).Even := fun r => by simp [logCounting, toClosedBall, restrict_apply]

/--
lemma `logCounting_mono` / 引理 `logCounting_mono`

English:
lemma logCounting_mono
  given: [ProperSpace E] {D : locallyFinsupp E Int} (hD : 0 <= D)
  proof: by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    repeat rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z in closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z in closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

中文:
引理 logCounting_mono
  条件: [真空间 E] {D : locallyFinsupp E 整数} (hD : 0 <= D)
  证明: by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    repeat rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z in closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z in closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_mk, Finite, ZeroHom, ZeroHom.coe_mk, closedBall, coe_mk, finiteSupport, finsum_eq_sum_of_support_subset, hs.mem_toFinset, hs.toFinset, isCompact_closedBall, logCounting, mem_Ioi, mem_toFinset, repeat, s.Finite, support, toClosedBall, toClosedBall_eval_within
-/
lemma logCounting_mono [ProperSpace E] {D : locallyFinsupp E Int} (hD : 0 <= D) :
    MonotoneOn (logCounting D) (Ioi 0) := by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    repeat rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z in closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z in closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

/--
lemma `logCounting_strictMono` / 引理 `logCounting_strictMono`

English:
lemma logCounting_strictMono
  statement: [DecidableEq E] [ProperSpace E] {D : locallyFinsupp E Int} {e : E}
  proof: by
  rw [(by aesop : logCounting D = logCounting (single e 1) + logCounting (D - single e 1))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le]; rw [logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

中文:
引理 logCounting_strictMono
  结论: [DecidableEq E] [真空间 E] {D : locallyFinsupp E 整数} {e : E}
  证明: by
  rw [(by aesop : logCounting D = logCounting (single e 1) + logCounting (D - single e 1))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le]; rw [logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

Depends on / 依赖: StrictMonoOn, StrictMonoOn.add_monotone, add_monotone, ha.le, hb.le, logCounting, logCounting_mono, logCounting_single_eq_log_sub_const, mem_Ioi, norm_nonneg, single, trans_lt
-/
lemma logCounting_strictMono [DecidableEq E] [ProperSpace E] {D : locallyFinsupp E Int} {e : E}
    (hD : single e 1 <= D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  rw [(by aesop : logCounting D = logCounting (single e 1) + logCounting (D - single e 1))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le]; rw [logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

/--
theorem `logCounting_nonneg` / 定理 `logCounting_nonneg`

English:
theorem logCounting_nonneg
  statement: {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  proof: by
  have h₃r : 0 < r := by linarith
  suffices forall z, 0 <= toClosedBall r f z * log (r * ‖z‖⁻¹) from
add_nonneg (finsum_nonneg this) mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a in closedBall 0 |r|
· refine mul_nonneg ?_ log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

中文:
定理 logCounting_nonneg
  结论: {E : 类型} [赋范交换加群 E] [真空间 E]
  证明: by
  have h₃r : 0 < r := by linarith
  suffices forall z, 0 <= toClosedBall r f z * log (r * ‖z‖⁻¹) from
add_nonneg (finsum_nonneg this) mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a in closedBall 0 |r|
· refine mul_nonneg ?_ log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

Depends on / 依赖: abs_of_pos, add_nonneg, apply_eq_zero_of_notMem, closedBall, finsum_nonneg, log_nonneg, mul_comm, mul_nonneg, norm_pos_iff, norm_pos_iff.mpr, toClosedBall
-/
theorem logCounting_nonneg {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f : locallyFinsupp E Int} {r : Real} (h : 0 <= f) (hr : 1 <= r) :
    0 <= logCounting f r := by
  have h₃r : 0 < r := by linarith
  suffices forall z, 0 <= toClosedBall r f z * log (r * ‖z‖⁻¹) from
add_nonneg (finsum_nonneg this) mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a in closedBall 0 |r|
· refine mul_nonneg ?_ log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

/--
theorem `logCounting_le` / 定理 `logCounting_le`

English:
theorem logCounting_le
  statement: {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  proof: by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

中文:
定理 logCounting_le
  结论: {E : 类型} [赋范交换加群 E] [真空间 E]
  证明: by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

Depends on / 依赖: logCounting_nonneg, sub_nonneg
-/
theorem logCounting_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E Int} {r : Real} (h : f₁ <= f₂) (hr : 1 <= r) :
    logCounting f₁ r <= logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

/--
theorem `logCounting_eventuallyLE` / 定理 `logCounting_eventuallyLE`

English:
theorem logCounting_eventuallyLE
  statement: {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  proof: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_le h hr

中文:
定理 logCounting_eventuallyLE
  结论: {E : 类型} [赋范交换加群 E] [真空间 E]
  证明: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_le h hr

Depends on / 依赖: eventually_ge_atTop, filter_upwards, logCounting_le
-/
theorem logCounting_eventuallyLE {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E Int} (h : f₁ <= f₂) :
    logCounting f₁ <=ᶠ[atTop] logCounting f₂ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_le h hr

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 -> E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
Definition of `logCounting` / `logCounting` 的定义

English:
definition logCounting
  signature: : Real -> Real
  body: by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (f · - a.untop₀) univ)⁺.logCounting

中文:
定义 logCounting
  签名: : 实数 -> 实数
  定义体: by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (f · - a.untop₀) univ)⁺.logCounting

Depends on / 依赖: a.untop, divisor, logCounting
-/
noncomputable def logCounting : Real -> Real := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (f · - a.untop₀) univ)⁺.logCounting

/--
lemma `_root_.locallyFinsuppWithin.logCounting_divisor` / 引理 `_root_.locallyFinsuppWithin.logCounting_divisor`

English:
lemma _root_.locallyFinsuppWithin.logCounting_divisor
  given: {f : Complex -> Complex}
  proof: by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

中文:
引理 _root_.locallyFinsuppWithin.logCounting_divisor
  条件: {f : 复形 -> 复形}
  证明: by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.logCounting.map_sub, logCounting, map_sub
-/
lemma _root_.locallyFinsuppWithin.logCounting_divisor {f : Complex -> Complex} :
    locallyFinsuppWithin.logCounting (divisor f univ) = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

/--
lemma `logCounting_coe` / 引理 `logCounting_coe`

English:
lemma logCounting_coe
  proof: by
  simp [logCounting]

中文:
引理 logCounting_coe
  证明: by
  simp [logCounting]

Depends on / 依赖: logCounting
-/
lemma logCounting_coe :
    logCounting f a₀ = (divisor (f · - a₀) univ)⁺.logCounting := by
  simp [logCounting]

/--
lemma `logCounting_coe_eq_logCounting_sub_const_zero` / 引理 `logCounting_coe_eq_logCounting_sub_const_zero`

English:
lemma logCounting_coe_eq_logCounting_sub_const_zero
  proof: by
  simp [logCounting]

中文:
引理 logCounting_coe_eq_logCounting_sub_const_zero
  证明: by
  simp [logCounting]

Depends on / 依赖: logCounting
-/
lemma logCounting_coe_eq_logCounting_sub_const_zero :
    logCounting f a₀ = logCounting (f - fun _ => a₀) 0 := by
  simp [logCounting]

/--
lemma `logCounting_zero` / 引理 `logCounting_zero`

English:
lemma logCounting_zero
  proof: by
  simp [logCounting]

中文:
引理 logCounting_zero
  证明: by
  simp [logCounting]

Depends on / 依赖: logCounting
-/
lemma logCounting_zero :
    logCounting f 0 = (divisor f univ)⁺.logCounting := by
  simp [logCounting]

/--
lemma `logCounting_top` / 引理 `logCounting_top`

English:
lemma logCounting_top
  proof: by
  simp [logCounting]

中文:
引理 logCounting_top
  证明: by
  simp [logCounting]

Depends on / 依赖: logCounting
-/
lemma logCounting_top :
    logCounting f ⊤ = (divisor f univ)⁻.logCounting := by
  simp [logCounting]

/--
lemma `logCounting_eval_zero` / 引理 `logCounting_eval_zero`

English:
lemma logCounting_eval_zero
  proof: by
  by_cases h : a = ⊤ <;> simp [logCounting, h]

中文:
引理 logCounting_eval_zero
  证明: by
  by_cases h : a = ⊤ <;> simp [logCounting, h]
-/
@[simp] lemma logCounting_eval_zero :
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [logCounting, h]

/--
theorem `log_counting_zero_sub_logCounting_top` / 定理 `log_counting_zero_sub_logCounting_top`

English:
theorem log_counting_zero_sub_logCounting_top
  given: {f : 𝕜 -> E}
  proof: by
  rw [← posPart_sub_negPart (divisor f univ)]; rw [logCounting_zero]; rw [logCounting_top]; rw [map_sub]

中文:
定理 log_counting_zero_sub_logCounting_top
  条件: {f : 𝕜 -> E}
  证明: by
  rw [← posPart_sub_negPart (divisor f univ)]; rw [logCounting_zero]; rw [logCounting_top]; rw [map_sub]

Depends on / 依赖: divisor, logCounting_top, logCounting_zero, map_sub, posPart_sub_negPart
-/
theorem log_counting_zero_sub_logCounting_top {f : 𝕜 -> E} :
    (divisor f univ).logCounting = logCounting f 0 - logCounting f ⊤ := by
  rw [← posPart_sub_negPart (divisor f univ)]; rw [logCounting_zero]; rw [logCounting_top]; rw [map_sub]

/--
theorem `logCounting_const` / 定理 `logCounting_const`

English:
theorem logCounting_const
  given: {c : E} {e : WithTop E}
  proof: by
  simp [logCounting]

中文:
定理 logCounting_const
  条件: {c : E} {e : WithTop E}
  证明: by
  simp [logCounting]
-/
@[simp] theorem logCounting_const {c : E} {e : WithTop E} :
    logCounting (fun _ => c : 𝕜 -> E) e = 0 := by
  simp [logCounting]

/--
theorem `logCounting_const_zero` / 定理 `logCounting_const_zero`

English:
theorem logCounting_const_zero
  given: {e : WithTop E}
  proof: logCounting_const

中文:
定理 logCounting_const_zero
  条件: {e : WithTop E}
  证明: logCounting_const
-/
@[simp] theorem logCounting_const_zero {e : WithTop E} :
    logCounting (0 : 𝕜 -> E) e = 0 := logCounting_const

/--
theorem `logCounting_even` / 定理 `logCounting_even`

English:
theorem logCounting_even
  given: {f : 𝕜 -> E} {e : WithTop E}
  proof: by
  intro r
  by_cases h : e = ⊤ <;> simp [logCounting, h, locallyFinsuppWithin.logCounting_even _ r]

中文:
定理 logCounting_even
  条件: {f : 𝕜 -> E} {e : WithTop E}
  证明: by
  intro r
  by_cases h : e = ⊤ <;> simp [logCounting, h, locallyFinsuppWithin.logCounting_even _ r]

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.logCounting_even, logCounting, logCounting_even
-/
theorem logCounting_even {f : 𝕜 -> E} {e : WithTop E} :
    (logCounting f e).Even := by
  intro r
  by_cases h : e = ⊤ <;> simp [logCounting, h, locallyFinsuppWithin.logCounting_even _ r]

/--
theorem `logCounting_monotoneOn` / 定理 `logCounting_monotoneOn`

English:
theorem logCounting_monotoneOn
  given: {f : 𝕜 -> E} {e : WithTop E}
  proof: by
  by_cases h : e = ⊤ <;>
    simpa [logCounting, h] using locallyFinsuppWithin.logCounting_mono (by positivity)

中文:
定理 logCounting_monotoneOn
  条件: {f : 𝕜 -> E} {e : WithTop E}
  证明: by
  by_cases h : e = ⊤ <;>
    simpa [logCounting, h] using locallyFinsuppWithin.logCounting_mono (by positivity)

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.logCounting_mono, logCounting, logCounting_mono
-/
theorem logCounting_monotoneOn {f : 𝕜 -> E} {e : WithTop E} :
    MonotoneOn (logCounting f e) (Ioi 0) := by
  by_cases h : e = ⊤ <;>
    simpa [logCounting, h] using locallyFinsuppWithin.logCounting_mono (by positivity)

/--
theorem `logCounting_nonneg` / 定理 `logCounting_nonneg`

English:
theorem logCounting_nonneg
  given: {r : Real} {f : 𝕜 -> E} {e : WithTop E} (hr : 1 <= r)
  proof: by
  by_cases h : e = ⊤
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (negPart_nonneg (divisor f univ)) hr]
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (posPart_nonneg (divisor (f · - e.untop₀) univ)) hr]

中文:
定理 logCounting_nonneg
  条件: {r : 实数} {f : 𝕜 -> E} {e : WithTop E} (hr : 1 <= r)
  证明: by
  by_cases h : e = ⊤
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (negPart_nonneg (divisor f univ)) hr]
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (posPart_nonneg (divisor (f · - e.untop₀) univ)) hr]

Depends on / 依赖: divisor, e.untop, locallyFinsuppWithin, locallyFinsuppWithin.logCounting_nonneg, logCounting, logCounting_nonneg, negPart_nonneg, posPart_nonneg
-/
theorem logCounting_nonneg {r : Real} {f : 𝕜 -> E} {e : WithTop E} (hr : 1 <= r) :
    0 <= logCounting f e r := by
  by_cases h : e = ⊤
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (negPart_nonneg (divisor f univ)) hr]
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (posPart_nonneg (divisor (f · - e.untop₀) univ)) hr]

/--
theorem `logCounting_eventually_nonneg` / 定理 `logCounting_eventually_nonneg`

English:
theorem logCounting_eventually_nonneg
  given: {f : 𝕜 -> E} {e : WithTop E}
  proof: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => by simp [logCounting_nonneg hr]

中文:
定理 logCounting_eventually_nonneg
  条件: {f : 𝕜 -> E} {e : WithTop E}
  证明: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => by simp [logCounting_nonneg hr]

Depends on / 依赖: eventually_ge_atTop, filter_upwards, logCounting_nonneg
-/
theorem logCounting_eventually_nonneg {f : 𝕜 -> E} {e : WithTop E} :
    0 <=ᶠ[atTop] logCounting f e := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => by simp [logCounting_nonneg hr]

/-!
## Elementary Properties of the Logarithmic Counting Function
-/

/--
theorem `logCounting_congr_codiscrete` / 定理 `logCounting_congr_codiscrete`

English:
theorem logCounting_congr_codiscrete
  given: [NormedSpace Complex E] {f g : Complex -> E} (hfg : f =ᶠ[codiscrete Complex] g)
  proof: by
  ext a : 1
  by_cases h : a = ⊤
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    exact divisor_congr_codiscreteWithin hfg isOpen_univ
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    apply divisor_congr_codiscreteWithin _ isOpen_univ
    filter_upwards [hfg] using by simp

中文:
定理 logCounting_congr_codiscrete
  条件: [赋范空间 复形 E] {f g : 复形 -> E} (hfg : f =ᶠ[codiscrete 复形] g)
  证明: by
  ext a : 1
  by_cases h : a = ⊤
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    exact divisor_congr_codiscreteWithin hfg isOpen_univ
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    apply divisor_congr_codiscreteWithin _ isOpen_univ
    filter_upwards [hfg] using by simp

Depends on / 依赖: divisor_congr_codiscreteWithin, filter_upwards, isOpen_univ, logCounting, reduceDIte
-/
theorem logCounting_congr_codiscrete [NormedSpace Complex E] {f g : Complex -> E} (hfg : f =ᶠ[codiscrete Complex] g) :
    logCounting f = logCounting g := by
  ext a : 1
  by_cases h : a = ⊤
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    exact divisor_congr_codiscreteWithin hfg isOpen_univ
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    apply divisor_congr_codiscreteWithin _ isOpen_univ
    filter_upwards [hfg] using by simp

/--
theorem `logCounting_inv` / 定理 `logCounting_inv`

English:
theorem logCounting_inv
  given: {f : 𝕜 -> 𝕜}
  proof: by
  simp [logCounting_zero, logCounting_top]

中文:
定理 logCounting_inv
  条件: {f : 𝕜 -> 𝕜}
  证明: by
  simp [logCounting_zero, logCounting_top]
-/
@[simp] theorem logCounting_inv {f : 𝕜 -> 𝕜} :
     logCounting f⁻¹ ⊤ = logCounting f 0 := by
  simp [logCounting_zero, logCounting_top]

/--
theorem `logCounting_add_analyticOn` / 定理 `logCounting_add_analyticOn`

English:
theorem logCounting_add_analyticOn
  given: (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ)
  proof: by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.meromorphicOn.negPart_divisor_add_of_analyticNhdOn_right
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

中文:
定理 logCounting_add_analyticOn
  条件: (hf : 亚纯 f) (hg : AnalyticOn 𝕜 g univ)
  证明: by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.meromorphicOn.negPart_divisor_add_of_analyticNhdOn_right
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

Depends on / 依赖: analyticOn_iff_analyticOnNhd, hf.meromorphicOn.negPart_divisor_add_of_analyticNhdOn_right, isOpen_univ, isOpen_univ.analyticOn_iff_analyticOnNhd, logCounting, meromorphicOn, negPart_divisor_add_of_analyticNhdOn_right, reduceDIte
-/
theorem logCounting_add_analyticOn (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.meromorphicOn.negPart_divisor_add_of_analyticNhdOn_right
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
theorem `logCounting_add_const` / 定理 `logCounting_add_const`

English:
theorem logCounting_add_const
  given: (hf : Meromorphic f)
  proof: by
  apply logCounting_add_analyticOn hf analyticOn_const

中文:
定理 logCounting_add_const
  条件: (hf : 亚纯 f)
  证明: by
  apply logCounting_add_analyticOn hf analyticOn_const
-/
@[simp] theorem logCounting_add_const (hf : Meromorphic f) :
    logCounting (f + fun _ => a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn hf analyticOn_const

/--
theorem `logCounting_sub_const` / 定理 `logCounting_sub_const`

English:
theorem logCounting_sub_const
  given: (hf : Meromorphic f)
  proof: by
  simpa [sub_eq_add_neg] using! logCounting_add_const hf

中文:
定理 logCounting_sub_const
  条件: (hf : 亚纯 f)
  证明: by
  simpa [sub_eq_add_neg] using! logCounting_add_const hf
-/
@[simp] theorem logCounting_sub_const (hf : Meromorphic f) :
    logCounting (f - fun _ => a₀) ⊤ = logCounting f ⊤ := by
  simpa [sub_eq_add_neg] using! logCounting_add_const hf

/-!
## Behaviour under Arithmetic Operations
-/

/--
theorem `logCounting_add_top_le` / 定理 `logCounting_add_top_le`

English:
theorem logCounting_add_top_le
  statement: {f₁ f₂ : 𝕜 -> E} {r : Real} (h₁f₁ : Meromorphic f₁)
  proof: by
  simp only [logCounting, ↓reduceDIte]
  rw [← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (negPart_divisor_add_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

中文:
定理 logCounting_add_top_le
  结论: {f₁ f₂ : 𝕜 -> E} {r : 实数} (h₁f₁ : 亚纯 f₁)
  证明: by
  simp only [logCounting, ↓reduceDIte]
  rw [← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (negPart_divisor_add_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.logCounting.map_add, locallyFinsuppWithin.logCounting_le, logCounting, logCounting_le, map_add, meromorphicOn, negPart_divisor_add_le_add, reduceDIte
-/
theorem logCounting_add_top_le {f₁ f₂ : 𝕜 -> E} {r : Real} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 <= r) :
    logCounting (f₁ + f₂) ⊤ r <= (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (negPart_divisor_add_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

/--
theorem `logCounting_add_top_eventuallyLE` / 定理 `logCounting_add_top_eventuallyLE`

English:
theorem logCounting_add_top_eventuallyLE
  statement: {f₁ f₂ : 𝕜 -> E} (h₁f₁ : Meromorphic f₁)
  proof: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_add_top_le h₁f₁ h₁f₂ hr

中文:
定理 logCounting_add_top_eventuallyLE
  结论: {f₁ f₂ : 𝕜 -> E} (h₁f₁ : 亚纯 f₁)
  证明: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_add_top_le h₁f₁ h₁f₂ hr

Depends on / 依赖: eventually_ge_atTop, filter_upwards, logCounting_add_top_le
-/
theorem logCounting_add_top_eventuallyLE {f₁ f₂ : 𝕜 -> E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    logCounting (f₁ + f₂) ⊤ <=ᶠ[atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_add_top_le h₁f₁ h₁f₂ hr

/--
theorem `logCounting_sum_top_le` / 定理 `logCounting_sum_top_le`

English:
theorem logCounting_sum_top_le
  statement: {α : Type*} (s : Finset α) (f : α -> 𝕜 -> E) {r : Real}
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]; rw [Finset.sum_insert ha]
    calc logCounting (f a + ∑ x in s, f x) ⊤ r
      _ <= (logCounting (f a) ⊤ + logCounting (∑ x in s, f x) ⊤) r :=
        logCounting_add_top_le (h₁f a (Finset.mem_insert_self a s))
          (Meromorphic.sum (fun σ hσ => h₁f σ (Finset.mem_insert_of_mem hσ))) hr
      _ <= (logCounting (f a) ⊤ + ∑ x in s, logCounting (f x) ⊤) r :=
        add_le_add (by trivial) (hs (fun a ha => h₁f a (Finset.mem_insert_of_mem ha)))

中文:
定理 logCounting_sum_top_le
  结论: {α : 类型} (s : 有限集 α) (f : α -> 𝕜 -> E) {r : 实数}
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]; rw [Finset.sum_insert ha]
    calc logCounting (f a + ∑ x in s, f x) ⊤ r
      _ <= (logCounting (f a) ⊤ + logCounting (∑ x in s, f x) ⊤) r :=
        logCounting_add_top_le (h₁f a (Finset.mem_insert_self a s))
          (Meromorphic.sum (fun σ hσ => h₁f σ (Finset.mem_insert_of_mem hσ))) hr
      _ <= (logCounting (f a) ⊤ + ∑ x in s, logCounting (f x) ⊤) r :=
        add_le_add (by trivial) (hs (fun a ha => h₁f a (Finset.mem_insert_of_mem ha)))

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_insert, Meromorphic, Meromorphic.sum, add_le_add, classical, insert, logCounting, logCounting_add_top_le, mem_insert_of_mem, mem_insert_self, sum_insert
-/
theorem logCounting_sum_top_le {α : Type*} (s : Finset α) (f : α -> 𝕜 -> E) {r : Real}
    (h₁f : forall a in s, Meromorphic (f a)) (hr : 1 <= r) :
    logCounting (∑ a in s, f a) ⊤ r <= (∑ a in s, (logCounting (f a) ⊤)) r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]; rw [Finset.sum_insert ha]
    calc logCounting (f a + ∑ x in s, f x) ⊤ r
      _ <= (logCounting (f a) ⊤ + logCounting (∑ x in s, f x) ⊤) r :=
        logCounting_add_top_le (h₁f a (Finset.mem_insert_self a s))
          (Meromorphic.sum (fun σ hσ => h₁f σ (Finset.mem_insert_of_mem hσ))) hr
      _ <= (logCounting (f a) ⊤ + ∑ x in s, logCounting (f x) ⊤) r :=
        add_le_add (by trivial) (hs (fun a ha => h₁f a (Finset.mem_insert_of_mem ha)))

/--
theorem `logCounting_sum_top_eventuallyLE` / 定理 `logCounting_sum_top_eventuallyLE`

English:
theorem logCounting_sum_top_eventuallyLE
  statement: {α : Type*} (s : Finset α) (f : α -> 𝕜 -> E)
  proof: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_sum_top_le s f h₁f hr

中文:
定理 logCounting_sum_top_eventuallyLE
  结论: {α : 类型} (s : 有限集 α) (f : α -> 𝕜 -> E)
  证明: by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_sum_top_le s f h₁f hr

Depends on / 依赖: eventually_ge_atTop, filter_upwards, logCounting_sum_top_le
-/
theorem logCounting_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α -> 𝕜 -> E)
    (h₁f : forall a in s, Meromorphic (f a)) :
    logCounting (∑ a in s, f a) ⊤ <=ᶠ[atTop] ∑ a in s, (logCounting (f a) ⊤) := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr => logCounting_sum_top_le s f h₁f hr

/--
theorem `logCounting_mul_zero_le` / 定理 `logCounting_mul_zero_le`

English:
theorem logCounting_mul_zero_le
  statement: {f₁ f₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r)
  proof: by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ => h₂f₁ z) (fun z _ => h₂f₂ z)]; rw [← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.posPart_add

中文:
定理 logCounting_mul_zero_le
  结论: {f₁ f₂ : 𝕜 -> 𝕜} {r : 实数} (hr : 1 <= r)
  证明: by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ => h₂f₁ z) (fun z _ => h₂f₂ z)]; rw [← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.posPart_add

Depends on / 依赖: WithTop, WithTop.untop, WithTop.zero_ne_top, divisor_mul, locallyFinsuppWithin, locallyFinsuppWithin.logCounting.map_add, locallyFinsuppWithin.logCounting_le, locallyFinsuppWithin.posPart_add, logCounting, logCounting_le, map_add, meromorphicOn, posPart_add, reduceDIte, sub_zero, zero_ne_top
-/
theorem logCounting_mul_zero_le {f₁ f₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    logCounting (f₁ * f₂) 0 r <= (logCounting f₁ 0 + logCounting f₂ 0) r := by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ => h₂f₁ z) (fun z _ => h₂f₂ z)]; rw [← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.posPart_add

/--
theorem `logCounting_mul_zero_eventuallyLE` / 定理 `logCounting_mul_zero_eventuallyLE`

English:
theorem logCounting_mul_zero_eventuallyLE
  statement: {f₁ f₂ : 𝕜 -> 𝕜}
  proof: by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr => logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

中文:
定理 logCounting_mul_zero_eventuallyLE
  结论: {f₁ f₂ : 𝕜 -> 𝕜}
  证明: by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr => logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

Depends on / 依赖: eventually_ge_atTop, filter_upwards, logCounting_mul_zero_le
-/
theorem logCounting_mul_zero_eventuallyLE {f₁ f₂ : 𝕜 -> 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    logCounting (f₁ * f₂) 0 <=ᶠ[atTop] logCounting f₁ 0 + logCounting f₂ 0 := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr => logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
theorem `logCounting_mul_top_le` / 定理 `logCounting_mul_top_le`

English:
theorem logCounting_mul_top_le
  statement: {f₁ f₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r)
  proof: by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ => h₂f₁ z) (fun z _ => h₂f₂ z)]; rw [← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.negPart_add

中文:
定理 logCounting_mul_top_le
  结论: {f₁ f₂ : 𝕜 -> 𝕜} {r : 实数} (hr : 1 <= r)
  证明: by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ => h₂f₁ z) (fun z _ => h₂f₂ z)]; rw [← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.negPart_add

Depends on / 依赖: divisor_mul, locallyFinsuppWithin, locallyFinsuppWithin.logCounting.map_add, locallyFinsuppWithin.logCounting_le, locallyFinsuppWithin.negPart_add, logCounting, logCounting_le, map_add, meromorphicOn, negPart_add, reduceDIte
-/
theorem logCounting_mul_top_le {f₁ f₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    logCounting (f₁ * f₂) ⊤ r <= (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ => h₂f₁ z) (fun z _ => h₂f₂ z)]; rw [← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.negPart_add

/--
theorem `logCounting_mul_top_eventuallyLE` / 定理 `logCounting_mul_top_eventuallyLE`

English:
theorem logCounting_mul_top_eventuallyLE
  statement: {f₁ f₂ : 𝕜 -> 𝕜}
  proof: by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr => logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

中文:
定理 logCounting_mul_top_eventuallyLE
  结论: {f₁ f₂ : 𝕜 -> 𝕜}
  证明: by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr => logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

Depends on / 依赖: eventually_ge_atTop, filter_upwards, logCounting_mul_top_le
-/
theorem logCounting_mul_top_eventuallyLE {f₁ f₂ : 𝕜 -> 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    logCounting (f₁ * f₂) ⊤ <=ᶠ[atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr => logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
theorem `logCounting_pow_zero` / 定理 `logCounting_pow_zero`

English:
theorem logCounting_pow_zero
  given: {f : 𝕜 -> 𝕜} {n : Nat} (hf : Meromorphic f)
  proof: by
  simp [logCounting, divisor_fun_pow hf.meromorphicOn n]

中文:
定理 logCounting_pow_zero
  条件: {f : 𝕜 -> 𝕜} {n : 自然数} (hf : 亚纯 f)
  证明: by
  simp [logCounting, divisor_fun_pow hf.meromorphicOn n]
-/
@[simp] theorem logCounting_pow_zero {f : 𝕜 -> 𝕜} {n : Nat} (hf : Meromorphic f) :
    logCounting (f ^ n) 0 = n • logCounting f 0 := by
  simp [logCounting, divisor_fun_pow hf.meromorphicOn n]

/--
theorem `logCounting_pow_top` / 定理 `logCounting_pow_top`

English:
theorem logCounting_pow_top
  given: {f : 𝕜 -> 𝕜} {n : Nat} (hf : Meromorphic f)
  proof: by
  simp [logCounting, divisor_pow hf.meromorphicOn n]

中文:
定理 logCounting_pow_top
  条件: {f : 𝕜 -> 𝕜} {n : 自然数} (hf : 亚纯 f)
  证明: by
  simp [logCounting, divisor_pow hf.meromorphicOn n]
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 -> 𝕜} {n : Nat} (hf : Meromorphic f) :
    logCounting (f ^ n) ⊤ = n • logCounting f ⊤ := by
  simp [logCounting, divisor_pow hf.meromorphicOn n]

end ValueDistribution

/-!
## Representation by Integrals

For `𝕜 = ℂ`, the theorems below describe the logarithmic counting function in terms of circle
averages.
-/

/--
theorem `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const` / 定理 `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`

English:
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
  statement: {R : Real}
  proof: by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, logCounting, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

中文:
定理 函数.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
  结论: {R : 实数}
  证明: by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, logCounting, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_mk, MeromorphicOn, MeromorphicOn.circleAverage_log_norm, ZeroHom, ZeroHom.coe_mk, add_sub_cancel_right, all_goals, circleAverage_log_norm, closedBall, coe_mk, divisor_apply, logCounting, norm_neg, zero_sub
-/
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : Real}
    {f : Complex -> Complex} (h : Meromorphic f) (hR : R != 0) :
    logCounting (divisor f univ) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, logCounting, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

/--
theorem `ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const` / 定理 `ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const`

English:
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
  statement: {R : Real}
  proof: by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR

中文:
定理 ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
  结论: {R : 实数}
  证明: by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.logCounting_divisor, locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const, logCounting_divisor, logCounting_divisor_eq_circleAverage_sub_const
-/
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const {R : Real}
    {f : Complex -> Complex} (h : Meromorphic f) (hR : R != 0) :
    (logCounting f 0 - logCounting f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR
