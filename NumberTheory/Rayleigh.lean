/-
Copyright (c) 2023 Jason Yuen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Yuen
-/
module

public import Mathlib.Data.Real.ConjExponents
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Rayleigh's theorem on Beatty sequences

This file proves Rayleigh's theorem on Beatty sequences. We start by proving `compl_beattySeq`,
which is a generalization of Rayleigh's theorem, and eventually prove
`Irrational.beattySeq_symmDiff_beattySeq_pos`, which is Rayleigh's theorem.

## Main definitions

* `beattySeq`: In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`.
* `beattySeq'`: In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`.

## Main statements

Define the following Beatty sets, where `r` denotes a real number:

* `B_r := {⌊k * r⌋ | k ∈ ℤ}`
* `B'_r := {⌈k * r⌉ - 1 | k ∈ ℤ}`
* `B⁺_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`
* `B⁺'_r := {⌈r⌉-1, ⌈2r⌉-1, ⌈3r⌉-1, ...}`

The main statements are:

* `compl_beattySeq`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then the complement of `B_r` is `B'_s`.
* `beattySeq_symmDiff_beattySeq'_pos`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then `B⁺_r` and `B⁺'_s` partition the positive integers.
* `Irrational.beattySeq_symmDiff_beattySeq_pos`: Let `r` be an irrational number greater than 1, and
  `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers.

## References

* [Wikipedia, *Beatty sequence*](https://en.wikipedia.org/wiki/Beatty_sequence)

## Tags

beatty, sequence, rayleigh, irrational, floor, positive
-/

@[expose] public section

/--
Definition of `beattySeq` / `beattySeq` 的定义

English:
definition beattySeq
  signature: (r : Real)
  body: fun k => ⌊k * r⌋

中文:
定义 beattySeq
  签名: (r : 实数)
  定义体: fun k => ⌊k * r⌋
-/
noncomputable def beattySeq (r : Real) : Int -> Int :=
  fun k => ⌊k * r⌋

/--
Definition of `beattySeq'` / `beattySeq'` 的定义

English:
definition beattySeq'
  signature: (r : Real)
  body: fun k => ⌈k * r⌉ - 1

中文:
定义 beattySeq'
  签名: (r : 实数)
  定义体: fun k => ⌈k * r⌉ - 1
-/
noncomputable def beattySeq' (r : Real) : Int -> Int :=
  fun k => ⌈k * r⌉ - 1

namespace Beatty

variable {r s : Real} {j : Int}

/--
theorem `no_collision` / 定理 `no_collision`

English:
theorem no_collision
  given: (hrs : r.HolderConjugate s)
  proof: by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySeq]; rw [Int.floor_eq_iff]; rw [← div_le_iff₀ hrs.pos]; rw [← lt_div_iff₀ hrs.pos] at h₁
  rw [beattySeq']; rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_sub_cancel_right]; rw [← div_lt_iff₀ hrs.symm.pos]; rw [← le_div_iff₀ hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

中文:
定理 no_collision
  条件: (hrs : r.HolderConjugate s)
  证明: by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySeq]; rw [Int.floor_eq_iff]; rw [← div_le_iff₀ hrs.pos]; rw [← lt_div_iff₀ hrs.pos] at h₁
  rw [beattySeq']; rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_sub_cancel_right]; rw [← div_lt_iff₀ hrs.symm.pos]; rw [← le_div_iff₀ hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃
-/
private theorem no_collision (hrs : r.HolderConjugate s) :
    Disjoint {beattySeq r k | k} {beattySeq' s k | k} := by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySeq]; rw [Int.floor_eq_iff]; rw [← div_le_iff₀ hrs.pos]; rw [← lt_div_iff₀ hrs.pos] at h₁
  rw [beattySeq']; rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_sub_cancel_right]; rw [← div_lt_iff₀ hrs.symm.pos]; rw [← le_div_iff₀ hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

/--
theorem `no_anticollision` / 定理 `no_anticollision`

English:
theorem no_anticollision
  given: (hrs : r.HolderConjugate s)
  proof: by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one]; rw [← add_assoc]; rw [add_lt_add_iff_right]; rw [add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

中文:
定理 no_anticollision
  条件: (hrs : r.HolderConjugate s)
  证明: by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one]; rw [← add_assoc]; rw [add_lt_add_iff_right]; rw [add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃
-/
private theorem no_anticollision (hrs : r.HolderConjugate s) :
    ¬exists j k m : Int, k < j / r ∧ (j + 1) / r <= k + 1 ∧ m <= j / s ∧ (j + 1) / s < m + 1 := by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one]; rw [← add_assoc]; rw [add_lt_add_iff_right]; rw [add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

/--
theorem `hit_or_miss` / 定理 `hit_or_miss`

English:
theorem hit_or_miss
  given: (h : r > 0)
  proof: by
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [Int.cast_sub]; rw [Int.cast_one]; rw [lt_div_iff₀ h]; rw [sub_add_cancel]
    exact ⟨‹_›, Int.le_ceil _⟩
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySeq]; rw [Int.floor_eq_iff]; rw [Int.cast_sub]; rw [Int.cast_one]; rw [← lt_div_iff₀ h]; rw [sub_lt_iff_lt_add]
    exact ⟨‹_›, Int.ceil_lt_add_one _⟩

中文:
定理 hit_or_miss
  条件: (h : r > 0)
  证明: by
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [Int.cast_sub]; rw [Int.cast_one]; rw [lt_div_iff₀ h]; rw [sub_add_cancel]
    exact ⟨‹_›, Int.le_ceil _⟩
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySeq]; rw [Int.floor_eq_iff]; rw [Int.cast_sub]; rw [Int.cast_one]; rw [← lt_div_iff₀ h]; rw [sub_lt_iff_lt_add]
    exact ⟨‹_›, Int.ceil_lt_add_one _⟩
-/
private theorem hit_or_miss (h : r > 0) :
    j in {beattySeq r k | k} ∨ exists k : Int, k < j / r ∧ (j + 1) / r <= k + 1 := by
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [Int.cast_sub]; rw [Int.cast_one]; rw [lt_div_iff₀ h]; rw [sub_add_cancel]
    exact ⟨‹_›, Int.le_ceil _⟩
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySeq]; rw [Int.floor_eq_iff]; rw [Int.cast_sub]; rw [Int.cast_one]; rw [← lt_div_iff₀ h]; rw [sub_lt_iff_lt_add]
    exact ⟨‹_›, Int.ceil_lt_add_one _⟩

/--
theorem `hit_or_miss'` / 定理 `hit_or_miss'`

English:
theorem hit_or_miss'
  given: (h : r > 0)
  proof: by
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · exact Or.inr ⟨⌊(j + 1) / r⌋, (le_div_iff₀ h).2 ‹_›, Int.lt_floor_add_one _⟩
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySeq']; rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]
    constructor
    · rwa [add_sub_cancel_right]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : Real) h)

中文:
定理 hit_or_miss'
  条件: (h : r > 0)
  证明: by
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · exact Or.inr ⟨⌊(j + 1) / r⌋, (le_div_iff₀ h).2 ‹_›, Int.lt_floor_add_one _⟩
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySeq']; rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]
    constructor
    · rwa [add_sub_cancel_right]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : Real) h)
-/
private theorem hit_or_miss' (h : r > 0) :
    j in {beattySeq' r k | k} ∨ exists k : Int, k <= j / r ∧ (j + 1) / r < k + 1 := by
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · exact Or.inr ⟨⌊(j + 1) / r⌋, (le_div_iff₀ h).2 ‹_›, Int.lt_floor_add_one _⟩
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySeq']; rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]
    constructor
    · rwa [add_sub_cancel_right]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : Real) h)

end Beatty

/--
theorem `compl_beattySeq` / 定理 `compl_beattySeq`

English:
theorem compl_beattySeq
  given: {r s : Real} (hrs : r.HolderConjugate s)
  proof: by
  ext j
  by_cases h₁ : j in {beattySeq r k | k} <;> by_cases h₂ : j in {beattySeq' s k | k}
  · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
  · simp only [Set.mem_compl_iff, h₁, h₂, not_true_eq_false]
  · simp only [Set.mem_compl_iff, h₁, h₂, not_false_eq_true]
  · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
    have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
    exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim

中文:
定理 compl_beattySeq
  条件: {r s : 实数} (hrs : r.HolderConjugate s)
  证明: by
  ext j
  by_cases h₁ : j in {beattySeq r k | k} <;> by_cases h₂ : j in {beattySeq' s k | k}
  · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
  · simp only [Set.mem_compl_iff, h₁, h₂, not_true_eq_false]
  · simp only [Set.mem_compl_iff, h₁, h₂, not_false_eq_true]
  · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
    have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
    exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim

Depends on / 依赖: Beatty, Beatty.hit_or_miss, Beatty.no_anticollision, Beatty.no_collision, Set.mem_compl_iff, Set.not_disjoint_iff, beattySeq, hit_or_miss, hrs.pos, hrs.symm.pos, mem_compl_iff, no_anticollision, no_collision, not_disjoint_iff, not_false_eq_true, not_true_eq_false, resolve_left
-/
theorem compl_beattySeq {r s : Real} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k}ᶜ = {beattySeq' s k | k} := by
  ext j
  by_cases h₁ : j in {beattySeq r k | k} <;> by_cases h₂ : j in {beattySeq' s k | k}
  · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
  · simp only [Set.mem_compl_iff, h₁, h₂, not_true_eq_false]
  · simp only [Set.mem_compl_iff, h₁, h₂, not_false_eq_true]
  · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
    have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
    exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim

/--
theorem `compl_beattySeq'` / 定理 `compl_beattySeq'`

English:
theorem compl_beattySeq'
  given: {r s : Real} (hrs : r.HolderConjugate s)
  proof: by
  rw [← compl_beattySeq hrs.symm]; rw [compl_compl]

中文:
定理 compl_beattySeq'
  条件: {r s : 实数} (hrs : r.HolderConjugate s)
  证明: by
  rw [← compl_beattySeq hrs.symm]; rw [compl_compl]

Depends on / 依赖: compl_beattySeq, compl_compl, hrs.symm
-/
theorem compl_beattySeq' {r s : Real} (hrs : r.HolderConjugate s) :
    {beattySeq' r k | k}ᶜ = {beattySeq s k | k} := by
  rw [← compl_beattySeq hrs.symm]; rw [compl_compl]

open scoped symmDiff

/--
theorem `beattySeq_symmDiff_beattySeq'_pos` / 定理 `beattySeq_symmDiff_beattySeq'_pos`

English:
theorem beattySeq_symmDiff_beattySeq'_pos
  given: {r s : Real} (hrs : r.HolderConjugate s)
  proof: by
  apply Set.eq_of_subset_of_subset
  · rintro j (⟨⟨k, hk, hjk⟩, -⟩ | ⟨⟨k, hk, hjk⟩, -⟩)
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.lt.le
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.lt
  intro j (hj : 0 < j)
  have hb₁ : forall s >= 0, j in {beattySeq s k | k > 0} ↔ j in {beattySeq s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, ?_, hk⟩⟩
    rw [← hk]; rw [beattySeq]; rw [Int.floor_pos] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans_le hj) hs
  have hb₂ : forall s >= 0, j in {beattySeq' s k | k > 0} ↔ j in {beattySeq' s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, ?_, hk⟩⟩
    rw [← hk]; rw [beattySeq']; rw [sub_pos]; rw [Int.lt_ceil]; rw [Int.cast_one] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans hj) hs
  rw [Set.mem_symmDiff]; rw [hb₁ _ hrs.nonneg]; rw [hb₂ _ hrs.symm.nonneg]; rw [← compl_beattySeq hrs]; rw [Set.notMem_compl_iff]; rw [Set.mem_compl_iff]; rw [and_self]; rw [and_self]
  exact or_not

中文:
定理 beattySeq_symmDiff_beattySeq'_pos
  条件: {r s : 实数} (hrs : r.HolderConjugate s)
  证明: by
  apply Set.eq_of_subset_of_subset
  · rintro j (⟨⟨k, hk, hjk⟩, -⟩ | ⟨⟨k, hk, hjk⟩, -⟩)
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.lt.le
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.lt
  intro j (hj : 0 < j)
  have hb₁ : forall s >= 0, j in {beattySeq s k | k > 0} ↔ j in {beattySeq s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, ?_, hk⟩⟩
    rw [← hk]; rw [beattySeq]; rw [Int.floor_pos] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans_le hj) hs
  have hb₂ : forall s >= 0, j in {beattySeq' s k | k > 0} ↔ j in {beattySeq' s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, ?_, hk⟩⟩
    rw [← hk]; rw [beattySeq']; rw [sub_pos]; rw [Int.lt_ceil]; rw [Int.cast_one] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans hj) hs
  rw [Set.mem_symmDiff]; rw [hb₁ _ hrs.nonneg]; rw [hb₂ _ hrs.symm.nonneg]; rw [← compl_beattySeq hrs]; rw [Set.notMem_compl_iff]; rw [Set.mem_compl_iff]; rw [and_self]; rw [and_self]
  exact or_not

Depends on / 依赖: Int.cast_one, Int.floor_pos, Int.lt_ceil, Set.eq_of_subset_of_subset, Set.mem_ofPred_eq, beattySeq, cast_one, eq_of_subset_of_subset, floor_pos, hrs.lt.le, hrs.symm.lt, lt_ceil, mem_ofPred_eq, one_le_mul_of_one_le_of_one_le, one_lt_mul_of_le_of_lt, sub_pos
-/
theorem beattySeq_symmDiff_beattySeq'_pos {r s : Real} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k > 0} ∆ {beattySeq' s k | k > 0} = {n | 0 < n} := by
  apply Set.eq_of_subset_of_subset
  · rintro j (⟨⟨k, hk, hjk⟩, -⟩ | ⟨⟨k, hk, hjk⟩, -⟩)
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.lt.le
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.lt
  intro j (hj : 0 < j)
  have hb₁ : forall s >= 0, j in {beattySeq s k | k > 0} ↔ j in {beattySeq s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, ?_, hk⟩⟩
    rw [← hk]; rw [beattySeq]; rw [Int.floor_pos] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans_le hj) hs
  have hb₂ : forall s >= 0, j in {beattySeq' s k | k > 0} ↔ j in {beattySeq' s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, ?_, hk⟩⟩
    rw [← hk]; rw [beattySeq']; rw [sub_pos]; rw [Int.lt_ceil]; rw [Int.cast_one] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans hj) hs
  rw [Set.mem_symmDiff]; rw [hb₁ _ hrs.nonneg]; rw [hb₂ _ hrs.symm.nonneg]; rw [← compl_beattySeq hrs]; rw [Set.notMem_compl_iff]; rw [Set.mem_compl_iff]; rw [and_self]; rw [and_self]
  exact or_not

/--
theorem `beattySeq'_symmDiff_beattySeq_pos` / 定理 `beattySeq'_symmDiff_beattySeq_pos`

English:
theorem beattySeq'_symmDiff_beattySeq_pos
  given: {r s : Real} (hrs : r.HolderConjugate s)
  proof: by
  rw [symmDiff_comm]; rw [beattySeq_symmDiff_beattySeq'_pos hrs.symm]

中文:
定理 beattySeq'_symmDiff_beattySeq_pos
  条件: {r s : 实数} (hrs : r.HolderConjugate s)
  证明: by
  rw [symmDiff_comm]; rw [beattySeq_symmDiff_beattySeq'_pos hrs.symm]
-/
theorem beattySeq'_symmDiff_beattySeq_pos {r s : Real} (hrs : r.HolderConjugate s) :
    {beattySeq' r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [symmDiff_comm]; rw [beattySeq_symmDiff_beattySeq'_pos hrs.symm]

/--
theorem `Irrational.beattySeq'_pos_eq` / 定理 `Irrational.beattySeq'_pos_eq`

English:
theorem Irrational.beattySeq'_pos_eq
  given: {r : Real} (hr : Irrational r)
  proof: by
  dsimp only [beattySeq, beattySeq']
  congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
  rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_sub_cancel_right]
  refine ⟨(Int.floor_le _).lt_of_ne fun h => ?_, (Int.lt_floor_add_one _).le⟩
  exact (hr.intCast_mul hk.ne').ne_int ⌊k * r⌋ h.symm

中文:
定理 Irrational.beattySeq'_pos_eq
  条件: {r : 实数} (hr : Irrational r)
  证明: by
  dsimp only [beattySeq, beattySeq']
  congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
  rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_sub_cancel_right]
  refine ⟨(Int.floor_le _).lt_of_ne fun h => ?_, (Int.lt_floor_add_one _).le⟩
  exact (hr.intCast_mul hk.ne').ne_int ⌊k * r⌋ h.symm

Depends on / 依赖: Int.cast_add, Int.cast_one, Int.ceil_eq_iff, Int.floor_le, Int.lt_floor_add_one, add_sub_cancel_right, and_congr_right_iff, beattySeq, cast_add, cast_one, ceil_eq_iff, floor_le, h.symm, hk.ne, hr.intCast_mul, intCast_mul, lt_floor_add_one, lt_of_ne, ne_int, rename_i
-/
theorem Irrational.beattySeq'_pos_eq {r : Real} (hr : Irrational r) :
    {beattySeq' r k | k > 0} = {beattySeq r k | k > 0} := by
  dsimp only [beattySeq, beattySeq']
  congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
  rw [sub_eq_iff_eq_add]; rw [Int.ceil_eq_iff]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_sub_cancel_right]
  refine ⟨(Int.floor_le _).lt_of_ne fun h => ?_, (Int.lt_floor_add_one _).le⟩
  exact (hr.intCast_mul hk.ne').ne_int ⌊k * r⌋ h.symm

/--
theorem `Irrational.beattySeq_symmDiff_beattySeq_pos` / 定理 `Irrational.beattySeq_symmDiff_beattySeq_pos`

English:
theorem Irrational.beattySeq_symmDiff_beattySeq_pos
  statement: {r s : Real}
  proof: by
  rw [← hr.beattySeq'_pos_eq]; rw [beattySeq'_symmDiff_beattySeq_pos hrs]

中文:
定理 Irrational.beattySeq_symmDiff_beattySeq_pos
  结论: {r s : 实数}
  证明: by
  rw [← hr.beattySeq'_pos_eq]; rw [beattySeq'_symmDiff_beattySeq_pos hrs]

Depends on / 依赖: _pos_eq, _symmDiff_beattySeq_pos, beattySeq, hr.beattySeq
-/
theorem Irrational.beattySeq_symmDiff_beattySeq_pos {r s : Real}
    (hrs : r.HolderConjugate s) (hr : Irrational r) :
    {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [← hr.beattySeq'_pos_eq]; rw [beattySeq'_symmDiff_beattySeq_pos hrs]
