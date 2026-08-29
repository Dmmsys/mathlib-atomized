/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Doga Can Sertbas
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

import Mathlib.Tactic.Rify

/-!
# Schnirelmann density

We define the Schnirelmann density of a set `A` of natural numbers as
$inf_{n > 0} |A ∩ {1,...,n}| / n$. As this density is very sensitive to changes in small values,
we must exclude `0` from the infimum, and from the intersection.

## Main statements

* Simple bounds on the Schnirelmann density, that it is between 0 and 1 are given in
  `schnirelmannDensity_nonneg` and `schnirelmannDensity_le_one`.
* `schnirelmannDensity_le_of_notMem`: If `k ∉ A`, the density can be easily upper-bounded by
  `1 - k⁻¹`

## Implementation notes

Despite the definition being noncomputable, we include a decidable instance argument, since this
makes the definition easier to use in explicit cases.
Further, we use `Finset.Ioc` rather than a set intersection since the set is finite by construction,
which reduces the proof obligations later that would arise with `Nat.card`.

## TODO
* Give other calculations of the density, for example powers and their sumsets.
* Define other densities like the lower and upper asymptotic density, and the natural density,
  and show how these relate to the Schnirelmann density.
* Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this density.

## References

* [Ruzsa, Imre, *Sumsets and structure*][ruzsa2009]
-/

@[expose] public section

open Finset

/--
Definition of `schnirelmannDensity` / `schnirelmannDensity` 的定义

English:
definition schnirelmannDensity
  signature: (A : Set Nat) [DecidablePred (· in A)]
  body: ⨅ n : {n : Nat // 0 < n}, #{a in Ioc 0 n | a in A} / n

中文:
定义 schnirelmannDensity
  签名: (A : 集合 自然数) [DecidablePred (· in A)]
  定义体: ⨅ n : {n : Nat // 0 < n}, #{a in Ioc 0 n | a in A} / n
-/
noncomputable def schnirelmannDensity (A : Set Nat) [DecidablePred (· in A)] : Real :=
  ⨅ n : {n : Nat // 0 < n}, #{a in Ioc 0 n | a in A} / n

section

variable {A : Set Nat} [DecidablePred (· in A)]

/--
lemma `schnirelmannDensity_nonneg` / 引理 `schnirelmannDensity_nonneg`

English:
lemma schnirelmannDensity_nonneg
  statement: 0 <= schnirelmannDensity A
  proof: Real.iInf_nonneg (fun _ => by positivity)

中文:
引理 schnirelmannDensity_nonneg
  结论: 0 <= schnirelmannDensity A
  证明: Real.iInf_nonneg (fun _ => by positivity)

Depends on / 依赖: Real.iInf_nonneg, iInf_nonneg
-/
lemma schnirelmannDensity_nonneg : 0 <= schnirelmannDensity A :=
  Real.iInf_nonneg (fun _ => by positivity)

/--
lemma `schnirelmannDensity_le_div` / 引理 `schnirelmannDensity_le_div`

English:
lemma schnirelmannDensity_le_div
  given: {n : Nat} (hn : n != 0)
  proof: ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : Nat // 0 < n})

中文:
引理 schnirelmannDensity_le_div
  条件: {n : 自然数} (hn : n != 0)
  证明: ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : Nat // 0 < n})

Depends on / 依赖: bot_lt, ciInf_le, hn.bot_lt
-/
lemma schnirelmannDensity_le_div {n : Nat} (hn : n != 0) :
    schnirelmannDensity A <= #{a in Ioc 0 n | a in A} / n :=
  ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : Nat // 0 < n})

/--
lemma `schnirelmannDensity_mul_le_card_filter` / 引理 `schnirelmannDensity_mul_le_card_filter`

English:
lemma schnirelmannDensity_mul_le_card_filter
  given: {n : Nat}
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)

中文:
引理 schnirelmannDensity_mul_le_card_filter
  条件: {n : 自然数}
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)

Depends on / 依赖: eq_or_ne, schnirelmannDensity_le_div
-/
lemma schnirelmannDensity_mul_le_card_filter {n : Nat} :
    schnirelmannDensity A * n <= #{a in Ioc 0 n | a in A} := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)

/--
lemma `schnirelmannDensity_le_of_le` / 引理 `schnirelmannDensity_le_of_le`

English:
lemma schnirelmannDensity_le_of_le
  statement: {x : Real} (n : Nat) (hn : n != 0)
  proof: (schnirelmannDensity_le_div hn).trans hx

中文:
引理 schnirelmannDensity_le_of_le
  结论: {x : 实数} (n : 自然数) (hn : n != 0)
  证明: (schnirelmannDensity_le_div hn).trans hx

Depends on / 依赖: schnirelmannDensity_le_div
-/
lemma schnirelmannDensity_le_of_le {x : Real} (n : Nat) (hn : n != 0)
    (hx : #{a in Ioc 0 n | a in A} / n <= x) : schnirelmannDensity A <= x :=
  (schnirelmannDensity_le_div hn).trans hx

/--
lemma `schnirelmannDensity_le_one` / 引理 `schnirelmannDensity_le_one`

English:
lemma schnirelmannDensity_le_one
  statement: schnirelmannDensity A <= 1
  proof: schnirelmannDensity_le_of_le 1 one_ne_zero
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _

中文:
引理 schnirelmannDensity_le_one
  结论: schnirelmannDensity A <= 1
  证明: schnirelmannDensity_le_of_le 1 one_ne_zero
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _

Depends on / 依赖: Nat.cast_le_one, Nat.cast_one, card_filter_le, cast_le_one, cast_one, div_one, one_ne_zero, schnirelmannDensity_le_of_le
-/
lemma schnirelmannDensity_le_one : schnirelmannDensity A <= 1 :=
schnirelmannDensity_le_of_le 1 one_ne_zero
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _

/--
lemma `schnirelmannDensity_le_of_notMem` / 引理 `schnirelmannDensity_le_of_notMem`

English:
lemma schnirelmannDensity_le_of_notMem
  given: {k : Nat} (hk : k ∉ A)
  proof: by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div]; rw [one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk']; rw [Nat.cast_le]
  suffices {a in Ioc 0 k | a in A} subseteq Ioo 0 k 

中文:
引理 schnirelmannDensity_le_of_notMem
  条件: {k : 自然数} (hk : k ∉ A)
  证明: by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div]; rw [one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk']; rw [Nat.cast_le]
  suffices {a in Ioc 0 k | a in A} subseteq Ioo 0 k 

Depends on / 依赖: Ioo_insert_right, Nat.cast_le, Nat.cast_pos, Nat.cast_pred, card_le_card, cast_le, cast_pos, cast_pred, eq_zero_or_pos, filter_insert, filter_subset, if_neg, k.eq_zero_or_pos, one_div, one_sub_div, schnirelmannDensity_le_of_le, schnirelmannDensity_le_one, subseteq, trans_eq
-/
lemma schnirelmannDensity_le_of_notMem {k : Nat} (hk : k ∉ A) :
    schnirelmannDensity A <= 1 - (k⁻¹ : Real) := by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div]; rw [one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk']; rw [Nat.cast_le]
  suffices {a in Ioc 0 k | a in A} subseteq Ioo 0 k from (card_le_card this).trans_eq (by simp)
  rw [← Ioo_insert_right hk']; rw [filter_insert]; rw [if_neg hk]
  exact filter_subset _ _

/--
lemma `schnirelmannDensity_eq_zero_of_one_notMem` / 引理 `schnirelmannDensity_eq_zero_of_one_notMem`

English:
lemma schnirelmannDensity_eq_zero_of_one_notMem
  given: (h : 1 ∉ A)
  statement: schnirelmannDensity A = 0
  proof: ((schnirelmannDensity_le_of_notMem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

中文:
引理 schnirelmannDensity_eq_zero_of_one_notMem
  条件: (h : 1 ∉ A)
  结论: schnirelmannDensity A = 0
  证明: ((schnirelmannDensity_le_of_notMem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

Depends on / 依赖: antisymm, schnirelmannDensity_le_of_notMem, schnirelmannDensity_nonneg
-/
lemma schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A) : schnirelmannDensity A = 0 :=
  ((schnirelmannDensity_le_of_notMem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

/--
lemma `schnirelmannDensity_le_of_subset` / 引理 `schnirelmannDensity_le_of_subset`

English:
lemma schnirelmannDensity_le_of_subset
  given: {B : Set Nat} [DecidablePred (· in B)] (h : A subseteq B)
  proof: ciInf_mono ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ fun _ => by gcongr

中文:
引理 schnirelmannDensity_le_of_subset
  条件: {B : 集合 自然数} [DecidablePred (· in B)] (h : A subseteq B)
  证明: ciInf_mono ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ fun _ => by gcongr

Depends on / 依赖: ciInf_mono
-/
lemma schnirelmannDensity_le_of_subset {B : Set Nat} [DecidablePred (· in B)] (h : A subseteq B) :
    schnirelmannDensity A <= schnirelmannDensity B :=
  ciInf_mono ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ fun _ => by gcongr

/--
lemma `schnirelmannDensity_eq_one_iff` / 引理 `schnirelmannDensity_eq_one_iff`

English:
lemma schnirelmannDensity_eq_one_iff
  statement: schnirelmannDensity A = 1 ↔ {0}ᶜ subseteq A
  proof: by
  rw [le_antisymm_iff]; rw [and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, and_imp]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_notMem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, in

中文:
引理 schnirelmannDensity_eq_one_iff
  结论: schnirelmannDensity A = 1 ↔ {0}ᶜ subseteq A
  证明: by
  rw [le_antisymm_iff]; rw [and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, and_imp]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_notMem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, in

Depends on / 依赖: Nat.card_Ioc, Nat.cast_le, Nat.cast_pos, Nat.sub_zero, Set.not_subset, and_iff_right, and_imp, card_Ioc, cast_le, cast_pos, filter_true_of_mem, forall_exists_index, inv_pos, le_antisymm_iff, le_ciInf, not_imp_not, not_le, not_subset, one_div, one_le_div
-/
lemma schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ subseteq A := by
  rw [le_antisymm_iff]; rw [and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, and_imp]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_notMem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, inv_pos, Nat.cast_pos, pos_iff_ne_zero] using! hx
  · intro h
    refine le_ciInf fun ⟨n, hn⟩ => ?_
    rw [one_le_div (Nat.cast_pos.2 hn)]; rw [Nat.cast_le]; rw [filter_true_of_mem]; rw [Nat.card_Ioc]; rw [Nat.sub_zero]
    rintro x hx
    exact h (mem_Ioc.1 hx).1.ne'

/--
lemma `schnirelmannDensity_eq_one_iff_of_zero_mem` / 引理 `schnirelmannDensity_eq_one_iff_of_zero_mem`

English:
lemma schnirelmannDensity_eq_one_iff_of_zero_mem
  given: (hA : 0 in A)
  proof: by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ

中文:
引理 schnirelmannDensity_eq_one_iff_of_zero_mem
  条件: (hA : 0 in A)
  证明: by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ

Depends on / 依赖: Set.eq_univ_of_forall, Set.subset_univ, eq_or_ne, eq_univ_of_forall, schnirelmannDensity_eq_one_iff, subset_univ
-/
lemma schnirelmannDensity_eq_one_iff_of_zero_mem (hA : 0 in A) :
    schnirelmannDensity A = 1 ↔ A = Set.univ := by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ

/--
lemma `le_schnirelmannDensity_iff` / 引理 `le_schnirelmannDensity_iff`

English:
lemma le_schnirelmannDensity_iff
  given: {x : Real}
  proof: (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall

中文:
引理 le_schnirelmannDensity_iff
  条件: {x : 实数}
  证明: (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall, le_ciInf_iff
-/
lemma le_schnirelmannDensity_iff {x : Real} :
    x <= schnirelmannDensity A ↔ forall n : Nat, 0 < n -> x <= #{a in Ioc 0 n | a in A} / n :=
  (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall

/--
lemma `schnirelmannDensity_lt_iff` / 引理 `schnirelmannDensity_lt_iff`

English:
lemma schnirelmannDensity_lt_iff
  given: {x : Real}
  proof: by
  rw [← not_le]; rw [le_schnirelmannDensity_iff]; simp

中文:
引理 schnirelmannDensity_lt_iff
  条件: {x : 实数}
  证明: by
  rw [← not_le]; rw [le_schnirelmannDensity_iff]; simp

Depends on / 依赖: le_schnirelmannDensity_iff, not_le
-/
lemma schnirelmannDensity_lt_iff {x : Real} :
    schnirelmannDensity A < x ↔ exists n : Nat, 0 < n ∧ #{a in Ioc 0 n | a in A} / n < x := by
  rw [← not_le]; rw [le_schnirelmannDensity_iff]; simp

/--
lemma `schnirelmannDensity_le_iff_forall` / 引理 `schnirelmannDensity_le_iff_forall`

English:
lemma schnirelmannDensity_le_iff_forall
  given: {x : Real}
  proof: by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]

中文:
引理 schnirelmannDensity_le_iff_对任意
  条件: {x : 实数}
  证明: by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]

Depends on / 依赖: le_iff_forall_pos_lt_add, schnirelmannDensity_lt_iff
-/
lemma schnirelmannDensity_le_iff_forall {x : Real} :
    schnirelmannDensity A <= x ↔
      forall ε : Real, 0 < ε -> exists n : Nat, 0 < n ∧ #{a in Ioc 0 n | a in A} / n < x + ε := by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]

/--
lemma `schnirelmannDensity_congr'` / 引理 `schnirelmannDensity_congr'`

English:
lemma schnirelmannDensity_congr'
  statement: {B : Set Nat} [DecidablePred (· in B)]
  proof: by
  rw [schnirelmannDensity]; rw [schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; simp_all

中文:
引理 schnirelmannDensity_congr'
  结论: {B : 集合 自然数} [DecidablePred (· in B)]
  证明: by
  rw [schnirelmannDensity]; rw [schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; simp_all

Depends on / 依赖: schnirelmannDensity
-/
lemma schnirelmannDensity_congr' {B : Set Nat} [DecidablePred (· in B)]
    (h : forall n > 0, n in A ↔ n in B) : schnirelmannDensity A = schnirelmannDensity B := by
  rw [schnirelmannDensity]; rw [schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; simp_all

/--
lemma `schnirelmannDensity_insert_zero` / 引理 `schnirelmannDensity_insert_zero`

English:
lemma schnirelmannDensity_insert_zero
  given: [DecidablePred (· in insert 0 A)]
  proof: schnirelmannDensity_congr' (by aesop)

中文:
引理 schnirelmannDensity_insert_zero
  条件: [DecidablePred (· in insert 0 A)]
  证明: schnirelmannDensity_congr' (by aesop)
-/
@[simp] lemma schnirelmannDensity_insert_zero [DecidablePred (· in insert 0 A)] :
    schnirelmannDensity (insert 0 A) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)

/--
lemma `schnirelmannDensity_sdiff_singleton_zero` / 引理 `schnirelmannDensity_sdiff_singleton_zero`

English:
lemma schnirelmannDensity_sdiff_singleton_zero
  given: [DecidablePred (· in A \ {0})]
  proof: schnirelmannDensity_congr' (by aesop)

@[deprecated (since := "2026-06-03")]
alias schnirelmannDensity_diff_singleton_zero := schnirelmannDensity_sdiff_singleton_zero

中文:
引理 schnirelmannDensity_sdiff_singleton_zero
  条件: [DecidablePred (· in A \ {0})]
  证明: schnirelmannDensity_congr' (by aesop)

@[deprecated (since := "2026-06-03")]
alias schnirelmannDensity_diff_singleton_zero := schnirelmannDensity_sdiff_singleton_zero

Depends on / 依赖: schnirelmannDensity_congr
-/
lemma schnirelmannDensity_sdiff_singleton_zero [DecidablePred (· in A \ {0})] :
    schnirelmannDensity (A \ {0}) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)

@[deprecated (since := "2026-06-03")]
alias schnirelmannDensity_diff_singleton_zero := schnirelmannDensity_sdiff_singleton_zero

/--
lemma `schnirelmannDensity_congr` / 引理 `schnirelmannDensity_congr`

English:
lemma schnirelmannDensity_congr
  given: {B : Set Nat} [DecidablePred (· in B)] (h : A = B)
  proof: schnirelmannDensity_congr' (by simp_all)

中文:
引理 schnirelmannDensity_congr
  条件: {B : 集合 自然数} [DecidablePred (· in B)] (h : A = B)
  证明: schnirelmannDensity_congr' (by simp_all)

Depends on / 依赖: schnirelmannDensity_congr
-/
lemma schnirelmannDensity_congr {B : Set Nat} [DecidablePred (· in B)] (h : A = B) :
    schnirelmannDensity A = schnirelmannDensity B :=
  schnirelmannDensity_congr' (by simp_all)

/--
lemma `exists_of_schnirelmannDensity_eq_zero` / 引理 `exists_of_schnirelmannDensity_eq_zero`

English:
lemma exists_of_schnirelmannDensity_eq_zero
  given: {ε : Real} (hε : 0 < ε) (hA : schnirelmannDensity A = 0)
  proof: by
  by_contra! h
  rw [← le_schnirelmannDensity_iff] at h
  linarith

中文:
引理 存在_of_schnirelmannDensity_eq_zero
  条件: {ε : 实数} (hε : 0 < ε) (hA : schnirelmannDensity A = 0)
  证明: by
  by_contra! h
  rw [← le_schnirelmannDensity_iff] at h
  linarith

Depends on / 依赖: le_schnirelmannDensity_iff
-/
lemma exists_of_schnirelmannDensity_eq_zero {ε : Real} (hε : 0 < ε) (hA : schnirelmannDensity A = 0) :
    exists n, 0 < n ∧ #{a in Ioc 0 n | a in A} / n < ε := by
  by_contra! h
  rw [← le_schnirelmannDensity_iff] at h
  linarith

end

/--
lemma `schnirelmannDensity_empty` / 引理 `schnirelmannDensity_empty`

English:
lemma schnirelmannDensity_empty
  statement: schnirelmannDensity ∅ = 0
  proof: schnirelmannDensity_eq_zero_of_one_notMem (by simp)

中文:
引理 schnirelmannDensity_empty
  结论: schnirelmannDensity ∅ = 0
  证明: schnirelmannDensity_eq_zero_of_one_notMem (by simp)
-/
@[simp] lemma schnirelmannDensity_empty : schnirelmannDensity ∅ = 0 :=
  schnirelmannDensity_eq_zero_of_one_notMem (by simp)

/--
lemma `schnirelmannDensity_finset` / 引理 `schnirelmannDensity_finset`

English:
lemma schnirelmannDensity_finset
  given: (A : Finset Nat)
  statement: schnirelmannDensity A = 0
  proof: by
  refine le_antisymm ?_ schnirelmannDensity_nonneg
  simp only [schnirelmannDensity_le_iff_forall, zero_add]
  intro ε hε
  wlog hε₁ : ε <= 1 generalizing ε
  · obtain ⟨n, hn, hn'⟩ := this 1 zero_lt_one le_rfl
    exact ⟨n, hn, hn'.trans_le (le_of_not_ge hε₁)⟩
  let n : Nat := ⌊#A / ε⌋₊ + 1
  hav

中文:
引理 schnirelmannDensity_finset
  条件: (A : 有限集 自然数)
  结论: schnirelmannDensity A = 0
  证明: by
  refine le_antisymm ?_ schnirelmannDensity_nonneg
  simp only [schnirelmannDensity_le_iff_forall, zero_add]
  intro ε hε
  wlog hε₁ : ε <= 1 generalizing ε
  · obtain ⟨n, hn, hn'⟩ := this 1 zero_lt_one le_rfl
    exact ⟨n, hn, hn'.trans_le (le_of_not_ge hε₁)⟩
  let n : Nat := ⌊#A / ε⌋₊ + 1
  hav

Depends on / 依赖: Nat.cast_add_one, Nat.cast_pos, Nat.lt_floor_add_one, Nat.succ_pos, cast_add_one, cast_pos, generalizing, le_antisymm, le_of_not_ge, le_rfl, lt_floor_add_one, schnirelmannDensity_le_iff_forall, schnirelmannDensity_nonneg, subset_iff, succ_pos, trans_le, zero_add, zero_lt_one
-/
lemma schnirelmannDensity_finset (A : Finset Nat) : schnirelmannDensity A = 0 := by
  refine le_antisymm ?_ schnirelmannDensity_nonneg
  simp only [schnirelmannDensity_le_iff_forall, zero_add]
  intro ε hε
  wlog hε₁ : ε <= 1 generalizing ε
  · obtain ⟨n, hn, hn'⟩ := this 1 zero_lt_one le_rfl
    exact ⟨n, hn, hn'.trans_le (le_of_not_ge hε₁)⟩
  let n : Nat := ⌊#A / ε⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  use n, hn
  rw [div_lt_iff₀ (Nat.cast_pos.2 hn)]; rw [← div_lt_iff₀' hε]; rw [Nat.cast_add_one]
exact (Nat.lt_floor_add_one _).trans_le' by gcongr; simp [subset_iff]

/--
lemma `schnirelmannDensity_finite` / 引理 `schnirelmannDensity_finite`

English:
lemma schnirelmannDensity_finite
  given: {A : Set Nat} [DecidablePred (· in A)] (hA : A.Finite)
  proof: by simpa using schnirelmannDensity_finset hA.toFinset

中文:
引理 schnirelmannDensity_finite
  条件: {A : 集合 自然数} [DecidablePred (· in A)] (hA : A.有限)
  证明: by simpa using schnirelmannDensity_finset hA.toFinset

Depends on / 依赖: hA.toFinset, schnirelmannDensity_finset, toFinset
-/
lemma schnirelmannDensity_finite {A : Set Nat} [DecidablePred (· in A)] (hA : A.Finite) :
    schnirelmannDensity A = 0 := by simpa using schnirelmannDensity_finset hA.toFinset

/--
lemma `schnirelmannDensity_univ` / 引理 `schnirelmannDensity_univ`

English:
lemma schnirelmannDensity_univ
  statement: schnirelmannDensity Set.univ = 1
  proof: (schnirelmannDensity_eq_one_iff_of_zero_mem (by simp)).2 (by simp)

中文:
引理 schnirelmannDensity_univ
  结论: schnirelmannDensity 集合.univ = 1
  证明: (schnirelmannDensity_eq_one_iff_of_zero_mem (by simp)).2 (by simp)
-/
@[simp] lemma schnirelmannDensity_univ : schnirelmannDensity Set.univ = 1 :=
  (schnirelmannDensity_eq_one_iff_of_zero_mem (by simp)).2 (by simp)

/--
lemma `schnirelmannDensity_setOfPred_even` / 引理 `schnirelmannDensity_setOfPred_even`

English:
lemma schnirelmannDensity_setOfPred_even
  statement: schnirelmannDensity (Set.ofPred Even) = 0
  proof: schnirelmannDensity_eq_zero_of_one_notMem by simp

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_even := schnirelmannDensity_setOfPred_even

中文:
引理 schnirelmannDensity_setOfPred_even
  结论: schnirelmannDensity (集合.ofPred Even) = 0
  证明: schnirelmannDensity_eq_zero_of_one_notMem by simp

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_even := schnirelmannDensity_setOfPred_even

Depends on / 依赖: schnirelmannDensity_eq_zero_of_one_notMem
-/
lemma schnirelmannDensity_setOfPred_even : schnirelmannDensity (Set.ofPred Even) = 0 :=
schnirelmannDensity_eq_zero_of_one_notMem by simp

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_even := schnirelmannDensity_setOfPred_even

/--
lemma `schnirelmannDensity_setOfPred_prime` / 引理 `schnirelmannDensity_setOfPred_prime`

English:
lemma schnirelmannDensity_setOfPred_prime
  statement: schnirelmannDensity (Set.ofPred Nat.Prime) = 0
  proof: schnirelmannDensity_eq_zero_of_one_notMem by simp [Nat.not_prime_one]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_prime := schnirelmannDensity_setOfPred_prime

中文:
引理 schnirelmannDensity_setOfPred_prime
  结论: schnirelmannDensity (集合.ofPred 自然数.素) = 0
  证明: schnirelmannDensity_eq_zero_of_one_notMem by simp [Nat.not_prime_one]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_prime := schnirelmannDensity_setOfPred_prime

Depends on / 依赖: Nat.not_prime_one, not_prime_one, schnirelmannDensity_eq_zero_of_one_notMem
-/
lemma schnirelmannDensity_setOfPred_prime : schnirelmannDensity (Set.ofPred Nat.Prime) = 0 :=
schnirelmannDensity_eq_zero_of_one_notMem by simp [Nat.not_prime_one]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_prime := schnirelmannDensity_setOfPred_prime

set_option backward.isDefEq.respectTransparency false in
/--
lemma `schnirelmannDensity_setOfPred_mod_eq_one` / 引理 `schnirelmannDensity_setOfPred_mod_eq_one`

English:
lemma schnirelmannDensity_setOfPred_mod_eq_one
  given: {m : Nat} (hm : m != 1)
  proof: by
  rcases m.eq_zero_or_pos with rfl | hm'
  · simp only [Nat.cast_zero, inv_zero]
    refine schnirelmannDensity_finite ?_
    simp
  apply le_antisymm (schnirelmannDensity_le_of_le m hm'.ne' _) _
  · rw [← one_div, ← @Nat.cast_one Real]
    gcongr
    simp only [Set.mem_ofPred_eq, card_le_one_iff

中文:
引理 schnirelmannDensity_setOfPred_mod_eq_one
  条件: {m : 自然数} (hm : m != 1)
  证明: by
  rcases m.eq_zero_or_pos with rfl | hm'
  · simp only [Nat.cast_zero, inv_zero]
    refine schnirelmannDensity_finite ?_
    simp
  apply le_antisymm (schnirelmannDensity_le_of_le m hm'.ne' _) _
  · rw [← one_div, ← @Nat.cast_one Real]
    gcongr
    simp only [Set.mem_ofPred_eq, card_le_one_iff

Depends on / 依赖: Nat.cast_one, Nat.cast_zero, Nat.mod_eq_of_lt, Set.mem_ofPred_eq, and_imp, card_le_one_iff_subset_singleton, cast_one, cast_zero, eq_or_lt_of_le, eq_zero_or_pos, inv_zero, le_antisymm, le_schnirelmannDensity_iff, m.eq_zero_or_pos, mem_Ioc, mem_filter, mem_ofPred_eq, mem_singleton, mod_eq_of_lt, one_div
-/
lemma schnirelmannDensity_setOfPred_mod_eq_one {m : Nat} (hm : m != 1) :
    schnirelmannDensity {n | n % m = 1} = (m⁻¹ : Real) := by
  rcases m.eq_zero_or_pos with rfl | hm'
  · simp only [Nat.cast_zero, inv_zero]
    refine schnirelmannDensity_finite ?_
    simp
  apply le_antisymm (schnirelmannDensity_le_of_le m hm'.ne' _) _
  · rw [← one_div, ← @Nat.cast_one Real]
    gcongr
    simp only [Set.mem_ofPred_eq, card_le_one_iff_subset_singleton, subset_iff,
      mem_filter, mem_Ioc, mem_singleton, and_imp]
    use 1
    intro x _ hxm h
    rcases eq_or_lt_of_le hxm with rfl | hxm'
    · simp at h
    rwa [Nat.mod_eq_of_lt hxm'] at h
  rw [le_schnirelmannDensity_iff]
  intro n hn
  simp only [Set.mem_ofPred_eq]
  have : (Icc 0 ((n - 1) / m)).image (· * m + 1) subseteq {x in Ioc 0 n | x % m = 1} := by
    simp only [subset_iff, mem_image, forall_exists_index, mem_filter, mem_Ioc, mem_Icc, and_imp]
    rintro _ y _ hy' rfl
    have hm : 2 <= m := hm.lt_of_le' hm'
    simp only [Nat.mul_add_mod', Nat.mod_eq_of_lt hm, add_pos_iff, or_true, and_true, true_and,
      ← Nat.le_sub_iff_add_le hn, zero_lt_one]
    exact Nat.mul_le_of_le_div _ _ _ hy'
  rw [le_div_iff₀ (Nat.cast_pos.2 hn)]; rw [mul_comm]; rw [← div_eq_mul_inv]
  apply (Nat.cast_le.2 (card_le_card this)).trans'
  rw [card_image_of_injective]; rw [Nat.card_Icc]; rw [Nat.sub_zero]; rw [div_le_iff₀ (Nat.cast_pos.2 hm')]; rw [← Nat.cast_mul]; rw [Nat.cast_le]; rw [add_one_mul (α := Nat)]
  · have := @Nat.lt_div_mul_add n.pred m hm'
    rwa [← Nat.succ_le_iff, Nat.succ_pred hn.ne'] at this
  intro a b
  simp [hm'.ne']

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_mod_eq_one := schnirelmannDensity_setOfPred_mod_eq_one

/--
lemma `schnirelmannDensity_setOfPred_modeq_one` / 引理 `schnirelmannDensity_setOfPred_modeq_one`

English:
lemma schnirelmannDensity_setOfPred_modeq_one
  given: {m : Nat}
  proof: by
  rcases eq_or_ne m 1 with rfl | hm
  · simp [Nat.modEq_one]
  rw [← schnirelmannDensity_setOfPred_mod_eq_one hm]
  simp [Nat.ModEq, Nat.one_mod_eq_one.mpr hm]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_modeq_one := schnirelmannDensity_setOfPred_modeq_one

中文:
引理 schnirelmannDensity_setOfPred_modeq_one
  条件: {m : 自然数}
  证明: by
  rcases eq_or_ne m 1 with rfl | hm
  · simp [Nat.modEq_one]
  rw [← schnirelmannDensity_setOfPred_mod_eq_one hm]
  simp [Nat.ModEq, Nat.one_mod_eq_one.mpr hm]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_modeq_one := schnirelmannDensity_setOfPred_modeq_one

Depends on / 依赖: Nat.ModEq, Nat.modEq_one, Nat.one_mod_eq_one.mpr, eq_or_ne, modEq_one, one_mod_eq_one, schnirelmannDensity_setOfPred_mod_eq_one
-/
lemma schnirelmannDensity_setOfPred_modeq_one {m : Nat} :
    schnirelmannDensity {n | n ≡ 1 [MOD m]} = (m⁻¹ : Real) := by
  rcases eq_or_ne m 1 with rfl | hm
  · simp [Nat.modEq_one]
  rw [← schnirelmannDensity_setOfPred_mod_eq_one hm]
  simp [Nat.ModEq, Nat.one_mod_eq_one.mpr hm]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_modeq_one := schnirelmannDensity_setOfPred_modeq_one

/--
lemma `schnirelmannDensity_setOfPred_Odd` / 引理 `schnirelmannDensity_setOfPred_Odd`

English:
lemma schnirelmannDensity_setOfPred_Odd
  statement: schnirelmannDensity (Set.ofPred Odd) = 2⁻¹
  proof: by
  have h : Set.ofPred Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOfPred_mod_eq_one (by norm_num1)]; rw [Nat.cast_two]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_Odd := schnirelmannDensity_setOfPred_Odd

中文:
引理 schnirelmannDensity_setOfPred_Odd
  结论: schnirelmannDensity (集合.ofPred Odd) = 2⁻¹
  证明: by
  have h : Set.ofPred Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOfPred_mod_eq_one (by norm_num1)]; rw [Nat.cast_two]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_Odd := schnirelmannDensity_setOfPred_Odd

Depends on / 依赖: Nat.cast_two, Nat.odd_iff, Set.ext, Set.ofPred, cast_two, norm_num1, odd_iff, ofPred, schnirelmannDensity_setOfPred_mod_eq_one
-/
lemma schnirelmannDensity_setOfPred_Odd : schnirelmannDensity (Set.ofPred Odd) = 2⁻¹ := by
  have h : Set.ofPred Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOfPred_mod_eq_one (by norm_num1)]; rw [Nat.cast_two]

@[deprecated (since := "2026-07-09")]
alias schnirelmannDensity_setOf_Odd := schnirelmannDensity_setOfPred_Odd

open scoped Pointwise

/--
theorem `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity` / 定理 `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`

English:
theorem add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
  statement: {A B : Set Nat}
  proof: by
  rw [Set.eq_univ_iff_forall]
  rintro (_ | m)
  · exact ⟨0, hA, 0, ⟨hB, rfl⟩⟩
  set n := m + 1
  by_cases hnA : n in A
  · exact ⟨n, by simp [hnA], 0, ⟨hB, rfl⟩⟩
  by_cases hnB : n in B
  · exact ⟨0, hA, n, ⟨hnB, by simp⟩⟩
  let f : Nat oplus Nat -> Nat
    | .inl x => x
    | .inr y => n - y
  

中文:
定理 add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
  结论: {A B : 集合 自然数}
  证明: by
  rw [Set.eq_univ_iff_forall]
  rintro (_ | m)
  · exact ⟨0, hA, 0, ⟨hB, rfl⟩⟩
  set n := m + 1
  by_cases hnA : n in A
  · exact ⟨n, by simp [hnA], 0, ⟨hB, rfl⟩⟩
  by_cases hnB : n in B
  · exact ⟨0, hA, n, ⟨hnB, by simp⟩⟩
  let f : Nat oplus Nat -> Nat
    | .inl x => x
    | .inr y => n - y
  

Depends on / 依赖: Set.eq_univ_iff_forall, disjSum, eq_univ_iff_forall, mem_disjSum
-/
theorem add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity {A B : Set Nat}
    [DecidablePred (· in A)] [DecidablePred (· in B)] (hA : 0 in A) (hB : 0 in B)
    (h : 1 <= schnirelmannDensity A + schnirelmannDensity B) : A + B = .univ := by
  rw [Set.eq_univ_iff_forall]
  rintro (_ | m)
  · exact ⟨0, hA, 0, ⟨hB, rfl⟩⟩
  set n := m + 1
  by_cases hnA : n in A
  · exact ⟨n, by simp [hnA], 0, ⟨hB, rfl⟩⟩
  by_cases hnB : n in B
  · exact ⟨0, hA, n, ⟨hnB, by simp⟩⟩
  let f : Nat oplus Nat -> Nat
    | .inl x => x
    | .inr y => n - y
  let sA := {a in Ioc 0 n | a in A}
  let sB := {b in Ioc 0 n | b in B}
  have hc : #(image f (disjSum sA sB)) < #(disjSum sA sB) := calc
    #(image f (disjSum sA sB)) <= #(Ioo 0 n) := by gcongr; grind [mem_disjSum]
    _ < n := by simp [Nat.card_Ioo, n]
    _ <= #(disjSum sA sB) := by
      rw [card_disjSum]
      rify
      nlinarith [@schnirelmannDensity_mul_le_card_filter A _ n,
        @schnirelmannDensity_mul_le_card_filter B _ n]
  obtain ⟨a | b, ha, a | b, hb, _, hxy⟩ := exists_ne_map_eq_of_card_image_lt hc <;>
  simp only [sA, sB, inl_mem_disjSum, mem_filter, mem_Ioc, inr_mem_disjSum] at ha hb <;>
  first | grind [inr_mem_disjSum] | exact ⟨a, by simp [*], b, by simp [*], by grind⟩
