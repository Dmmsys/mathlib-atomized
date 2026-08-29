/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Borel-Cantelli lemma, part 1

In this file we show one implication of the **Borel-Cantelli lemma**:
if `s i` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely many sets of the family.

We prove several versions of this lemma:

- `MeasureTheory.ae_finite_setOfPred_mem`: as stated above;
- `MeasureTheory.measure_limsup_cofinite_eq_zero`:
  in terms of `Filter.limsup` along `Filter.cofinite`;
- `MeasureTheory.measure_limsup_atTop_eq_zero`:
  in terms of `Filter.limsup` along `(Filter.atTop : Filter ℕ)`.

For the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι F : Type*} [FunLike F (Set α) Real>=0∞] [OuterMeasureClass F α] [Countable ι] {μ : F}

/--
theorem `measure_limsup_cofinite_eq_zero` / 定理 `measure_limsup_cofinite_eq_zero`

English:
theorem measure_limsup_cofinite_eq_zero
  given: {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞)
  proof: by
refine bot_unique ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun t => ?_
  calc
    μ (limsup s cofinite) <= μ (⋃ i : {i // i ∉ t}, s i) := by
      gcongr
      rw [hasBasis_cofinite.limsup_eq_iInf_iSup]; rw [iUnion_subtype]
      exact iInter₂_subset _ t.finite_toSet
    _ <= ∑' 

中文:
定理 measure_limsup_cofinite_eq_zero
  条件: {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞)
  证明: by
refine bot_unique ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun t => ?_
  calc
    μ (limsup s cofinite) <= μ (⋃ i : {i // i ∉ t}, s i) := by
      gcongr
      rw [hasBasis_cofinite.limsup_eq_iInf_iSup]; rw [iUnion_subtype]
      exact iInter₂_subset _ t.finite_toSet
    _ <= ∑' 

Depends on / 依赖: ENNReal, ENNReal.tendsto_tsum_compl_atTop_zero, bot_unique, cofinite, finite_toSet, ge_of_tendsto, hasBasis_cofinite, hasBasis_cofinite.limsup_eq_iInf_iSup, iUnion_subtype, limsup, limsup_eq_iInf_iSup, measure_iUnion_le, t.finite_toSet, tendsto_tsum_compl_atTop_zero
-/
theorem measure_limsup_cofinite_eq_zero {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞) :
    μ (limsup s cofinite) = 0 := by
refine bot_unique ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun t => ?_
  calc
    μ (limsup s cofinite) <= μ (⋃ i : {i // i ∉ t}, s i) := by
      gcongr
      rw [hasBasis_cofinite.limsup_eq_iInf_iSup]; rw [iUnion_subtype]
      exact iInter₂_subset _ t.finite_toSet
    _ <= ∑' i : {i // i ∉ t}, μ (s i) := measure_iUnion_le _

/--
theorem `measure_limsup_atTop_eq_zero` / 定理 `measure_limsup_atTop_eq_zero`

English:
theorem measure_limsup_atTop_eq_zero
  given: {s : Nat -> Set α} (hs : ∑' i, μ (s i) != ∞)
  proof: by
  rw [← Nat.cofinite_eq_atTop]; rw [measure_limsup_cofinite_eq_zero hs]

中文:
定理 measure_limsup_atTop_eq_zero
  条件: {s : 自然数 -> Set α} (hs : ∑' i, μ (s i) != ∞)
  证明: by
  rw [← Nat.cofinite_eq_atTop]; rw [measure_limsup_cofinite_eq_zero hs]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, measure_limsup_cofinite_eq_zero
-/
theorem measure_limsup_atTop_eq_zero {s : Nat -> Set α} (hs : ∑' i, μ (s i) != ∞) :
    μ (limsup s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop]; rw [measure_limsup_cofinite_eq_zero hs]

/--
theorem `ae_finite_setOfPred_mem` / 定理 `ae_finite_setOfPred_mem`

English:
theorem ae_finite_setOfPred_mem
  given: {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞)
  proof: by
  rw [ae_iff]; rw [← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

@[deprecated (since := "2026-07-09")]
alias ae_finite_setOf_mem := ae_finite_setOfPred_mem

中文:
定理 ae_finite_setOfPred_mem
  条件: {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞)
  证明: by
  rw [ae_iff]; rw [← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

@[deprecated (since := "2026-07-09")]
alias ae_finite_setOf_mem := ae_finite_setOfPred_mem

Depends on / 依赖: Filter, Filter.Frequently, Frequently, ae_iff, measure_limsup_cofinite_eq_zero, mem_limsup_iff_frequently_mem
-/
theorem ae_finite_setOfPred_mem {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞) :
    forallᵐ x ∂μ, {i | x in s i}.Finite := by
  rw [ae_iff]; rw [← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

@[deprecated (since := "2026-07-09")]
alias ae_finite_setOf_mem := ae_finite_setOfPred_mem

/--
theorem `measure_setOfPred_frequently_eq_zero` / 定理 `measure_setOfPred_frequently_eq_zero`

English:
theorem measure_setOfPred_frequently_eq_zero
  given: {p : Nat -> α -> Prop} (hp : ∑' i, μ { x | p i x } != ∞)
  proof: by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, ofPred_forall,
    ofPred_exists] using! measure_limsup_atTop_eq_zero hp

@[deprecated (since := "2026-07-09")]
alias measure_setOf_frequently_eq_zero := measure_setOfPred_frequently_eq_zero

中文:
定理 measure_setOfPred_frequently_eq_zero
  条件: {p : 自然数 -> α -> 命题} (hp : ∑' i, μ { x | p i x } != ∞)
  证明: by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, ofPred_forall,
    ofPred_exists] using! measure_limsup_atTop_eq_zero hp

@[deprecated (since := "2026-07-09")]
alias measure_setOf_frequently_eq_zero := measure_setOfPred_frequently_eq_zero

Depends on / 依赖: bex_def, frequently_atTop, limsup_eq_iInf_iSup_of_nat, measure_limsup_atTop_eq_zero, ofPred_exists, ofPred_forall
-/
theorem measure_setOfPred_frequently_eq_zero {p : Nat -> α -> Prop} (hp : ∑' i, μ { x | p i x } != ∞) :
    μ { x | existsᶠ n in atTop, p n x } = 0 := by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, ofPred_forall,
    ofPred_exists] using! measure_limsup_atTop_eq_zero hp

@[deprecated (since := "2026-07-09")]
alias measure_setOf_frequently_eq_zero := measure_setOfPred_frequently_eq_zero

/--
theorem `ae_eventually_notMem` / 定理 `ae_eventually_notMem`

English:
theorem ae_eventually_notMem
  given: {s : Nat -> Set α} (hs : (∑' i, μ (s i)) != ∞)
  proof: measure_setOfPred_frequently_eq_zero hs

中文:
定理 ae_eventually_notMem
  条件: {s : 自然数 -> Set α} (hs : (∑' i, μ (s i)) != ∞)
  证明: measure_setOfPred_frequently_eq_zero hs

Depends on / 依赖: measure_setOfPred_frequently_eq_zero
-/
theorem ae_eventually_notMem {s : Nat -> Set α} (hs : (∑' i, μ (s i)) != ∞) :
    forallᵐ x ∂μ, forallᶠ n in atTop, x ∉ s n :=
  measure_setOfPred_frequently_eq_zero hs

/--
theorem `measure_liminf_cofinite_eq_zero` / 定理 `measure_liminf_cofinite_eq_zero`

English:
theorem measure_liminf_cofinite_eq_zero
  given: [Infinite ι] {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞)
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup

中文:
定理 measure_liminf_cofinite_eq_zero
  条件: [Infinite ι] {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞)
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup

Depends on / 依赖: liminf_le_limsup, measure_limsup_cofinite_eq_zero, measure_mono, nonpos_iff_eq_zero
-/
theorem measure_liminf_cofinite_eq_zero [Infinite ι] {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞) :
    μ (liminf s cofinite) = 0 := by
  rw [← nonpos_iff_eq_zero]; rw [← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup

/--
theorem `measure_liminf_atTop_eq_zero` / 定理 `measure_liminf_atTop_eq_zero`

English:
theorem measure_liminf_atTop_eq_zero
  given: {s : Nat -> Set α} (h : (∑' i, μ (s i)) != ∞)
  proof: by
  rw [← Nat.cofinite_eq_atTop]; rw [measure_liminf_cofinite_eq_zero h]

中文:
定理 measure_liminf_atTop_eq_zero
  条件: {s : 自然数 -> Set α} (h : (∑' i, μ (s i)) != ∞)
  证明: by
  rw [← Nat.cofinite_eq_atTop]; rw [measure_liminf_cofinite_eq_zero h]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, measure_liminf_cofinite_eq_zero
-/
theorem measure_liminf_atTop_eq_zero {s : Nat -> Set α} (h : (∑' i, μ (s i)) != ∞) :
    μ (liminf s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop]; rw [measure_liminf_cofinite_eq_zero h]

-- TODO: the next 2 lemmas are true for any filter with countable intersections, not only `ae`.
-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/pull/19041
/--
theorem `limsup_ae_eq_of_forall_ae_eq` / 定理 `limsup_ae_eq_of_forall_ae_eq`

English:
theorem limsup_ae_eq_of_forall_ae_eq
  statement: (s : Nat -> Set α) {t : Set α}
  proof: by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
refine eventuallyEq_set.2 h.mono fun x hx => ?_
  simp [mem_limsup_iff_frequently_mem, hx]

中文:
定理 limsup_ae_eq_of_forall_ae_eq
  结论: (s : 自然数 -> Set α) {t : Set α}
  证明: by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
refine eventuallyEq_set.2 h.mono fun x hx => ?_
  simp [mem_limsup_iff_frequently_mem, hx]

Depends on / 依赖: eventuallyEq_set, eventually_countable_forall, h.mono, mem_limsup_iff_frequently_mem
-/
theorem limsup_ae_eq_of_forall_ae_eq (s : Nat -> Set α) {t : Set α}
    (h : forall n, s n =ᵐ[μ] t) : limsup (α := Set α) s atTop =ᵐ[μ] t := by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
refine eventuallyEq_set.2 h.mono fun x hx => ?_
  simp [mem_limsup_iff_frequently_mem, hx]

-- Need to specify `α := Set α` above because of diamond; see https://github.com/leanprover-community/mathlib4/pull/19041
/--
theorem `liminf_ae_eq_of_forall_ae_eq` / 定理 `liminf_ae_eq_of_forall_ae_eq`

English:
theorem liminf_ae_eq_of_forall_ae_eq
  statement: (s : Nat -> Set α) {t : Set α}
  proof: by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
refine eventuallyEq_set.2 h.mono fun x hx => ?_
  simp only [mem_liminf_iff_eventually_mem, hx, eventually_const]

中文:
定理 liminf_ae_eq_of_forall_ae_eq
  结论: (s : 自然数 -> Set α) {t : Set α}
  证明: by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
refine eventuallyEq_set.2 h.mono fun x hx => ?_
  simp only [mem_liminf_iff_eventually_mem, hx, eventually_const]

Depends on / 依赖: eventuallyEq_set, eventually_const, eventually_countable_forall, h.mono, mem_liminf_iff_eventually_mem
-/
theorem liminf_ae_eq_of_forall_ae_eq (s : Nat -> Set α) {t : Set α}
    (h : forall n, s n =ᵐ[μ] t) : liminf (α := Set α) s atTop =ᵐ[μ] t := by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
refine eventuallyEq_set.2 h.mono fun x hx => ?_
  simp only [mem_liminf_iff_eventually_mem, hx, eventually_const]

end MeasureTheory
