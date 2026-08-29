/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Heather Macbeth, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Infinite sums in (semi)normed groups

In a complete (semi)normed group,

- `summable_iff_vanishing_norm`: a series `∑' i, f i` is summable if and only if for any `ε > 0`,
  there exists a finite set `s` such that the sum `∑ i ∈ t, f i` over any finite set `t` disjoint
  with `s` has norm less than `ε`;

- `Summable.of_norm_bounded`, `Summable.of_norm_bounded_eventually`: if `‖f i‖` is bounded above by
  a summable series `∑' i, g i`, then `∑' i, f i` is summable as well; the same is true if the
  inequality hold only off some finite set.

- `tsum_of_norm_bounded`, `HasSum.norm_le_of_bounded`: if `‖f i‖ ≤ g i`, where `∑' i, g i` is a
  summable series, then `‖∑' i, f i‖ ≤ ∑' i, g i`.

- versions of these lemmas for `nnnorm` and `enorm`.

## Tags

infinite series, absolute convergence, normed group
-/

public section

open Topology ENNReal NNReal

open Finset Filter Metric

variable {ι α E F ε : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [TopologicalSpace ε] [ESeminormedAddCommMonoid ε]

/--
theorem `cauchySeq_finset_iff_vanishing_norm` / 定理 `cauchySeq_finset_iff_vanishing_norm`

English:
theorem cauchySeq_finset_iff_vanishing_norm
  given: {f : ι -> E}
  proof: by
  rw [cauchySeq_finset_iff_sum_vanishing]; rw [nhds_basis_ball.forall_iff]
  · simp only [ball_zero_eq, Set.mem_ofPred_eq]
  · rintro s t hst ⟨s', hs'⟩
exact ⟨s', fun t' ht' => hst hs' _ ht'⟩

中文:
定理 cauchySeq_finset_iff_vanishing_norm
  条件: {f : ι -> E}
  证明: by
  rw [cauchySeq_finset_iff_sum_vanishing]; rw [nhds_basis_ball.forall_iff]
  · simp only [ball_zero_eq, Set.mem_ofPred_eq]
  · rintro s t hst ⟨s', hs'⟩
exact ⟨s', fun t' ht' => hst hs' _ ht'⟩

Depends on / 依赖: Set.mem_ofPred_eq, ball_zero_eq, cauchySeq_finset_iff_sum_vanishing, forall_iff, mem_ofPred_eq, nhds_basis_ball, nhds_basis_ball.forall_iff
-/
theorem cauchySeq_finset_iff_vanishing_norm {f : ι -> E} :
    (CauchySeq fun s : Finset ι => ∑ i in s, f i) ↔
      forall ε > (0 : Real), exists s : Finset ι, forall t, Disjoint t s -> ‖∑ i in t, f i‖ < ε := by
  rw [cauchySeq_finset_iff_sum_vanishing]; rw [nhds_basis_ball.forall_iff]
  · simp only [ball_zero_eq, Set.mem_ofPred_eq]
  · rintro s t hst ⟨s', hs'⟩
exact ⟨s', fun t' ht' => hst hs' _ ht'⟩

/--
theorem `summable_iff_vanishing_norm` / 定理 `summable_iff_vanishing_norm`

English:
theorem summable_iff_vanishing_norm
  given: [CompleteSpace E] {f : ι -> E}
  proof: by
  rw [summable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_vanishing_norm]

中文:
定理 summable_iff_vanishing_norm
  条件: [CompleteSpace E] {f : ι -> E}
  证明: by
  rw [summable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_vanishing_norm]

Depends on / 依赖: cauchySeq_finset_iff_vanishing_norm, summable_iff_cauchySeq_finset
-/
theorem summable_iff_vanishing_norm [CompleteSpace E] {f : ι -> E} :
    Summable f ↔ forall ε > (0 : Real), exists s : Finset ι, forall t, Disjoint t s -> ‖∑ i in t, f i‖ < ε := by
  rw [summable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_vanishing_norm]

/--
theorem `cauchySeq_finset_of_norm_bounded_eventually` / 定理 `cauchySeq_finset_of_norm_bounded_eventually`

English:
theorem cauchySeq_finset_of_norm_bounded_eventually
  statement: {f : ι -> E} {g : ι -> Real} (hg : Summable g)
  proof: by
  refine cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => ?_
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩
  classical
  refine ⟨s union h.toFinset, fun t ht => ?_⟩
  have : forall i in t, ‖f i‖ <= g i := by
    intro i hi
    simp only [disjoint_left, mem_union, not_or, h.mem_toFi

中文:
定理 cauchySeq_finset_of_norm_bounded_eventually
  结论: {f : ι -> E} {g : ι -> 实数} (hg : Summable g)
  证明: by
  refine cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => ?_
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩
  classical
  refine ⟨s union h.toFinset, fun t ht => ?_⟩
  have : forall i in t, ‖f i‖ <= g i := by
    intro i hi
    simp only [disjoint_left, mem_union, not_or, h.mem_toFi

Depends on / 依赖: Classical, Classical.not_not, Set.mem_compl_iff, cauchySeq_finset_iff_vanishing_norm, classical, disjoint_left, h.mem_toFinset, h.toFinset, ht.mono_right, le_abs_self, le_sup_left, mem_compl_iff, mem_toFinset, mem_union, mono_right, norm_sum_le_of_le, not_not, not_or, summable_iff_vanishing_norm, toFinset
-/
theorem cauchySeq_finset_of_norm_bounded_eventually {f : ι -> E} {g : ι -> Real} (hg : Summable g)
    (h : forallᶠ i in cofinite, ‖f i‖ <= g i) : CauchySeq fun s => ∑ i in s, f i := by
  refine cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => ?_
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩
  classical
  refine ⟨s union h.toFinset, fun t ht => ?_⟩
  have : forall i in t, ‖f i‖ <= g i := by
    intro i hi
    simp only [disjoint_left, mem_union, not_or, h.mem_toFinset, Set.mem_compl_iff,
      Classical.not_not] at ht
    exact (ht hi).2
  calc
    ‖∑ i in t, f i‖ <= ∑ i in t, g i := norm_sum_le_of_le _ this
    _ <= ‖∑ i in t, g i‖ := le_abs_self _
    _ < ε := hs _ (ht.mono_right le_sup_left)

/--
theorem `cauchySeq_finset_of_norm_bounded` / 定理 `cauchySeq_finset_of_norm_bounded`

English:
theorem cauchySeq_finset_of_norm_bounded
  statement: {f : ι -> E} {g : ι -> Real} (hg : Summable g)
  proof: cauchySeq_finset_of_norm_bounded_eventually hg Eventually.of_forall h

中文:
定理 cauchySeq_finset_of_norm_bounded
  结论: {f : ι -> E} {g : ι -> 实数} (hg : Summable g)
  证明: cauchySeq_finset_of_norm_bounded_eventually hg Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, cauchySeq_finset_of_norm_bounded_eventually, of_forall
-/
theorem cauchySeq_finset_of_norm_bounded {f : ι -> E} {g : ι -> Real} (hg : Summable g)
    (h : forall i, ‖f i‖ <= g i) : CauchySeq fun s : Finset ι => ∑ i in s, f i :=
cauchySeq_finset_of_norm_bounded_eventually hg Eventually.of_forall h

/--
theorem `cauchySeq_range_of_norm_bounded` / 定理 `cauchySeq_range_of_norm_bounded`

English:
theorem cauchySeq_range_of_norm_bounded
  statement: {f : Nat -> E} {g : Nat -> Real}
  proof: by
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  refine (Metric.cauchySeq_iff'.1 hg ε hε).imp fun N hg n hn => ?_
  specialize hg n hn
  rw [dist_eq_norm]; rw [← sum_Ico_eq_sub _ hn] at hg ⊢
  calc
    ‖∑ k in Ico N n, f k‖ <= ∑ k in _, ‖f k‖ := norm_sum_le _ _
    _ <= ∑ k in _, g k := sum_le_s

中文:
定理 cauchySeq_range_of_norm_bounded
  结论: {f : 自然数 -> E} {g : 自然数 -> 实数}
  证明: by
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  refine (Metric.cauchySeq_iff'.1 hg ε hε).imp fun N hg n hn => ?_
  specialize hg n hn
  rw [dist_eq_norm]; rw [← sum_Ico_eq_sub _ hn] at hg ⊢
  calc
    ‖∑ k in Ico N n, f k‖ <= ∑ k in _, ‖f k‖ := norm_sum_le _ _
    _ <= ∑ k in _, g k := sum_le_s

Depends on / 依赖: Metric, Metric.cauchySeq_iff, cauchySeq_iff, dist_eq_norm, le_abs_self, norm_sum_le, specialize, sum_Ico_eq_sub, sum_le_sum
-/
theorem cauchySeq_range_of_norm_bounded {f : Nat -> E} {g : Nat -> Real}
    (hg : CauchySeq fun n => ∑ i in range n, g i) (hf : forall i, ‖f i‖ <= g i) :
    CauchySeq fun n => ∑ i in range n, f i := by
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  refine (Metric.cauchySeq_iff'.1 hg ε hε).imp fun N hg n hn => ?_
  specialize hg n hn
  rw [dist_eq_norm]; rw [← sum_Ico_eq_sub _ hn] at hg ⊢
  calc
    ‖∑ k in Ico N n, f k‖ <= ∑ k in _, ‖f k‖ := norm_sum_le _ _
    _ <= ∑ k in _, g k := sum_le_sum fun x _ => hf x
    _ <= ‖∑ k in _, g k‖ := le_abs_self _
    _ < ε := hg

/--
theorem `cauchySeq_finset_of_summable_norm` / 定理 `cauchySeq_finset_of_summable_norm`

English:
theorem cauchySeq_finset_of_summable_norm
  given: {f : ι -> E} (hf : Summable fun a => ‖f a‖)
  proof: cauchySeq_finset_of_norm_bounded hf fun _i => le_rfl

中文:
定理 cauchySeq_finset_of_summable_norm
  条件: {f : ι -> E} (hf : Summable fun a => ‖f a‖)
  证明: cauchySeq_finset_of_norm_bounded hf fun _i => le_rfl

Depends on / 依赖: cauchySeq_finset_of_norm_bounded, le_rfl
-/
theorem cauchySeq_finset_of_summable_norm {f : ι -> E} (hf : Summable fun a => ‖f a‖) :
    CauchySeq fun s : Finset ι => ∑ a in s, f a :=
  cauchySeq_finset_of_norm_bounded hf fun _i => le_rfl

/--
theorem `hasSum_of_subseq_of_summable` / 定理 `hasSum_of_subseq_of_summable`

English:
theorem hasSum_of_subseq_of_summable
  statement: {f : ι -> E} (hf : Summable fun a => ‖f a‖) {s : α -> Finset ι}
  proof: tendsto_nhds_of_cauchySeq_of_subseq (cauchySeq_finset_of_summable_norm hf) hs ha

中文:
定理 hasSum_of_subseq_of_summable
  结论: {f : ι -> E} (hf : Summable fun a => ‖f a‖) {s : α -> Finset ι}
  证明: tendsto_nhds_of_cauchySeq_of_subseq (cauchySeq_finset_of_summable_norm hf) hs ha

Depends on / 依赖: cauchySeq_finset_of_summable_norm, tendsto_nhds_of_cauchySeq_of_subseq
-/
theorem hasSum_of_subseq_of_summable {f : ι -> E} (hf : Summable fun a => ‖f a‖) {s : α -> Finset ι}
    {p : Filter α} [NeBot p] (hs : Tendsto s p atTop) {a : E}
    (ha : Tendsto (fun b => ∑ i in s b, f i) p (𝓝 a)) : HasSum f a :=
  tendsto_nhds_of_cauchySeq_of_subseq (cauchySeq_finset_of_summable_norm hf) hs ha

/--
theorem `hasSum_iff_tendsto_nat_of_summable_norm` / 定理 `hasSum_iff_tendsto_nat_of_summable_norm`

English:
theorem hasSum_iff_tendsto_nat_of_summable_norm
  given: {f : Nat -> E} {a : E} (hf : Summable fun i => ‖f i‖)
  proof: ⟨fun h => h.tendsto_sum_nat, fun h => hasSum_of_subseq_of_summable hf tendsto_finset_range h⟩

中文:
定理 hasSum_iff_tendsto_nat_of_summable_norm
  条件: {f : 自然数 -> E} {a : E} (hf : Summable fun i => ‖f i‖)
  证明: ⟨fun h => h.tendsto_sum_nat, fun h => hasSum_of_subseq_of_summable hf tendsto_finset_range h⟩

Depends on / 依赖: h.tendsto_sum_nat, hasSum_of_subseq_of_summable, tendsto_finset_range, tendsto_sum_nat
-/
theorem hasSum_iff_tendsto_nat_of_summable_norm {f : Nat -> E} {a : E} (hf : Summable fun i => ‖f i‖) :
    HasSum f a ↔ Tendsto (fun n : Nat => ∑ i in range n, f i) atTop (𝓝 a) :=
  ⟨fun h => h.tendsto_sum_nat, fun h => hasSum_of_subseq_of_summable hf tendsto_finset_range h⟩

/--
theorem `Summable.of_norm_bounded` / 定理 `Summable.of_norm_bounded`

English:
theorem Summable.of_norm_bounded
  statement: [CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g)
  proof: by
  rw [summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_of_norm_bounded hg h

中文:
定理 Summable.of_norm_bounded
  结论: [CompleteSpace E] {f : ι -> E} {g : ι -> 实数} (hg : Summable g)
  证明: by
  rw [summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_of_norm_bounded hg h

Depends on / 依赖: cauchySeq_finset_of_norm_bounded, summable_iff_cauchySeq_finset
-/
theorem Summable.of_norm_bounded [CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g)
    (h : forall i, ‖f i‖ <= g i) : Summable f := by
  rw [summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_of_norm_bounded hg h

/--
theorem `HasSum.enorm_le_of_bounded` / 定理 `HasSum.enorm_le_of_bounded`

English:
theorem HasSum.enorm_le_of_bounded
  statement: {f : ι -> ε} {g : ι -> Real>=0∞} {a : ε} {b : Real>=0∞} (hf : HasSum f a)
  proof: by
  exact le_of_tendsto_of_tendsto' hf.enorm hg fun _s => enorm_sum_le_of_le _ fun i _hi => h i

中文:
定理 HasSum.enorm_le_of_bounded
  结论: {f : ι -> ε} {g : ι -> 实数>=0∞} {a : ε} {b : 实数>=0∞} (hf : HasSum f a)
  证明: by
  exact le_of_tendsto_of_tendsto' hf.enorm hg fun _s => enorm_sum_le_of_le _ fun i _hi => h i

Depends on / 依赖: enorm_sum_le_of_le, hf.enorm, le_of_tendsto_of_tendsto
-/
theorem HasSum.enorm_le_of_bounded {f : ι -> ε} {g : ι -> Real>=0∞} {a : ε} {b : Real>=0∞} (hf : HasSum f a)
    (hg : HasSum g b) (h : forall i, ‖f i‖ₑ <= g i) : ‖a‖ₑ <= b := by
  exact le_of_tendsto_of_tendsto' hf.enorm hg fun _s => enorm_sum_le_of_le _ fun i _hi => h i

/--
theorem `HasSum.norm_le_of_bounded` / 定理 `HasSum.norm_le_of_bounded`

English:
theorem HasSum.norm_le_of_bounded
  statement: {f : ι -> E} {g : ι -> Real} {a : E} {b : Real} (hf : HasSum f a)
  proof: by
  exact le_of_tendsto_of_tendsto' hf.norm hg fun _s => norm_sum_le_of_le _ fun i _hi => h i

中文:
定理 HasSum.norm_le_of_bounded
  结论: {f : ι -> E} {g : ι -> 实数} {a : E} {b : 实数} (hf : HasSum f a)
  证明: by
  exact le_of_tendsto_of_tendsto' hf.norm hg fun _s => norm_sum_le_of_le _ fun i _hi => h i

Depends on / 依赖: hf.norm, le_of_tendsto_of_tendsto, norm_sum_le_of_le
-/
theorem HasSum.norm_le_of_bounded {f : ι -> E} {g : ι -> Real} {a : E} {b : Real} (hf : HasSum f a)
    (hg : HasSum g b) (h : forall i, ‖f i‖ <= g i) : ‖a‖ <= b := by
  exact le_of_tendsto_of_tendsto' hf.norm hg fun _s => norm_sum_le_of_le _ fun i _hi => h i

/--
theorem `tsum_of_enorm_bounded` / 定理 `tsum_of_enorm_bounded`

English:
theorem tsum_of_enorm_bounded
  statement: {f : ι -> ε} {g : ι -> Real>=0∞} {a : Real>=0∞} (hg : HasSum g a)
  proof: by
  by_cases hf : Summable f
  · exact hf.hasSum.enorm_le_of_bounded hg h
  · simp [tsum_eq_zero_of_not_summable hf]

中文:
定理 tsum_of_enorm_bounded
  结论: {f : ι -> ε} {g : ι -> 实数>=0∞} {a : 实数>=0∞} (hg : HasSum g a)
  证明: by
  by_cases hf : Summable f
  · exact hf.hasSum.enorm_le_of_bounded hg h
  · simp [tsum_eq_zero_of_not_summable hf]

Depends on / 依赖: Summable, enorm_le_of_bounded, hasSum, hf.hasSum.enorm_le_of_bounded, tsum_eq_zero_of_not_summable
-/
theorem tsum_of_enorm_bounded {f : ι -> ε} {g : ι -> Real>=0∞} {a : Real>=0∞} (hg : HasSum g a)
    (h : forall i, ‖f i‖ₑ <= g i) : ‖∑' i : ι, f i‖ₑ <= a := by
  by_cases hf : Summable f
  · exact hf.hasSum.enorm_le_of_bounded hg h
  · simp [tsum_eq_zero_of_not_summable hf]

/--
theorem `enorm_tsum_le_tsum_enorm` / 定理 `enorm_tsum_le_tsum_enorm`

English:
theorem enorm_tsum_le_tsum_enorm
  given: {f : ι -> ε}
  proof: tsum_of_enorm_bounded ENNReal.summable.hasSum fun _i => le_rfl

中文:
定理 enorm_tsum_le_tsum_enorm
  条件: {f : ι -> ε}
  证明: tsum_of_enorm_bounded ENNReal.summable.hasSum fun _i => le_rfl

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, hasSum, le_rfl, summable, tsum_of_enorm_bounded
-/
theorem enorm_tsum_le_tsum_enorm {f : ι -> ε} :
    ‖∑' i, f i‖ₑ <= ∑' i, ‖f i‖ₑ :=
  tsum_of_enorm_bounded ENNReal.summable.hasSum fun _i => le_rfl

/--
theorem `tsum_of_norm_bounded` / 定理 `tsum_of_norm_bounded`

English:
theorem tsum_of_norm_bounded
  statement: {f : ι -> E} {g : ι -> Real} {a : Real} (hg : HasSum g a)
  proof: by
  by_cases hf : Summable f
  · exact hf.hasSum.norm_le_of_bounded hg h
  · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
    exact ge_of_tendsto' hg fun s => sum_nonneg fun i _hi => (norm_nonneg _).trans (h i)

中文:
定理 tsum_of_norm_bounded
  结论: {f : ι -> E} {g : ι -> 实数} {a : 实数} (hg : HasSum g a)
  证明: by
  by_cases hf : Summable f
  · exact hf.hasSum.norm_le_of_bounded hg h
  · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
    exact ge_of_tendsto' hg fun s => sum_nonneg fun i _hi => (norm_nonneg _).trans (h i)

Depends on / 依赖: Summable, ge_of_tendsto, hasSum, hf.hasSum.norm_le_of_bounded, norm_le_of_bounded, norm_nonneg, norm_zero, sum_nonneg, tsum_eq_zero_of_not_summable
-/
theorem tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} {a : Real} (hg : HasSum g a)
    (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a := by
  by_cases hf : Summable f
  · exact hf.hasSum.norm_le_of_bounded hg h
  · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
    exact ge_of_tendsto' hg fun s => sum_nonneg fun i _hi => (norm_nonneg _).trans (h i)

/--
theorem `norm_tsum_le_tsum_norm` / 定理 `norm_tsum_le_tsum_norm`

English:
theorem norm_tsum_le_tsum_norm
  given: {f : ι -> E} (hf : Summable fun i => ‖f i‖)
  proof: tsum_of_norm_bounded hf.hasSum fun _i => le_rfl

中文:
定理 norm_tsum_le_tsum_norm
  条件: {f : ι -> E} (hf : Summable fun i => ‖f i‖)
  证明: tsum_of_norm_bounded hf.hasSum fun _i => le_rfl

Depends on / 依赖: hasSum, hf.hasSum, le_rfl, tsum_of_norm_bounded
-/
theorem norm_tsum_le_tsum_norm {f : ι -> E} (hf : Summable fun i => ‖f i‖) :
    ‖∑' i, f i‖ <= ∑' i, ‖f i‖ :=
  tsum_of_norm_bounded hf.hasSum fun _i => le_rfl

/--
theorem `tsum_of_nnnorm_bounded` / 定理 `tsum_of_nnnorm_bounded`

English:
theorem tsum_of_nnnorm_bounded
  statement: {f : ι -> E} {g : ι -> Real>=0} {a : Real>=0} (hg : HasSum g a)
  proof: by
  simp only [← NNReal.coe_le_coe, ← NNReal.hasSum_coe, coe_nnnorm] at *
  exact tsum_of_norm_bounded hg h

中文:
定理 tsum_of_nnnorm_bounded
  结论: {f : ι -> E} {g : ι -> 实数>=0} {a : 实数>=0} (hg : HasSum g a)
  证明: by
  simp only [← NNReal.coe_le_coe, ← NNReal.hasSum_coe, coe_nnnorm] at *
  exact tsum_of_norm_bounded hg h

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.hasSum_coe, coe_le_coe, coe_nnnorm, hasSum_coe, tsum_of_norm_bounded
-/
theorem tsum_of_nnnorm_bounded {f : ι -> E} {g : ι -> Real>=0} {a : Real>=0} (hg : HasSum g a)
    (h : forall i, ‖f i‖₊ <= g i) : ‖∑' i : ι, f i‖₊ <= a := by
  simp only [← NNReal.coe_le_coe, ← NNReal.hasSum_coe, coe_nnnorm] at *
  exact tsum_of_norm_bounded hg h

/--
theorem `nnnorm_tsum_le` / 定理 `nnnorm_tsum_le`

English:
theorem nnnorm_tsum_le
  given: {f : ι -> E} (hf : Summable fun i => ‖f i‖₊)
  statement: ‖∑' i, f i‖₊ <= ∑' i, ‖f i‖₊
  proof: tsum_of_nnnorm_bounded hf.hasSum fun _i => le_rfl

中文:
定理 nnnorm_tsum_le
  条件: {f : ι -> E} (hf : Summable fun i => ‖f i‖₊)
  结论: ‖∑' i, f i‖₊ <= ∑' i, ‖f i‖₊
  证明: tsum_of_nnnorm_bounded hf.hasSum fun _i => le_rfl

Depends on / 依赖: hasSum, hf.hasSum, le_rfl, tsum_of_nnnorm_bounded
-/
theorem nnnorm_tsum_le {f : ι -> E} (hf : Summable fun i => ‖f i‖₊) : ‖∑' i, f i‖₊ <= ∑' i, ‖f i‖₊ :=
  tsum_of_nnnorm_bounded hf.hasSum fun _i => le_rfl

/--
theorem `tsum_enorm_ne_top_iff_summable_nnnorm` / 定理 `tsum_enorm_ne_top_iff_summable_nnnorm`

English:
theorem tsum_enorm_ne_top_iff_summable_nnnorm
  given: {ι : Type*} {f : ι -> E}
  proof: by
  simp only [enorm_eq_nnnorm, ENNReal.tsum_coe_ne_top_iff_summable]

中文:
定理 tsum_enorm_ne_top_iff_summable_nnnorm
  条件: {ι : 类型} {f : ι -> E}
  证明: by
  simp only [enorm_eq_nnnorm, ENNReal.tsum_coe_ne_top_iff_summable]

Depends on / 依赖: ENNReal, ENNReal.tsum_coe_ne_top_iff_summable, enorm_eq_nnnorm, tsum_coe_ne_top_iff_summable
-/
theorem tsum_enorm_ne_top_iff_summable_nnnorm {ι : Type*} {f : ι -> E} :
    ∑' i, ‖f i‖ₑ != ∞ ↔ Summable fun i => ‖f i‖₊ := by
  simp only [enorm_eq_nnnorm, ENNReal.tsum_coe_ne_top_iff_summable]

/--
lemma `tsum_enorm_ne_top_iff_summable_norm` / 引理 `tsum_enorm_ne_top_iff_summable_norm`

English:
lemma tsum_enorm_ne_top_iff_summable_norm
  given: {ι : Type*} {f : ι -> E}
  proof: by
  simp only [tsum_enorm_ne_top_iff_summable_nnnorm, ← coe_nnnorm, NNReal.summable_coe]

中文:
引理 tsum_enorm_ne_top_iff_summable_norm
  条件: {ι : 类型} {f : ι -> E}
  证明: by
  simp only [tsum_enorm_ne_top_iff_summable_nnnorm, ← coe_nnnorm, NNReal.summable_coe]

Depends on / 依赖: NNReal, NNReal.summable_coe, coe_nnnorm, summable_coe, tsum_enorm_ne_top_iff_summable_nnnorm
-/
lemma tsum_enorm_ne_top_iff_summable_norm {ι : Type*} {f : ι -> E} :
    ∑' i, ‖f i‖ₑ != ∞ ↔ Summable fun i => ‖f i‖ := by
  simp only [tsum_enorm_ne_top_iff_summable_nnnorm, ← coe_nnnorm, NNReal.summable_coe]

variable [CompleteSpace E]

/--
theorem `Summable.of_norm_bounded_eventually` / 定理 `Summable.of_norm_bounded_eventually`

English:
theorem Summable.of_norm_bounded_eventually
  statement: {f : ι -> E} {g : ι -> Real} (hg : Summable g)
  proof: summable_iff_cauchySeq_finset.2 cauchySeq_finset_of_norm_bounded_eventually hg h

中文:
定理 Summable.of_norm_bounded_eventually
  结论: {f : ι -> E} {g : ι -> 实数} (hg : Summable g)
  证明: summable_iff_cauchySeq_finset.2 cauchySeq_finset_of_norm_bounded_eventually hg h

Depends on / 依赖: cauchySeq_finset_of_norm_bounded_eventually, summable_iff_cauchySeq_finset
-/
theorem Summable.of_norm_bounded_eventually {f : ι -> E} {g : ι -> Real} (hg : Summable g)
    (h : forallᶠ i in cofinite, ‖f i‖ <= g i) : Summable f :=
summable_iff_cauchySeq_finset.2 cauchySeq_finset_of_norm_bounded_eventually hg h

/--
theorem `Summable.of_norm_bounded_eventually_nat` / 定理 `Summable.of_norm_bounded_eventually_nat`

English:
theorem Summable.of_norm_bounded_eventually_nat
  statement: {f : Nat -> E} {g : Nat -> Real} (hg : Summable g)
  proof: .of_norm_bounded_eventually hg Nat.cofinite_eq_atTop ▸ h

中文:
定理 Summable.of_norm_bounded_eventually_nat
  结论: {f : 自然数 -> E} {g : 自然数 -> 实数} (hg : Summable g)
  证明: .of_norm_bounded_eventually hg Nat.cofinite_eq_atTop ▸ h

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, of_norm_bounded_eventually
-/
theorem Summable.of_norm_bounded_eventually_nat {f : Nat -> E} {g : Nat -> Real} (hg : Summable g)
    (h : forallᶠ i in atTop, ‖f i‖ <= g i) : Summable f :=
.of_norm_bounded_eventually hg Nat.cofinite_eq_atTop ▸ h

/--
theorem `Summable.of_nnnorm_bounded` / 定理 `Summable.of_nnnorm_bounded`

English:
theorem Summable.of_nnnorm_bounded
  statement: {f : ι -> E} {g : ι -> Real>=0} (hg : Summable g)
  proof: .of_norm_bounded (NNReal.summable_coe.2 hg) h

中文:
定理 Summable.of_nnnorm_bounded
  结论: {f : ι -> E} {g : ι -> 实数>=0} (hg : Summable g)
  证明: .of_norm_bounded (NNReal.summable_coe.2 hg) h

Depends on / 依赖: NNReal, NNReal.summable_coe, of_norm_bounded, summable_coe
-/
theorem Summable.of_nnnorm_bounded {f : ι -> E} {g : ι -> Real>=0} (hg : Summable g)
    (h : forall i, ‖f i‖₊ <= g i) : Summable f :=
  .of_norm_bounded (NNReal.summable_coe.2 hg) h

/--
theorem `Summable.of_norm` / 定理 `Summable.of_norm`

English:
theorem Summable.of_norm
  given: {f : ι -> E} (hf : Summable fun a => ‖f a‖)
  statement: Summable f
  proof: .of_norm_bounded hf fun _i => le_rfl

中文:
定理 Summable.of_norm
  条件: {f : ι -> E} (hf : Summable fun a => ‖f a‖)
  结论: Summable f
  证明: .of_norm_bounded hf fun _i => le_rfl

Depends on / 依赖: le_rfl, of_norm_bounded
-/
theorem Summable.of_norm {f : ι -> E} (hf : Summable fun a => ‖f a‖) : Summable f :=
  .of_norm_bounded hf fun _i => le_rfl

/--
theorem `Summable.of_nnnorm` / 定理 `Summable.of_nnnorm`

English:
theorem Summable.of_nnnorm
  given: {f : ι -> E} (hf : Summable fun a => ‖f a‖₊)
  statement: Summable f
  proof: .of_nnnorm_bounded hf fun _i => le_rfl

中文:
定理 Summable.of_nnnorm
  条件: {f : ι -> E} (hf : Summable fun a => ‖f a‖₊)
  结论: Summable f
  证明: .of_nnnorm_bounded hf fun _i => le_rfl

Depends on / 依赖: le_rfl, of_nnnorm_bounded
-/
theorem Summable.of_nnnorm {f : ι -> E} (hf : Summable fun a => ‖f a‖₊) : Summable f :=
  .of_nnnorm_bounded hf fun _i => le_rfl

/--
theorem `Summable.of_enorm` / 定理 `Summable.of_enorm`

English:
theorem Summable.of_enorm
  given: {f : ι -> E} (hf : ∑' a, ‖f a‖ₑ != ∞)
  statement: Summable f
  proof: Summable.of_nnnorm_bounded (tsum_coe_ne_top_iff_summable.1 hf) fun _i => le_rfl

中文:
定理 Summable.of_enorm
  条件: {f : ι -> E} (hf : ∑' a, ‖f a‖ₑ != ∞)
  结论: Summable f
  证明: Summable.of_nnnorm_bounded (tsum_coe_ne_top_iff_summable.1 hf) fun _i => le_rfl

Depends on / 依赖: Summable, Summable.of_nnnorm_bounded, le_rfl, of_nnnorm_bounded, tsum_coe_ne_top_iff_summable
-/
theorem Summable.of_enorm {f : ι -> E} (hf : ∑' a, ‖f a‖ₑ != ∞) : Summable f :=
  Summable.of_nnnorm_bounded (tsum_coe_ne_top_iff_summable.1 hf) fun _i => le_rfl
