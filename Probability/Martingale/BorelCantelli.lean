/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Order.Archimedean.IndicatorCard
public import Mathlib.Probability.Martingale.Centering
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalStopping

/-!

# Generalized Borel-Cantelli lemma

This file proves Lévy's generalized Borel-Cantelli lemma which is a generalization of the
Borel-Cantelli lemmas. With this generalization, one can easily deduce the Borel-Cantelli lemmas
by choosing appropriate filtrations. This file also contains the one-sided martingale bound which
is required to prove the generalized Borel-Cantelli.

**Note**: the usual Borel-Cantelli lemmas are not in this file.
See `MeasureTheory.measure_limsup_atTop_eq_zero` for the first (which does not depend on
the results here), and `ProbabilityTheory.measure_limsup_eq_one` for the second (which does).

## Main results

- `MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto`: the one-sided martingale bound: given
  a submartingale `f` with uniformly bounded differences, the set for which `f` converges is almost
  everywhere equal to the set for which it is bounded.
- `MeasureTheory.ae_mem_limsup_atTop_iff`: Lévy's generalized Borel-Cantelli:
  given a filtration `ℱ` and a sequence of sets `s` such that `s n ∈ ℱ n` for all `n`,
  `limsup atTop s` is almost everywhere equal to the set for which `∑ ℙ[s (n + 1)∣ℱ n] = ∞`.

-/

@[expose] public section


open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {ι Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
/-!
### One-sided martingale bound
-/

/--
Definition of `leastGE` / `leastGE` 的定义

English:
definition leastGE
  signature: [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
  body: hittingAfter f (Set.Ici r) ⊥

中文:
定义 leastGE
  签名: [预序 ι] [有底序 ι] [下确界集 ι] [预序 β]
  定义体: hittingAfter f (Set.Ici r) ⊥

Depends on / 依赖: Set.Ici, hittingAfter
-/
noncomputable def leastGE [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι -> Ω -> β) (r : β) : Ω -> WithTop ι :=
  hittingAfter f (Set.Ici r) ⊥

/--
theorem `StronglyAdapted.isStoppingTime_leastGE` / 定理 `StronglyAdapted.isStoppingTime_leastGE`

English:
theorem StronglyAdapted.isStoppingTime_leastGE
  statement: [ConditionallyCompleteLinearOrderBot ι]
  proof: hf.adapted.isStoppingTime_hittingAfter measurableSet_Ici

中文:
定理 StronglyAdapted.isStoppingTime_leastGE
  结论: [余nditionallyCompleteLinearOrderBot ι]
  证明: hf.adapted.isStoppingTime_hittingAfter measurableSet_Ici

Depends on / 依赖: adapted, hf.adapted.isStoppingTime_hittingAfter, isStoppingTime_hittingAfter, measurableSet_Ici
-/
theorem StronglyAdapted.isStoppingTime_leastGE [ConditionallyCompleteLinearOrderBot ι]
    {ℱ : Filtration ι m0} [WellFoundedLT ι] [Countable ι] [TopologicalSpace β]
    [Preorder β] [ClosedIciTopology β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {f : ι -> Ω -> β} (r : β) (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (leastGE f r) :=
  hf.adapted.isStoppingTime_hittingAfter measurableSet_Ici

/--
Definition of `stoppedAbove` / `stoppedAbove` 的定义

English:
definition stoppedAbove
  signature: [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β]
  body: stoppedProcess f (leastGE f r)

中文:
定义 stoppedAbove
  签名: [线性序 ι] [有底序 ι] [下确界集 ι] [预序 β]
  定义体: stoppedProcess f (leastGE f r)

Depends on / 依赖: leastGE, stoppedProcess
-/
noncomputable def stoppedAbove [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι -> Ω -> β) (r : β) : ι -> Ω -> β :=
  stoppedProcess f (leastGE f r)

variable {ℱ : Filtration Nat m0} {f : Nat -> Ω -> Real}

/--
lemma `Submartingale.stoppedAbove` / 引理 `Submartingale.stoppedAbove`

English:
lemma Submartingale.stoppedAbove
  given: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (r : Real)
  proof: hf.stoppedProcess (hf.stronglyAdapted.isStoppingTime_leastGE r)

中文:
引理 Submartingale.stoppedAbove
  条件: [是有限测度 μ] (hf : Submartingale f ℱ μ) (r : 实数)
  证明: hf.stoppedProcess (hf.stronglyAdapted.isStoppingTime_leastGE r)
-/
protected lemma Submartingale.stoppedAbove [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (r : Real) :
    Submartingale (stoppedAbove f r) ℱ μ :=
  hf.stoppedProcess (hf.stronglyAdapted.isStoppingTime_leastGE r)

variable {r : Real} {R : Real>=0}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `stoppedAbove_le` / 定理 `stoppedAbove_le`

English:
theorem stoppedAbove_le
  statement: (hr : 0 <= r) (hf0 : f 0 = 0)
  proof: by
  filter_upwards [hbdd] with ω hbddω
  rw [stoppedAbove]; rw [stoppedProcess]; rw [ENat.some_eq_natCast]
  by_cases h_zero : (min (i : Nat∞) (leastGE f r ω)).untopA = 0
  · simp only [h_zero, hf0, Pi.zero_apply]
    positivity
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h_zero
  rw [hk]; rw [add_comm r]; rw [← sub_le_iff_le_add]
  have := notMem_of_lt_hittingAfter (?_ : k < leastGE f r ω)
  · simp only [bot_eq_zero, zero_le, Set.mem_Ici, not_le, forall_const] at this
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _))
  · suffices (k : Nat∞) < min (i : Nat∞) (leastGE f r ω) from this.trans_le (min_le_right _ _)
    have h_top : min (i : Nat∞) (leastGE f r ω) != ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    lift min (i : Nat∞) (leastGE f r ω) to Nat using h_top with p
    simp only [untopD_coe_enat, Nat.cast_lt, gt_iff_lt] at *
    lia

中文:
定理 stoppedAbove_le
  结论: (hr : 0 <= r) (hf0 : f 0 = 0)
  证明: by
  filter_upwards [hbdd] with ω hbddω
  rw [stoppedAbove]; rw [stoppedProcess]; rw [ENat.some_eq_natCast]
  by_cases h_zero : (min (i : Nat∞) (leastGE f r ω)).untopA = 0
  · simp only [h_zero, hf0, Pi.zero_apply]
    positivity
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h_zero
  rw [hk]; rw [add_comm r]; rw [← sub_le_iff_le_add]
  have := notMem_of_lt_hittingAfter (?_ : k < leastGE f r ω)
  · simp only [bot_eq_zero, zero_le, Set.mem_Ici, not_le, forall_const] at this
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _))
  · suffices (k : Nat∞) < min (i : Nat∞) (leastGE f r ω) from this.trans_le (min_le_right _ _)
    have h_top : min (i : Nat∞) (leastGE f r ω) != ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    lift min (i : Nat∞) (leastGE f r ω) to Nat using h_top with p
    simp only [untopD_coe_enat, Nat.cast_lt, gt_iff_lt] at *
    lia

Depends on / 依赖: ENat.some_eq_natCast, Nat.exists_eq_add_one_of_ne_zero, Pi.zero_apply, Set.mem_Ici, add_comm, bot_eq_zero, exists_eq_add_one_of_ne_zero, filter_upwards, forall_const, h_zero, le.tr, leastGE, mem_Ici, notMem_of_lt_hittingAfter, not_le, some_eq_natCast, stoppedAbove, stoppedProcess, sub_le_iff_le_add, sub_lt_sub_left
-/
theorem stoppedAbove_le (hr : 0 <= r) (hf0 : f 0 = 0)
    (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) (i : Nat) :
    forallᵐ ω ∂μ, stoppedAbove f r i ω <= r + R := by
  filter_upwards [hbdd] with ω hbddω
  rw [stoppedAbove]; rw [stoppedProcess]; rw [ENat.some_eq_natCast]
  by_cases h_zero : (min (i : Nat∞) (leastGE f r ω)).untopA = 0
  · simp only [h_zero, hf0, Pi.zero_apply]
    positivity
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h_zero
  rw [hk]; rw [add_comm r]; rw [← sub_le_iff_le_add]
  have := notMem_of_lt_hittingAfter (?_ : k < leastGE f r ω)
  · simp only [bot_eq_zero, zero_le, Set.mem_Ici, not_le, forall_const] at this
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _))
  · suffices (k : Nat∞) < min (i : Nat∞) (leastGE f r ω) from this.trans_le (min_le_right _ _)
    have h_top : min (i : Nat∞) (leastGE f r ω) != ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    lift min (i : Nat∞) (leastGE f r ω) to Nat using h_top with p
    simp only [untopD_coe_enat, Nat.cast_lt, gt_iff_lt] at *
    lia

/--
theorem `Submartingale.eLpNorm_stoppedAbove_le` / 定理 `Submartingale.eLpNorm_stoppedAbove_le`

English:
theorem Submartingale.eLpNorm_stoppedAbove_le
  statement: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: by
  refine eLpNorm_one_le_of_le' ((hf.stoppedAbove r).integrable _) ?_
    (stoppedAbove_le hr hf0 hbdd i)
  rw [← setIntegral_univ]
  refine le_trans ?_ ((hf.stoppedAbove r).setIntegral_le zero_le MeasurableSet.univ)
  simp [stoppedAbove, stoppedProcess, hf0]

中文:
定理 Submartingale.eLpNorm_stoppedAbove_le
  结论: [是有限测度 μ] (hf : Submartingale f ℱ μ)
  证明: by
  refine eLpNorm_one_le_of_le' ((hf.stoppedAbove r).integrable _) ?_
    (stoppedAbove_le hr hf0 hbdd i)
  rw [← setIntegral_univ]
  refine le_trans ?_ ((hf.stoppedAbove r).setIntegral_le zero_le MeasurableSet.univ)
  simp [stoppedAbove, stoppedProcess, hf0]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, eLpNorm_one_le_of_le, hf.stoppedAbove, integrable, le_trans, setIntegral_le, setIntegral_univ, stoppedAbove, stoppedAbove_le, stoppedProcess, zero_le
-/
theorem Submartingale.eLpNorm_stoppedAbove_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hr : 0 <= r) (hf0 : f 0 = 0) (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) (i : Nat) :
    eLpNorm (stoppedAbove f r i) 1 μ <= 2 * μ Set.univ * ENNReal.ofReal (r + R) := by
  refine eLpNorm_one_le_of_le' ((hf.stoppedAbove r).integrable _) ?_
    (stoppedAbove_le hr hf0 hbdd i)
  rw [← setIntegral_univ]
  refine le_trans ?_ ((hf.stoppedAbove r).setIntegral_le zero_le MeasurableSet.univ)
  simp [stoppedAbove, stoppedProcess, hf0]

/--
theorem `Submartingale.eLpNorm_stoppedAbove_le'` / 定理 `Submartingale.eLpNorm_stoppedAbove_le'`

English:
theorem Submartingale.eLpNorm_stoppedAbove_le'
  statement: [IsFiniteMeasure μ]
  proof: by
  refine (hf.eLpNorm_stoppedAbove_le hr hf0 hbdd i).trans ?_
  simp [ENNReal.coe_toNNReal (measure_ne_top μ _), ENNReal.coe_toNNReal]

中文:
定理 Submartingale.eLpNorm_stoppedAbove_le'
  结论: [是有限测度 μ]
  证明: by
  refine (hf.eLpNorm_stoppedAbove_le hr hf0 hbdd i).trans ?_
  simp [ENNReal.coe_toNNReal (measure_ne_top μ _), ENNReal.coe_toNNReal]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, coe_toNNReal, eLpNorm_stoppedAbove_le, hf.eLpNorm_stoppedAbove_le, measure_ne_top
-/
theorem Submartingale.eLpNorm_stoppedAbove_le' [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hr : 0 <= r) (hf0 : f 0 = 0)
    (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) (i : Nat) :
    eLpNorm (stoppedAbove f r i) 1 μ
      <= ENNReal.toNNReal (2 * μ Set.univ * ENNReal.ofReal (r + R)) := by
  refine (hf.eLpNorm_stoppedAbove_le hr hf0 hbdd i).trans ?_
  simp [ENNReal.coe_toNNReal (measure_ne_top μ _), ENNReal.coe_toNNReal]

/--
theorem `Submartingale.exists_tendsto_of_abs_bddAbove_aux` / 定理 `Submartingale.exists_tendsto_of_abs_bddAbove_aux`

English:
theorem Submartingale.exists_tendsto_of_abs_bddAbove_aux
  statement: [IsFiniteMeasure μ]
  proof: by
  have ht : forallᵐ ω ∂μ, forall i : Nat, exists c, Tendsto (fun n => stoppedAbove f i n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    exact fun i => Submartingale.exists_ae_tendsto_of_bdd (hf.stoppedAbove i)
      (hf.eLpNorm_stoppedAbove_le' i.cast_nonneg hf0 hbdd)
  filter_upwards [ht] with ω hω hωb
  rw [BddAbove] at hωb
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some
  have hib : forall n, f n ω < i := by
    intro n
    exact lt_of_le_of_lt ((mem_upperBounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi
  have heq : forall n, stoppedAbove f i n ω = f n ω := by
    intro n
    rw [stoppedAbove]; rw [stoppedProcess]; rw [leastGE]; rw [hittingAfter_eq_top_iff.mpr]
    · simp only [le_top, inf_of_le_left]
      congr
    · simp [hib]
  simp only [← heq, hω i]

中文:
定理 Submartingale.存在_tendsto_of_abs_bddAbove_aux
  结论: [是有限测度 μ]
  证明: by
  have ht : forallᵐ ω ∂μ, forall i : Nat, exists c, Tendsto (fun n => stoppedAbove f i n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    exact fun i => Submartingale.exists_ae_tendsto_of_bdd (hf.stoppedAbove i)
      (hf.eLpNorm_stoppedAbove_le' i.cast_nonneg hf0 hbdd)
  filter_upwards [ht] with ω hω hωb
  rw [BddAbove] at hωb
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some
  have hib : forall n, f n ω < i := by
    intro n
    exact lt_of_le_of_lt ((mem_upperBounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi
  have heq : forall n, stoppedAbove f i n ω = f n ω := by
    intro n
    rw [stoppedAbove]; rw [stoppedProcess]; rw [leastGE]; rw [hittingAfter_eq_top_iff.mpr]
    · simp only [le_top, inf_of_le_left]
      congr
    · simp [hib]
  simp only [← heq, hω i]

Depends on / 依赖: BddAbove, Submartingale, Submartingale.exists_ae_tendsto_of_bdd, Tendsto, ae_all_iff, b.some, b.some_mem, cast_nonneg, eLpNorm_stoppedAbove_le, exists_ae_tendsto_of_bdd, exists_nat_gt, filter_upwards, hf.eLpNorm_stoppedAbove_le, hf.stoppedAbove, i.cast_nonneg, lt_of_le_of_lt, mem_upperBounds, some_mem, stoppedAbove
-/
theorem Submartingale.exists_tendsto_of_abs_bddAbove_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hf0 : f 0 = 0) (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) :
    forallᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) -> exists c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  have ht : forallᵐ ω ∂μ, forall i : Nat, exists c, Tendsto (fun n => stoppedAbove f i n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    exact fun i => Submartingale.exists_ae_tendsto_of_bdd (hf.stoppedAbove i)
      (hf.eLpNorm_stoppedAbove_le' i.cast_nonneg hf0 hbdd)
  filter_upwards [ht] with ω hω hωb
  rw [BddAbove] at hωb
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some
  have hib : forall n, f n ω < i := by
    intro n
    exact lt_of_le_of_lt ((mem_upperBounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi
  have heq : forall n, stoppedAbove f i n ω = f n ω := by
    intro n
    rw [stoppedAbove]; rw [stoppedProcess]; rw [leastGE]; rw [hittingAfter_eq_top_iff.mpr]
    · simp only [le_top, inf_of_le_left]
      congr
    · simp [hib]
  simp only [← heq, hω i]

/--
theorem `Submartingale.bddAbove_iff_exists_tendsto_aux` / 定理 `Submartingale.bddAbove_iff_exists_tendsto_aux`

English:
theorem Submartingale.bddAbove_iff_exists_tendsto_aux
  statement: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: by
  filter_upwards [hf.exists_tendsto_of_abs_bddAbove_aux hf0 hbdd] with ω hω using
    ⟨hω, fun ⟨c, hc⟩ => hc.bddAbove_range⟩

中文:
定理 Submartingale.bddAbove_iff_存在_tendsto_aux
  结论: [是有限测度 μ] (hf : Submartingale f ℱ μ)
  证明: by
  filter_upwards [hf.exists_tendsto_of_abs_bddAbove_aux hf0 hbdd] with ω hω using
    ⟨hω, fun ⟨c, hc⟩ => hc.bddAbove_range⟩

Depends on / 依赖: bddAbove_range, exists_tendsto_of_abs_bddAbove_aux, filter_upwards, hc.bddAbove_range, hf.exists_tendsto_of_abs_bddAbove_aux
-/
theorem Submartingale.bddAbove_iff_exists_tendsto_aux [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hf0 : f 0 = 0) (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) :
    forallᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ exists c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.exists_tendsto_of_abs_bddAbove_aux hf0 hbdd] with ω hω using
    ⟨hω, fun ⟨c, hc⟩ => hc.bddAbove_range⟩

/--
theorem `Submartingale.bddAbove_iff_exists_tendsto` / 定理 `Submartingale.bddAbove_iff_exists_tendsto`

English:
theorem Submartingale.bddAbove_iff_exists_tendsto
  statement: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: by
  set g : Nat -> Ω -> Real := fun n ω => f n ω - f 0 ω
  have hg : Submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.stronglyAdapted 0) (hf.integrable 0))
  have hg0 : g 0 = 0 := by
    ext ω
    simp only [g, sub_self, Pi.zero_apply]
  have hgbdd : forallᵐ ω ∂μ, forall i : Nat, |g (i + 1) ω - g i ω| <= ↑R := by
    simpa only [g, sub_sub_sub_cancel_right]
  filter_upwards [hg.bddAbove_iff_exists_tendsto_aux hg0 hgbdd] with ω hω
  convert! hω using 1
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨b, hb⟩ := h <;>
    refine ⟨b + |f 0 ω|, fun y hy => ?_⟩ <;> obtain ⟨n, rfl⟩ := hy
    · simp_rw [g, sub_eq_add_neg]
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs _)
    · exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩))
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨c, hc⟩ := h
    · exact ⟨c - f 0 ω, hc.sub_const _⟩
    · refine ⟨c + f 0 ω, ?_⟩
      have := hc.add_const (f 0 ω)
      simpa only [g, sub_add_cancel]

中文:
定理 Submartingale.bddAbove_iff_存在_tendsto
  结论: [是有限测度 μ] (hf : Submartingale f ℱ μ)
  证明: by
  set g : Nat -> Ω -> Real := fun n ω => f n ω - f 0 ω
  have hg : Submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.stronglyAdapted 0) (hf.integrable 0))
  have hg0 : g 0 = 0 := by
    ext ω
    simp only [g, sub_self, Pi.zero_apply]
  have hgbdd : forallᵐ ω ∂μ, forall i : Nat, |g (i + 1) ω - g i ω| <= ↑R := by
    simpa only [g, sub_sub_sub_cancel_right]
  filter_upwards [hg.bddAbove_iff_exists_tendsto_aux hg0 hgbdd] with ω hω
  convert! hω using 1
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨b, hb⟩ := h <;>
    refine ⟨b + |f 0 ω|, fun y hy => ?_⟩ <;> obtain ⟨n, rfl⟩ := hy
    · simp_rw [g, sub_eq_add_neg]
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs _)
    · exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩))
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨c, hc⟩ := h
    · exact ⟨c - f 0 ω, hc.sub_const _⟩
    · refine ⟨c + f 0 ω, ?_⟩
      have := hc.add_const (f 0 ω)
      simpa only [g, sub_add_cancel]

Depends on / 依赖: Pi.zero_apply, Submartingale, bddAbove_iff_exists_tendsto_aux, convert, filter_upwards, hf.integrable, hf.stronglyAdapted, hf.sub_martingale, hg.bddAbove_iff_exists_tendsto_aux, integrable, martingale_const_fun, stronglyAdapted, sub_martingale, sub_self, sub_sub_sub_cancel_right, zero_apply
-/
theorem Submartingale.bddAbove_iff_exists_tendsto [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) :
    forallᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ exists c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  set g : Nat -> Ω -> Real := fun n ω => f n ω - f 0 ω
  have hg : Submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.stronglyAdapted 0) (hf.integrable 0))
  have hg0 : g 0 = 0 := by
    ext ω
    simp only [g, sub_self, Pi.zero_apply]
  have hgbdd : forallᵐ ω ∂μ, forall i : Nat, |g (i + 1) ω - g i ω| <= ↑R := by
    simpa only [g, sub_sub_sub_cancel_right]
  filter_upwards [hg.bddAbove_iff_exists_tendsto_aux hg0 hgbdd] with ω hω
  convert! hω using 1
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨b, hb⟩ := h <;>
    refine ⟨b + |f 0 ω|, fun y hy => ?_⟩ <;> obtain ⟨n, rfl⟩ := hy
    · simp_rw [g, sub_eq_add_neg]
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs _)
    · exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩))
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨c, hc⟩ := h
    · exact ⟨c - f 0 ω, hc.sub_const _⟩
    · refine ⟨c + f 0 ω, ?_⟩
      have := hc.add_const (f 0 ω)
      simpa only [g, sub_add_cancel]



/--
theorem `Martingale.bddAbove_range_iff_bddBelow_range` / 定理 `Martingale.bddAbove_range_iff_bddBelow_range`

English:
theorem Martingale.bddAbove_range_iff_bddBelow_range
  statement: [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
  proof: by
  have hbdd' : forallᵐ ω ∂μ, forall i, |(-f) (i + 1) ω - (-f) i ω| <= R := by
    filter_upwards [hbdd] with ω hω i
    simp only [Pi.neg_apply]
    grind
  have hup := hf.submartingale.bddAbove_iff_exists_tendsto hbdd
  have hdown := hf.neg.submartingale.bddAbove_iff_exists_tendsto hbdd'
  filter_upwards [hup, hdown] with ω hω₁ hω₂
  have : (exists c, Tendsto (fun n => f n ω) atTop (𝓝 c)) ↔
      exists c, Tendsto (fun n => (-f) n ω) atTop (𝓝 c) := by
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨-c, hc.neg⟩
    · refine ⟨-c, ?_⟩
      convert! hc.neg
      simp only [neg_neg, Pi.neg_apply]
  rw [hω₁]; rw [this]; rw [← hω₂]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨-c, fun ω hω => ?_⟩
  · rw [mem_upperBounds] at hc
    refine neg_le.2 (hc _ ?_)
    simpa only [Pi.neg_apply, Set.mem_range, neg_inj]
  · rw [mem_lowerBounds] at hc
    simp_rw [Set.mem_range, Pi.neg_apply, neg_eq_iff_eq_neg] at hω
    refine le_neg.1 (hc _ ?_)
    simpa only [Set.mem_range]

中文:
定理 鞅.bddAbove_range_iff_bddBelow_range
  结论: [是有限测度 μ] (hf : 鞅 f ℱ μ)
  证明: by
  have hbdd' : forallᵐ ω ∂μ, forall i, |(-f) (i + 1) ω - (-f) i ω| <= R := by
    filter_upwards [hbdd] with ω hω i
    simp only [Pi.neg_apply]
    grind
  have hup := hf.submartingale.bddAbove_iff_exists_tendsto hbdd
  have hdown := hf.neg.submartingale.bddAbove_iff_exists_tendsto hbdd'
  filter_upwards [hup, hdown] with ω hω₁ hω₂
  have : (exists c, Tendsto (fun n => f n ω) atTop (𝓝 c)) ↔
      exists c, Tendsto (fun n => (-f) n ω) atTop (𝓝 c) := by
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨-c, hc.neg⟩
    · refine ⟨-c, ?_⟩
      convert! hc.neg
      simp only [neg_neg, Pi.neg_apply]
  rw [hω₁]; rw [this]; rw [← hω₂]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨-c, fun ω hω => ?_⟩
  · rw [mem_upperBounds] at hc
    refine neg_le.2 (hc _ ?_)
    simpa only [Pi.neg_apply, Set.mem_range, neg_inj]
  · rw [mem_lowerBounds] at hc
    simp_rw [Set.mem_range, Pi.neg_apply, neg_eq_iff_eq_neg] at hω
    refine le_neg.1 (hc _ ?_)
    simpa only [Set.mem_range]

Depends on / 依赖: Pi.neg_apply, Tendsto, bddAbove_iff_exists_tendsto, filter_upwards, hc.neg, hf.neg.submartingale.bddAbove_iff_exists_tendsto, hf.submartingale.bddAbove_iff_exists_tendsto, neg_apply, submartingale
-/
theorem Martingale.bddAbove_range_iff_bddBelow_range [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) :
    forallᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ BddBelow (Set.range fun n => f n ω) := by
  have hbdd' : forallᵐ ω ∂μ, forall i, |(-f) (i + 1) ω - (-f) i ω| <= R := by
    filter_upwards [hbdd] with ω hω i
    simp only [Pi.neg_apply]
    grind
  have hup := hf.submartingale.bddAbove_iff_exists_tendsto hbdd
  have hdown := hf.neg.submartingale.bddAbove_iff_exists_tendsto hbdd'
  filter_upwards [hup, hdown] with ω hω₁ hω₂
  have : (exists c, Tendsto (fun n => f n ω) atTop (𝓝 c)) ↔
      exists c, Tendsto (fun n => (-f) n ω) atTop (𝓝 c) := by
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨-c, hc.neg⟩
    · refine ⟨-c, ?_⟩
      convert! hc.neg
      simp only [neg_neg, Pi.neg_apply]
  rw [hω₁]; rw [this]; rw [← hω₂]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨-c, fun ω hω => ?_⟩
  · rw [mem_upperBounds] at hc
    refine neg_le.2 (hc _ ?_)
    simpa only [Pi.neg_apply, Set.mem_range, neg_inj]
  · rw [mem_lowerBounds] at hc
    simp_rw [Set.mem_range, Pi.neg_apply, neg_eq_iff_eq_neg] at hω
    refine le_neg.1 (hc _ ?_)
    simpa only [Set.mem_range]

/--
theorem `Martingale.ae_not_tendsto_atTop_atTop` / 定理 `Martingale.ae_not_tendsto_atTop_atTop`

English:
theorem Martingale.ae_not_tendsto_atTop_atTop
  statement: [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
  proof: by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddAbove_of_tendsto_atTop htop (hω.2 <| bddBelow_range_of_tendsto_atTop_atTop htop)

中文:
定理 鞅.ae_not_tendsto_atTop_atTop
  结论: [是有限测度 μ] (hf : 鞅 f ℱ μ)
  证明: by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddAbove_of_tendsto_atTop htop (hω.2 <| bddBelow_range_of_tendsto_atTop_atTop htop)

Depends on / 依赖: bddAbove_range_iff_bddBelow_range, bddBelow_range_of_tendsto_atTop_atTop, filter_upwards, hf.bddAbove_range_iff_bddBelow_range, not_bddAbove_of_tendsto_atTop
-/
theorem Martingale.ae_not_tendsto_atTop_atTop [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) :
    forallᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atTop := by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddAbove_of_tendsto_atTop htop (hω.2 <| bddBelow_range_of_tendsto_atTop_atTop htop)

/--
theorem `Martingale.ae_not_tendsto_atTop_atBot` / 定理 `Martingale.ae_not_tendsto_atTop_atBot`

English:
theorem Martingale.ae_not_tendsto_atTop_atBot
  statement: [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
  proof: by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddBelow_of_tendsto_atBot htop (hω.1 <| bddAbove_range_of_tendsto_atTop_atBot htop)

中文:
定理 鞅.ae_not_tendsto_atTop_atBot
  结论: [是有限测度 μ] (hf : 鞅 f ℱ μ)
  证明: by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddBelow_of_tendsto_atBot htop (hω.1 <| bddAbove_range_of_tendsto_atTop_atBot htop)

Depends on / 依赖: bddAbove_range_iff_bddBelow_range, bddAbove_range_of_tendsto_atTop_atBot, filter_upwards, hf.bddAbove_range_iff_bddBelow_range, not_bddBelow_of_tendsto_atBot
-/
theorem Martingale.ae_not_tendsto_atTop_atBot [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : forallᵐ ω ∂μ, forall i, |f (i + 1) ω - f i ω| <= R) :
    forallᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atBot := by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddBelow_of_tendsto_atBot htop (hω.1 <| bddAbove_range_of_tendsto_atTop_atBot htop)

namespace BorelCantelli

/--
Definition of `process` / `process` 的定义

English:
definition process
  signature: (s : Nat -> Set Ω) (n : Nat)
  body: ∑ k in Finset.range n, (s (k + 1)).indicator 1

中文:
定义 process
  签名: (s : 自然数 -> 集合 Ω) (n : 自然数)
  定义体: ∑ k in Finset.range n, (s (k + 1)).indicator 1

Depends on / 依赖: Finset, Finset.range, indicator
-/
noncomputable def process (s : Nat -> Set Ω) (n : Nat) : Ω -> Real :=
  ∑ k in Finset.range n, (s (k + 1)).indicator 1

variable {s : Nat -> Set Ω}

/--
theorem `process_zero` / 定理 `process_zero`

English:
theorem process_zero
  statement: process s 0 = 0
  proof: by rw [process, Finset.range_zero, Finset.sum_empty]

中文:
定理 process_zero
  结论: process s 0 = 0
  证明: by rw [process, Finset.range_zero, Finset.sum_empty]

Depends on / 依赖: Finset, Finset.range_zero, Finset.sum_empty, process, range_zero, sum_empty
-/
theorem process_zero : process s 0 = 0 := by rw [process, Finset.range_zero, Finset.sum_empty]

/--
theorem `stronglyAdapted_process` / 定理 `stronglyAdapted_process`

English:
theorem stronglyAdapted_process
  given: (hs : forall n, MeasurableSet[ℱ n] (s n))
  proof: fun _ => Finset.stronglyMeasurable_sum _ fun _ hk =>
stronglyMeasurable_one.indicator ℱ.mono (Finset.mem_range.1 hk) _ hs _

中文:
定理 stronglyAdapted_process
  条件: (hs : 对任意 n, 可测集[ℱ n] (s n))
  证明: fun _ => Finset.stronglyMeasurable_sum _ fun _ hk =>
stronglyMeasurable_one.indicator ℱ.mono (Finset.mem_range.1 hk) _ hs _

Depends on / 依赖: Finset, Finset.mem_range, Finset.stronglyMeasurable_sum, indicator, mem_range, stronglyMeasurable_one, stronglyMeasurable_one.indicator, stronglyMeasurable_sum
-/
theorem stronglyAdapted_process (hs : forall n, MeasurableSet[ℱ n] (s n)) :
    StronglyAdapted ℱ (process s) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hk =>
stronglyMeasurable_one.indicator ℱ.mono (Finset.mem_range.1 hk) _ hs _

/--
theorem `martingalePart_process_ae_eq` / 定理 `martingalePart_process_ae_eq`

English:
theorem martingalePart_process_ae_eq
  given: (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : Nat -> Set Ω) (n : Nat)
  proof: by
  simp only [martingalePart_eq_sum, process_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [process, Finset.sum_range_succ_sub_sum]

中文:
定理 martingalePart_process_ae_eq
  条件: (ℱ : 滤子 自然数 m0) (μ : 测度 Ω) (s : 自然数 -> 集合 Ω) (n : 自然数)
  证明: by
  simp only [martingalePart_eq_sum, process_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [process, Finset.sum_range_succ_sub_sum]

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_range_succ_sub_sum, martingalePart_eq_sum, process, process_zero, sum_congr, sum_range_succ_sub_sum, zero_add
-/
theorem martingalePart_process_ae_eq (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : Nat -> Set Ω) (n : Nat) :
    martingalePart (process s) ℱ μ n =
      ∑ k in Finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k]) := by
  simp only [martingalePart_eq_sum, process_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [process, Finset.sum_range_succ_sub_sum]

/--
theorem `predictablePart_process_ae_eq` / 定理 `predictablePart_process_ae_eq`

English:
theorem predictablePart_process_ae_eq
  statement: (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : Nat -> Set Ω)
  proof: by
  have := martingalePart_process_ae_eq ℱ μ s n
  simp_rw [martingalePart, process, Finset.sum_sub_distrib] at this
  exact sub_right_injective this

中文:
定理 predictablePart_process_ae_eq
  结论: (ℱ : 滤子 自然数 m0) (μ : 测度 Ω) (s : 自然数 -> 集合 Ω)
  证明: by
  have := martingalePart_process_ae_eq ℱ μ s n
  simp_rw [martingalePart, process, Finset.sum_sub_distrib] at this
  exact sub_right_injective this

Depends on / 依赖: Finset, Finset.sum_sub_distrib, martingalePart, martingalePart_process_ae_eq, process, simp_rw, sub_right_injective, sum_sub_distrib
-/
theorem predictablePart_process_ae_eq (ℱ : Filtration Nat m0) (μ : Measure Ω) (s : Nat -> Set Ω)
    (n : Nat) : predictablePart (process s) ℱ μ n =
    ∑ k in Finset.range n, μ[(s (k + 1)).indicator (1 : Ω -> Real) | ℱ k] := by
  have := martingalePart_process_ae_eq ℱ μ s n
  simp_rw [martingalePart, process, Finset.sum_sub_distrib] at this
  exact sub_right_injective this

/--
theorem `process_difference_le` / 定理 `process_difference_le`

English:
theorem process_difference_le
  given: (s : Nat -> Set Ω) (ω : Ω) (n : Nat)
  proof: by
  norm_cast
  rw [process]; rw [process]; rw [Finset.sum_apply]; rw [Finset.sum_apply]; rw [Finset.sum_range_succ_sub_sum]; rw [← Real.norm_eq_abs]; rw [norm_indicator_eq_indicator_norm]
  refine Set.indicator_le' (fun _ _ => ?_) (fun _ _ => zero_le_one) _
  rw [Pi.one_apply]; rw [norm_one]

中文:
定理 process_difference_le
  条件: (s : 自然数 -> 集合 Ω) (ω : Ω) (n : 自然数)
  证明: by
  norm_cast
  rw [process]; rw [process]; rw [Finset.sum_apply]; rw [Finset.sum_apply]; rw [Finset.sum_range_succ_sub_sum]; rw [← Real.norm_eq_abs]; rw [norm_indicator_eq_indicator_norm]
  refine Set.indicator_le' (fun _ _ => ?_) (fun _ _ => zero_le_one) _
  rw [Pi.one_apply]; rw [norm_one]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_range_succ_sub_sum, Pi.one_apply, Real.norm_eq_abs, Set.indicator_le, indicator_le, norm_eq_abs, norm_indicator_eq_indicator_norm, norm_one, one_apply, process, sum_apply, sum_range_succ_sub_sum, zero_le_one
-/
theorem process_difference_le (s : Nat -> Set Ω) (ω : Ω) (n : Nat) :
    |process s (n + 1) ω - process s n ω| <= (1 : Real>=0) := by
  norm_cast
  rw [process]; rw [process]; rw [Finset.sum_apply]; rw [Finset.sum_apply]; rw [Finset.sum_range_succ_sub_sum]; rw [← Real.norm_eq_abs]; rw [norm_indicator_eq_indicator_norm]
  refine Set.indicator_le' (fun _ _ => ?_) (fun _ _ => zero_le_one) _
  rw [Pi.one_apply]; rw [norm_one]

/--
theorem `integrable_process` / 定理 `integrable_process`

English:
theorem integrable_process
  statement: (μ : Measure Ω) [IsFiniteMeasure μ] (hs : forall n, MeasurableSet[ℱ n] (s n))
  proof: integrable_finsetSum' _ fun _ _ =>
IntegrableOn.integrable_indicator (integrable_const 1) ℱ.le _ _ hs _

中文:
定理 integrable_process
  结论: (μ : 测度 Ω) [是有限测度 μ] (hs : 对任意 n, 可测集[ℱ n] (s n))
  证明: integrable_finsetSum' _ fun _ _ =>
IntegrableOn.integrable_indicator (integrable_const 1) ℱ.le _ _ hs _

Depends on / 依赖: IntegrableOn, IntegrableOn.integrable_indicator, integrable_const, integrable_finsetSum, integrable_indicator
-/
theorem integrable_process (μ : Measure Ω) [IsFiniteMeasure μ] (hs : forall n, MeasurableSet[ℱ n] (s n))
    (n : Nat) : Integrable (process s n) μ :=
  integrable_finsetSum' _ fun _ _ =>
IntegrableOn.integrable_indicator (integrable_const 1) ℱ.le _ _ hs _

end BorelCantelli

open BorelCantelli

/--
theorem `tendsto_sum_indicator_atTop_iff` / 定理 `tendsto_sum_indicator_atTop_iff`

English:
theorem tendsto_sum_indicator_atTop_iff
  statement: [IsFiniteMeasure μ]
  proof: by
  simp only [← Real.norm_eq_abs] at hbdd
  have h₀ := martingalePart_bdd_difference ℱ hbdd
  simp only [Real.norm_eq_abs, ← NNReal.coe_ofNat, ← NNReal.coe_mul 2 R] at h₀
  have h₁ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atTop h₀
  have h₂ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atBot h₀
  have h₃ : forallᵐ ω ∂μ, forall n, 0 <= (μ[f (n + 1) - f n | ℱ n]) ω := by
    refine ae_all_iff.2 fun n => condExp_nonneg ?_
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄
  constructor <;> intro ht
  · refine tendsto_atTop_atTop_of_monotone' ?_ ?_
    · intro n m hnm
      simp only [predictablePart, Finset.sum_apply]
      exact Finset.sum_mono_set_of_nonneg hω₃ (Finset.range_mono hnm)
    rintro ⟨b, hbdd⟩
    rw [← tendsto_neg_atBot_iff] at ht
    simp only [martingalePart, sub_eq_add_neg] at hω₁
    exact hω₁ (tendsto_atTop_add_right_of_le _ (-b) (tendsto_neg_atBot_iff.1 ht) fun n =>
      neg_le_neg (hbdd ⟨n, rfl⟩))
  · refine tendsto_atTop_atTop_of_monotone' (monotone_nat_of_le_succ hω₄) ?_
    rintro ⟨b, hbdd⟩
    exact hω₂ ((tendsto_atBot_add_left_of_ge _ b fun n =>
      hbdd ⟨n, rfl⟩) <| tendsto_neg_atBot_iff.2 ht)

中文:
定理 tendsto_sum_indicator_atTop_iff
  结论: [是有限测度 μ]
  证明: by
  simp only [← Real.norm_eq_abs] at hbdd
  have h₀ := martingalePart_bdd_difference ℱ hbdd
  simp only [Real.norm_eq_abs, ← NNReal.coe_ofNat, ← NNReal.coe_mul 2 R] at h₀
  have h₁ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atTop h₀
  have h₂ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atBot h₀
  have h₃ : forallᵐ ω ∂μ, forall n, 0 <= (μ[f (n + 1) - f n | ℱ n]) ω := by
    refine ae_all_iff.2 fun n => condExp_nonneg ?_
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄
  constructor <;> intro ht
  · refine tendsto_atTop_atTop_of_monotone' ?_ ?_
    · intro n m hnm
      simp only [predictablePart, Finset.sum_apply]
      exact Finset.sum_mono_set_of_nonneg hω₃ (Finset.range_mono hnm)
    rintro ⟨b, hbdd⟩
    rw [← tendsto_neg_atBot_iff] at ht
    simp only [martingalePart, sub_eq_add_neg] at hω₁
    exact hω₁ (tendsto_atTop_add_right_of_le _ (-b) (tendsto_neg_atBot_iff.1 ht) fun n =>
      neg_le_neg (hbdd ⟨n, rfl⟩))
  · refine tendsto_atTop_atTop_of_monotone' (monotone_nat_of_le_succ hω₄) ?_
    rintro ⟨b, hbdd⟩
    exact hω₂ ((tendsto_atBot_add_left_of_ge _ b fun n =>
      hbdd ⟨n, rfl⟩) <| tendsto_neg_atBot_iff.2 ht)

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.coe_ofNat, Real.norm_eq_abs, ae_all_iff, ae_not_tendsto_atTop_atBot, ae_not_tendsto_atTop_atTop, coe_mul, coe_ofNat, condExp_nonneg, filter_upwards, hfmono, martingalePart_bdd_difference, martingale_martingalePart, norm_eq_abs
-/
theorem tendsto_sum_indicator_atTop_iff [IsFiniteMeasure μ]
    (hfmono : forallᵐ ω ∂μ, forall n, f n ω <= f (n + 1) ω) (hf : StronglyAdapted ℱ f)
    (hint : forall n, Integrable (f n) μ) (hbdd : forallᵐ ω ∂μ, forall n, |f (n + 1) ω - f n ω| <= R) :
    forallᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop atTop ↔
      Tendsto (fun n => predictablePart f ℱ μ n ω) atTop atTop := by
  simp only [← Real.norm_eq_abs] at hbdd
  have h₀ := martingalePart_bdd_difference ℱ hbdd
  simp only [Real.norm_eq_abs, ← NNReal.coe_ofNat, ← NNReal.coe_mul 2 R] at h₀
  have h₁ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atTop h₀
  have h₂ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atBot h₀
  have h₃ : forallᵐ ω ∂μ, forall n, 0 <= (μ[f (n + 1) - f n | ℱ n]) ω := by
    refine ae_all_iff.2 fun n => condExp_nonneg ?_
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄
  constructor <;> intro ht
  · refine tendsto_atTop_atTop_of_monotone' ?_ ?_
    · intro n m hnm
      simp only [predictablePart, Finset.sum_apply]
      exact Finset.sum_mono_set_of_nonneg hω₃ (Finset.range_mono hnm)
    rintro ⟨b, hbdd⟩
    rw [← tendsto_neg_atBot_iff] at ht
    simp only [martingalePart, sub_eq_add_neg] at hω₁
    exact hω₁ (tendsto_atTop_add_right_of_le _ (-b) (tendsto_neg_atBot_iff.1 ht) fun n =>
      neg_le_neg (hbdd ⟨n, rfl⟩))
  · refine tendsto_atTop_atTop_of_monotone' (monotone_nat_of_le_succ hω₄) ?_
    rintro ⟨b, hbdd⟩
    exact hω₂ ((tendsto_atBot_add_left_of_ge _ b fun n =>
      hbdd ⟨n, rfl⟩) <| tendsto_neg_atBot_iff.2 ht)

open BorelCantelli

/--
theorem `tendsto_sum_indicator_atTop_iff'` / 定理 `tendsto_sum_indicator_atTop_iff'`

English:
theorem tendsto_sum_indicator_atTop_iff'
  statement: [IsFiniteMeasure μ] {s : Nat -> Set Ω}
  proof: by
  have := tendsto_sum_indicator_atTop_iff (Eventually.of_forall fun ω n => ?_)
    (stronglyAdapted_process hs) (integrable_process μ hs)
    (Eventually.of_forall <| process_difference_le s)
  swap
  · rw [process, process, ← sub_nonneg, Finset.sum_apply, Finset.sum_apply,
      Finset.sum_range_succ_sub_sum]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  simp_rw [process, predictablePart_process_ae_eq] at this
  simpa using this

中文:
定理 tendsto_sum_indicator_atTop_iff'
  结论: [是有限测度 μ] {s : 自然数 -> 集合 Ω}
  证明: by
  have := tendsto_sum_indicator_atTop_iff (Eventually.of_forall fun ω n => ?_)
    (stronglyAdapted_process hs) (integrable_process μ hs)
    (Eventually.of_forall <| process_difference_le s)
  swap
  · rw [process, process, ← sub_nonneg, Finset.sum_apply, Finset.sum_apply,
      Finset.sum_range_succ_sub_sum]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  simp_rw [process, predictablePart_process_ae_eq] at this
  simpa using this

Depends on / 依赖: Eventually, Eventually.of_forall, Finset, Finset.sum_apply, Finset.sum_range_succ_sub_sum, Set.indicator_nonneg, indicator_nonneg, integrable_process, of_forall, predictablePart_process_ae_eq, process, process_difference_le, simp_rw, stronglyAdapted_process, sub_nonneg, sum_apply, sum_range_succ_sub_sum, tendsto_sum_indicator_atTop_iff, zero_le_one
-/
theorem tendsto_sum_indicator_atTop_iff' [IsFiniteMeasure μ] {s : Nat -> Set Ω}
    (hs : forall n, MeasurableSet[ℱ n] (s n)) : forallᵐ ω ∂μ,
    Tendsto (fun n => ∑ k in Finset.range n,
      (s (k + 1)).indicator (1 : Ω -> Real) ω) atTop atTop ↔
    Tendsto (fun n => ∑ k in Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω -> Real) | ℱ k]) ω) atTop atTop := by
  have := tendsto_sum_indicator_atTop_iff (Eventually.of_forall fun ω n => ?_)
    (stronglyAdapted_process hs) (integrable_process μ hs)
    (Eventually.of_forall <| process_difference_le s)
  swap
  · rw [process, process, ← sub_nonneg, Finset.sum_apply, Finset.sum_apply,
      Finset.sum_range_succ_sub_sum]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  simp_rw [process, predictablePart_process_ae_eq] at this
  simpa using this

/--
theorem `ae_mem_limsup_atTop_iff` / 定理 `ae_mem_limsup_atTop_iff`

English:
theorem ae_mem_limsup_atTop_iff
  statement: (μ : Measure Ω) [IsFiniteMeasure μ] {s : Nat -> Set Ω}
  proof: by
  rw [← limsup_nat_add s 1]; rw [Set.limsup_eq_tendsto_sum_indicator_atTop (zero_lt_one (α := Real)) (fun n => s (n + 1))]
  exact tendsto_sum_indicator_atTop_iff' hs

中文:
定理 ae_mem_limsup_atTop_iff
  结论: (μ : 测度 Ω) [是有限测度 μ] {s : 自然数 -> 集合 Ω}
  证明: by
  rw [← limsup_nat_add s 1]; rw [Set.limsup_eq_tendsto_sum_indicator_atTop (zero_lt_one (α := Real)) (fun n => s (n + 1))]
  exact tendsto_sum_indicator_atTop_iff' hs

Depends on / 依赖: Set.limsup_eq_tendsto_sum_indicator_atTop, limsup_eq_tendsto_sum_indicator_atTop, limsup_nat_add, tendsto_sum_indicator_atTop_iff, zero_lt_one
-/
theorem ae_mem_limsup_atTop_iff (μ : Measure Ω) [IsFiniteMeasure μ] {s : Nat -> Set Ω}
    (hs : forall n, MeasurableSet[ℱ n] (s n)) : forallᵐ ω ∂μ, ω in limsup s atTop ↔
    Tendsto (fun n => ∑ k in Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω -> Real) | ℱ k]) ω) atTop atTop := by
  rw [← limsup_nat_add s 1]; rw [Set.limsup_eq_tendsto_sum_indicator_atTop (zero_lt_one (α := Real)) (fun n => s (n + 1))]
  exact tendsto_sum_indicator_atTop_iff' hs

end MeasureTheory
