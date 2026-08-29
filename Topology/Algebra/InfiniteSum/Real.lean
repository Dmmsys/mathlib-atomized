/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Infinite sum in the reals

This file provides lemmas about Cauchy sequences in terms of infinite sums and infinite sums valued
in the reals.
-/

public section

open Filter Finset NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α] {f : Nat -> α} {a : α}

/--
theorem `cauchySeq_of_dist_le_of_summable` / 定理 `cauchySeq_of_dist_le_of_summable`

English:
theorem cauchySeq_of_dist_le_of_summable
  statement: (d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n)
  proof: by
  lift d to Nat -> Real>=0 using fun n => dist_nonneg.trans (hf n)
  apply cauchySeq_of_edist_le_of_summable d (α := α) (f := f)
  · exact_mod_cast hf
  · exact_mod_cast hd

中文:
定理 cauchySeq_of_dist_le_of_summable
  结论: (d : 自然数 -> 实数) (hf : 对任意 n, dist (f n) (f n.succ) <= d n)
  证明: by
  lift d to Nat -> Real>=0 using fun n => dist_nonneg.trans (hf n)
  apply cauchySeq_of_edist_le_of_summable d (α := α) (f := f)
  · exact_mod_cast hf
  · exact_mod_cast hd

Depends on / 依赖: cauchySeq_of_edist_le_of_summable, dist_nonneg, dist_nonneg.trans
-/
theorem cauchySeq_of_dist_le_of_summable (d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n)
    (hd : Summable d) : CauchySeq f := by
  lift d to Nat -> Real>=0 using fun n => dist_nonneg.trans (hf n)
  apply cauchySeq_of_edist_le_of_summable d (α := α) (f := f)
  · exact_mod_cast hf
  · exact_mod_cast hd

/--
theorem `cauchySeq_of_summable_dist` / 定理 `cauchySeq_of_summable_dist`

English:
theorem cauchySeq_of_summable_dist
  given: (h : Summable fun n => dist (f n) (f n.succ))
  statement: CauchySeq f
  proof: cauchySeq_of_dist_le_of_summable _ (fun _ => le_rfl) h

中文:
定理 cauchySeq_of_summable_dist
  条件: (h : Summable fun n => dist (f n) (f n.succ))
  结论: CauchySeq f
  证明: cauchySeq_of_dist_le_of_summable _ (fun _ => le_rfl) h

Depends on / 依赖: cauchySeq_of_dist_le_of_summable, le_rfl
-/
theorem cauchySeq_of_summable_dist (h : Summable fun n => dist (f n) (f n.succ)) : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ (fun _ => le_rfl) h

/--
theorem `dist_le_tsum_of_dist_le_of_tendsto` / 定理 `dist_le_tsum_of_dist_le_of_tendsto`

English:
theorem dist_le_tsum_of_dist_le_of_tendsto
  statement: (d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n)
  proof: by
  refine le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_atTop.2 ⟨n, fun m hnm => ?_⟩)
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm fun _ _ => hf _) ?_
  rw [sum_Ico_eq_sum_range]
  refine Summable.sum_le_tsum (range _) (fun _ _ => le_trans dist_nonneg (hf _)) ?_
  exact hd.comp_injective (add_right_injective n)

中文:
定理 dist_le_tsum_of_dist_le_of_tendsto
  结论: (d : 自然数 -> 实数) (hf : 对任意 n, dist (f n) (f n.succ) <= d n)
  证明: by
  refine le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_atTop.2 ⟨n, fun m hnm => ?_⟩)
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm fun _ _ => hf _) ?_
  rw [sum_Ico_eq_sum_range]
  refine Summable.sum_le_tsum (range _) (fun _ _ => le_trans dist_nonneg (hf _)) ?_
  exact hd.comp_injective (add_right_injective n)

Depends on / 依赖: Summable, Summable.sum_le_tsum, add_right_injective, comp_injective, dist_le_Ico_sum_of_dist_le, dist_nonneg, eventually_atTop, hd.comp_injective, le_of_tendsto, le_trans, sum_Ico_eq_sum_range, sum_le_tsum, tendsto_const_nhds, tendsto_const_nhds.dist
-/
theorem dist_le_tsum_of_dist_le_of_tendsto (d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n)
    (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) :
    dist (f n) a <= ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_atTop.2 ⟨n, fun m hnm => ?_⟩)
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm fun _ _ => hf _) ?_
  rw [sum_Ico_eq_sum_range]
  refine Summable.sum_le_tsum (range _) (fun _ _ => le_trans dist_nonneg (hf _)) ?_
  exact hd.comp_injective (add_right_injective n)

/--
theorem `dist_le_tsum_of_dist_le_of_tendsto₀` / 定理 `dist_le_tsum_of_dist_le_of_tendsto₀`

English:
theorem dist_le_tsum_of_dist_le_of_tendsto₀
  statement: (d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n)
  proof: by
  simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

中文:
定理 dist_le_tsum_of_dist_le_of_tendsto₀
  结论: (d : 自然数 -> 实数) (hf : 对任意 n, dist (f n) (f n.succ) <= d n)
  证明: by
  simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

Depends on / 依赖: dist_le_tsum_of_dist_le_of_tendsto, zero_add
-/
theorem dist_le_tsum_of_dist_le_of_tendsto₀ (d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n)
    (hd : Summable d) (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a <= tsum d := by
  simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

/--
theorem `dist_le_tsum_dist_of_tendsto` / 定理 `dist_le_tsum_dist_of_tendsto`

English:
theorem dist_le_tsum_dist_of_tendsto
  statement: (h : Summable fun n => dist (f n) (f n.succ))
  proof: show dist (f n) a <= ∑' m, (fun x => dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n => dist (f n) (f n.succ)) (fun _ => le_rfl) h ha n

中文:
定理 dist_le_tsum_dist_of_tendsto
  结论: (h : Summable fun n => dist (f n) (f n.succ))
  证明: show dist (f n) a <= ∑' m, (fun x => dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n => dist (f n) (f n.succ)) (fun _ => le_rfl) h ha n

Depends on / 依赖: dist_le_tsum_of_dist_le_of_tendsto, le_rfl, n.succ, x.succ
-/
theorem dist_le_tsum_dist_of_tendsto (h : Summable fun n => dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a <= ∑' m, dist (f (n + m)) (f (n + m).succ) :=
  show dist (f n) a <= ∑' m, (fun x => dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n => dist (f n) (f n.succ)) (fun _ => le_rfl) h ha n

/--
theorem `dist_le_tsum_dist_of_tendsto₀` / 定理 `dist_le_tsum_dist_of_tendsto₀`

English:
theorem dist_le_tsum_dist_of_tendsto₀
  statement: (h : Summable fun n => dist (f n) (f n.succ))
  proof: by
  simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0

中文:
定理 dist_le_tsum_dist_of_tendsto₀
  结论: (h : Summable fun n => dist (f n) (f n.succ))
  证明: by
  simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0

Depends on / 依赖: dist_le_tsum_dist_of_tendsto, zero_add
-/
theorem dist_le_tsum_dist_of_tendsto₀ (h : Summable fun n => dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a <= ∑' n, dist (f n) (f n.succ) := by
  simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0

section summable

/--
theorem `not_summable_iff_tendsto_nat_atTop_of_nonneg` / 定理 `not_summable_iff_tendsto_nat_atTop_of_nonneg`

English:
theorem not_summable_iff_tendsto_nat_atTop_of_nonneg
  given: {f : Nat -> Real} (hf : forall n, 0 <= f n)
  proof: by
  lift f to Nat -> Real>=0 using hf
  simpa using mod_cast NNReal.not_summable_iff_tendsto_nat_atTop

中文:
定理 not_summable_iff_tendsto_nat_atTop_of_nonneg
  条件: {f : 自然数 -> 实数} (hf : 对任意 n, 0 <= f n)
  证明: by
  lift f to Nat -> Real>=0 using hf
  simpa using mod_cast NNReal.not_summable_iff_tendsto_nat_atTop

Depends on / 依赖: NNReal, NNReal.not_summable_iff_tendsto_nat_atTop, mod_cast, not_summable_iff_tendsto_nat_atTop
-/
theorem not_summable_iff_tendsto_nat_atTop_of_nonneg {f : Nat -> Real} (hf : forall n, 0 <= f n) :
    ¬Summable f ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop atTop := by
  lift f to Nat -> Real>=0 using hf
  simpa using mod_cast NNReal.not_summable_iff_tendsto_nat_atTop

/--
theorem `summable_iff_not_tendsto_nat_atTop_of_nonneg` / 定理 `summable_iff_not_tendsto_nat_atTop_of_nonneg`

English:
theorem summable_iff_not_tendsto_nat_atTop_of_nonneg
  given: {f : Nat -> Real} (hf : forall n, 0 <= f n)
  proof: by
  rw [← not_iff_not]; rw [Classical.not_not]; rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hf]

中文:
定理 summable_iff_not_tendsto_nat_atTop_of_nonneg
  条件: {f : 自然数 -> 实数} (hf : 对任意 n, 0 <= f n)
  证明: by
  rw [← not_iff_not]; rw [Classical.not_not]; rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hf]

Depends on / 依赖: Classical, Classical.not_not, not_iff_not, not_not, not_summable_iff_tendsto_nat_atTop_of_nonneg
-/
theorem summable_iff_not_tendsto_nat_atTop_of_nonneg {f : Nat -> Real} (hf : forall n, 0 <= f n) :
    Summable f ↔ ¬Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not]; rw [Classical.not_not]; rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hf]

/--
theorem `summable_sigma_of_nonneg` / 定理 `summable_sigma_of_nonneg`

English:
theorem summable_sigma_of_nonneg
  given: {α} {β : α -> Type*} {f : (Σ x, β x) -> Real} (hf : forall x, 0 <= f x)
  proof: by
  lift f to (Σ x, β x) -> Real>=0 using hf
  simpa using mod_cast NNReal.summable_sigma

中文:
定理 summable_sigma_of_nonneg
  条件: {α} {β : α -> 类型} {f : (Σ x, β x) -> 实数} (hf : 对任意 x, 0 <= f x)
  证明: by
  lift f to (Σ x, β x) -> Real>=0 using hf
  simpa using mod_cast NNReal.summable_sigma

Depends on / 依赖: NNReal, NNReal.summable_sigma, mod_cast, summable_sigma
-/
theorem summable_sigma_of_nonneg {α} {β : α -> Type*} {f : (Σ x, β x) -> Real} (hf : forall x, 0 <= f x) :
    Summable f ↔ (forall x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  lift f to (Σ x, β x) -> Real>=0 using hf
  simpa using mod_cast NNReal.summable_sigma

/--
lemma `summable_partition` / 引理 `summable_partition`

English:
lemma summable_partition
  statement: {α β : Type*} {f : β -> Real} (hf : 0 <= f) {s : α -> Set β}
  proof: by
  simpa only [← (Set.sigmaEquiv s hs).summable_iff] using! summable_sigma_of_nonneg (fun _ => hf _)

中文:
引理 summable_partition
  结论: {α β : 类型} {f : β -> 实数} (hf : 0 <= f) {s : α -> 集合 β}
  证明: by
  simpa only [← (Set.sigmaEquiv s hs).summable_iff] using! summable_sigma_of_nonneg (fun _ => hf _)

Depends on / 依赖: Set.sigmaEquiv, sigmaEquiv, summable_iff, summable_sigma_of_nonneg
-/
lemma summable_partition {α β : Type*} {f : β -> Real} (hf : 0 <= f) {s : α -> Set β}
    (hs : forall i, exists! j, i in s j) : Summable f ↔
      (forall j, Summable fun i : s j => f i) ∧ Summable fun j => ∑' i : s j, f i := by
  simpa only [← (Set.sigmaEquiv s hs).summable_iff] using! summable_sigma_of_nonneg (fun _ => hf _)

/--
theorem `summable_prod_of_nonneg` / 定理 `summable_prod_of_nonneg`

English:
theorem summable_prod_of_nonneg
  given: {α β} {f : (α × β) -> Real} (hf : 0 <= f)
  proof: (Equiv.sigmaEquivProd _ _).summable_iff.symm.trans summable_sigma_of_nonneg fun _ => hf _

中文:
定理 summable_prod_of_nonneg
  条件: {α β} {f : (α × β) -> 实数} (hf : 0 <= f)
  证明: (Equiv.sigmaEquivProd _ _).summable_iff.symm.trans summable_sigma_of_nonneg fun _ => hf _

Depends on / 依赖: Equiv.sigmaEquivProd, sigmaEquivProd, summable_iff, summable_iff.symm.trans, summable_sigma_of_nonneg
-/
theorem summable_prod_of_nonneg {α β} {f : (α × β) -> Real} (hf : 0 <= f) :
    Summable f ↔ (forall x, Summable fun y => f (x, y)) ∧ Summable fun x => ∑' y, f (x, y) :=
(Equiv.sigmaEquivProd _ _).summable_iff.symm.trans summable_sigma_of_nonneg fun _ => hf _

/--
theorem `summable_of_sum_le` / 定理 `summable_of_sum_le`

English:
theorem summable_of_sum_le
  statement: {ι : Type*} {f : ι -> Real} {c : Real} (hf : 0 <= f)
  proof: ⟨⨆ u : Finset ι, ∑ x in u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun _ ⟨u, hu⟩ => hu ▸ h u⟩⟩

中文:
定理 summable_of_sum_le
  结论: {ι : 类型} {f : ι -> 实数} {c : 实数} (hf : 0 <= f)
  证明: ⟨⨆ u : Finset ι, ∑ x in u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun _ ⟨u, hu⟩ => hu ▸ h u⟩⟩

Depends on / 依赖: Finset, Finset.sum_mono_set_of_nonneg, sum_mono_set_of_nonneg, tendsto_atTop_ciSup
-/
theorem summable_of_sum_le {ι : Type*} {f : ι -> Real} {c : Real} (hf : 0 <= f)
    (h : forall u : Finset ι, ∑ x in u, f x <= c) : Summable f :=
  ⟨⨆ u : Finset ι, ∑ x in u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun _ ⟨u, hu⟩ => hu ▸ h u⟩⟩

/--
theorem `summable_of_sum_range_le` / 定理 `summable_of_sum_range_le`

English:
theorem summable_of_sum_range_le
  statement: {f : Nat -> Real} {c : Real} (hf : forall n, 0 <= f n)
  proof: by
  refine (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

中文:
定理 summable_of_sum_range_le
  结论: {f : 自然数 -> 实数} {c : 实数} (hf : 对任意 n, 0 <= f n)
  证明: by
  refine (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

Depends on / 依赖: exists_lt_of_tendsto_atTop, hn.trans_le, lt_irrefl, summable_iff_not_tendsto_nat_atTop_of_nonneg, trans_le
-/
theorem summable_of_sum_range_le {f : Nat -> Real} {c : Real} (hf : forall n, 0 <= f n)
    (h : forall n, ∑ i in Finset.range n, f i <= c) : Summable f := by
  refine (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

/--
theorem `Real.tsum_le_of_sum_le` / 定理 `Real.tsum_le_of_sum_le`

English:
theorem Real.tsum_le_of_sum_le
  statement: {ι : Type*} {f : ι -> Real} {c : Real} (hf : 0 <= f)
  proof: (summable_of_sum_le hf h).tsum_le_of_sum_le h

中文:
定理 实数.tsum_le_of_sum_le
  结论: {ι : 类型} {f : ι -> 实数} {c : 实数} (hf : 0 <= f)
  证明: (summable_of_sum_le hf h).tsum_le_of_sum_le h

Depends on / 依赖: summable_of_sum_le, tsum_le_of_sum_le
-/
theorem Real.tsum_le_of_sum_le {ι : Type*} {f : ι -> Real} {c : Real} (hf : 0 <= f)
    (h : forall u : Finset ι, ∑ x in u, f x <= c) : ∑' x, f x <= c :=
  (summable_of_sum_le hf h).tsum_le_of_sum_le h

/--
theorem `Real.tsum_le_of_sum_range_le` / 定理 `Real.tsum_le_of_sum_range_le`

English:
theorem Real.tsum_le_of_sum_range_le
  statement: {f : Nat -> Real} {c : Real} (hf : forall n, 0 <= f n)
  proof: (summable_of_sum_range_le hf h).tsum_le_of_sum_range_le h

中文:
定理 实数.tsum_le_of_sum_range_le
  结论: {f : 自然数 -> 实数} {c : 实数} (hf : 对任意 n, 0 <= f n)
  证明: (summable_of_sum_range_le hf h).tsum_le_of_sum_range_le h

Depends on / 依赖: summable_of_sum_range_le, tsum_le_of_sum_range_le
-/
theorem Real.tsum_le_of_sum_range_le {f : Nat -> Real} {c : Real} (hf : forall n, 0 <= f n)
    (h : forall n, ∑ i in Finset.range n, f i <= c) : ∑' n, f n <= c :=
  (summable_of_sum_range_le hf h).tsum_le_of_sum_range_le h

/--
theorem `Summable.tsum_lt_tsum_of_nonneg` / 定理 `Summable.tsum_lt_tsum_of_nonneg`

English:
theorem Summable.tsum_lt_tsum_of_nonneg
  statement: {i : Nat} {f g : Nat -> Real} (h0 : forall b : Nat, 0 <= f b)
  proof: Summable.tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg

中文:
定理 Summable.tsum_lt_tsum_of_nonneg
  结论: {i : 自然数} {f g : 自然数 -> 实数} (h0 : 对任意 b : 自然数, 0 <= f b)
  证明: Summable.tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg
-/
protected theorem Summable.tsum_lt_tsum_of_nonneg {i : Nat} {f g : Nat -> Real} (h0 : forall b : Nat, 0 <= f b)
    (h : forall b : Nat, f b <= g b) (hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  Summable.tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg

end summable
