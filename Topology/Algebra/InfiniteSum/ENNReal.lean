/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Edward van de Meent
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.Bound

/-!
# Infinite sums in extended nonnegative reals

This file proves results on infinite sums in `ℝ≥0∞`.

In particular, we give lemmas relating sums of constants to the cardinality of the domain of
these sums.

## TODO

+ Once we have a topology on `ENat`, provide an `ENat`-valued version
+ Provide versions which sum over the whole type.
-/

public section

open Set Function

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : Real>=0∞} {r : Real>=0} {x : Real>=0∞} {ε : Real>=0∞}

section tsum

variable {f g : α -> Real>=0∞}

@[norm_cast]
/--
theorem `hasSum_coe` / 定理 `hasSum_coe`

English:
theorem hasSum_coe
  given: {f : α -> Real>=0} {r : Real>=0}
  proof: by
  simp only [HasSum, ← ofNNReal_finsetSum, tendsto_coe]

中文:
定理 hasSum_coe
  条件: {f : α -> 实数>=0} {r : 实数>=0}
  证明: by
  simp only [HasSum, ← ofNNReal_finsetSum, tendsto_coe]
-/
protected theorem hasSum_coe {f : α -> Real>=0} {r : Real>=0} :
    HasSum (fun a => (f a : Real>=0∞)) ↑r ↔ HasSum f r := by
  simp only [HasSum, ← ofNNReal_finsetSum, tendsto_coe]

/--
theorem `tsum_coe_eq` / 定理 `tsum_coe_eq`

English:
theorem tsum_coe_eq
  given: {f : α -> Real>=0} (h : HasSum f r)
  statement: (∑' a, (f a : Real>=0∞)) = r
  proof: (ENNReal.hasSum_coe.2 h).tsum_eq

中文:
定理 tsum_coe_eq
  条件: {f : α -> 实数>=0} (h : HasSum f r)
  结论: (∑' a, (f a : 实数>=0∞)) = r
  证明: (ENNReal.hasSum_coe.2 h).tsum_eq
-/
protected theorem tsum_coe_eq {f : α -> Real>=0} (h : HasSum f r) : (∑' a, (f a : Real>=0∞)) = r :=
  (ENNReal.hasSum_coe.2 h).tsum_eq

/--
theorem `coe_tsum` / 定理 `coe_tsum`

English:
theorem coe_tsum
  given: {f : α -> Real>=0}
  statement: Summable f -> ↑(tsum f) = ∑' a, (f a : Real>=0∞)

中文:
定理 coe_tsum
  条件: {f : α -> 实数>=0}
  结论: Summable f -> ↑(tsum f) = ∑' a, (f a : 实数>=0∞)
-/
protected theorem coe_tsum {f : α -> Real>=0} : Summable f -> ↑(tsum f) = ∑' a, (f a : Real>=0∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]

/--
theorem `hasSum` / 定理 `hasSum`

English:
theorem hasSum
  statement: HasSum f (⨆ s : Finset α, ∑ a in s, f a)
  proof: tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]

中文:
定理 hasSum
  结论: HasSum f (⨆ s : Finset α, ∑ a in s, f a)
  证明: tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]
-/
protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]
/--
theorem `summable` / 定理 `summable`

English:
theorem summable
  statement: Summable f
  proof: ⟨_, ENNReal.hasSum⟩

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)

中文:
定理 summable
  结论: Summable f
  证明: ⟨_, ENNReal.hasSum⟩

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)
-/
protected theorem summable : Summable f :=
  ⟨_, ENNReal.hasSum⟩

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)

/--
theorem `tsum_coe_ne_top_iff_summable` / 定理 `tsum_coe_ne_top_iff_summable`

English:
theorem tsum_coe_ne_top_iff_summable
  given: {f : β -> Real>=0}
  statement: (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
  proof: by
  refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : Real>=0∞) to Real>=0 using h with a ha
  refine ⟨a, ENNReal.hasSum_coe.1 ?_⟩
  rw [ha]
  exact ENNReal.summable.hasSum

中文:
定理 tsum_coe_ne_top_iff_summable
  条件: {f : β -> 实数>=0}
  结论: (∑' b, (f b : 实数>=0∞)) != ∞ ↔ Summable f
  证明: by
  refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : Real>=0∞) to Real>=0 using h with a ha
  refine ⟨a, ENNReal.hasSum_coe.1 ?_⟩
  rw [ha]
  exact ENNReal.summable.hasSum

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.coe_tsum, ENNReal.hasSum_coe, ENNReal.summable.hasSum, coe_ne_top, coe_tsum, hasSum, hasSum_coe, summable
-/
theorem tsum_coe_ne_top_iff_summable {f : β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f := by
  refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : Real>=0∞) to Real>=0 using h with a ha
  refine ⟨a, ENNReal.hasSum_coe.1 ?_⟩
  rw [ha]
  exact ENNReal.summable.hasSum

/--
theorem `tsum_eq_iSup_sum` / 定理 `tsum_eq_iSup_sum`

English:
theorem tsum_eq_iSup_sum
  statement: ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a
  proof: ENNReal.hasSum.tsum_eq

中文:
定理 tsum_eq_iSup_sum
  结论: ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a
  证明: ENNReal.hasSum.tsum_eq
-/
protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a :=
  ENNReal.hasSum.tsum_eq

/--
theorem `tsum_eq_iSup_sum'` / 定理 `tsum_eq_iSup_sum'`

English:
theorem tsum_eq_iSup_sum'
  given: {ι : Type*} (s : ι -> Finset α) (hs : forall t, exists i, t subseteq s i)
  proof: by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a in t, f a) (s i) = ⨆ s : Finset α, ∑ a in s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs

中文:
定理 tsum_eq_iSup_sum'
  条件: {ι : 类型} (s : ι -> Finset α) (hs : 对任意 t, 存在 i, t subseteq s i)
  证明: by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a in t, f a) (s i) = ⨆ s : Finset α, ∑ a in s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs
-/
protected theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι -> Finset α) (hs : forall t, exists i, t subseteq s i) :
    ∑' a, f a = ⨆ i, ∑ a in s i, f a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a in t, f a) (s i) = ⨆ s : Finset α, ∑ a in s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs

/--
theorem `tsum_sigma` / 定理 `tsum_sigma`

English:
theorem tsum_sigma
  given: {β : α -> Type*} (f : forall a, β a -> Real>=0∞)
  proof: ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

中文:
定理 tsum_sigma
  条件: {β : α -> 类型} (f : 对任意 a, β a -> 实数>=0∞)
  证明: ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable
-/
protected theorem tsum_sigma {β : α -> Type*} (f : forall a, β a -> Real>=0∞) :
    ∑' p : Σ a, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

/--
theorem `tsum_sigma'` / 定理 `tsum_sigma'`

English:
theorem tsum_sigma'
  given: {β : α -> Type*} (f : (Σ a, β a) -> Real>=0∞)
  proof: ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

中文:
定理 tsum_sigma'
  条件: {β : α -> 类型} (f : (Σ a, β a) -> 实数>=0∞)
  证明: ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable
-/
protected theorem tsum_sigma' {β : α -> Type*} (f : (Σ a, β a) -> Real>=0∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

/--
theorem `tsum_biUnion'` / 定理 `tsum_biUnion'`

English:
theorem tsum_biUnion'
  statement: {ι : Type*} {S : Set ι} {f : α -> ENNReal} {t : ι -> Set α}
  proof: by
  simp [← ENNReal.tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]

中文:
定理 tsum_biUnion'
  结论: {ι : 类型} {S : Set ι} {f : α -> ENN实数} {t : ι -> Set α}
  证明: by
  simp [← ENNReal.tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]
-/
protected theorem tsum_biUnion' {ι : Type*} {S : Set ι} {f : α -> ENNReal} {t : ι -> Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i in S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  simp [← ENNReal.tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]

/--
theorem `tsum_biUnion` / 定理 `tsum_biUnion`

English:
theorem tsum_biUnion
  statement: {ι : Type*} {f : α -> ENNReal} {t : ι -> Set α}
  proof: by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h]; rw [Set.biUnion_univ]

中文:
定理 tsum_biUnion
  结论: {ι : 类型} {f : α -> ENN实数} {t : ι -> Set α}
  证明: by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h]; rw [Set.biUnion_univ]
-/
protected theorem tsum_biUnion {ι : Type*} {f : α -> ENNReal} {t : ι -> Set α}
    (h : Set.univ.PairwiseDisjoint t) : ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h]; rw [Set.biUnion_univ]

/--
theorem `tsum_prod` / 定理 `tsum_prod`

English:
theorem tsum_prod
  given: {f : α -> β -> Real>=0∞}
  statement: ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b
  proof: ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

中文:
定理 tsum_prod
  条件: {f : α -> β -> 实数>=0∞}
  结论: ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b
  证明: ENNReal.summable.tsum_prod' fun _ => ENNReal.summable
-/
protected theorem tsum_prod {f : α -> β -> Real>=0∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

/--
theorem `tsum_prod'` / 定理 `tsum_prod'`

English:
theorem tsum_prod'
  given: {f : α × β -> Real>=0∞}
  statement: ∑' p : α × β, f p = ∑' (a) (b), f (a, b)
  proof: ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

中文:
定理 tsum_prod'
  条件: {f : α × β -> 实数>=0∞}
  结论: ∑' p : α × β, f p = ∑' (a) (b), f (a, b)
  证明: ENNReal.summable.tsum_prod' fun _ => ENNReal.summable
-/
protected theorem tsum_prod' {f : α × β -> Real>=0∞} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

/--
theorem `tsum_comm` / 定理 `tsum_comm`

English:
theorem tsum_comm
  given: {f : α -> β -> Real>=0∞}
  statement: ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b
  proof: ENNReal.summable.tsum_comm' (fun _ => ENNReal.summable) fun _ => ENNReal.summable

中文:
定理 tsum_comm
  条件: {f : α -> β -> 实数>=0∞}
  结论: ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b
  证明: ENNReal.summable.tsum_comm' (fun _ => ENNReal.summable) fun _ => ENNReal.summable
-/
protected theorem tsum_comm {f : α -> β -> Real>=0∞} : ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b :=
  ENNReal.summable.tsum_comm' (fun _ => ENNReal.summable) fun _ => ENNReal.summable

/--
theorem `tsum_add` / 定理 `tsum_add`

English:
theorem tsum_add
  statement: ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a
  proof: ENNReal.summable.tsum_add ENNReal.summable

中文:
定理 tsum_add
  结论: ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a
  证明: ENNReal.summable.tsum_add ENNReal.summable
-/
protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  ENNReal.summable.tsum_add ENNReal.summable

/--
lemma `sum_add_tsum_compl` / 引理 `sum_add_tsum_compl`

English:
lemma sum_add_tsum_compl
  given: {ι : Type*} (s : Finset ι) (f : ι -> Real>=0∞)
  proof: by
  rw [tsum_subtype]; rw [sum_eq_tsum_indicator]
  simp [← ENNReal.tsum_add]

中文:
引理 sum_add_tsum_compl
  条件: {ι : 类型} (s : Finset ι) (f : ι -> 实数>=0∞)
  证明: by
  rw [tsum_subtype]; rw [sum_eq_tsum_indicator]
  simp [← ENNReal.tsum_add]
-/
protected lemma sum_add_tsum_compl {ι : Type*} (s : Finset ι) (f : ι -> Real>=0∞) :
    ∑ i in s, f i + ∑' i : ↥(s : Set ι)ᶜ, f i = ∑' i, f i := by
  rw [tsum_subtype]; rw [sum_eq_tsum_indicator]
  simp [← ENNReal.tsum_add]

/--
theorem `tsum_le_tsum` / 定理 `tsum_le_tsum`

English:
theorem tsum_le_tsum
  given: (h : forall a, f a <= g a)
  statement: ∑' a, f a <= ∑' a, g a
  proof: ENNReal.summable.tsum_le_tsum h ENNReal.summable

中文:
定理 tsum_le_tsum
  条件: (h : 对任意 a, f a <= g a)
  结论: ∑' a, f a <= ∑' a, g a
  证明: ENNReal.summable.tsum_le_tsum h ENNReal.summable
-/
protected theorem tsum_le_tsum (h : forall a, f a <= g a) : ∑' a, f a <= ∑' a, g a :=
  ENNReal.summable.tsum_le_tsum h ENNReal.summable

/--
theorem `sum_le_tsum` / 定理 `sum_le_tsum`

English:
theorem sum_le_tsum
  given: {f : α -> Real>=0∞} (s : Finset α)
  statement: ∑ x in s, f x <= ∑' x, f x
  proof: ENNReal.summable.sum_le_tsum s (fun _ _ => zero_le)

中文:
定理 sum_le_tsum
  条件: {f : α -> 实数>=0∞} (s : Finset α)
  结论: ∑ x in s, f x <= ∑' x, f x
  证明: ENNReal.summable.sum_le_tsum s (fun _ _ => zero_le)
-/
protected theorem sum_le_tsum {f : α -> Real>=0∞} (s : Finset α) : ∑ x in s, f x <= ∑' x, f x :=
  ENNReal.summable.sum_le_tsum s (fun _ _ => zero_le)

/--
lemma `le_tsum_of_forall_lt_exists_sum` / 引理 `le_tsum_of_forall_lt_exists_sum`

English:
lemma le_tsum_of_forall_lt_exists_sum
  proof: by
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨I, hI⟩ := h b hb
  exact lt_of_lt_of_le hI (ENNReal.sum_le_tsum I)

中文:
引理 le_tsum_of_forall_lt_exists_sum
  证明: by
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨I, hI⟩ := h b hb
  exact lt_of_lt_of_le hI (ENNReal.sum_le_tsum I)
-/
protected lemma le_tsum_of_forall_lt_exists_sum
    (h : forall b < a, exists I : Finset α, b < ∑ i in I, f i) : a <= ∑' i, f i := by
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨I, hI⟩ := h b hb
  exact lt_of_lt_of_le hI (ENNReal.sum_le_tsum I)

/--
theorem `tsum_eq_iSup_nat'` / 定理 `tsum_eq_iSup_nat'`

English:
theorem tsum_eq_iSup_nat'
  given: {f : Nat -> Real>=0∞} {N : Nat -> Nat} (hN : Tendsto N atTop atTop)
  proof: ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

中文:
定理 tsum_eq_iSup_nat'
  条件: {f : 自然数 -> 实数>=0∞} {N : 自然数 -> 自然数} (hN : Tendsto N atTop atTop)
  证明: ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩
-/
protected theorem tsum_eq_iSup_nat' {f : Nat -> Real>=0∞} {N : Nat -> Nat} (hN : Tendsto N atTop atTop) :
    ∑' i : Nat, f i = ⨆ i : Nat, ∑ a in Finset.range (N i), f a :=
  ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

/--
theorem `tsum_eq_iSup_nat` / 定理 `tsum_eq_iSup_nat`

English:
theorem tsum_eq_iSup_nat
  given: {f : Nat -> Real>=0∞}
  proof: ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range

中文:
定理 tsum_eq_iSup_nat
  条件: {f : 自然数 -> 实数>=0∞}
  证明: ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range
-/
protected theorem tsum_eq_iSup_nat {f : Nat -> Real>=0∞} :
    ∑' i : Nat, f i = ⨆ i : Nat, ∑ a in Finset.range i, f a :=
  ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range

/--
theorem `tsum_eq_liminf_sum_nat` / 定理 `tsum_eq_liminf_sum_nat`

English:
theorem tsum_eq_liminf_sum_nat
  given: {f : Nat -> Real>=0∞}
  proof: ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm

中文:
定理 tsum_eq_liminf_sum_nat
  条件: {f : 自然数 -> 实数>=0∞}
  证明: ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm
-/
protected theorem tsum_eq_liminf_sum_nat {f : Nat -> Real>=0∞} :
    ∑' i, f i = liminf (fun n => ∑ i in Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm

/--
theorem `tsum_eq_limsup_sum_nat` / 定理 `tsum_eq_limsup_sum_nat`

English:
theorem tsum_eq_limsup_sum_nat
  given: {f : Nat -> Real>=0∞}
  proof: ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm

中文:
定理 tsum_eq_limsup_sum_nat
  条件: {f : 自然数 -> 实数>=0∞}
  证明: ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm
-/
protected theorem tsum_eq_limsup_sum_nat {f : Nat -> Real>=0∞} :
    ∑' i, f i = limsup (fun n => ∑ i in Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm

/--
theorem `le_tsum` / 定理 `le_tsum`

English:
theorem le_tsum
  given: (a : α)
  statement: f a <= ∑' a, f a
  proof: ENNReal.summable.le_tsum' a

@[simp]

中文:
定理 le_tsum
  条件: (a : α)
  结论: f a <= ∑' a, f a
  证明: ENNReal.summable.le_tsum' a

@[simp]
-/
protected theorem le_tsum (a : α) : f a <= ∑' a, f a :=
  ENNReal.summable.le_tsum' a

@[simp]
/--
theorem `tsum_eq_zero` / 定理 `tsum_eq_zero`

English:
theorem tsum_eq_zero
  statement: ∑' i, f i = 0 ↔ forall i, f i = 0
  proof: ENNReal.summable.tsum_eq_zero_iff

中文:
定理 tsum_eq_zero
  结论: ∑' i, f i = 0 ↔ 对任意 i, f i = 0
  证明: ENNReal.summable.tsum_eq_zero_iff
-/
protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ forall i, f i = 0 :=
  ENNReal.summable.tsum_eq_zero_iff

/--
theorem `tsum_eq_top_of_eq_top` / 定理 `tsum_eq_top_of_eq_top`

English:
theorem tsum_eq_top_of_eq_top
  statement: (exists a, f a = ∞) -> ∑' a, f a = ∞

中文:
定理 tsum_eq_top_of_eq_top
  结论: (存在 a, f a = ∞) -> ∑' a, f a = ∞
-/
protected theorem tsum_eq_top_of_eq_top : (exists a, f a = ∞) -> ∑' a, f a = ∞
| ⟨a, ha⟩ => top_unique ha ▸ ENNReal.le_tsum a

/--
theorem `lt_top_of_tsum_ne_top` / 定理 `lt_top_of_tsum_ne_top`

English:
theorem lt_top_of_tsum_ne_top
  given: {a : α -> Real>=0∞} (tsum_ne_top : ∑' i, a i != ∞) (j : α)
  proof: by
  contrapose! tsum_ne_top with h
  exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp]

中文:
定理 lt_top_of_tsum_ne_top
  条件: {a : α -> 实数>=0∞} (tsum_ne_top : ∑' i, a i != ∞) (j : α)
  证明: by
  contrapose! tsum_ne_top with h
  exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp]
-/
protected theorem lt_top_of_tsum_ne_top {a : α -> Real>=0∞} (tsum_ne_top : ∑' i, a i != ∞) (j : α) :
    a j < ∞ := by
  contrapose! tsum_ne_top with h
  exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp]
/--
theorem `tsum_top` / 定理 `tsum_top`

English:
theorem tsum_top
  given: [Nonempty α]
  statement: ∑' _ : α, ∞ = ∞
  proof: let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

中文:
定理 tsum_top
  条件: [Nonempty α]
  结论: ∑' _ : α, ∞ = ∞
  证明: let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩
-/
protected theorem tsum_top [Nonempty α] : ∑' _ : α, ∞ = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

/--
theorem `tsum_const_eq_top_of_ne_zero` / 定理 `tsum_const_eq_top_of_ne_zero`

English:
theorem tsum_const_eq_top_of_ne_zero
  given: {α : Type*} [Infinite α] {c : Real>=0∞} (hc : c != 0)
  proof: by
  have A : Tendsto (fun n : Nat => (n : Real>=0∞) * c) atTop (𝓝 (∞ * c)) := by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or, top_ne_zero, Ne, not_false_iff]
  have B : forall n : Nat, (n : Real>=0∞) * c <= ∑' _ : α, c := fun n => by
    rcases Infinite.exists_su

中文:
定理 tsum_const_eq_top_of_ne_zero
  条件: {α : 类型} [Infinite α] {c : 实数>=0∞} (hc : c != 0)
  证明: by
  have A : Tendsto (fun n : Nat => (n : Real>=0∞) * c) atTop (𝓝 (∞ * c)) := by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or, top_ne_zero, Ne, not_false_iff]
  have B : forall n : Nat, (n : Real>=0∞) * c <= ∑' _ : α, c := fun n => by
    rcases Infinite.exists_su

Depends on / 依赖: ENNReal, ENNReal.Tendsto.mul_const, ENNReal.sum_le_tsum, Infinite, Infinite.exists_subset_card_eq, Tendsto, exists_subset_card_eq, le_of_tendsto, mul_const, not_false_iff, sum_le_tsum, tendsto_nat_nhds_top, top_ne_zero, true_or
-/
theorem tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : Real>=0∞} (hc : c != 0) :
    ∑' _ : α, c = ∞ := by
  have A : Tendsto (fun n : Nat => (n : Real>=0∞) * c) atTop (𝓝 (∞ * c)) := by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or, top_ne_zero, Ne, not_false_iff]
  have B : forall n : Nat, (n : Real>=0∞) * c <= ∑' _ : α, c := fun n => by
    rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
    simpa [hs] using @ENNReal.sum_le_tsum α (fun _ => c) s
  simpa [hc] using le_of_tendsto' A B

/--
theorem `ne_top_of_tsum_ne_top` / 定理 `ne_top_of_tsum_ne_top`

English:
theorem ne_top_of_tsum_ne_top
  given: (h : ∑' a, f a != ∞) (a : α)
  statement: f a != ∞
  proof: fun ha =>
h ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩

中文:
定理 ne_top_of_tsum_ne_top
  条件: (h : ∑' a, f a != ∞) (a : α)
  结论: f a != ∞
  证明: fun ha =>
h ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩
-/
protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a != ∞) (a : α) : f a != ∞ := fun ha =>
h ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩

/--
theorem `tsum_mul_left` / 定理 `tsum_mul_left`

English:
theorem tsum_mul_left
  statement: ∑' i, a * f i = a * ∑' i, f i
  proof: by
  by_cases hf : forall i, f i = 0
  · simp [hf]
  · rw [← ENNReal.tsum_eq_zero] at hf
    have : Tendsto (fun s : Finset α => ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      simp only [← Finset.mul_sum]
      exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
    exact H

中文:
定理 tsum_mul_left
  结论: ∑' i, a * f i = a * ∑' i, f i
  证明: by
  by_cases hf : forall i, f i = 0
  · simp [hf]
  · rw [← ENNReal.tsum_eq_zero] at hf
    have : Tendsto (fun s : Finset α => ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      simp only [← Finset.mul_sum]
      exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
    exact H
-/
protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
  by_cases hf : forall i, f i = 0
  · simp [hf]
  · rw [← ENNReal.tsum_eq_zero] at hf
    have : Tendsto (fun s : Finset α => ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      simp only [← Finset.mul_sum]
      exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
    exact HasSum.tsum_eq this

/--
theorem `tsum_mul_right` / 定理 `tsum_mul_right`

English:
theorem tsum_mul_right
  statement: ∑' i, f i * a = (∑' i, f i) * a
  proof: by
  simp [mul_comm, ENNReal.tsum_mul_left]

中文:
定理 tsum_mul_right
  结论: ∑' i, f i * a = (∑' i, f i) * a
  证明: by
  simp [mul_comm, ENNReal.tsum_mul_left]
-/
protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
  simp [mul_comm, ENNReal.tsum_mul_left]

/--
theorem `tsum_const_smul` / 定理 `tsum_const_smul`

English:
theorem tsum_const_smul
  given: {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (a : R)
  proof: by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : Real>=0∞)) _

@[simp]

中文:
定理 tsum_const_smul
  条件: {R} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞] (a : R)
  证明: by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : Real>=0∞)) _

@[simp]
-/
protected theorem tsum_const_smul {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (a : R) :
    ∑' i, a • f i = a • ∑' i, f i := by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : Real>=0∞)) _

@[simp]
/--
theorem `tsum_iSup_eq` / 定理 `tsum_iSup_eq`

English:
theorem tsum_iSup_eq
  given: {α : Type*} (a : α) {f : α -> Real>=0∞}
  statement: (∑' b : α, ⨆ _ : a = b, f b) = f a
  proof: (tsum_eq_single a fun _ h => by simp [h.symm]).trans by simp

中文:
定理 tsum_iSup_eq
  条件: {α : 类型} (a : α) {f : α -> 实数>=0∞}
  结论: (∑' b : α, ⨆ _ : a = b, f b) = f a
  证明: (tsum_eq_single a fun _ h => by simp [h.symm]).trans by simp

Depends on / 依赖: h.symm, tsum_eq_single
-/
theorem tsum_iSup_eq {α : Type*} (a : α) {f : α -> Real>=0∞} : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
(tsum_eq_single a fun _ h => by simp [h.symm]).trans by simp

/--
theorem `hasSum_iff_tendsto_nat` / 定理 `hasSum_iff_tendsto_nat`

English:
theorem hasSum_iff_tendsto_nat
  given: {f : Nat -> Real>=0∞} (r : Real>=0∞)
  proof: by
  refine ⟨HasSum.tendsto_sum_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h]; rw [← ENNReal.tsum_eq_iSup_nat]
  · exact ENNReal.summable.hasSum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hst)

中文:
定理 hasSum_iff_tendsto_nat
  条件: {f : 自然数 -> 实数>=0∞} (r : 实数>=0∞)
  证明: by
  refine ⟨HasSum.tendsto_sum_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h]; rw [← ENNReal.tsum_eq_iSup_nat]
  · exact ENNReal.summable.hasSum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hst)

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, ENNReal.tsum_eq_iSup_nat, Finset, Finset.range_subset_range, Finset.sum_le_sum_of_subset, HasSum, HasSum.tendsto_sum_nat, hasSum, iSup_eq_of_tendsto, range_subset_range, sum_le_sum_of_subset, summable, tendsto_sum_nat, tsum_eq_iSup_nat
-/
theorem hasSum_iff_tendsto_nat {f : Nat -> Real>=0∞} (r : Real>=0∞) :
    HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 r) := by
  refine ⟨HasSum.tendsto_sum_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h]; rw [← ENNReal.tsum_eq_iSup_nat]
  · exact ENNReal.summable.hasSum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hst)

/--
theorem `tendsto_nat_tsum` / 定理 `tendsto_nat_tsum`

English:
theorem tendsto_nat_tsum
  given: (f : Nat -> Real>=0∞)
  proof: by
  rw [← hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum

中文:
定理 tendsto_nat_tsum
  条件: (f : 自然数 -> 实数>=0∞)
  证明: by
  rw [← hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, hasSum, hasSum_iff_tendsto_nat, summable
-/
theorem tendsto_nat_tsum (f : Nat -> Real>=0∞) :
    Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
  rw [← hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum

/--
theorem `toNNReal_apply_of_tsum_ne_top` / 定理 `toNNReal_apply_of_tsum_ne_top`

English:
theorem toNNReal_apply_of_tsum_ne_top
  given: {α : Type*} {f : α -> Real>=0∞} (hf : ∑' i, f i != ∞) (x : α)
  proof: coe_toNNReal ENNReal.ne_top_of_tsum_ne_top hf _

中文:
定理 toNNReal_apply_of_tsum_ne_top
  条件: {α : 类型} {f : α -> 实数>=0∞} (hf : ∑' i, f i != ∞) (x : α)
  证明: coe_toNNReal ENNReal.ne_top_of_tsum_ne_top hf _

Depends on / 依赖: ENNReal, ENNReal.ne_top_of_tsum_ne_top, coe_toNNReal, ne_top_of_tsum_ne_top
-/
theorem toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α -> Real>=0∞} (hf : ∑' i, f i != ∞) (x : α) :
    (((ENNReal.toNNReal ∘ f) x : Real>=0) : Real>=0∞) = f x :=
coe_toNNReal ENNReal.ne_top_of_tsum_ne_top hf _

/--
theorem `summable_toNNReal_of_tsum_ne_top` / 定理 `summable_toNNReal_of_tsum_ne_top`

English:
theorem summable_toNNReal_of_tsum_ne_top
  given: {α : Type*} {f : α -> Real>=0∞} (hf : ∑' i, f i != ∞)
  proof: by
  simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

中文:
定理 summable_toNNReal_of_tsum_ne_top
  条件: {α : 类型} {f : α -> 实数>=0∞} (hf : ∑' i, f i != ∞)
  证明: by
  simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

Depends on / 依赖: toNNReal_apply_of_tsum_ne_top, tsum_coe_ne_top_iff_summable
-/
theorem summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α -> Real>=0∞} (hf : ∑' i, f i != ∞) :
    Summable (ENNReal.toNNReal ∘ f) := by
  simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

/--
theorem `tendsto_cofinite_zero_of_tsum_ne_top` / 定理 `tendsto_cofinite_zero_of_tsum_ne_top`

English:
theorem tendsto_cofinite_zero_of_tsum_ne_top
  given: {α} {f : α -> Real>=0∞} (hf : ∑' x, f x != ∞)
  proof: by
  have f_ne_top : forall n, f n != ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_toNNReal (f_ne_top n)).symm
  rw [h_f_coe]; rw [← @coe_zero]; rw [tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_t

中文:
定理 tendsto_cofinite_zero_of_tsum_ne_top
  条件: {α} {f : α -> 实数>=0∞} (hf : ∑' x, f x != ∞)
  证明: by
  have f_ne_top : forall n, f n != ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_toNNReal (f_ne_top n)).symm
  rw [h_f_coe]; rw [← @coe_zero]; rw [tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_t

Depends on / 依赖: ENNReal, ENNReal.ne_top_of_tsum_ne_top, NNReal, NNReal.tendsto_cofinite_zero_of_summable, coe_toNNReal, coe_zero, f_ne_top, h_f_coe, ne_top_of_tsum_ne_top, summable_toNNReal_of_tsum_ne_top, tendsto_coe, tendsto_cofinite_zero_of_summable, toNNReal
-/
theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α -> Real>=0∞} (hf : ∑' x, f x != ∞) :
    Tendsto f cofinite (𝓝 0) := by
  have f_ne_top : forall n, f n != ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_toNNReal (f_ne_top n)).symm
  rw [h_f_coe]; rw [← @coe_zero]; rw [tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)

/--
theorem `tendsto_atTop_zero_of_tsum_ne_top` / 定理 `tendsto_atTop_zero_of_tsum_ne_top`

English:
theorem tendsto_atTop_zero_of_tsum_ne_top
  given: {f : Nat -> Real>=0∞} (hf : ∑' x, f x != ∞)
  proof: by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf

中文:
定理 tendsto_atTop_zero_of_tsum_ne_top
  条件: {f : 自然数 -> 实数>=0∞} (hf : ∑' x, f x != ∞)
  证明: by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, tendsto_cofinite_zero_of_tsum_ne_top
-/
theorem tendsto_atTop_zero_of_tsum_ne_top {f : Nat -> Real>=0∞} (hf : ∑' x, f x != ∞) :
    Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf

/--
theorem `tendsto_tsum_compl_atTop_zero` / 定理 `tendsto_tsum_compl_atTop_zero`

English:
theorem tendsto_tsum_compl_atTop_zero
  given: {α : Type*} {f : α -> Real>=0∞} (hf : ∑' x, f x != ∞)
  proof: by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert! ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

中文:
定理 tendsto_tsum_compl_atTop_zero
  条件: {α : 类型} {f : α -> 实数>=0∞} (hf : ∑' x, f x != ∞)
  证明: by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert! ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

Depends on / 依赖: ENNReal, ENNReal.coe_tsum, ENNReal.ne_top_of_tsum_ne_top, ENNReal.tendsto_coe, NNReal, NNReal.summable_comp_injective, NNReal.tendsto_tsum_compl_atTop_zero, Subtype, Subtype.coe_injective, coe_injective, coe_tsum, convert, ne_top_of_tsum_ne_top, summable_comp_injective, tendsto_coe, tendsto_tsum_compl_atTop_zero, tsum_coe_ne_top_iff_summable
-/
theorem tendsto_tsum_compl_atTop_zero {α : Type*} {f : α -> Real>=0∞} (hf : ∑' x, f x != ∞) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert! ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

/--
theorem `tsum_apply` / 定理 `tsum_apply`

English:
theorem tsum_apply
  given: {ι α : Type*} {f : ι -> α -> Real>=0∞} {x : α}
  proof: tsum_apply Pi.summable.mpr fun _ => ENNReal.summable

中文:
定理 tsum_apply
  条件: {ι α : 类型} {f : ι -> α -> 实数>=0∞} {x : α}
  证明: tsum_apply Pi.summable.mpr fun _ => ENNReal.summable
-/
protected theorem tsum_apply {ι α : Type*} {f : ι -> α -> Real>=0∞} {x : α} :
    (∑' i, f i) x = ∑' i, f i x :=
tsum_apply Pi.summable.mpr fun _ => ENNReal.summable

/--
theorem `tsum_sub` / 定理 `tsum_sub`

English:
theorem tsum_sub
  given: {f : Nat -> Real>=0∞} {g : Nat -> Real>=0∞} (h₁ : ∑' i, g i != ∞) (h₂ : g <= f)
  proof: have : forall i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
ENNReal.eq_sub_of_add_eq h₁ by simp only [← ENNReal.tsum_add, this]

中文:
定理 tsum_sub
  条件: {f : 自然数 -> 实数>=0∞} {g : 自然数 -> 实数>=0∞} (h₁ : ∑' i, g i != ∞) (h₂ : g <= f)
  证明: have : forall i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
ENNReal.eq_sub_of_add_eq h₁ by simp only [← ENNReal.tsum_add, this]

Depends on / 依赖: ENNReal, ENNReal.eq_sub_of_add_eq, ENNReal.tsum_add, eq_sub_of_add_eq, tsub_add_cancel_of_le, tsum_add
-/
theorem tsum_sub {f : Nat -> Real>=0∞} {g : Nat -> Real>=0∞} (h₁ : ∑' i, g i != ∞) (h₂ : g <= f) :
    ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
  have : forall i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
ENNReal.eq_sub_of_add_eq h₁ by simp only [← ENNReal.tsum_add, this]

/--
theorem `tsum_comp_le_tsum_of_injective` / 定理 `tsum_comp_le_tsum_of_injective`

English:
theorem tsum_comp_le_tsum_of_injective
  given: {f : α -> β} (hf : Injective f) (g : β -> Real>=0∞)
  proof: ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le) (fun _ => le_rfl)
    ENNReal.summable

中文:
定理 tsum_comp_le_tsum_of_injective
  条件: {f : α -> β} (hf : Injective f) (g : β -> 实数>=0∞)
  证明: ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le) (fun _ => le_rfl)
    ENNReal.summable

Depends on / 依赖: ENNReal, ENNReal.summable, ENNReal.summable.tsum_le_tsum_of_inj, le_rfl, summable, tsum_le_tsum_of_inj, zero_le
-/
theorem tsum_comp_le_tsum_of_injective {f : α -> β} (hf : Injective f) (g : β -> Real>=0∞) :
    ∑' x, g (f x) <= ∑' y, g y :=
  ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le) (fun _ => le_rfl)
    ENNReal.summable

/--
theorem `tsum_le_tsum_comp_of_surjective` / 定理 `tsum_le_tsum_comp_of_surjective`

English:
theorem tsum_le_tsum_comp_of_surjective
  given: {f : α -> β} (hf : Surjective f) (g : β -> Real>=0∞)
  proof: calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
  _ <= ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

中文:
定理 tsum_le_tsum_comp_of_surjective
  条件: {f : α -> β} (hf : Surjective f) (g : β -> 实数>=0∞)
  证明: calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
  _ <= ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

Depends on / 依赖: injective_surjInv, surjInv, surjInv_eq, tsum_comp_le_tsum_of_injective
-/
theorem tsum_le_tsum_comp_of_surjective {f : α -> β} (hf : Surjective f) (g : β -> Real>=0∞) :
    ∑' y, g y <= ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
  _ <= ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

/--
theorem `tsum_mono_subtype` / 定理 `tsum_mono_subtype`

English:
theorem tsum_mono_subtype
  given: (f : α -> Real>=0∞) {s t : Set α} (h : s subseteq t)
  proof: tsum_comp_le_tsum_of_injective (inclusion_injective h) _

中文:
定理 tsum_mono_subtype
  条件: (f : α -> 实数>=0∞) {s t : Set α} (h : s subseteq t)
  证明: tsum_comp_le_tsum_of_injective (inclusion_injective h) _

Depends on / 依赖: inclusion_injective, tsum_comp_le_tsum_of_injective
-/
theorem tsum_mono_subtype (f : α -> Real>=0∞) {s t : Set α} (h : s subseteq t) :
    ∑' x : s, f x <= ∑' x : t, f x :=
  tsum_comp_le_tsum_of_injective (inclusion_injective h) _

/--
theorem `tsum_iUnion_le_tsum` / 定理 `tsum_iUnion_le_tsum`

English:
theorem tsum_iUnion_le_tsum
  given: {ι : Type*} (f : α -> Real>=0∞) (t : ι -> Set α)
  proof: calc ∑' x : ⋃ i, t i, f x <= ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

中文:
定理 tsum_iUnion_le_tsum
  条件: {ι : 类型} (f : α -> 实数>=0∞) (t : ι -> Set α)
  证明: calc ∑' x : ⋃ i, t i, f x <= ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

Depends on / 依赖: ENNReal, ENNReal.tsum_sigma, sigmaToiUnion_surjective, tsum_le_tsum_comp_of_surjective, tsum_sigma
-/
theorem tsum_iUnion_le_tsum {ι : Type*} (f : α -> Real>=0∞) (t : ι -> Set α) :
    ∑' x : ⋃ i, t i, f x <= ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x <= ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

/--
theorem `tsum_biUnion_le_tsum` / 定理 `tsum_biUnion_le_tsum`

English:
theorem tsum_biUnion_le_tsum
  given: {ι : Type*} (f : α -> Real>=0∞) (s : Set ι) (t : ι -> Set α)
  proof: calc ∑' x : ⋃ i in s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ by simp
  _ <= ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

中文:
定理 tsum_biUnion_le_tsum
  条件: {ι : 类型} (f : α -> 实数>=0∞) (s : Set ι) (t : ι -> Set α)
  证明: calc ∑' x : ⋃ i in s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ by simp
  _ <= ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

Depends on / 依赖: tsum_congr_set_coe, tsum_iUnion_le_tsum
-/
theorem tsum_biUnion_le_tsum {ι : Type*} (f : α -> Real>=0∞) (s : Set ι) (t : ι -> Set α) :
    ∑' x : ⋃ i in s, t i, f x <= ∑' i : s, ∑' x : t i, f x :=
calc ∑' x : ⋃ i in s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ by simp
  _ <= ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

/--
theorem `tsum_biUnion_le` / 定理 `tsum_biUnion_le`

English:
theorem tsum_biUnion_le
  given: {ι : Type*} (f : α -> Real>=0∞) (s : Finset ι) (t : ι -> Set α)
  proof: (tsum_biUnion_le_tsum f s t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

中文:
定理 tsum_biUnion_le
  条件: {ι : 类型} (f : α -> 实数>=0∞) (s : Finset ι) (t : ι -> Set α)
  证明: (tsum_biUnion_le_tsum f s t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

Depends on / 依赖: Finset, Finset.tsum_subtype, trans_eq, tsum_biUnion_le_tsum, tsum_subtype
-/
theorem tsum_biUnion_le {ι : Type*} (f : α -> Real>=0∞) (s : Finset ι) (t : ι -> Set α) :
    ∑' x : ⋃ i in s, t i, f x <= ∑ i in s, ∑' x : t i, f x :=
  (tsum_biUnion_le_tsum f s t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

/--
theorem `tsum_iUnion_le` / 定理 `tsum_iUnion_le`

English:
theorem tsum_iUnion_le
  given: {ι : Type*} [Fintype ι] (f : α -> Real>=0∞) (t : ι -> Set α)
  proof: by
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_iUnion_le_tsum f t

中文:
定理 tsum_iUnion_le
  条件: {ι : 类型} [Fintype ι] (f : α -> 实数>=0∞) (t : ι -> Set α)
  证明: by
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_iUnion_le_tsum f t

Depends on / 依赖: SummationFilter, SummationFilter.unconditional, tsum_fintype, tsum_iUnion_le_tsum, unconditional
-/
theorem tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α -> Real>=0∞) (t : ι -> Set α) :
    ∑' x : ⋃ i, t i, f x <= ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_iUnion_le_tsum f t

/--
theorem `tsum_union_le` / 定理 `tsum_union_le`

English:
theorem tsum_union_le
  given: (f : α -> Real>=0∞) (s t : Set α)
  proof: calc ∑' x : ↑(s union t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
  _ <= _ := by simpa using tsum_iUnion_le f (cond · s t)

中文:
定理 tsum_union_le
  条件: (f : α -> 实数>=0∞) (s t : Set α)
  证明: calc ∑' x : ↑(s union t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
  _ <= _ := by simpa using tsum_iUnion_le f (cond · s t)

Depends on / 依赖: tsum_congr_set_coe, tsum_iUnion_le, union_eq_iUnion
-/
theorem tsum_union_le (f : α -> Real>=0∞) (s t : Set α) :
    ∑' x : ↑(s union t), f x <= ∑' x : s, f x + ∑' x : t, f x :=
  calc ∑' x : ↑(s union t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
  _ <= _ := by simpa using tsum_iUnion_le f (cond · s t)

open scoped Classical in
/--
theorem `tsum_eq_add_tsum_ite` / 定理 `tsum_eq_add_tsum_ite`

English:
theorem tsum_eq_add_tsum_ite
  given: {f : β -> Real>=0∞} (b : β)
  proof: ENNReal.summable.tsum_eq_add_tsum_ite' b

中文:
定理 tsum_eq_add_tsum_ite
  条件: {f : β -> 实数>=0∞} (b : β)
  证明: ENNReal.summable.tsum_eq_add_tsum_ite' b

Depends on / 依赖: ENNReal, ENNReal.summable.tsum_eq_add_tsum_ite, summable, tsum_eq_add_tsum_ite
-/
theorem tsum_eq_add_tsum_ite {f : β -> Real>=0∞} (b : β) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  ENNReal.summable.tsum_eq_add_tsum_ite' b

/--
theorem `tsum_add_one_eq_top` / 定理 `tsum_add_one_eq_top`

English:
theorem tsum_add_one_eq_top
  given: {f : Nat -> Real>=0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 != ∞)
  proof: by
  rw [tsum_eq_zero_add' ENNReal.summable]; rw [add_eq_top] at hf
  exact hf.resolve_left hf0

中文:
定理 tsum_add_one_eq_top
  条件: {f : 自然数 -> 实数>=0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 != ∞)
  证明: by
  rw [tsum_eq_zero_add' ENNReal.summable]; rw [add_eq_top] at hf
  exact hf.resolve_left hf0

Depends on / 依赖: ENNReal, ENNReal.summable, add_eq_top, hf.resolve_left, resolve_left, summable, tsum_eq_zero_add
-/
theorem tsum_add_one_eq_top {f : Nat -> Real>=0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 != ∞) :
    ∑' n, f (n + 1) = ∞ := by
  rw [tsum_eq_zero_add' ENNReal.summable]; rw [add_eq_top] at hf
  exact hf.resolve_left hf0

/--
theorem `finite_const_le_of_tsum_ne_top` / 定理 `finite_const_le_of_tsum_ne_top`

English:
theorem finite_const_le_of_tsum_ne_top
  statement: {ι : Type*} {a : ι -> Real>=0∞} (tsum_ne_top : ∑' i, a i != ∞)
  proof: by
  by_contra h
  have := Infinite.to_subtype h
  refine tsum_ne_top (top_unique ?_)
  calc ∞ = ∑' _ : { i | ε <= a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
  _ <= ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
    Subtype.val_injective (fun _ _ => zero_le) (fun i => i.2) ENNR

中文:
定理 finite_const_le_of_tsum_ne_top
  结论: {ι : 类型} {a : ι -> 实数>=0∞} (tsum_ne_top : ∑' i, a i != ∞)
  证明: by
  by_contra h
  have := Infinite.to_subtype h
  refine tsum_ne_top (top_unique ?_)
  calc ∞ = ∑' _ : { i | ε <= a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
  _ <= ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
    Subtype.val_injective (fun _ _ => zero_le) (fun i => i.2) ENNR

Depends on / 依赖: ENNReal, ENNReal.summable, ENNReal.summable.tsum_le_tsum_of_inj, Infinite, Infinite.to_subtype, Subtype, Subtype.val_injective, summable, to_subtype, top_unique, tsum_const_eq_top_of_ne_zero, tsum_le_tsum_of_inj, tsum_ne_top, val_injective, zero_le
-/
theorem finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι -> Real>=0∞} (tsum_ne_top : ∑' i, a i != ∞)
    {ε : Real>=0∞} (ε_ne_zero : ε != 0) : { i : ι | ε <= a i }.Finite := by
  by_contra h
  have := Infinite.to_subtype h
  refine tsum_ne_top (top_unique ?_)
  calc ∞ = ∑' _ : { i | ε <= a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
  _ <= ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
    Subtype.val_injective (fun _ _ => zero_le) (fun i => i.2) ENNReal.summable

/--
theorem `finset_card_const_le_le_of_tsum_le` / 定理 `finset_card_const_le_le_of_tsum_le`

English:
theorem finset_card_const_le_le_of_tsum_le
  statement: {ι : Type*} {a : ι -> Real>=0∞} {c : Real>=0∞} (c_ne_top : c != ∞)
  proof: by
  have hf : { i : ι | ε <= a i }.Finite :=
    finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
  refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
  calc #hf.toFinset * ε = ∑ _i in hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_m

中文:
定理 finset_card_const_le_le_of_tsum_le
  结论: {ι : 类型} {a : ι -> 实数>=0∞} {c : 实数>=0∞} (c_ne_top : c != ∞)
  证明: by
  have hf : { i : ι | ε <= a i }.Finite :=
    finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
  refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
  calc #hf.toFinset * ε = ∑ _i in hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_m

Depends on / 依赖: ENNReal, ENNReal.le_div_iff_mul_le, ENNReal.sum_le_tsum, Finite, Finset, Finset.sum_const, Finset.sum_le_sum, c_ne_top, finite_const_le_of_tsum_ne_top, hf.mem_toFinset, hf.toFinset, le_div_iff_mul_le, mem_toFinset, ne_top_of_le_ne_top, nsmul_eq_mul, sum_const, sum_le_sum, sum_le_tsum, toFinset, tsum_le_c
-/
theorem finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι -> Real>=0∞} {c : Real>=0∞} (c_ne_top : c != ∞)
    (tsum_le_c : ∑' i, a i <= c) {ε : Real>=0∞} (ε_ne_zero : ε != 0) :
    exists hf : { i : ι | ε <= a i }.Finite, #hf.toFinset <= c / ε := by
  have hf : { i : ι | ε <= a i }.Finite :=
    finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
  refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
  calc #hf.toFinset * ε = ∑ _i in hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ i in hf.toFinset, a i := Finset.sum_le_sum fun i => hf.mem_toFinset.1
    _ <= ∑' i, a i := ENNReal.sum_le_tsum _
    _ <= c := tsum_le_c

/--
theorem `tsum_fiberwise` / 定理 `tsum_fiberwise`

English:
theorem tsum_fiberwise
  given: (f : β -> Real>=0∞) (g : β -> γ)
  proof: by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
  exact fun _ => ENNReal.summable.hasSum_iff.mpr rfl

中文:
定理 tsum_fiberwise
  条件: (f : β -> 实数>=0∞) (g : β -> γ)
  证明: by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
  exact fun _ => ENNReal.summable.hasSum_iff.mpr rfl

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, ENNReal.summable.hasSum_iff.mpr, Equiv.sigmaFiberEquiv, HasSum, HasSum.tsum_eq, equiv.hasSum_iff.mpr, hasSum, hasSum_iff, sigmaFiberEquiv, summable, tsum_eq
-/
theorem tsum_fiberwise (f : β -> Real>=0∞) (g : β -> γ) :
    ∑' x, ∑' b : g ⁻¹' {x}, f b = ∑' i, f i := by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
  exact fun _ => ENNReal.summable.hasSum_iff.mpr rfl

end tsum

/--
theorem `tsum_coe_ne_top_iff_summable_coe` / 定理 `tsum_coe_ne_top_iff_summable_coe`

English:
theorem tsum_coe_ne_top_iff_summable_coe
  given: {f : α -> Real>=0}
  proof: by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable

中文:
定理 tsum_coe_ne_top_iff_summable_coe
  条件: {f : α -> 实数>=0}
  证明: by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable

Depends on / 依赖: NNReal, NNReal.summable_coe, summable_coe, tsum_coe_ne_top_iff_summable
-/
theorem tsum_coe_ne_top_iff_summable_coe {f : α -> Real>=0} :
    (∑' a, (f a : Real>=0∞)) != ∞ ↔ Summable fun a => (f a : Real) := by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable

/--
theorem `tsum_coe_eq_top_iff_not_summable_coe` / 定理 `tsum_coe_eq_top_iff_not_summable_coe`

English:
theorem tsum_coe_eq_top_iff_not_summable_coe
  given: {f : α -> Real>=0}
  proof: tsum_coe_ne_top_iff_summable_coe.not_right

中文:
定理 tsum_coe_eq_top_iff_not_summable_coe
  条件: {f : α -> 实数>=0}
  证明: tsum_coe_ne_top_iff_summable_coe.not_right

Depends on / 依赖: not_right, tsum_coe_ne_top_iff_summable_coe, tsum_coe_ne_top_iff_summable_coe.not_right
-/
theorem tsum_coe_eq_top_iff_not_summable_coe {f : α -> Real>=0} :
    (∑' a, (f a : Real>=0∞)) = ∞ ↔ ¬Summable fun a => (f a : Real) :=
  tsum_coe_ne_top_iff_summable_coe.not_right

/--
theorem `hasSum_toReal` / 定理 `hasSum_toReal`

English:
theorem hasSum_toReal
  given: {f : α -> Real>=0∞} (hsum : ∑' x, f x != ∞)
  proof: by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_toReal, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum

中文:
定理 hasSum_toReal
  条件: {f : α -> 实数>=0∞} (hsum : ∑' x, f x != ∞)
  证明: by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_toReal, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum

Depends on / 依赖: ENNReal, ENNReal.ne_top_of_tsum_ne_top, NNReal, NNReal.coe_tsum, NNReal.hasSum_coe, coe_toReal, coe_tsum, hasSum, hasSum_coe, ne_top_of_tsum_ne_top, tsum_coe_ne_top_iff_summable
-/
theorem hasSum_toReal {f : α -> Real>=0∞} (hsum : ∑' x, f x != ∞) :
    HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal) := by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_toReal, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum

/--
theorem `summable_toReal` / 定理 `summable_toReal`

English:
theorem summable_toReal
  given: {f : α -> Real>=0∞} (hsum : ∑' x, f x != ∞)
  statement: Summable fun x => (f x).toReal
  proof: (hasSum_toReal hsum).summable

中文:
定理 summable_toReal
  条件: {f : α -> 实数>=0∞} (hsum : ∑' x, f x != ∞)
  结论: Summable fun x => (f x).to实数
  证明: (hasSum_toReal hsum).summable

Depends on / 依赖: hasSum_toReal, summable
-/
theorem summable_toReal {f : α -> Real>=0∞} (hsum : ∑' x, f x != ∞) : Summable fun x => (f x).toReal :=
  (hasSum_toReal hsum).summable

end ENNReal

namespace NNReal


/--
theorem `tsum_eq_toNNReal_tsum` / 定理 `tsum_eq_toNNReal_tsum`

English:
theorem tsum_eq_toNNReal_tsum
  given: {f : β -> Real>=0}
  statement: ∑' b, f b = (∑' b, (f b : Real>=0∞)).toNNReal
  proof: by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.toNNReal_top, A]

中文:
定理 tsum_eq_toNNReal_tsum
  条件: {f : β -> 实数>=0}
  结论: ∑' b, f b = (∑' b, (f b : 实数>=0∞)).toNN实数
  证明: by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.toNNReal_top, A]

Depends on / 依赖: Classical, Classical.not_not, ENNReal, ENNReal.coe_tsum, ENNReal.toNNReal_coe, ENNReal.toNNReal_top, ENNReal.tsum_coe_ne_top_iff_summable, Summable, coe_tsum, not_not, toNNReal_coe, toNNReal_top, tsum_coe_ne_top_iff_summable, tsum_eq_zero_of_not_summable
-/
theorem tsum_eq_toNNReal_tsum {f : β -> Real>=0} : ∑' b, f b = (∑' b, (f b : Real>=0∞)).toNNReal := by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.toNNReal_top, A]

/--
theorem `exists_le_hasSum_of_le` / 定理 `exists_le_hasSum_of_le`

English:
theorem exists_le_hasSum_of_le
  given: {f g : β -> Real>=0} {r : Real>=0} (hgf : forall b, g b <= f b) (hfr : HasSum f r)
  proof: have : (∑' b, (g b : Real>=0∞)) <= r := by
    refine hasSum_le (fun b => ?_) ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
⟨p, hpr, ENNReal.hasSum_coe.1 Eq ▸ ENNReal.summable.hasSum⟩

中文:
定理 exists_le_hasSum_of_le
  条件: {f g : β -> 实数>=0} {r : 实数>=0} (hgf : 对任意 b, g b <= f b) (hfr : HasSum f r)
  证明: have : (∑' b, (g b : Real>=0∞)) <= r := by
    refine hasSum_le (fun b => ?_) ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
⟨p, hpr, ENNReal.hasSum_coe.1 Eq ▸ ENNReal.summable.hasSum⟩

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.hasSum_coe, ENNReal.le_coe_iff, ENNReal.summable.hasSum, coe_le_coe, hasSum, hasSum_coe, hasSum_le, le_coe_iff, summable
-/
theorem exists_le_hasSum_of_le {f g : β -> Real>=0} {r : Real>=0} (hgf : forall b, g b <= f b) (hfr : HasSum f r) :
    exists p <= r, HasSum g p :=
  have : (∑' b, (g b : Real>=0∞)) <= r := by
    refine hasSum_le (fun b => ?_) ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
⟨p, hpr, ENNReal.hasSum_coe.1 Eq ▸ ENNReal.summable.hasSum⟩

/--
theorem `summable_of_le` / 定理 `summable_of_le`

English:
theorem summable_of_le
  given: {f g : β -> Real>=0} (hgf : forall b, g b <= f b)
  statement: Summable f -> Summable g
  proof: exists_le_hasSum_of_le hgf hfr
    hp.summable

中文:
定理 summable_of_le
  条件: {f g : β -> 实数>=0} (hgf : 对任意 b, g b <= f b)
  结论: Summable f -> Summable g
  证明: exists_le_hasSum_of_le hgf hfr
    hp.summable

Depends on / 依赖: exists_le_hasSum_of_le
-/
theorem summable_of_le {f g : β -> Real>=0} (hgf : forall b, g b <= f b) : Summable f -> Summable g
  | ⟨_r, hfr⟩ =>
    let ⟨_p, _, hp⟩ := exists_le_hasSum_of_le hgf hfr
    hp.summable

/--
theorem `_root_.Summable.countable_support_nnreal` / 定理 `_root_.Summable.countable_support_nnreal`

English:
theorem _root_.Summable.countable_support_nnreal
  given: (f : α -> Real>=0) (h : Summable f)
  proof: by
  rw [← NNReal.summable_coe] at h
  simpa [support] using h.countable_support

中文:
定理 _root_.Summable.countable_support_nnreal
  条件: (f : α -> 实数>=0) (h : Summable f)
  证明: by
  rw [← NNReal.summable_coe] at h
  simpa [support] using h.countable_support

Depends on / 依赖: NNReal, NNReal.summable_coe, countable_support, h.countable_support, summable_coe, support
-/
theorem _root_.Summable.countable_support_nnreal (f : α -> Real>=0) (h : Summable f) :
    f.support.Countable := by
  rw [← NNReal.summable_coe] at h
  simpa [support] using h.countable_support

/--
theorem `hasSum_iff_tendsto_nat` / 定理 `hasSum_iff_tendsto_nat`

English:
theorem hasSum_iff_tendsto_nat
  given: {f : Nat -> Real>=0} {r : Real>=0}
  proof: by
  rw [← ENNReal.hasSum_coe]; rw [ENNReal.hasSum_iff_tendsto_nat]
  norm_cast

中文:
定理 hasSum_iff_tendsto_nat
  条件: {f : 自然数 -> 实数>=0} {r : 实数>=0}
  证明: by
  rw [← ENNReal.hasSum_coe]; rw [ENNReal.hasSum_iff_tendsto_nat]
  norm_cast

Depends on / 依赖: ENNReal, ENNReal.hasSum_coe, ENNReal.hasSum_iff_tendsto_nat, hasSum_coe, hasSum_iff_tendsto_nat
-/
theorem hasSum_iff_tendsto_nat {f : Nat -> Real>=0} {r : Real>=0} :
    HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 r) := by
  rw [← ENNReal.hasSum_coe]; rw [ENNReal.hasSum_iff_tendsto_nat]
  norm_cast

/--
theorem `not_summable_iff_tendsto_nat_atTop` / 定理 `not_summable_iff_tendsto_nat_atTop`

English:
theorem not_summable_iff_tendsto_nat_atTop
  given: {f : Nat -> Real>=0}
  proof: by
  constructor
  · intro h
    refine ((tendsto_atTop_of_monotone ?_).resolve_right h).comp ?_
    exacts [Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (hasSum_iff_tendsto_nat.1 hr)

中文:
定理 not_summable_iff_tendsto_nat_atTop
  条件: {f : 自然数 -> 实数>=0}
  证明: by
  constructor
  · intro h
    refine ((tendsto_atTop_of_monotone ?_).resolve_right h).comp ?_
    exacts [Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (hasSum_iff_tendsto_nat.1 hr)

Depends on / 依赖: Finset, Finset.sum_mono_set, exacts, hasSum_iff_tendsto_nat, not_tendsto_nhds_of_tendsto_atTop, resolve_right, sum_mono_set, tendsto_atTop_of_monotone, tendsto_finset_range
-/
theorem not_summable_iff_tendsto_nat_atTop {f : Nat -> Real>=0} :
    ¬Summable f ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop atTop := by
  constructor
  · intro h
    refine ((tendsto_atTop_of_monotone ?_).resolve_right h).comp ?_
    exacts [Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (hasSum_iff_tendsto_nat.1 hr)

/--
theorem `summable_iff_not_tendsto_nat_atTop` / 定理 `summable_iff_not_tendsto_nat_atTop`

English:
theorem summable_iff_not_tendsto_nat_atTop
  given: {f : Nat -> Real>=0}
  proof: by
  rw [← not_iff_not]; rw [Classical.not_not]; rw [not_summable_iff_tendsto_nat_atTop]

中文:
定理 summable_iff_not_tendsto_nat_atTop
  条件: {f : 自然数 -> 实数>=0}
  证明: by
  rw [← not_iff_not]; rw [Classical.not_not]; rw [not_summable_iff_tendsto_nat_atTop]

Depends on / 依赖: Classical, Classical.not_not, not_iff_not, not_not, not_summable_iff_tendsto_nat_atTop
-/
theorem summable_iff_not_tendsto_nat_atTop {f : Nat -> Real>=0} :
    Summable f ↔ ¬Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not]; rw [Classical.not_not]; rw [not_summable_iff_tendsto_nat_atTop]

/--
theorem `summable_of_sum_range_le` / 定理 `summable_of_sum_range_le`

English:
theorem summable_of_sum_range_le
  statement: {f : Nat -> Real>=0} {c : Real>=0}
  proof: by
  refine summable_iff_not_tendsto_nat_atTop.2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

中文:
定理 summable_of_sum_range_le
  结论: {f : 自然数 -> 实数>=0} {c : 实数>=0}
  证明: by
  refine summable_iff_not_tendsto_nat_atTop.2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

Depends on / 依赖: exists_lt_of_tendsto_atTop, hn.trans_le, lt_irrefl, summable_iff_not_tendsto_nat_atTop, trans_le
-/
theorem summable_of_sum_range_le {f : Nat -> Real>=0} {c : Real>=0}
    (h : forall n, ∑ i in Finset.range n, f i <= c) : Summable f := by
  refine summable_iff_not_tendsto_nat_atTop.2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

/--
theorem `tsum_le_of_sum_range_le` / 定理 `tsum_le_of_sum_range_le`

English:
theorem tsum_le_of_sum_range_le
  statement: {f : Nat -> Real>=0} {c : Real>=0}
  proof: (summable_of_sum_range_le h).tsum_le_of_sum_range_le h

中文:
定理 tsum_le_of_sum_range_le
  结论: {f : 自然数 -> 实数>=0} {c : 实数>=0}
  证明: (summable_of_sum_range_le h).tsum_le_of_sum_range_le h

Depends on / 依赖: summable_of_sum_range_le, tsum_le_of_sum_range_le
-/
theorem tsum_le_of_sum_range_le {f : Nat -> Real>=0} {c : Real>=0}
    (h : forall n, ∑ i in Finset.range n, f i <= c) : ∑' n, f n <= c :=
  (summable_of_sum_range_le h).tsum_le_of_sum_range_le h

/--
theorem `tsum_comp_le_tsum_of_inj` / 定理 `tsum_comp_le_tsum_of_inj`

English:
theorem tsum_comp_le_tsum_of_inj
  statement: {β : Type*} {f : α -> Real>=0} (hf : Summable f) {i : β -> α}
  proof: (summable_comp_injective hf hi).tsum_le_tsum_of_inj i hi (fun _ _ => zero_le) (fun _ => le_rfl)
    hf

中文:
定理 tsum_comp_le_tsum_of_inj
  结论: {β : 类型} {f : α -> 实数>=0} (hf : Summable f) {i : β -> α}
  证明: (summable_comp_injective hf hi).tsum_le_tsum_of_inj i hi (fun _ _ => zero_le) (fun _ => le_rfl)
    hf

Depends on / 依赖: le_rfl, summable_comp_injective, tsum_le_tsum_of_inj, zero_le
-/
theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α -> Real>=0} (hf : Summable f) {i : β -> α}
    (hi : Function.Injective i) : (∑' x, f (i x)) <= ∑' x, f x :=
  (summable_comp_injective hf hi).tsum_le_tsum_of_inj i hi (fun _ _ => zero_le) (fun _ => le_rfl)
    hf

/--
theorem `summable_sigma` / 定理 `summable_sigma`

English:
theorem summable_sigma
  given: {β : α -> Type*} {f : (Σ x, β x) -> Real>=0}
  proof: by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma',
      ENNReal.coe_tsum (h₁ _)] using h₂

中文:
定理 summable_sigma
  条件: {β : α -> 类型} {f : (Σ x, β x) -> 实数>=0}
  证明: by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma',
      ENNReal.coe_tsum (h₁ _)] using h₂

Depends on / 依赖: ENNReal, ENNReal.coe_tsum, ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma, NNReal, NNReal.coe_tsum, NNReal.summable_coe, coe_tsum, h.sigma, h.sigma_factor, sigma_factor, summable_coe, tsum_coe_ne_top_iff_summable, tsum_sigma
-/
theorem summable_sigma {β : α -> Type*} {f : (Σ x, β x) -> Real>=0} :
    Summable f ↔ (forall x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma',
      ENNReal.coe_tsum (h₁ _)] using h₂

/--
theorem `indicator_summable` / 定理 `indicator_summable`

English:
theorem indicator_summable
  given: {f : α -> Real>=0} (hf : Summable f) (s : Set α)
  proof: by
  classical
  refine NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) ?_) hf
  split_ifs
  · exact le_refl (f a)
  · exact zero_le_coe

中文:
定理 indicator_summable
  条件: {f : α -> 实数>=0} (hf : Summable f) (s : Set α)
  证明: by
  classical
  refine NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) ?_) hf
  split_ifs
  · exact le_refl (f a)
  · exact zero_le_coe

Depends on / 依赖: NNReal, NNReal.summable_of_le, classical, indicator_apply, le_of_eq, le_refl, le_trans, s.indicator_apply, split_ifs, summable_of_le, zero_le_coe
-/
theorem indicator_summable {f : α -> Real>=0} (hf : Summable f) (s : Set α) :
    Summable (s.indicator f) := by
  classical
  refine NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) ?_) hf
  split_ifs
  · exact le_refl (f a)
  · exact zero_le_coe

/--
theorem `tsum_indicator_ne_zero` / 定理 `tsum_indicator_ne_zero`

English:
theorem tsum_indicator_ne_zero
  given: {f : α -> Real>=0} (hf : Summable f) {s : Set α} (h : exists a in s, f a != 0)
  proof: fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap ((Set.indicator_apply_eq_self.mpr (absurd ha)).symm.trans
    ((indicator_summable hf s).tsum_eq_zero_iff.1 h' a))

中文:
定理 tsum_indicator_ne_zero
  条件: {f : α -> 实数>=0} (hf : Summable f) {s : Set α} (h : 存在 a in s, f a != 0)
  证明: fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap ((Set.indicator_apply_eq_self.mpr (absurd ha)).symm.trans
    ((indicator_summable hf s).tsum_eq_zero_iff.1 h' a))
-/
theorem tsum_indicator_ne_zero {f : α -> Real>=0} (hf : Summable f) {s : Set α} (h : exists a in s, f a != 0) :
    (∑' x, (s.indicator f) x) != 0 := fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap ((Set.indicator_apply_eq_self.mpr (absurd ha)).symm.trans
    ((indicator_summable hf s).tsum_eq_zero_iff.1 h' a))

open Finset

/--
theorem `tendsto_sum_nat_add` / 定理 `tendsto_sum_nat_add`

English:
theorem tendsto_sum_nat_add
  given: (f : Nat -> Real>=0)
  statement: Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)
  proof: by
  rw [← tendsto_coe]
  convert! _root_.tendsto_sum_nat_add fun i => (f i : Real)
  norm_cast

nonrec theorem hasSum_lt {f g : α -> Real>=0} {sf sg : Real>=0} {i : α} (h : forall a : α, f a <= g a)
    (hi : f i < g i) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  have A : forall a : α, 

中文:
定理 tendsto_sum_nat_add
  条件: (f : 自然数 -> 实数>=0)
  结论: Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)
  证明: by
  rw [← tendsto_coe]
  convert! _root_.tendsto_sum_nat_add fun i => (f i : Real)
  norm_cast

nonrec theorem hasSum_lt {f g : α -> Real>=0} {sf sg : Real>=0} {i : α} (h : forall a : α, f a <= g a)
    (hi : f i < g i) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  have A : forall a : α, 

Depends on / 依赖: _root_, _root_.tendsto_sum_nat_add, convert, tendsto_coe, tendsto_sum_nat_add
-/
theorem tendsto_sum_nat_add (f : Nat -> Real>=0) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  rw [← tendsto_coe]
  convert! _root_.tendsto_sum_nat_add fun i => (f i : Real)
  norm_cast

nonrec theorem hasSum_lt {f g : α -> Real>=0} {sf sg : Real>=0} {i : α} (h : forall a : α, f a <= g a)
    (hi : f i < g i) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  have A : forall a : α, (f a : Real) <= g a := fun a => NNReal.coe_le_coe.2 (h a)
  have : (sf : Real) < sg := hasSum_lt A (NNReal.coe_lt_coe.2 hi) (hasSum_coe.2 hf) (hasSum_coe.2 hg)
  exact NNReal.coe_lt_coe.1 this

@[mono]
/--
theorem `hasSum_strict_mono` / 定理 `hasSum_strict_mono`

English:
theorem hasSum_strict_mono
  statement: {f g : α -> Real>=0} {sf sg : Real>=0} (hf : HasSum f sf) (hg : HasSum g sg)
  proof: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg

中文:
定理 hasSum_strict_mono
  结论: {f g : α -> 实数>=0} {sf sg : 实数>=0} (hf : HasSum f sf) (hg : HasSum g sg)
  证明: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg

Depends on / 依赖: Pi.lt_def.mp, hasSum_lt, lt_def
-/
theorem hasSum_strict_mono {f g : α -> Real>=0} {sf sg : Real>=0} (hf : HasSum f sf) (hg : HasSum g sg)
    (h : f < g) : sf < sg :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg

/--
theorem `tsum_lt_tsum` / 定理 `tsum_lt_tsum`

English:
theorem tsum_lt_tsum
  statement: {f g : α -> Real>=0} {i : α} (h : forall a : α, f a <= g a) (hi : f i < g i)
  proof: hasSum_lt h hi (summable_of_le h hg).hasSum hg.hasSum

@[gcongr, mono]

中文:
定理 tsum_lt_tsum
  结论: {f g : α -> 实数>=0} {i : α} (h : 对任意 a : α, f a <= g a) (hi : f i < g i)
  证明: hasSum_lt h hi (summable_of_le h hg).hasSum hg.hasSum

@[gcongr, mono]

Depends on / 依赖: hasSum, hasSum_lt, hg.hasSum, summable_of_le
-/
theorem tsum_lt_tsum {f g : α -> Real>=0} {i : α} (h : forall a : α, f a <= g a) (hi : f i < g i)
    (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  hasSum_lt h hi (summable_of_le h hg).hasSum hg.hasSum

@[gcongr, mono]
/--
theorem `tsum_strict_mono` / 定理 `tsum_strict_mono`

English:
theorem tsum_strict_mono
  given: {f g : α -> Real>=0} (hg : Summable g) (h : f < g)
  statement: ∑' n, f n < ∑' n, g n
  proof: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg

中文:
定理 tsum_strict_mono
  条件: {f g : α -> 实数>=0} (hg : Summable g) (h : f < g)
  结论: ∑' n, f n < ∑' n, g n
  证明: let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg

Depends on / 依赖: Pi.lt_def.mp, lt_def, tsum_lt_tsum
-/
theorem tsum_strict_mono {f g : α -> Real>=0} (hg : Summable g) (h : f < g) : ∑' n, f n < ∑' n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg

/--
theorem `tsum_pos` / 定理 `tsum_pos`

English:
theorem tsum_pos
  given: {g : α -> Real>=0} (hg : Summable g) (i : α) (hi : 0 < g i)
  statement: 0 < ∑' b, g b
  proof: by
  simpa using tsum_lt_tsum (fun a => zero_le) hi hg

中文:
定理 tsum_pos
  条件: {g : α -> 实数>=0} (hg : Summable g) (i : α) (hi : 0 < g i)
  结论: 0 < ∑' b, g b
  证明: by
  simpa using tsum_lt_tsum (fun a => zero_le) hi hg

Depends on / 依赖: tsum_lt_tsum, zero_le
-/
theorem tsum_pos {g : α -> Real>=0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑' b, g b := by
  simpa using tsum_lt_tsum (fun a => zero_le) hi hg

open scoped Classical in
/--
theorem `tsum_eq_add_tsum_ite` / 定理 `tsum_eq_add_tsum_ite`

English:
theorem tsum_eq_add_tsum_ite
  given: {f : α -> Real>=0} (hf : Summable f) (i : α)
  proof: by
  refine (NNReal.summable_of_le (fun i' => ?_) hf).tsum_eq_add_tsum_ite' i
  rw [Function.update_apply]
  split_ifs <;> simp

中文:
定理 tsum_eq_add_tsum_ite
  条件: {f : α -> 实数>=0} (hf : Summable f) (i : α)
  证明: by
  refine (NNReal.summable_of_le (fun i' => ?_) hf).tsum_eq_add_tsum_ite' i
  rw [Function.update_apply]
  split_ifs <;> simp

Depends on / 依赖: Function, Function.update_apply, NNReal, NNReal.summable_of_le, split_ifs, summable_of_le, tsum_eq_add_tsum_ite, update_apply
-/
theorem tsum_eq_add_tsum_ite {f : α -> Real>=0} (hf : Summable f) (i : α) :
    ∑' x, f x = f i + ∑' x, ite (x = i) 0 (f x) := by
  refine (NNReal.summable_of_le (fun i' => ?_) hf).tsum_eq_add_tsum_ite' i
  rw [Function.update_apply]
  split_ifs <;> simp

end NNReal

namespace ENNReal

/--
theorem `tsum_toNNReal_eq` / 定理 `tsum_toNNReal_eq`

English:
theorem tsum_toNNReal_eq
  given: {f : α -> Real>=0∞} (hf : forall a, f a != ∞)
  proof: (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm

中文:
定理 tsum_toNNReal_eq
  条件: {f : α -> 实数>=0∞} (hf : 对任意 a, f a != ∞)
  证明: (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm

Depends on / 依赖: ENNReal, ENNReal.toNNReal, NNReal, NNReal.tsum_eq_toNNReal_tsum.symm, coe_toNNReal, congr_arg, toNNReal, tsum_congr, tsum_eq_toNNReal_tsum
-/
theorem tsum_toNNReal_eq {f : α -> Real>=0∞} (hf : forall a, f a != ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm

/--
theorem `tsum_toReal_eq` / 定理 `tsum_toReal_eq`

English:
theorem tsum_toReal_eq
  given: {f : α -> Real>=0∞} (hf : forall a, f a != ∞)
  proof: by
  simp only [ENNReal.toReal, tsum_toNNReal_eq hf, NNReal.coe_tsum]

中文:
定理 tsum_toReal_eq
  条件: {f : α -> 实数>=0∞} (hf : 对任意 a, f a != ∞)
  证明: by
  simp only [ENNReal.toReal, tsum_toNNReal_eq hf, NNReal.coe_tsum]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_tsum, coe_tsum, toReal, tsum_toNNReal_eq
-/
theorem tsum_toReal_eq {f : α -> Real>=0∞} (hf : forall a, f a != ∞) :
    (∑' a, f a).toReal = ∑' a, (f a).toReal := by
  simp only [ENNReal.toReal, tsum_toNNReal_eq hf, NNReal.coe_tsum]

/--
theorem `tendsto_sum_nat_add` / 定理 `tendsto_sum_nat_add`

English:
theorem tendsto_sum_nat_add
  given: (f : Nat -> Real>=0∞) (hf : ∑' i, f i != ∞)
  proof: by
  lift f to Nat -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact mod_cast NNReal.tendsto_sum_nat_add f

中文:
定理 tendsto_sum_nat_add
  条件: (f : 自然数 -> 实数>=0∞) (hf : ∑' i, f i != ∞)
  证明: by
  lift f to Nat -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact mod_cast NNReal.tendsto_sum_nat_add f

Depends on / 依赖: ENNReal, ENNReal.coe_tsum, ENNReal.coe_zero, ENNReal.ne_top_of_tsum_ne_top, NNReal, NNReal.summable_nat_add, NNReal.tendsto_sum_nat_add, Summable, coe_tsum, coe_zero, mod_cast, ne_top_of_tsum_ne_top, replace, summable_nat_add, tendsto_sum_nat_add, tsum_coe_ne_top_iff_summable
-/
theorem tendsto_sum_nat_add (f : Nat -> Real>=0∞) (hf : ∑' i, f i != ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  lift f to Nat -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact mod_cast NNReal.tendsto_sum_nat_add f

/--
theorem `tsum_le_of_sum_range_le` / 定理 `tsum_le_of_sum_range_le`

English:
theorem tsum_le_of_sum_range_le
  statement: {f : Nat -> Real>=0∞} {c : Real>=0∞}
  proof: ENNReal.summable.tsum_le_of_sum_range_le h

中文:
定理 tsum_le_of_sum_range_le
  结论: {f : 自然数 -> 实数>=0∞} {c : 实数>=0∞}
  证明: ENNReal.summable.tsum_le_of_sum_range_le h

Depends on / 依赖: ENNReal, ENNReal.summable.tsum_le_of_sum_range_le, summable, tsum_le_of_sum_range_le
-/
theorem tsum_le_of_sum_range_le {f : Nat -> Real>=0∞} {c : Real>=0∞}
    (h : forall n, ∑ i in Finset.range n, f i <= c) : ∑' n, f n <= c :=
  ENNReal.summable.tsum_le_of_sum_range_le h

/--
theorem `hasSum_lt` / 定理 `hasSum_lt`

English:
theorem hasSum_lt
  statement: {f g : α -> Real>=0∞} {sf sg : Real>=0∞} {i : α} (h : forall a : α, f a <= g a) (hi : f i < g i)
  proof: by
  by_cases hsg : sg = ∞
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : forall x, g x != ∞ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α -> Real>=0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α -> Rea

中文:
定理 hasSum_lt
  结论: {f g : α -> 实数>=0∞} {sf sg : 实数>=0∞} {i : α} (h : 对任意 a : α, f a <= g a) (hi : f i < g i)
  证明: by
  by_cases hsg : sg = ∞
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : forall x, g x != ∞ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α -> Real>=0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α -> Rea

Depends on / 依赖: ENNReal, ENNReal.hasSum_coe, ENNReal.ne_top_of_tsum_ne_top, NNReal, NNReal.hasSum_lt, coe_le_coe, coe_lt_coe, hasSum_coe, hasSum_lt, hg.tsum_eq.symm, hsg.symm, le_top, lt_of_le_of_lt, lt_of_le_of_ne, ne_of_lt, ne_top_of_tsum_ne_top, tsum_eq
-/
theorem hasSum_lt {f g : α -> Real>=0∞} {sf sg : Real>=0∞} {i : α} (h : forall a : α, f a <= g a) (hi : f i < g i)
    (hsf : sf != ∞) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  by_cases hsg : sg = ∞
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : forall x, g x != ∞ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α -> Real>=0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α -> Real>=0 using hg'
    lift sf to Real>=0 using hsf
    lift sg to Real>=0 using hsg
    simp only [coe_le_coe, coe_lt_coe] at h hi ⊢
    exact NNReal.hasSum_lt h hi (ENNReal.hasSum_coe.1 hf) (ENNReal.hasSum_coe.1 hg)

/--
theorem `tsum_lt_tsum` / 定理 `tsum_lt_tsum`

English:
theorem tsum_lt_tsum
  statement: {f g : α -> Real>=0∞} {i : α} (hfi : tsum f != ∞) (h : forall a : α, f a <= g a)
  proof: hasSum_lt h hi hfi ENNReal.summable.hasSum ENNReal.summable.hasSum

中文:
定理 tsum_lt_tsum
  结论: {f g : α -> 实数>=0∞} {i : α} (hfi : tsum f != ∞) (h : 对任意 a : α, f a <= g a)
  证明: hasSum_lt h hi hfi ENNReal.summable.hasSum ENNReal.summable.hasSum

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, hasSum, hasSum_lt, summable
-/
theorem tsum_lt_tsum {f g : α -> Real>=0∞} {i : α} (hfi : tsum f != ∞) (h : forall a : α, f a <= g a)
    (hi : f i < g i) : ∑' x, f x < ∑' x, g x :=
  hasSum_lt h hi hfi ENNReal.summable.hasSum ENNReal.summable.hasSum

end ENNReal

/--
theorem `tsum_comp_le_tsum_of_inj` / 定理 `tsum_comp_le_tsum_of_inj`

English:
theorem tsum_comp_le_tsum_of_inj
  statement: {β : Type*} {f : α -> Real} (hf : Summable f) (hn : forall a, 0 <= f a)
  proof: by
  lift f to α -> Real>=0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [Function.comp_def, ← NNReal.coe_tsum] using! NNReal.tsum_comp_le_tsum_of_inj hf hi

中文:
定理 tsum_comp_le_tsum_of_inj
  结论: {β : 类型} {f : α -> 实数} (hf : Summable f) (hn : 对任意 a, 0 <= f a)
  证明: by
  lift f to α -> Real>=0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [Function.comp_def, ← NNReal.coe_tsum] using! NNReal.tsum_comp_le_tsum_of_inj hf hi

Depends on / 依赖: Function, Function.comp_def, NNReal, NNReal.coe_tsum, NNReal.summable_coe, NNReal.tsum_comp_le_tsum_of_inj, coe_tsum, comp_def, summable_coe, tsum_comp_le_tsum_of_inj
-/
theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α -> Real} (hf : Summable f) (hn : forall a, 0 <= f a)
    {i : β -> α} (hi : Function.Injective i) : tsum (f ∘ i) <= tsum f := by
  lift f to α -> Real>=0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [Function.comp_def, ← NNReal.coe_tsum] using! NNReal.tsum_comp_le_tsum_of_inj hf hi

/--
theorem `Summable.of_nonneg_of_le` / 定理 `Summable.of_nonneg_of_le`

English:
theorem Summable.of_nonneg_of_le
  statement: {f g : β -> Real} (hg : forall b, 0 <= g b) (hgf : forall b, g b <= f b)
  proof: by
  lift f to β -> Real>=0 using fun b => (hg b).trans (hgf b)
  lift g to β -> Real>=0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf

中文:
定理 Summable.of_nonneg_of_le
  结论: {f g : β -> 实数} (hg : 对任意 b, 0 <= g b) (hgf : 对任意 b, g b <= f b)
  证明: by
  lift f to β -> Real>=0 using fun b => (hg b).trans (hgf b)
  lift g to β -> Real>=0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.summable_coe, NNReal.summable_of_le, coe_le_coe, summable_coe, summable_of_le
-/
theorem Summable.of_nonneg_of_le {f g : β -> Real} (hg : forall b, 0 <= g b) (hgf : forall b, g b <= f b)
    (hf : Summable f) : Summable g := by
  lift f to β -> Real>=0 using fun b => (hg b).trans (hgf b)
  lift g to β -> Real>=0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf

/--
theorem `Summable.toNNReal` / 定理 `Summable.toNNReal`

English:
theorem Summable.toNNReal
  given: {f : α -> Real} (hf : Summable f)
  statement: Summable fun n => (f n).toNNReal
  proof: by
  apply NNReal.summable_coe.1
  refine .of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => ?_) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]

中文:
定理 Summable.toNNReal
  条件: {f : α -> 实数} (hf : Summable f)
  结论: Summable fun n => (f n).toNN实数
  证明: by
  apply NNReal.summable_coe.1
  refine .of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => ?_) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]

Depends on / 依赖: NNReal, NNReal.coe_nonneg, NNReal.summable_coe, Real.coe_toNNReal, abs_nonneg, and_self_iff, coe_nonneg, coe_toNNReal, hf.abs, le_abs_self, max_le_iff, of_nonneg_of_le, summable_coe
-/
theorem Summable.toNNReal {f : α -> Real} (hf : Summable f) : Summable fun n => (f n).toNNReal := by
  apply NNReal.summable_coe.1
  refine .of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => ?_) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]

/--
lemma `Summable.tsum_ofReal_lt_top` / 引理 `Summable.tsum_ofReal_lt_top`

English:
lemma Summable.tsum_ofReal_lt_top
  given: {f : α -> Real} (hf : Summable f)
  statement: ∑' i, .ofReal (f i) < ∞
  proof: by
  unfold ENNReal.ofReal
  rw [lt_top_iff_ne_top]; rw [ENNReal.tsum_coe_ne_top_iff_summable]
  exact hf.toNNReal

中文:
引理 Summable.tsum_ofReal_lt_top
  条件: {f : α -> 实数} (hf : Summable f)
  结论: ∑' i, .of实数 (f i) < ∞
  证明: by
  unfold ENNReal.ofReal
  rw [lt_top_iff_ne_top]; rw [ENNReal.tsum_coe_ne_top_iff_summable]
  exact hf.toNNReal

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.tsum_coe_ne_top_iff_summable, hf.toNNReal, lt_top_iff_ne_top, ofReal, toNNReal, tsum_coe_ne_top_iff_summable
-/
lemma Summable.tsum_ofReal_lt_top {f : α -> Real} (hf : Summable f) : ∑' i, .ofReal (f i) < ∞ := by
  unfold ENNReal.ofReal
  rw [lt_top_iff_ne_top]; rw [ENNReal.tsum_coe_ne_top_iff_summable]
  exact hf.toNNReal

/--
lemma `Summable.tsum_ofReal_ne_top` / 引理 `Summable.tsum_ofReal_ne_top`

English:
lemma Summable.tsum_ofReal_ne_top
  given: {f : α -> Real} (hf : Summable f)
  statement: ∑' i, .ofReal (f i) != ∞
  proof: hf.tsum_ofReal_lt_top.ne

中文:
引理 Summable.tsum_ofReal_ne_top
  条件: {f : α -> 实数} (hf : Summable f)
  结论: ∑' i, .of实数 (f i) != ∞
  证明: hf.tsum_ofReal_lt_top.ne

Depends on / 依赖: hf.tsum_ofReal_lt_top.ne, tsum_ofReal_lt_top
-/
lemma Summable.tsum_ofReal_ne_top {f : α -> Real} (hf : Summable f) : ∑' i, .ofReal (f i) != ∞ :=
  hf.tsum_ofReal_lt_top.ne

/--
theorem `_root_.Summable.countable_support_ennreal` / 定理 `_root_.Summable.countable_support_ennreal`

English:
theorem _root_.Summable.countable_support_ennreal
  given: {f : α -> Real>=0∞} (h : ∑' (i : α), f i != ∞)
  proof: by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top h
  simpa [support] using (ENNReal.tsum_coe_ne_top_iff_summable.1 h).countable_support_nnreal

中文:
定理 _root_.Summable.countable_support_ennreal
  条件: {f : α -> 实数>=0∞} (h : ∑' (i : α), f i != ∞)
  证明: by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top h
  simpa [support] using (ENNReal.tsum_coe_ne_top_iff_summable.1 h).countable_support_nnreal

Depends on / 依赖: ENNReal, ENNReal.ne_top_of_tsum_ne_top, ENNReal.tsum_coe_ne_top_iff_summable, countable_support_nnreal, ne_top_of_tsum_ne_top, support, tsum_coe_ne_top_iff_summable
-/
theorem _root_.Summable.countable_support_ennreal {f : α -> Real>=0∞} (h : ∑' (i : α), f i != ∞) :
    f.support.Countable := by
  lift f to α -> Real>=0 using ENNReal.ne_top_of_tsum_ne_top h
  simpa [support] using (ENNReal.tsum_coe_ne_top_iff_summable.1 h).countable_support_nnreal

/--
theorem `hasSum_iff_tendsto_nat_of_nonneg` / 定理 `hasSum_iff_tendsto_nat_of_nonneg`

English:
theorem hasSum_iff_tendsto_nat_of_nonneg
  given: {f : Nat -> Real} (hf : forall i, 0 <= f i) (r : Real)
  proof: by
  lift f to Nat -> Real>=0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat

中文:
定理 hasSum_iff_tendsto_nat_of_nonneg
  条件: {f : 自然数 -> 实数} (hf : 对任意 i, 0 <= f i) (r : 实数)
  证明: by
  lift f to Nat -> Real>=0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat

Depends on / 依赖: HasSum, NNReal, NNReal.coe_sum, NNReal.hasSum_iff_tendsto_nat, NNReal.tendsto_coe, coe_sum, exists_congr, hasSum_iff_tendsto_nat, tendsto_coe
-/
theorem hasSum_iff_tendsto_nat_of_nonneg {f : Nat -> Real} (hf : forall i, 0 <= f i) (r : Real) :
    HasSum f r ↔ Tendsto (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 r) := by
  lift f to Nat -> Real>=0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat

/--
theorem `ENNReal.ofReal_tsum_of_nonneg` / 定理 `ENNReal.ofReal_tsum_of_nonneg`

English:
theorem ENNReal.ofReal_tsum_of_nonneg
  given: {f : α -> Real} (hf_nonneg : forall n, 0 <= f n) (hf : Summable f)
  proof: by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]

中文:
定理 ENNReal.ofReal_tsum_of_nonneg
  条件: {f : α -> 实数} (hf_nonneg : 对任意 n, 0 <= f n) (hf : Summable f)
  证明: by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.tsum_coe_eq, NNReal, NNReal.hasSum_real_toNNReal_of_nonneg, hasSum_real_toNNReal_of_nonneg, hf_nonneg, ofReal, simp_rw, tsum_coe_eq
-/
theorem ENNReal.ofReal_tsum_of_nonneg {f : α -> Real} (hf_nonneg : forall n, 0 <= f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n) := by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]

section tprod

/--
theorem `ENNReal.multipliable_of_le_one` / 定理 `ENNReal.multipliable_of_le_one`

English:
theorem ENNReal.multipliable_of_le_one
  given: {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1)
  proof: ⟨_, _root_.hasProd_of_isGLB_of_le_one _ h₀ (isGLB_sInf _)⟩

中文:
定理 ENNReal.multipliable_of_le_one
  条件: {f : α -> 实数>=0∞} (h₀ : 对任意 i, f i <= 1)
  证明: ⟨_, _root_.hasProd_of_isGLB_of_le_one _ h₀ (isGLB_sInf _)⟩

Depends on / 依赖: _root_, _root_.hasProd_of_isGLB_of_le_one, hasProd_of_isGLB_of_le_one, isGLB_sInf
-/
theorem ENNReal.multipliable_of_le_one {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1) :
    Multipliable f :=
  ⟨_, _root_.hasProd_of_isGLB_of_le_one _ h₀ (isGLB_sInf _)⟩

/--
theorem `ENNReal.hasProd_iInf_prod` / 定理 `ENNReal.hasProd_iInf_prod`

English:
theorem ENNReal.hasProd_iInf_prod
  given: {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1)
  proof: tendsto_atTop_iInf (Finset.prod_anti_set_of_le_one' h₀)

中文:
定理 ENNReal.hasProd_iInf_prod
  条件: {f : α -> 实数>=0∞} (h₀ : 对任意 i, f i <= 1)
  证明: tendsto_atTop_iInf (Finset.prod_anti_set_of_le_one' h₀)

Depends on / 依赖: Finset, Finset.prod_anti_set_of_le_one, prod_anti_set_of_le_one, tendsto_atTop_iInf
-/
theorem ENNReal.hasProd_iInf_prod {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1) :
    HasProd f (⨅ s : Finset α, ∏ i in s, f i) :=
  tendsto_atTop_iInf (Finset.prod_anti_set_of_le_one' h₀)

/--
theorem `ENNReal.tprod_eq_iInf_prod` / 定理 `ENNReal.tprod_eq_iInf_prod`

English:
theorem ENNReal.tprod_eq_iInf_prod
  given: {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1)
  proof: (hasProd_iInf_prod h₀).tprod_eq

中文:
定理 ENNReal.tprod_eq_iInf_prod
  条件: {f : α -> 实数>=0∞} (h₀ : 对任意 i, f i <= 1)
  证明: (hasProd_iInf_prod h₀).tprod_eq

Depends on / 依赖: hasProd_iInf_prod, tprod_eq
-/
theorem ENNReal.tprod_eq_iInf_prod {f : α -> Real>=0∞} (h₀ : forall i, f i <= 1) :
    ∏' i, f i = ⨅ s : Finset α, ∏ i in s, f i :=
  (hasProd_iInf_prod h₀).tprod_eq

end tprod

variable [PseudoEMetricSpace α]

/--
theorem `cauchySeq_of_edist_le_of_summable` / 定理 `cauchySeq_of_edist_le_of_summable`

English:
theorem cauchySeq_of_edist_le_of_summable
  statement: {f : Nat -> α} (d : Nat -> Real>=0)
  proof: by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos => ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence.
  replace hd : CauchySeq fun n : Nat => ∑ x in Finset.range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the def

中文:
定理 cauchySeq_of_edist_le_of_summable
  结论: {f : 自然数 -> α} (d : 自然数 -> 实数>=0)
  证明: by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos => ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence.
  replace hd : CauchySeq fun n : Nat => ∑ x in Finset.range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the def

Depends on / 依赖: EMetric, EMetric.cauchySeq_iff_NNReal, cauchySeq_iff_NNReal
-/
theorem cauchySeq_of_edist_le_of_summable {f : Nat -> α} (d : Nat -> Real>=0)
    (hf : forall n, edist (f n) (f n.succ) <= d n) (hd : Summable d) : CauchySeq f := by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos => ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence.
  replace hd : CauchySeq fun n : Nat => ∑ x in Finset.range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence.
  refine (Metric.cauchySeq_iff'.1 hd ε (NNReal.coe_pos.2 εpos)).imp fun N hN n hn => ?_
  specialize hN n hn
  -- We simplify the known inequality.
  rw [dist_nndist]; rw [NNReal.nndist_eq]; rw [← Finset.sum_range_add_sum_Ico _ hn]; rw [add_tsub_cancel_left]; rw [NNReal.coe_lt_coe]; rw [max_lt_iff] at hN
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form.
  refine lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn fun _ _ => hf _) ?_
  exact mod_cast hN.1

/--
theorem `cauchySeq_of_edist_le_of_tsum_ne_top` / 定理 `cauchySeq_of_edist_le_of_tsum_ne_top`

English:
theorem cauchySeq_of_edist_le_of_tsum_ne_top
  statement: {f : Nat -> α} (d : Nat -> Real>=0∞)
  proof: by
  lift d to Nat -> NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd

中文:
定理 cauchySeq_of_edist_le_of_tsum_ne_top
  结论: {f : 自然数 -> α} (d : 自然数 -> 实数>=0∞)
  证明: by
  lift d to Nat -> NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd

Depends on / 依赖: ENNReal, ENNReal.ne_top_of_tsum_ne_top, ENNReal.tsum_coe_ne_top_iff_summable, NNReal, cauchySeq_of_edist_le_of_summable, ne_top_of_tsum_ne_top, tsum_coe_ne_top_iff_summable
-/
theorem cauchySeq_of_edist_le_of_tsum_ne_top {f : Nat -> α} (d : Nat -> Real>=0∞)
    (hf : forall n, edist (f n) (f n.succ) <= d n) (hd : tsum d != ∞) : CauchySeq f := by
  lift d to Nat -> NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd

/--
theorem `edist_le_tsum_of_edist_le_of_tendsto` / 定理 `edist_le_tsum_of_edist_le_of_tendsto`

English:
theorem edist_le_tsum_of_edist_le_of_tendsto
  statement: {f : Nat -> α} (d : Nat -> Real>=0∞)
  proof: by
  refine le_of_tendsto (tendsto_const_nhds.edist ha) (mem_atTop_sets.2 ⟨n, fun m hnm => ?_⟩)
  change edist _ _ <= _
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm fun _ _ => hf _) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le)

中文:
定理 edist_le_tsum_of_edist_le_of_tendsto
  结论: {f : 自然数 -> α} (d : 自然数 -> 实数>=0∞)
  证明: by
  refine le_of_tendsto (tendsto_const_nhds.edist ha) (mem_atTop_sets.2 ⟨n, fun m hnm => ?_⟩)
  change edist _ _ <= _
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm fun _ _ => hf _) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le)

Depends on / 依赖: ENNReal, ENNReal.summable.sum_le_tsum, Finset, Finset.sum_Ico_eq_sum_range, edist_le_Ico_sum_of_edist_le, le_of_tendsto, le_trans, mem_atTop_sets, sum_Ico_eq_sum_range, sum_le_tsum, summable, tendsto_const_nhds, tendsto_const_nhds.edist, zero_le
-/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : Nat -> α} (d : Nat -> Real>=0∞)
    (hf : forall n, edist (f n) (f n.succ) <= d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) :
    edist (f n) a <= ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.edist ha) (mem_atTop_sets.2 ⟨n, fun m hnm => ?_⟩)
  change edist _ _ <= _
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm fun _ _ => hf _) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le)

/--
theorem `edist_le_tsum_of_edist_le_of_tendsto₀` / 定理 `edist_le_tsum_of_edist_le_of_tendsto₀`

English:
theorem edist_le_tsum_of_edist_le_of_tendsto₀
  statement: {f : Nat -> α} (d : Nat -> Real>=0∞)
  proof: by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0

中文:
定理 edist_le_tsum_of_edist_le_of_tendsto₀
  结论: {f : 自然数 -> α} (d : 自然数 -> 实数>=0∞)
  证明: by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0

Depends on / 依赖: edist_le_tsum_of_edist_le_of_tendsto
-/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : Nat -> α} (d : Nat -> Real>=0∞)
    (hf : forall n, edist (f n) (f n.succ) <= d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a <= ∑' m, d m := by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0


namespace ENNReal

variable {α : Type*} (s : Set α)

/--
lemma `tsum_set_one` / 引理 `tsum_set_one`

English:
lemma tsum_set_one
  statement: ∑' _ : s, (1 : Real>=0∞) = s.encard
  proof: by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero]; rw [encard_eq_top hinf]; rw [ENat.toENNReal_top]

中文:
引理 tsum_set_one
  结论: ∑' _ : s, (1 : 实数>=0∞) = s.encard
  证明: by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero]; rw [encard_eq_top hinf]; rw [ENat.toENNReal_top]

Depends on / 依赖: ENat.toENNReal_top, Finset, Infinite, Set.finite_or_infinite, encard_eq_top, finite_or_infinite, infinite_coe_iff, infinite_coe_iff.mpr, one_ne_zero, toENNReal_top, tsum_const_eq_top_of_ne_zero, tsum_fintype
-/
lemma tsum_set_one : ∑' _ : s, (1 : Real>=0∞) = s.encard := by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero]; rw [encard_eq_top hinf]; rw [ENat.toENNReal_top]

/--
lemma `tsum_set_const` / 引理 `tsum_set_const`

English:
lemma tsum_set_const
  given: (c : Real>=0∞)
  statement: ∑' _ : s, c = s.encard * c
  proof: by
  simp [← tsum_set_one, ← ENNReal.tsum_mul_right]

@[simp]

中文:
引理 tsum_set_const
  条件: (c : 实数>=0∞)
  结论: ∑' _ : s, c = s.encard * c
  证明: by
  simp [← tsum_set_one, ← ENNReal.tsum_mul_right]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_mul_right, tsum_mul_right, tsum_set_one
-/
lemma tsum_set_const (c : Real>=0∞) : ∑' _ : s, c = s.encard * c := by
  simp [← tsum_set_one, ← ENNReal.tsum_mul_right]

@[simp]
/--
lemma `tsum_one` / 引理 `tsum_one`

English:
lemma tsum_one
  statement: ∑' _ : α, (1 : Real>=0∞) = ENat.card α
  proof: by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_one univ

@[simp]

中文:
引理 tsum_one
  结论: ∑' _ : α, (1 : 实数>=0∞) = E自然数.card α
  证明: by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_one univ

@[simp]

Depends on / 依赖: encard_univ, tsum_set_one, tsum_univ
-/
lemma tsum_one : ∑' _ : α, (1 : Real>=0∞) = ENat.card α := by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_one univ

@[simp]
/--
lemma `tsum_const` / 引理 `tsum_const`

English:
lemma tsum_const
  given: (c : Real>=0∞)
  statement: ∑' _ : α, c = ENat.card α * c
  proof: by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_const univ c

中文:
引理 tsum_const
  条件: (c : 实数>=0∞)
  结论: ∑' _ : α, c = E自然数.card α * c
  证明: by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_const univ c

Depends on / 依赖: encard_univ, tsum_set_const, tsum_univ
-/
lemma tsum_const (c : Real>=0∞) : ∑' _ : α, c = ENat.card α * c := by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_const univ c

end ENNReal
