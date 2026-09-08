/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (ediam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Carathéodory's theorem
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, ediam (t n) ≤ r), ∑' n, ediam (t n) ^ d
```

For every set `s` and any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`MeasureTheory.Measure.hausdorffMeasure_zero_or_top`. In
`Mathlib/Topology/MetricSpace/HausdorffDimension.lean` we use this fact to define the Hausdorff
dimension `dimH` of a set in an (extended) metric space.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`MeasureTheory.Measure.mkMetric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `MeasureTheory.Measure.mkMetric'`) we use any function
of `m : Set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : Set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `MeasureTheory.extend m`.

We also define a predicate `MeasureTheory.OuterMeasure.IsMetric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for Carathéodory's theorem
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mkMetric'` are metric outer
measures.

## Main definitions

* `MeasureTheory.OuterMeasure.IsMetric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Carathéodory condition, see
  `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`.
* `MeasureTheory.OuterMeasure.mkMetric'` and its particular case
  `MeasureTheory.OuterMeasure.mkMetric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `MeasureTheory.Measure.mkMetric'` and
  `MeasureTheory.Measure.mkMetric`.
* `MeasureTheory.Measure.hausdorffMeasure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, ediam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬Set.Subsingleton (t n)), (ediam (t n)) ^ d`,
  see `MeasureTheory.Measure.hausdorffMeasure_apply`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬Set.Subsingleton (t n))` part.

## Main statements

### Basic properties

* `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Carathéodory measurable (hence, `μ` defines an actual
  `MeasureTheory.Measure`). See also `MeasureTheory.Measure.mkMetric`.
* `MeasureTheory.Measure.hausdorffMeasure_mono`: `μH[d] s` is an antitone function
  of `d`.
* `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `MeasureTheory.Measure.nullSingletonClass_hausdorff`: Hausdorff measure has value zero on
  singletons.

### Hausdorff measure in `ℝⁿ`

* `MeasureTheory.hausdorffMeasure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.

## Notation

We use the following notation localized in `MeasureTheory`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, measure, metric measure
-/

@[expose] public section


open scoped NNReal ENNReal Topology

open Metric EMetric Set Function Filter Encodable Module TopologicalSpace

noncomputable section

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

namespace MeasureTheory

namespace OuterMeasure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Carathéodory's theorem: a metric outer
measure has the Carathéodory property.
-/


/-- We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t) = μ s + μ t`
for any two metric separated sets `s`, `t`. -/
/-
**MeasureTheory.OuterMeasure.IsMetric** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：IsMetric (μ : OuterMeasure X) : Prop
参数：μ : OuterMeasure X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t)
 = μ s + μ t`
for any two metric separated sets `s`, `t`.
-/
def IsMetric (μ : OuterMeasure X) : Prop :=
  ∀ s t : Set X, Metric.AreSeparated s t → μ (s ∪ t) = μ s + μ t

namespace IsMetric

variable {μ : OuterMeasure X}

/-- A metric outer measure is additive on a finite set of pairwise metric separated sets. -/
/-
**MeasureTheory.OuterMeasure.IsMetric.finset_iUnion_of_pairwise_separated** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.OuterMeasure.IsMetric`。
形式化陈述：finset_iUnion_of_pairwise_separated (hm : IsMetric μ) {I : Finset ι} {s : 
ι -> Set X} (hI : forall i in I, forall j in I, i != j -> Metric.AreSeparated (s
 i) (s j)) : μ (⋃ i in I, s i) = ∑ i in I, μ (s i)
参数：hm : IsMetric μ；hI : forall i in I, forall j in I, i != j -> Metric.AreSepara
ted (s i) (s j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.set_biUnion_insert`：set_biUnion_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `Metric.AreSeparated.finset_iUnion_right`：∀ {X : Type u_1} [inst : Pseudo
EMetricSpace X] {ι : Type u_3} {I : Finset ι} {s : Set X} {t : ι → Set X},   (∀ 
i ∈ I, Metric.AreSeparated s …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…

--- 原说明 ---
A metric outer measure is additive on a finite set of pairwise metric separated 
sets.
-/
theorem finset_iUnion_of_pairwise_separated (hm : IsMetric μ) {I : Finset ι} {s : ι → Set X}
    (hI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Metric.AreSeparated (s i) (s j)) :
    μ (⋃ i ∈ I, s i) = ∑ i ∈ I, μ (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hiI ihI =>
    simp only [Finset.mem_insert] at hI
    rw [Finset.set_biUnion_insert, hm, ihI, Finset.sum_insert hiI]
    exacts [fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
      Metric.AreSeparated.finset_iUnion_right fun j hj =>
        hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

/-- **Carathéodory's theorem**. If `m` is a metric outer measure, then every Borel measurable set
`t` is Carathéodory measurable: for any (not necessarily measurable) set `s` we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
/-
**MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.OuterMeasure.IsMetric`。
形式化陈述：borel_le_caratheodory (hm : IsMetric μ) : borel X <= μ.caratheodory
参数：hm : IsMetric μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `borel_eq_generateFrom_isClosed`：borel_eq_generateFrom_isClosed [Topologi
calSpace α] : borel α = .generateFrom { s | IsClosed s }
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff_le`：isCaratheodory_iff_le 
{s : Set α} : MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m (t inte
r s) + m (t \ s) <= m t
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y
· 使用定理 `Metric.AreSeparated.mono`：mono {s' t'} (hs : s subseteq s') (ht : t subs
eteq t') : AreSeparated s' t' -> AreSeparated s t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Metric.AreSeparated.subset_compl_right`：subset_compl_right (h : AreSepar
ated s t) : s subseteq tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.AreSeparated.symm`：symm (h : AreSeparated s t) : AreSeparated t s
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `ENNReal.exists_inv_nat_lt`：exists_inv_nat_lt {a : Real>=0∞} (h : a != 0)
 : exists n : Nat, (n : Real>=0∞)⁻¹ < a
· 使用定理 `Metric.mem_iff_infEDist_zero_of_closed`：mem_iff_infEDist_zero_of_closed 
(h : IsClosed s) : x in s ↔ infEDist x s = 0
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
**Carathéodory's theorem**. If `m` is a metric outer measure, then every Borel m
easurable set
`t` is Carathéodory measurable: for any (not necessarily measurable) set `s` we 
have
`μ (s ∩ t) + μ (s \ t) = μ s`.
-/
theorem borel_le_caratheodory (hm : IsMetric μ) : borel X ≤ μ.caratheodory := by
  rw [borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun t ht => μ.isCaratheodory_iff_le.2 fun s => ?_
  set S : ℕ → Set X := fun n => {x ∈ s | (↑n)⁻¹ ≤ infEDist x t}
  have Ssep (n) : Metric.AreSeparated (S n) t :=
    ⟨n⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _),
      fun x hx y hy ↦ hx.2.trans <| infEDist_le_edist_of_mem hy⟩
  have Ssep' : ∀ n, Metric.AreSeparated (S n) (s ∩ t) := fun n =>
    (Ssep n).mono Subset.rfl inter_subset_right
  have S_sub : ∀ n, S n ⊆ s \ t := fun n =>
    subset_inter inter_subset_left (Ssep n).subset_compl_right
  have hSs : ∀ n, μ (s ∩ t) + μ (S n) ≤ μ s := fun n =>
    calc
      μ (s ∩ t) + μ (S n) = μ (s ∩ t ∪ S n) := Eq.symm <| hm _ _ <| (Ssep' n).symm
      _ ≤ μ (s ∩ t ∪ s \ t) := μ.mono <| union_subset_union_right _ <| S_sub n
      _ = μ s := by rw [inter_union_sdiff]
  have iUnion_S : ⋃ n, S n = s \ t := by
    refine Subset.antisymm (iUnion_subset S_sub) ?_
    rintro x ⟨hxs, hxt⟩
    rw [mem_iff_infEDist_zero_of_closed ht] at hxt
    rcases ENNReal.exists_inv_nat_lt hxt with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hxs, hn.le⟩
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
    `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
    `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞
  · rw [htop, add_top, ← htop]
    exact μ.mono sdiff_subset
  suffices μ (⋃ n, S n) ≤ ⨆ n, μ (S n) by calc
    μ (s ∩ t) + μ (s \ t) = μ (s ∩ t) + μ (⋃ n, S n) := by rw [iUnion_S]
    _ ≤ μ (s ∩ t) + ⨆ n, μ (S n) := by gcongr
    _ = ⨆ n, μ (s ∩ t) + μ (S n) := ENNReal.add_iSup ..
    _ ≤ μ s := iSup_le hSs
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
    then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
    and the second term tends to zero, see `OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top`
    for details. -/
  have : ∀ n, S n ⊆ S (n + 1) := fun n x hx =>
    ⟨hx.1, le_trans (ENNReal.inv_le_inv.2 <| Nat.cast_le.2 n.le_succ) hx.2⟩
  refine (μ.iUnion_nat_of_monotone_of_tsum_ne_top this ?_).le; clear this
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
    subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
    so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable, ENNReal.add_ne_top]
  suffices ∀ a, (∑' k : ℕ, μ (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞ from
    ⟨by simpa using this 0, by simpa using this 1⟩
  refine fun r => ne_top_of_le_ne_top htop ?_
  rw [← iUnion_S, ENNReal.tsum_eq_iSup_nat, iSup_le_iff]
  intro n
  rw [← hm.finset_iUnion_of_pairwise_separated]
  · exact μ.mono (iUnion_subset fun i => iUnion_subset fun _ x hx => mem_iUnion.2 ⟨_, hx.1⟩)
  suffices ∀ i j, i < j → Metric.AreSeparated (S (2 * i + 1 + r)) (s \ S (2 * j + r)) from
    fun i _ j _ hij => hij.lt_or_gt.elim
      (fun h => (this i j h).mono inter_subset_left fun x hx => by exact ⟨hx.1.1, hx.2⟩)
      fun h => (this j i h).symm.mono (fun x hx => by exact ⟨hx.1.1, hx.2⟩) inter_subset_left
  intro i j hj
  have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹ := by
    rw [ENNReal.inv_lt_inv, Nat.cast_lt]; lia
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa [tsub_eq_zero_iff_le] using A,
    fun x hx y hy => ?_⟩
  have : infEDist y t < (↑(2 * j + r))⁻¹ := not_le.1 fun hle => hy.2 ⟨hy.1, hle⟩
  rcases infEDist_lt_iff.mp this with ⟨z, hzt, hyz⟩
  have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z := le_infEDist.1 hx.2 _ hzt
  apply ENNReal.le_of_add_le_add_right hyz.ne_top
  refine le_trans ?_ (edist_triangle _ _ _)
  refine (add_le_add le_rfl hyz.le).trans (Eq.trans_le ?_ hxz)
  rw [tsub_add_cancel_of_le A.le]
/-
**MeasureTheory.OuterMeasure.IsMetric.le_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.OuterMeasure.IsMetric`。
形式化陈述：le_caratheodory [MeasurableSpace X] [BorelSpace X] (hm : IsMetric μ) : ‹Me
asurableSpace X› <= μ.caratheodory
参数：hm : IsMetric μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`：borel_le_cara
theodory (hm : IsMetric μ) : borel X <= μ.caratheodory
-/
theorem le_caratheodory [MeasurableSpace X] [BorelSpace X] (hm : IsMetric μ) :
    ‹MeasurableSpace X› ≤ μ.caratheodory := by
  rw [BorelSpace.measurable_eq (α := X)]
  exact hm.borel_le_caratheodory

end IsMetric

/-!
### Constructors of metric outer measures

In this section we provide constructors `MeasureTheory.OuterMeasure.mkMetric'` and
`MeasureTheory.OuterMeasure.mkMetric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/


/-- Auxiliary definition for `OuterMeasure.mkMetric'`: given a function on sets
`m : Set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diameter at most `r`. -/
/-
**MeasureTheory.OuterMeasure.mkMetric'.pre** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.OuterMeasure.mkMetric'`。
形式化陈述：{X : Type u_2} → [EMetricSpace X] → (Set X → ENNReal) → ENNReal → MeasureT
heory.OuterMeasure X
参数：Set X → ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `OuterMeasure.mkMetric'`: given a function on sets
`m : Set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diameter at most `r`.
-/
def mkMetric'.pre (m : Set X → ℝ≥0∞) (r : ℝ≥0∞) : OuterMeasure X :=
  boundedBy <| extend fun s (_ : ediam s ≤ r) => m s

/-- Given a function `m : Set X → ℝ≥0∞`, `mkMetric' m` is the supremum of `mkMetric'.pre m r`
over `r > 0`. Equivalently, it is the limit of `mkMetric'.pre m r` as `r` tends to zero from
the right. -/
/-
**MeasureTheory.OuterMeasure.mkMetric'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：mkMetric'.pre (m : Set X -> Real>=0∞) (r : Real>=0∞) : OuterMeasure X
参数：m : Set X -> Real>=0∞；r : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `m : Set X → ℝ≥0∞`, `mkMetric' m` is the supremum of `mkMetric'
.pre m r`
over `r > 0`. Equivalently, it is the limit of `mkMetric'.pre m r` as `r` tends 
to zero from
the right.
-/
def mkMetric' (m : Set X → ℝ≥0∞) : OuterMeasure X :=
  ⨆ r > 0, mkMetric'.pre m r

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞` and `r > 0`, let `μ r` be the maximal outer measure such that
`μ s ≤ m (ediam s)` whenever `ediam s < r`. Then `mkMetric m = ⨆ r > 0, μ r`. -/
/-
**MeasureTheory.OuterMeasure.mkMetric** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：mkMetric (m : Real>=0∞ -> Real>=0∞) : OuterMeasure X
参数：m : Real>=0∞ -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `m : ℝ≥0∞ → ℝ≥0∞` and `r > 0`, let `μ r` be the maximal outer m
easure such that
`μ s ≤ m (ediam s)` whenever `ediam s < r`. Then `mkMetric m = ⨆ r > 0, μ r`.
-/
def mkMetric (m : ℝ≥0∞ → ℝ≥0∞) : OuterMeasure X :=
  mkMetric' fun s => m (ediam s)

namespace mkMetric'

variable {m : Set X → ℝ≥0∞} {r : ℝ≥0∞} {μ : OuterMeasure X} {s : Set X}

/-
**MeasureTheory.OuterMeasure.mkMetric.le_pre** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_pre : μ ≤ pre m r ↔ ∀ s : Set X, ediam s ≤ r → μ s ≤ m s := by
  simp only [pre, le_boundedBy, extend, le_iInf_iff]
/-
**MeasureTheory.OuterMeasure.mkMetric.pre_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pre_le (hs : ediam s ≤ r) : pre m r s ≤ m s :=
  (boundedBy_le _).trans <| iInf_le _ hs
/-
**MeasureTheory.OuterMeasure.mkMetric.mono_pre** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_pre (m : Set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') : pre m r' ≤ pre m r :=
  le_pre.2 fun _ hs => pre_le (hs.trans h)
/-
**MeasureTheory.OuterMeasure.mkMetric.mono_pre_nat** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_pre_nat (m : Set X → ℝ≥0∞) : Monotone fun k : ℕ => pre m k⁻¹ :=
  fun k l h => le_pre.2 fun _ hs => pre_le (hs.trans <| by simpa)
/-
**MeasureTheory.OuterMeasure.mkMetric.tendsto_pre** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_pre (m : Set X → ℝ≥0∞) (s : Set X) :
    Tendsto (fun r => pre m r s) (𝓝[>] 0) (𝓝 <| mkMetric' m s) := by
  rw [← tendsto_comp_coe_Ioi_atBot]
  simp only [mkMetric', OuterMeasure.iSup_apply, iSup_subtype']
  exact tendsto_atBot_iSup fun r r' hr => mono_pre _ hr _
/-
**MeasureTheory.OuterMeasure.mkMetric.tendsto_pre_nat** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_pre_nat (m : Set X → ℝ≥0∞) (s : Set X) :
    Tendsto (fun n : ℕ => pre m n⁻¹ s) atTop (𝓝 <| mkMetric' m s) := by
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ENNReal.tendsto_inv_nat_nhds_zero, ?_⟩)
  refine tendsto_principal.2 (Eventually.of_forall fun n => ?_)
  simp
/-
**MeasureTheory.OuterMeasure.mkMetric.eq_iSup_nat** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_iSup_nat (m : Set X → ℝ≥0∞) : mkMetric' m = ⨆ n : ℕ, mkMetric'.pre m n⁻¹ := by
  ext1 s
  rw [iSup_apply]
  refine tendsto_nhds_unique (mkMetric'.tendsto_pre_nat m s)
    (tendsto_atTop_iSup fun k l hkl => mkMetric'.mono_pre_nat m hkl s)

/-- `MeasureTheory.OuterMeasure.mkMetric'.pre m r` is a trimmed measure provided that
`m (closure s) = m s` for any set `s`. -/
/-
**MeasureTheory.OuterMeasure.mkMetric.trim_pre** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.OuterMeasure.mkMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MeasureTheory.OuterMeasure.mkMetric'.pre m r` is a trimmed measure provided tha
t
`m (closure s) = m s` for any set `s`.
-/
theorem trim_pre [MeasurableSpace X] [OpensMeasurableSpace X] (m : Set X → ℝ≥0∞)
    (hcl : ∀ s, m (closure s) = m s) (r : ℝ≥0∞) : (pre m r).trim = pre m r := by
  refine le_antisymm (le_pre.2 fun s hs => ?_) (le_trim _)
  rw [trim_eq_iInf]
  refine iInf_le_of_le (closure s) <| iInf_le_of_le subset_closure <|
    iInf_le_of_le measurableSet_closure ((pre_le ?_).trans_eq (hcl _))
  rwa [ediam_closure]

end mkMetric'

/-- An outer measure constructed using `OuterMeasure.mkMetric'` is a metric outer measure. -/
/-
**MeasureTheory.OuterMeasure.mkMetric'_isMetric** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：∀ {X : Type u_2} [inst : EMetricSpace X] (m : Set X → ENNReal), (MeasureTh
eory.OuterMeasure.mkMetric' m).IsMetric
参数：m : Set X → ENNReal；MeasureTheory.OuterMeasure.mkMetric' m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric'.tendsto_pre`：tendsto_pre (m : Set X
 -> Real>=0∞) (s : Set X) : Tendsto (fun r => pre m r s) (𝓝[>] 0) (𝓝 <| mkMetric
' m s)
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_union_of_top_of_nonempty_inter`：bou
ndedBy_union_of_top_of_nonempty_inter {s t : Set α} (h : forall u, (s inter u).N
onempty -> (t inter u).Nonempty -> m u = ∞) : boundedBy m…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_eq_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{s : ι → α}, iInf s = ⊤ ↔ ∀ (i : ι), s i = ⊤
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a

--- 原说明 ---
An outer measure constructed using `OuterMeasure.mkMetric'` is a metric outer me
asure.
-/
theorem mkMetric'_isMetric (m : Set X → ℝ≥0∞) : (mkMetric' m).IsMetric := by
  rintro s t ⟨r, r0, hr⟩
  refine tendsto_nhds_unique_of_eventuallyEq
    (mkMetric'.tendsto_pre _ _) ((mkMetric'.tendsto_pre _ _).add (mkMetric'.tendsto_pre _ _)) ?_
  rw [← pos_iff_ne_zero] at r0
  filter_upwards [Ioo_mem_nhdsGT r0]
  rintro ε ⟨_, εr⟩
  refine boundedBy_union_of_top_of_nonempty_inter ?_
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩
  have : ε < ediam u := εr.trans_le ((hr x hxs y hyt).trans <| edist_le_ediam_of_mem hxu hyu)
  exact iInf_eq_top.2 fun h => (this.not_ge h).elim

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mkMetric m₁ hm₁ ≤ c • mkMetric m₂ hm₂`. -/
/-
**MeasureTheory.OuterMeasure.mkMetric_mono_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：mkMetric_mono_smul {m₁ m₂ : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c !
= ∞) (h0 : c != 0) (hle : m₁ <=ᶠ[𝓝[>=] 0] c • m₂) : (mkMetric m₁ : OuterMeasure 
X) <= c • mkMetric m₂
参数：hc : c != ∞；h0 : c != 0；hle : m₁ <=ᶠ[𝓝[>=] 0] c • m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsGE_iff_exists_Ico_subset'`：mem_nhdsGE_iff_exists_Ico_subset' {a 
u' : α} {s : Set α} (hu' : a < u') : s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u s
ubseteq s
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric'.tendsto_pre`：tendsto_pre (m : Set X
 -> Real>=0∞) (s : Set X) : Tendsto (fun r => pre m r s) (𝓝[>] 0) (𝓝 <| mkMetric
' m s)
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
· 使用定理 `MeasureTheory.OuterMeasure.smul_boundedBy`：smul_boundedBy {c : Real>=0∞}
 (hc : c != ∞) : c • boundedBy m = boundedBy (c • m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.le_boundedBy`：le_boundedBy {μ : OuterMeasure 
α} : μ <= boundedBy m ↔ forall s, μ s <= m s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_le`：boundedBy_le (s : Set α) : boun
dedBy m s <= m s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mkMetric m₁ hm₁ ≤ c • mkMetric m₂ hm₂
`.
-/
theorem mkMetric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
    (hle : m₁ ≤ᶠ[𝓝[≥] 0] c • m₂) : (mkMetric m₁ : OuterMeasure X) ≤ c • mkMetric m₂ := by
  rcases (mem_nhdsGE_iff_exists_Ico_subset' zero_lt_one).1 hle with ⟨r, hr0, hr⟩
  refine fun s =>
    le_of_tendsto_of_tendsto (mkMetric'.tendsto_pre _ s)
      (ENNReal.Tendsto.const_mul (mkMetric'.tendsto_pre _ s) (Or.inr hc))
      (mem_of_superset (Ioo_mem_nhdsGT hr0) fun r' hr' => ?_)
  simp only [mem_ofPred_eq, mkMetric'.pre]
  rw [← smul_eq_mul, ← smul_apply, smul_boundedBy hc]
  refine le_boundedBy.2 (fun t => (boundedBy_le _).trans ?_) _
  simp only [smul_eq_mul, Pi.smul_apply, extend, iInf_eq_if]
  split_ifs with ht
  · exact hr ⟨zero_le, ht.trans_lt hr'.2⟩
  · simp [h0]

@[simp]
/-
**MeasureTheory.OuterMeasure.mkMetric_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：mkMetric_top : (mkMetric (fun _ => ∞ : Real>=0∞ -> Real>=0∞) : OuterMeasur
e X) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.extend_top`：extend_top {α : Type*} {P : α -> Prop} : exten
d (fun _ _ => ∞ : forall s : α, P s -> Real>=0∞) = ⊤
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_top`：boundedBy_top : boundedBy (⊤ :
 Set α -> Real>=0∞) = ⊤
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem mkMetric_top : (mkMetric (fun _ => ∞ : ℝ≥0∞ → ℝ≥0∞) : OuterMeasure X) = ⊤ := by
  simp_rw [mkMetric, mkMetric', mkMetric'.pre, extend_top, boundedBy_top, eq_top_iff]
  rw [le_iSup_iff]
  intro b hb
  simpa using hb ⊤

/-- If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝 0]` to state this), then
`mkMetric m₁ hm₁ ≤ mkMetric m₂ hm₂`. -/
/-
**MeasureTheory.OuterMeasure.mkMetric_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：mkMetric_mono {m₁ m₂ : Real>=0∞ -> Real>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂) : (mkM
etric m₁ : OuterMeasure X) <= mkMetric m₂
参数：hle : m₁ <=ᶠ[𝓝 0] m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric_mono_smul`：mkMetric_mono_smul {m₁ m₂
 : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0) (hle : m₁ <=
ᶠ[𝓝[>=] 0] c • m₂) : (mkMetric m₁ :…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ici_zero_eq_univ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Zer
o α] [IsBotZeroClass α], Set.Ici 0 = Set.univ
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝 0]` to state this), 
then
`mkMetric m₁ hm₁ ≤ mkMetric m₂ hm₂`.
-/
theorem mkMetric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝 0] m₂) :
    (mkMetric m₁ : OuterMeasure X) ≤ mkMetric m₂ := by
  convert! @mkMetric_mono_smul X _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]
/-
**MeasureTheory.OuterMeasure.isometry_comap_mkMetric** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.OuterMeasure`。
形式化陈述：isometry_comap_mkMetric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isom
etry f) (H : Monotone m ∨ Surjective f) : comap f (mkMetric m) = mkMetric m
参数：m : Real>=0∞ -> Real>=0∞；hf : Isometry f；H : Monotone m ∨ Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.OuterMeasure.comap_iSup`：comap_iSup {β ι} (f : α -> β) (m 
: ι -> OuterMeasure β) : comap f (⨆ i, m i) = ⨆ i, comap f (m i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `MeasureTheory.OuterMeasure.comap_boundedBy`：comap_boundedBy {β} (f : β -
> α) (h : (Monotone fun s : { s : Set α // s.Nonempty } => m s) ∨ Surjective f) 
: comap f (boundedBy m) = bounde…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `ciInf_pos`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderInf
 α] {p : Prop} {f : p → α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `MeasureTheory.extend_congr`：extend_congr {β : Type*} {Pb : β -> Prop} {m
b : forall s : β, Pb s -> Real>=0∞} {sa : α} {sb : β} (hP : P sa ↔ Pb sb) (hm : 
forall (ha : P s…
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isometry_comap_mkMetric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : Isometry f)
    (H : Monotone m ∨ Surjective f) : comap f (mkMetric m) = mkMetric m := by
  simp only [mkMetric, mkMetric', mkMetric'.pre, comap_iSup]
  refine surjective_id.iSup_congr id fun ε => surjective_id.iSup_congr id fun hε => ?_
  rw [comap_boundedBy _ (H.imp _ id)]
  · congr with s : 1
    apply extend_congr <;> simp [hf.ediam_image]
  · intro h_mono s t hst
    simp only [extend, le_iInf_iff]
    intro ht
    apply le_trans _ (h_mono (ediam_mono hst))
    simp only [(ediam_mono hst).trans ht, le_refl, ciInf_pos]
/-
**MeasureTheory.OuterMeasure.mkMetric_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：mkMetric_smul (m : Real>=0∞ -> Real>=0∞) {c : Real>=0∞} (hc : c != ∞) (hc'
 : c != 0) : (mkMetric (c • m) : OuterMeasure X) = c • mkMetric m
参数：m : Real>=0∞ -> Real>=0∞；hc : c != ∞；hc' : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.OuterMeasure.smul_iSup`：smul_iSup {R : Type*} [SMul R Real
>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] {ι : Sort*} (f : ι -> OuterMeasure α) 
(c : R) : (c • ⨆ i, f i) =…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.OuterMeasure.smul_boundedBy`：smul_boundedBy {c : Real>=0∞}
 (hc : c != ∞) : c • boundedBy m = boundedBy (c • m)
· 使用引理 `MeasureTheory.ennreal_smul_extend`：ennreal_smul_extend {c : Real>=0∞} (h
c : c != 0) : c • extend m = extend fun s h => c • m s h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkMetric_smul (m : ℝ≥0∞ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) (hc' : c ≠ 0) :
    (mkMetric (c • m) : OuterMeasure X) = c • mkMetric m := by
  simp only [mkMetric, mkMetric', mkMetric'.pre]
  simp_rw [smul_iSup, smul_boundedBy hc, ennreal_smul_extend _ hc', Pi.smul_apply]
/-
**MeasureTheory.OuterMeasure.mkMetric_nnreal_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：mkMetric_nnreal_smul (m : Real>=0∞ -> Real>=0∞) {c : Real>=0} (hc : c != 0
) : (mkMetric (c • m) : OuterMeasure X) = c • mkMetric m
参数：m : Real>=0∞ -> Real>=0∞；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric_smul`：mkMetric_smul (m : Real>=0∞ ->
 Real>=0∞) {c : Real>=0∞} (hc : c != ∞) (hc' : c != 0) : (mkMetric (c • m) : Out
erMeasure X) = c • mkMetric m
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
-/
theorem mkMetric_nnreal_smul (m : ℝ≥0∞ → ℝ≥0∞) {c : ℝ≥0} (hc : c ≠ 0) :
    (mkMetric (c • m) : OuterMeasure X) = c • mkMetric m := by
  rw [ENNReal.smul_def, ENNReal.smul_def,
    mkMetric_smul m ENNReal.coe_ne_top (ENNReal.coe_ne_zero.mpr hc)]
/-
**MeasureTheory.OuterMeasure.isometry_map_mkMetric** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：isometry_map_mkMetric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isomet
ry f) (H : Monotone m ∨ Surjective f) : map f (mkMetric m) = restrict (range f) 
(mkMetric m)
参数：m : Real>=0∞ -> Real>=0∞；hf : Isometry f；H : Monotone m ∨ Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.isometry_comap_mkMetric`：isometry_comap_mkMet
ric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f) (H : Monotone m ∨ 
Surjective f) : comap f (mkMetric m) = m…
· 使用定理 `MeasureTheory.OuterMeasure.map_comap`：map_comap {β} (f : α -> β) (m : Ou
terMeasure β) : map f (comap f m) = restrict (range f) m
-/
theorem isometry_map_mkMetric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : Isometry f)
    (H : Monotone m ∨ Surjective f) : map f (mkMetric m) = restrict (range f) (mkMetric m) := by
  rw [← isometry_comap_mkMetric _ hf H, map_comap]
/-
**MeasureTheory.OuterMeasure.isometryEquiv_comap_mkMetric** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：isometryEquiv_comap_mkMetric (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y) : com
ap f (mkMetric m) = mkMetric m
参数：m : Real>=0∞ -> Real>=0∞；f : X ≃ᵢ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.isometry_comap_mkMetric`：isometry_comap_mkMet
ric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f) (H : Monotone m ∨ 
Surjective f) : comap f (mkMetric m) = m…
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.surjective`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β),   Function.Surjective 
⇑h
-/
theorem isometryEquiv_comap_mkMetric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
    comap f (mkMetric m) = mkMetric m :=
  isometry_comap_mkMetric _ f.isometry (Or.inr f.surjective)
/-
**MeasureTheory.OuterMeasure.isometryEquiv_map_mkMetric** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.OuterMeasure`。
形式化陈述：isometryEquiv_map_mkMetric (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y) : map f
 (mkMetric m) = mkMetric m
参数：m : Real>=0∞ -> Real>=0∞；f : X ≃ᵢ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.isometryEquiv_comap_mkMetric`：isometryEquiv_c
omap_mkMetric (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y) : comap f (mkMetric m) = m
kMetric m
· 使用定理 `MeasureTheory.OuterMeasure.map_comap_of_surjective`：map_comap_of_surject
ive {β} {f : α -> β} (hf : Surjective f) (m : OuterMeasure β) : map f (comap f m
) = m
· 使用定理 `IsometryEquiv.surjective`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β),   Function.Surjective 
⇑h
-/
theorem isometryEquiv_map_mkMetric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
    map f (mkMetric m) = mkMetric m := by
  rw [← isometryEquiv_comap_mkMetric _ f, map_comap_of_surjective f.surjective]
/-
**MeasureTheory.OuterMeasure.trim_mkMetric** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：trim_mkMetric [MeasurableSpace X] [BorelSpace X] (m : Real>=0∞ -> Real>=0∞
) : (mkMetric m : OuterMeasure X).trim = mkMetric m
参数：m : Real>=0∞ -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric'.eq_iSup_nat`：eq_iSup_nat (m : Set X
 -> Real>=0∞) : mkMetric' m = ⨆ n : Nat, mkMetric'.pre m n⁻¹
· 使用定理 `MeasureTheory.OuterMeasure.trim_iSup`：trim_iSup {ι} [Countable ι] (μ : ι
 -> OuterMeasure α) : trim (⨆ i, μ i) = ⨆ i, trim (μ i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric'.trim_pre`：trim_pre [MeasurableSpace
 X] [OpensMeasurableSpace X] (m : Set X -> Real>=0∞) (hcl : forall s, m (closure
 s) = m s) (r : Real>=0∞) : (pre m …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.ediam_closure`：Metric.ediam_closure (s : Set α) : ediam (closure 
s) = ediam s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trim_mkMetric [MeasurableSpace X] [BorelSpace X] (m : ℝ≥0∞ → ℝ≥0∞) :
    (mkMetric m : OuterMeasure X).trim = mkMetric m := by
  simp only [mkMetric, mkMetric'.eq_iSup_nat, trim_iSup]
  congr 1 with n : 1
  refine mkMetric'.trim_pre _ (fun s => ?_) _
  simp
/-
**MeasureTheory.OuterMeasure.le_mkMetric** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：le_mkMetric (m : Real>=0∞ -> Real>=0∞) (μ : OuterMeasure X) (r : Real>=0∞)
 (h0 : 0 < r) (hr : forall s, ediam s <= r -> μ s <= m (ediam s)) : μ <= mkMetri
c m
参数：m : Real>=0∞ -> Real>=0∞；μ : OuterMeasure X；r : Real>=0∞；h0 : 0 < r；hr : fora
ll s, ediam s <= r -> μ s <= m (ediam s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric'.le_pre`：le_pre : μ <= pre m r ↔ for
all s : Set X, ediam s <= r -> μ s <= m s
-/
theorem le_mkMetric (m : ℝ≥0∞ → ℝ≥0∞) (μ : OuterMeasure X) (r : ℝ≥0∞) (h0 : 0 < r)
    (hr : ∀ s, ediam s ≤ r → μ s ≤ m (ediam s)) : μ ≤ mkMetric m :=
  le_iSup₂_of_le r h0 <| mkMetric'.le_pre.2 fun _ hs => hr _ hs

end OuterMeasure

/-!
### Metric measures

In this section we use `MeasureTheory.OuterMeasure.toMeasure` and theorems about
`MeasureTheory.OuterMeasure.mkMetric'`/`MeasureTheory.OuterMeasure.mkMetric` to define
`MeasureTheory.Measure.mkMetric'`/`MeasureTheory.Measure.mkMetric`. We also restate some lemmas
about metric outer measures for metric measures.
-/


namespace Measure

variable [MeasurableSpace X] [BorelSpace X]

/-- Given a function `m : Set X → ℝ≥0∞`, `mkMetric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure. -/
/-
**MeasureTheory.Measure.mkMetric'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：mkMetric' (m : Set X -> Real>=0∞) : Measure X
参数：m : Set X -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `m : Set X → ℝ≥0∞`, `mkMetric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure.
-/
def mkMetric' (m : Set X → ℝ≥0∞) : Measure X :=
  (OuterMeasure.mkMetric' m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mkMetric m` is the supremum of `μ r` over `r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` that contain at least
two points. While each `mkMetric'.pre` is an *outer* measure, the supremum is a measure. -/
/-
**MeasureTheory.Measure.mkMetric** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：mkMetric (m : Real>=0∞ -> Real>=0∞) : Measure X
参数：m : Real>=0∞ -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mkMetric m` is the supremum of `μ r` over `
r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` th
at contain at least
two points. While each `mkMetric'.pre` is an *outer* measure, the supremum is a 
measure.
-/
def mkMetric (m : ℝ≥0∞ → ℝ≥0∞) : Measure X :=
  (OuterMeasure.mkMetric m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

@[simp]
/-
**MeasureTheory.Measure.mkMetric'_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：∀ {X : Type u_2} [inst : EMetricSpace X] [inst_1 : MeasurableSpace X] [ins
t_2 : BorelSpace X] (m : Set X → ENNReal),   (MeasureTheory.Measure.mkMetric' m)
.toOuterMeasure = (MeasureTheory.OuterMeasure.mkMetric' m).trim
参数：m : Set X → ENNReal；MeasureTheory.Measure.mkMetric' m；MeasureTheory.OuterMeas
ure.mkMetric' m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkMetric'_toOuterMeasure (m : Set X → ℝ≥0∞) :
    (mkMetric' m).toOuterMeasure = (OuterMeasure.mkMetric' m).trim :=
  rfl

@[simp]
/-
**MeasureTheory.Measure.mkMetric_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：mkMetric_toOuterMeasure (m : Real>=0∞ -> Real>=0∞) : (mkMetric m : Measure
 X).toOuterMeasure = OuterMeasure.mkMetric m
参数：m : Real>=0∞ -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.trim_mkMetric`：trim_mkMetric [MeasurableSpace
 X] [BorelSpace X] (m : Real>=0∞ -> Real>=0∞) : (mkMetric m : OuterMeasure X).tr
im = mkMetric m
-/
theorem mkMetric_toOuterMeasure (m : ℝ≥0∞ → ℝ≥0∞) :
    (mkMetric m : Measure X).toOuterMeasure = OuterMeasure.mkMetric m :=
  OuterMeasure.trim_mkMetric m

end Measure

/-
**MeasureTheory.OuterMeasure.coe_mkMetric** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：∀ {X : Type u_2} [inst : EMetricSpace X] [inst_1 : MeasurableSpace X] [ins
t_2 : BorelSpace X] (m : ENNReal → ENNReal),   ⇑(MeasureTheory.OuterMeasure.mkMe
tric m) = ⇑(MeasureTheory.Measure.mkMetric m)
参数：m : ENNReal → ENNReal；MeasureTheory.OuterMeasure.mkMetric m；MeasureTheory.Mea
sure.mkMetric m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.mkMetric_toOuterMeasure`：mkMetric_toOuterMeasure (
m : Real>=0∞ -> Real>=0∞) : (mkMetric m : Measure X).toOuterMeasure = OuterMeasu
re.mkMetric m
· 使用定理 `MeasureTheory.Measure.coe_toOuterMeasure`：∀ {α : Type u_1} [inst : Measu
rableSpace α] (μ : MeasureTheory.Measure α), ⇑μ.toOuterMeasure = ⇑μ
-/
theorem OuterMeasure.coe_mkMetric [MeasurableSpace X] [BorelSpace X] (m : ℝ≥0∞ → ℝ≥0∞) :
    ⇑(OuterMeasure.mkMetric m : OuterMeasure X) = Measure.mkMetric m := by
  rw [← Measure.mkMetric_toOuterMeasure, Measure.coe_toOuterMeasure]

namespace Measure

variable [MeasurableSpace X] [BorelSpace X]

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mkMetric m₁ hm₁ ≤ c • mkMetric m₂ hm₂`. -/
/-
**MeasureTheory.Measure.mkMetric_mono_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：mkMetric_mono_smul {m₁ m₂ : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c !
= ∞) (h0 : c != 0) (hle : m₁ <=ᶠ[𝓝[>=] 0] c • m₂) : (mkMetric m₁ : Measure X) <=
 c • mkMetric m₂
参数：hc : c != ∞；h0 : c != 0；hle : m₁ <=ᶠ[𝓝[>=] 0] c • m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.coe_mkMetric`：∀ {X : Type u_2} [inst : EMetri
cSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X] (m : ENNReal → EN
NReal),   ⇑(MeasureTheory.Out…
· 使用定理 `MeasureTheory.Measure.coe_smul`：coe_smul {_m : MeasurableSpace α} (c : R
) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric_mono_smul`：mkMetric_mono_smul {m₁ m₂
 : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0) (hle : m₁ <=
ᶠ[𝓝[>=] 0] c • m₂) : (mkMetric m₁ :…

--- 原说明 ---
If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mkMetric m₁ hm₁ ≤ c • mkMetric m₂ hm₂
`.
-/
theorem mkMetric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
    (hle : m₁ ≤ᶠ[𝓝[≥] 0] c • m₂) : (mkMetric m₁ : Measure X) ≤ c • mkMetric m₂ := fun s ↦ by
  rw [← OuterMeasure.coe_mkMetric, coe_smul, ← OuterMeasure.coe_mkMetric]
  exact OuterMeasure.mkMetric_mono_smul hc h0 hle s

@[simp]
/-
**MeasureTheory.Measure.mkMetric_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：mkMetric_top : (mkMetric (fun _ => ∞ : Real>=0∞ -> Real>=0∞) : Measure X) 
= ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_injective`：∀ {α : Type u_1} [inst :
 MeasurableSpace α], Function.Injective MeasureTheory.Measure.toOuterMeasure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.mkMetric_toOuterMeasure`：mkMetric_toOuterMeasure (
m : Real>=0∞ -> Real>=0∞) : (mkMetric m : Measure X).toOuterMeasure = OuterMeasu
re.mkMetric m
· 使用定理 `MeasureTheory.OuterMeasure.mkMetric_top`：mkMetric_top : (mkMetric (fun _
 => ∞ : Real>=0∞ -> Real>=0∞) : OuterMeasure X) = ⊤
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_top`：toOuterMeasure_top {_ : Measur
ableSpace α} : (⊤ : Measure α).toOuterMeasure = (⊤ : OuterMeasure α)
-/
theorem mkMetric_top : (mkMetric (fun _ => ∞ : ℝ≥0∞ → ℝ≥0∞) : Measure X) = ⊤ := by
  apply toOuterMeasure_injective
  rw [mkMetric_toOuterMeasure, OuterMeasure.mkMetric_top, toOuterMeasure_top]

/-- If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝 0]` to state this), then
`mkMetric m₁ hm₁ ≤ mkMetric m₂ hm₂`. -/
/-
**MeasureTheory.Measure.mkMetric_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：mkMetric_mono {m₁ m₂ : Real>=0∞ -> Real>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂) : (mkM
etric m₁ : Measure X) <= mkMetric m₂
参数：hle : m₁ <=ᶠ[𝓝 0] m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.mkMetric_mono_smul`：mkMetric_mono_smul {m₁ m₂ : Re
al>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0) (hle : m₁ <=ᶠ[𝓝[>
=] 0] c • m₂) : (mkMetric m₁ :…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ici_zero_eq_univ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Zer
o α] [IsBotZeroClass α], Set.Ici 0 = Set.univ
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝 0]` to state this), 
then
`mkMetric m₁ hm₁ ≤ mkMetric m₂ hm₂`.
-/
theorem mkMetric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝 0] m₂) :
    (mkMetric m₁ : Measure X) ≤ mkMetric m₂ := by
  convert! @mkMetric_mono_smul X _ _ _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

/-- A formula for `MeasureTheory.Measure.mkMetric`. -/
/-
**MeasureTheory.Measure.mkMetric_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：mkMetric_apply (m : Real>=0∞ -> Real>=0∞) (s : Set X) : mkMetric m s = ⨆ (
r : Real>=0∞) (_ : 0 < r), ⨅ (t : Nat -> Set X) (_ : s subseteq iUnion t) (_ : f
orall n, ediam (t n) <= r), ∑' n, ⨆ _ : (t n).Nonempty, m (ediam (t n))
参数：m : Real>=0∞ -> Real>=0∞；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_apply`：boundedBy_apply (s : Set α) 
: boundedBy m s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨆ _ : (t
 n).Nonempty, m (t n)
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Function.Surjective.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : InfSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `iInf_eq_if`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} [inst
_1 : Decidable p] (a : α), ⨅ (_ : p), a = if p then a else ⊤
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `ENNReal.tsum_eq_top_of_eq_top`：∀ {α : Type u_1} {f : α → ENNReal}, (∃ a,
 f a = ⊤) → ∑' (a : α), f a = ⊤
· 使用定理 `iSup_eq_if`：iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = i
f p then a else ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.ediam_pos_iff`：ediam_pos_iff : 0 < ediam s ↔ s.Nontrivial
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a

--- 原说明 ---
A formula for `MeasureTheory.Measure.mkMetric`.
-/
theorem mkMetric_apply (m : ℝ≥0∞ → ℝ≥0∞) (s : Set X) :
    mkMetric m s =
      ⨆ (r : ℝ≥0∞) (_ : 0 < r),
        ⨅ (t : ℕ → Set X) (_ : s ⊆ iUnion t) (_ : ∀ n, ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, m (ediam (t n)) := by
  classical
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  simp only [← OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
    OuterMeasure.iSup_apply, OuterMeasure.mkMetric'.pre, OuterMeasure.boundedBy_apply, extend]
  refine
    surjective_id.iSup_congr id fun r =>
      iSup_congr_Prop Iff.rfl fun _ =>
        surjective_id.iInf_congr _ fun t => iInf_congr_Prop Iff.rfl fun ht => ?_
  dsimp
  by_cases htr : ∀ n, ediam (t n) ≤ r
  · rw [iInf_eq_if, if_pos htr]
    congr 1 with n : 1
    simp only [iInf_eq_if, htr n, if_true]
  · rw [iInf_eq_if, if_neg htr]
    push Not at htr; rcases htr with ⟨n, hn⟩
    refine ENNReal.tsum_eq_top_of_eq_top ⟨n, ?_⟩
    rw [iSup_eq_if, if_pos, iInf_eq_if, if_neg]
    · exact hn.not_ge
    rcases ediam_pos_iff.1 hn.pos with ⟨x, hx, -⟩
    exact ⟨x, hx⟩
/-
**MeasureTheory.Measure.le_mkMetric** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：le_mkMetric (m : Real>=0∞ -> Real>=0∞) (μ : Measure X) (ε : Real>=0∞) (h₀ 
: 0 < ε) (h : forall s : Set X, ediam s <= ε -> μ s <= m (ediam s)) : μ <= mkMet
ric m
参数：m : Real>=0∞ -> Real>=0∞；μ : Measure X；ε : Real>=0∞；h₀ : 0 < ε；h : forall s :
 Set X, ediam s <= ε -> μ s <= m (ediam s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_le`：toOuterMeasure_le : μ₁.toOuterM
easure <= μ₂.toOuterMeasure ↔ μ₁ <= μ₂
· 使用定理 `MeasureTheory.Measure.mkMetric_toOuterMeasure`：mkMetric_toOuterMeasure (
m : Real>=0∞ -> Real>=0∞) : (mkMetric m : Measure X).toOuterMeasure = OuterMeasu
re.mkMetric m
· 使用定理 `MeasureTheory.OuterMeasure.le_mkMetric`：le_mkMetric (m : Real>=0∞ -> Rea
l>=0∞) (μ : OuterMeasure X) (r : Real>=0∞) (h0 : 0 < r) (hr : forall s, ediam s 
<= r -> μ s <= m (ediam s)) …
-/
theorem le_mkMetric (m : ℝ≥0∞ → ℝ≥0∞) (μ : Measure X) (ε : ℝ≥0∞) (h₀ : 0 < ε)
    (h : ∀ s : Set X, ediam s ≤ ε → μ s ≤ m (ediam s)) : μ ≤ mkMetric m := by
  rw [← toOuterMeasure_le, mkMetric_toOuterMeasure]
  exact OuterMeasure.le_mkMetric m μ.toOuterMeasure ε h₀ h

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`MeasureTheory.Measure.mkMetric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of countable types. -/
/-
**MeasureTheory.Measure.mkMetric_le_liminf_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：mkMetric_le_liminf_tsum {β : Type*} {ι : β -> Type*} [forall n, Countable 
(ι n)] (s : Set X) {l : Filter β} (r : β -> Real>=0∞) (hr : Tendsto r l (𝓝 0)) (
t : forall n : β, ι n -> Set X) (ht : forallᶠ n in l, forall i, ediam (t n i) <=
 r n) (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) (m : Real>=0∞ -> Real>=0∞) :
 mkMetric m s <= liminf (fun n => ∑' i, m (ediam (t n i))) l
参数：ι n；s : Set X；r : β -> Real>=0∞；hr : Tendsto r l (𝓝 0)；t : forall n : β, ι n 
-> Set X；ht : forallᶠ n in l, forall i, ediam (t n i) <= r n；hst : forallᶠ n in 
l, s subseteq ⋃ i, t n i；m : Real>=0∞ -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.mkMetric_apply`：mkMetric_apply (m : Real>=0∞ -> Re
al>=0∞) (s : Set X) : mkMetric m s = ⨆ (r : Real>=0∞) (_ : 0 < r), ⨅ (t : Nat ->
 Set X) (_ : s subseteq iU…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_liminf_lt`：frequently_lt_of_liminf_lt {b : β} (h
u : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `Encodable.iUnion_decode₂`：iUnion_decode₂ (f : β -> Set α) : ⋃ (i : Nat) 
(b in decode₂ β i), f b = ⋃ b, f b
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Metric.ediam_iUnion_mem_option`：ediam_iUnion_mem_option {ι : Type*} (o :
 Option ι) (s : ι -> Set X) : ediam (⋃ i in o, s i) = ⨆ i in o, ediam (s i)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `tsum_iUnion_decode₂`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 :
 TopologicalSpace M] {α : Type u_3} {β : Type u_4}   [inst_2 : Encodable β] (m :
 Set α → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Metric.ediam_empty`：ediam_empty : ediam (∅ : Set X) = 0
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
To bound the Hausdorff measure (or, more generally, for a measure defined using
`MeasureTheory.Measure.mkMetric`) of a set, one may use coverings with maximum d
iameter tending to
`0`, indexed by any sequence of countable types.
-/
theorem mkMetric_le_liminf_tsum {β : Type*} {ι : β → Type*} [∀ n, Countable (ι n)] (s : Set X)
    {l : Filter β} (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0)) (t : ∀ n : β, ι n → Set X)
    (ht : ∀ᶠ n in l, ∀ i, ediam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) (m : ℝ≥0∞ → ℝ≥0∞) :
    mkMetric m s ≤ liminf (fun n => ∑' i, m (ediam (t n i))) l := by
  have : ∀ n, Encodable (ι n) := fun n => Encodable.ofCountable _
  simp only [mkMetric_apply]
  refine iSup₂_le fun ε hε => ?_
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases ((frequently_lt_of_liminf_lt (by isBoundedDefault) hc).and_eventually
        ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists with
    ⟨n, hn, hrn, htn, hstn⟩
  set u : ℕ → Set X := fun j => ⋃ b ∈ decode₂ (ι n) j, t n b
  refine iInf₂_le_of_le u (by rwa [iUnion_decode₂]) ?_
  refine iInf_le_of_le (fun j => ?_) ?_
  · rw [ediam_iUnion_mem_option]
    exact iSup₂_le fun _ _ => (htn _).trans hrn.le
  · calc
      (∑' j : ℕ, ⨆ _ : (u j).Nonempty, m (ediam (u j))) = _ :=
        tsum_iUnion_decode₂ (fun t : Set X => ⨆ _ : t.Nonempty, m (ediam t)) (by simp) _
      _ ≤ ∑' i : ι n, m (ediam (t n i)) := ENNReal.tsum_le_tsum fun b => iSup_le fun _ => le_rfl
      _ ≤ c := hn.le

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`MeasureTheory.Measure.mkMetric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of finite types. -/
/-
**MeasureTheory.Measure.mkMetric_le_liminf_sum** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：mkMetric_le_liminf_sum {β : Type*} {ι : β -> Type*} [hι : forall n, Fintyp
e (ι n)] (s : Set X) {l : Filter β} (r : β -> Real>=0∞) (hr : Tendsto r l (𝓝 0))
 (t : forall n : β, ι n -> Set X) (ht : forallᶠ n in l, forall i, ediam (t n i) 
<= r n) (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) (m : Real>=0∞ -> Real>=0∞)
 : mkMetric m s <= liminf (fun n => ∑ i, m (ediam (t n i))) l
参数：ι n；s : Set X；r : β -> Real>=0∞；hr : Tendsto r l (𝓝 0)；t : forall n : β, ι n 
-> Set X；ht : forallᶠ n in l, forall i, ediam (t n i) <= r n；hst : forallᶠ n in 
l, s subseteq ⋃ i, t n i；m : Real>=0∞ -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `MeasureTheory.Measure.mkMetric_le_liminf_tsum`：mkMetric_le_liminf_tsum {
β : Type*} {ι : β -> Type*} [forall n, Countable (ι n)] (s : Set X) {l : Filter 
β} (r : β -> Real>=0∞) (hr : Tendst…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
To bound the Hausdorff measure (or, more generally, for a measure defined using
`MeasureTheory.Measure.mkMetric`) of a set, one may use coverings with maximum d
iameter tending to
`0`, indexed by any sequence of finite types.
-/
theorem mkMetric_le_liminf_sum {β : Type*} {ι : β → Type*} [hι : ∀ n, Fintype (ι n)] (s : Set X)
    {l : Filter β} (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0)) (t : ∀ n : β, ι n → Set X)
    (ht : ∀ᶠ n in l, ∀ i, ediam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) (m : ℝ≥0∞ → ℝ≥0∞) :
    mkMetric m s ≤ liminf (fun n => ∑ i, m (ediam (t n i))) l := by
  simpa only [tsum_fintype] using mkMetric_le_liminf_tsum s r hr t ht hst m

/-!
### Hausdorff measure and Hausdorff dimension
-/


/-- Hausdorff measure on an (e)metric space. -/
/-
**MeasureTheory.Measure.hausdorffMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：hausdorffMeasure (d : Real) : Measure X
参数：d : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Hausdorff measure on an (e)metric space.
-/
def hausdorffMeasure (d : ℝ) : Measure X :=
  mkMetric fun r => r ^ d

@[inherit_doc]
scoped[MeasureTheory] notation "μH[" d "]" => MeasureTheory.Measure.hausdorffMeasure d
/-
**MeasureTheory.Measure.le_hausdorffMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：le_hausdorffMeasure (d : Real) (μ : Measure X) (ε : Real>=0∞) (h₀ : 0 < ε)
 (h : forall s : Set X, ediam s <= ε -> μ s <= ediam s ^ d) : μ <= μH[d]
参数：d : Real；μ : Measure X；ε : Real>=0∞；h₀ : 0 < ε；h : forall s : Set X, ediam s 
<= ε -> μ s <= ediam s ^ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.le_mkMetric`：le_mkMetric (m : Real>=0∞ -> Real>=0∞
) (μ : Measure X) (ε : Real>=0∞) (h₀ : 0 < ε) (h : forall s : Set X, ediam s <= 
ε -> μ s <= m (ediam s)…
-/
theorem le_hausdorffMeasure (d : ℝ) (μ : Measure X) (ε : ℝ≥0∞) (h₀ : 0 < ε)
    (h : ∀ s : Set X, ediam s ≤ ε → μ s ≤ ediam s ^ d) : μ ≤ μH[d] :=
  le_mkMetric _ μ ε h₀ h

/-- A formula for `μH[d] s`. -/
/-
**MeasureTheory.Measure.hausdorffMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：hausdorffMeasure_apply (d : Real) (s : Set X) : μH[d] s = ⨆ (r : Real>=0∞)
 (_ : 0 < r), ⨅ (t : Nat -> Set X) (_ : s subseteq ⋃ n, t n) (_ : forall n, edia
m (t n) <= r), ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d
参数：d : Real；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.mkMetric_apply`：mkMetric_apply (m : Real>=0∞ -> Re
al>=0∞) (s : Set X) : mkMetric m s = ⨆ (r : Real>=0∞) (_ : 0 < r), ⨅ (t : Nat ->
 Set X) (_ : s subseteq iU…

--- 原说明 ---
A formula for `μH[d] s`.
-/
theorem hausdorffMeasure_apply (d : ℝ) (s : Set X) :
    μH[d] s =
      ⨆ (r : ℝ≥0∞) (_ : 0 < r),
        ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d :=
  mkMetric_apply _ _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of countable types. -/
/-
**MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：hausdorffMeasure_le_liminf_tsum {β : Type*} {ι : β -> Type*} [forall n, Co
untable (ι n)] (d : Real) (s : Set X) {l : Filter β} (r : β -> Real>=0∞) (hr : T
endsto r l (𝓝 0)) (t : forall n : β, ι n -> Set X) (ht : forallᶠ n in l, forall 
i, ediam (t n i) <= r n) (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) : μH[d] s
 <= liminf (fun n => ∑' i, ediam (t n i) ^ d) l
参数：ι n；d : Real；s : Set X；r : β -> Real>=0∞；hr : Tendsto r l (𝓝 0)；t : forall n 
: β, ι n -> Set X；ht : forallᶠ n in l, forall i, ediam (t n i) <= r n；hst : fora
llᶠ n in l, s subseteq ⋃ i, t n i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.mkMetric_le_liminf_tsum`：mkMetric_le_liminf_tsum {
β : Type*} {ι : β -> Type*} [forall n, Countable (ι n)] (s : Set X) {l : Filter 
β} (r : β -> Real>=0∞) (hr : Tendst…

--- 原说明 ---
To bound the Hausdorff measure of a set, one may use coverings with maximum diam
eter tending
to `0`, indexed by any sequence of countable types.
-/
theorem hausdorffMeasure_le_liminf_tsum {β : Type*} {ι : β → Type*} [∀ n, Countable (ι n)]
    (d : ℝ) (s : Set X) {l : Filter β} (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0))
    (t : ∀ n : β, ι n → Set X) (ht : ∀ᶠ n in l, ∀ i, ediam (t n i) ≤ r n)
    (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) : μH[d] s ≤ liminf (fun n => ∑' i, ediam (t n i) ^ d) l :=
  mkMetric_le_liminf_tsum s r hr t ht hst _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of finite types. -/
/-
**MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：hausdorffMeasure_le_liminf_sum {β : Type*} {ι : β -> Type*} [forall n, Fin
type (ι n)] (d : Real) (s : Set X) {l : Filter β} (r : β -> Real>=0∞) (hr : Tend
sto r l (𝓝 0)) (t : forall n : β, ι n -> Set X) (ht : forallᶠ n in l, forall i, 
ediam (t n i) <= r n) (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) : μH[d] s <=
 liminf (fun n => ∑ i, ediam (t n i) ^ d) l
参数：ι n；d : Real；s : Set X；r : β -> Real>=0∞；hr : Tendsto r l (𝓝 0)；t : forall n 
: β, ι n -> Set X；ht : forallᶠ n in l, forall i, ediam (t n i) <= r n；hst : fora
llᶠ n in l, s subseteq ⋃ i, t n i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.mkMetric_le_liminf_sum`：mkMetric_le_liminf_sum {β 
: Type*} {ι : β -> Type*} [hι : forall n, Fintype (ι n)] (s : Set X) {l : Filter
 β} (r : β -> Real>=0∞) (hr : Tend…

--- 原说明 ---
To bound the Hausdorff measure of a set, one may use coverings with maximum diam
eter tending
to `0`, indexed by any sequence of finite types.
-/
theorem hausdorffMeasure_le_liminf_sum {β : Type*} {ι : β → Type*} [∀ n, Fintype (ι n)]
    (d : ℝ) (s : Set X) {l : Filter β} (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0))
    (t : ∀ n : β, ι n → Set X) (ht : ∀ᶠ n in l, ∀ i, ediam (t n i) ≤ r n)
    (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) : μH[d] s ≤ liminf (fun n => ∑ i, ediam (t n i) ^ d) l :=
  mkMetric_le_liminf_sum s r hr t ht hst _

/-- If `d₁ < d₂`, then for any set `s` we have either `μH[d₂] s = 0`, or `μH[d₁] s = ∞`. -/
/-
**MeasureTheory.Measure.hausdorffMeasure_zero_or_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：hausdorffMeasure_zero_or_top {d₁ d₂ : Real} (h : d₁ < d₂) (s : Set X) : μH
[d₂] s = 0 ∨ μH[d₁] s = ∞
参数：h : d₁ < d₂；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
· 使用定理 `MeasureTheory.Measure.mkMetric_mono_smul`：mkMetric_mono_smul {m₁ m₂ : Re
al>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0) (hle : m₁ <=ᶠ[𝓝[>
=] 0] c • m₂) : (mkMetric m₁ :…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `NNReal.rpow_eq_zero_iff`：rpow_eq_zero_iff {x : Real>=0} {y : Real} : x ^
 y = 0 ↔ x = 0 ∧ y != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ico_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ico b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
If `d₁ < d₂`, then for any set `s` we have either `μH[d₂] s = 0`, or `μH[d₁] s =
 ∞`.
-/
theorem hausdorffMeasure_zero_or_top {d₁ d₂ : ℝ} (h : d₁ < d₂) (s : Set X) :
    μH[d₂] s = 0 ∨ μH[d₁] s = ∞ := by
  by_contra! H
  suffices ∀ c : ℝ≥0, c ≠ 0 → μH[d₂] s ≤ c * μH[d₁] s by
    rcases ENNReal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩
    exact hc.not_ge (this c (pos_iff_ne_zero.1 hc0))
  intro c hc
  refine le_iff'.1 (mkMetric_mono_smul ENNReal.coe_ne_top (mod_cast hc) ?_) s
  have : 0 < ((c : ℝ≥0∞) ^ (d₂ - d₁)⁻¹) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hc, pos_iff_ne_zero, Ne, ENNReal.coe_eq_zero,
      NNReal.rpow_eq_zero_iff]
    exact mt And.left hc
  filter_upwards [Ico_mem_nhdsGE this]
  rintro r ⟨hr₀, hrc⟩
  lift r to ℝ≥0 using ne_top_of_lt hrc
  rw [Pi.smul_apply, smul_eq_mul,
    ← ENNReal.div_le_iff_le_mul (Or.inr ENNReal.coe_ne_top) (Or.inr <| mt ENNReal.coe_eq_zero.1 hc)]
  rcases eq_or_ne r 0 with (rfl | hr₀)
  · rcases lt_or_ge 0 d₂ with (h₂ | h₂)
    · simp only [h₂, ENNReal.zero_rpow_of_pos, zero_le, ENNReal.zero_div, ENNReal.coe_zero]
    · simp only [h.trans_le h₂, ENNReal.div_top, zero_le, ENNReal.zero_rpow_of_neg,
        ENNReal.coe_zero]
  · have : (r : ℝ≥0∞) ≠ 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using hr₀
    rw [← ENNReal.rpow_sub _ _ this ENNReal.coe_ne_top]
    refine (ENNReal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans ?_
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (sub_pos.2 h).ne', ENNReal.rpow_one]

/-- Hausdorff measure `μH[d] s` is monotone in `d`. -/
/-
**MeasureTheory.Measure.hausdorffMeasure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：hausdorffMeasure_mono {d₁ d₂ : Real} (h : d₁ <= d₂) (s : Set X) : μH[d₂] s
 <= μH[d₁] s
参数：h : d₁ <= d₂；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`：hausdorffMeasure_zer
o_or_top {d₁ d₂ : Real} (h : d₁ < d₂) (s : Set X) : μH[d₂] s = 0 ∨ μH[d₁] s = ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
Hausdorff measure `μH[d] s` is monotone in `d`.
-/
theorem hausdorffMeasure_mono {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (s : Set X) : μH[d₂] s ≤ μH[d₁] s := by
  rcases h.eq_or_lt with (rfl | h); · exact le_rfl
  rcases hausdorffMeasure_zero_or_top h s with hs | hs <;> simp [hs]

variable (X) in
/-
**MeasureTheory.Measure.nullSingletonClass_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：nullSingletonClass_hausdorff {d : Real} (hd : 0 < d) : NullSingletonClass 
(hausdorffMeasure d : Measure X)
参数：hd : 0 < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_apply`：hausdorffMeasure_apply (d 
: Real) (s : Set X) : μH[d] s = ⨆ (r : Real>=0∞) (_ : 0 < r), ⨅ (t : Nat -> Set 
X) (_ : s subseteq ⋃ n, t n) (_ : …
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
-/
theorem nullSingletonClass_hausdorff {d : ℝ} (hd : 0 < d) :
    NullSingletonClass (hausdorffMeasure d : Measure X) := by
  refine ⟨fun x => ?_⟩
  rw [← nonpos_iff_eq_zero, hausdorffMeasure_apply]
  refine iSup₂_le fun ε _ => iInf₂_le_of_le (fun _ => {x}) ?_ <| iInf_le_of_le (fun _ => ?_) ?_
  · exact subset_iUnion (fun _ => {x} : ℕ → Set X) 0
  · simp only [ediam_singleton, zero_le]
  · simp [hd]

@[deprecated (since := "2026-06-09")]
alias noAtoms_hausdorff := nullSingletonClass_hausdorff

@[simp]
/-
**MeasureTheory.Measure.hausdorffMeasure_zero_singleton** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：hausdorffMeasure_zero_singleton (x : X) : μH[0] ({x} : Set X) = 1
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Metric.ediam_singleton`：ediam_singleton : ediam ({x} : Set X) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum`：hausdorffMeasure_l
e_liminf_sum {β : Type*} {ι : β -> Type*} [forall n, Fintype (ι n)] (d : Real) (
s : Set X) {l : Filter β} (r : β -> Real>=…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_apply`：hausdorffMeasure_apply (d 
: Real) (s : Set X) : μH[d] s = ⨆ (r : Real>=0∞) (_ : 0 < r), ⨅ (t : Nat -> Set 
X) (_ : s subseteq ⋃ n, t n) (_ : …
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
（共 46 条，此处仅展示前 30 条）
-/
theorem hausdorffMeasure_zero_singleton (x : X) : μH[0] ({x} : Set X) = 1 := by
  apply le_antisymm
  · let r : ℕ → ℝ≥0∞ := fun _ => 0
    let t : ℕ → Unit → Set X := fun _ _ => {x}
    have ht : ∀ᶠ n in atTop, ∀ i, ediam (t n i) ≤ r n := by
      simp only [t, r, imp_true_iff, ediam_singleton, eventually_atTop,
        nonpos_iff_eq_zero, exists_const]
    simpa [t, liminf_const] using hausdorffMeasure_le_liminf_sum 0 {x} r tendsto_const_nhds t ht
  · rw [hausdorffMeasure_apply]
    suffices
      (1 : ℝ≥0∞) ≤
        ⨅ (t : ℕ → Set X) (_ : {x} ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ 1),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (0 : ℝ) by
      apply le_trans this _
      convert! le_iSup₂ (α := ℝ≥0∞) (1 : ℝ≥0∞) zero_lt_one
      rfl
    simp only [ENNReal.rpow_zero, le_iInf_iff]
    intro t hst _
    rcases mem_iUnion.1 (hst (mem_singleton x)) with ⟨m, hm⟩
    have A : (t m).Nonempty := ⟨x, hm⟩
    calc
      (1 : ℝ≥0∞) = ⨆ h : (t m).Nonempty, 1 := by simp only [A, ciSup_pos]
      _ ≤ ∑' n, ⨆ h : (t n).Nonempty, 1 := ENNReal.le_tsum _
/-
**MeasureTheory.Measure.one_le_hausdorffMeasure_zero_of_nonempty** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：one_le_hausdorffMeasure_zero_of_nonempty {s : Set X} (h : s.Nonempty) : 1 
<= μH[0] s
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_singleton`：hausdorffMeasure_
zero_singleton (x : X) : μH[0] ({x} : Set X) = 1
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem one_le_hausdorffMeasure_zero_of_nonempty {s : Set X} (h : s.Nonempty) : 1 ≤ μH[0] s := by
  rcases h with ⟨x, hx⟩
  calc
    (1 : ℝ≥0∞) = μH[0] ({x} : Set X) := (hausdorffMeasure_zero_singleton x).symm
    _ ≤ μH[0] s := measure_mono (singleton_subset_iff.2 hx)
/-
**MeasureTheory.Measure.hausdorffMeasure_le_one_of_subsingleton** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：hausdorffMeasure_le_one_of_subsingleton {s : Set X} (hs : s.Subsingleton) 
{d : Real} (hd : 0 <= d) : μH[d] s <= 1
参数：hs : s.Subsingleton；hd : 0 <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_singleton`：hausdorffMeasure_
zero_singleton (x : X) : μH[0] ({x} : Set X) = 1
· 使用定理 `MeasureTheory.Measure.nullSingletonClass_hausdorff`：nullSingletonClass_h
ausdorff {d : Real} (hd : 0 < d) : NullSingletonClass (hausdorffMeasure d : Meas
ure X)
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem hausdorffMeasure_le_one_of_subsingleton {s : Set X} (hs : s.Subsingleton) {d : ℝ}
    (hd : 0 ≤ d) : μH[d] s ≤ 1 := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  · simp only [measure_empty, zero_le]
  · rw [(subsingleton_iff_singleton hx).1 hs]
    rcases eq_or_lt_of_le hd with (rfl | dpos)
    · simp only [le_refl, hausdorffMeasure_zero_singleton]
    · have := nullSingletonClass_hausdorff X dpos
      simp only [zero_le, measure_singleton]

end Measure

end MeasureTheory

/-!
### Hausdorff measure, Hausdorff dimension, and Hölder or Lipschitz continuous maps
-/


open scoped MeasureTheory

open MeasureTheory MeasureTheory.Measure

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

namespace HolderOnWith

variable {C r : ℝ≥0} {f : X → Y} {s : Set X}

/-- If `f : X → Y` is Hölder continuous on `s` with a positive exponent `r`, then
`μH[d] (f '' s) ≤ C ^ d * μH[r * d] s`. -/
/-
**HolderOnWith.hausdorffMeasure_image_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith
`。
形式化陈述：hausdorffMeasure_image_le (h : HolderOnWith C r f s) (hr : 0 < r) {d : Rea
l} (hd : 0 <= d) : μH[d] (f '' s) <= (C : Real>=0∞) ^ d * μH[r * d] s
参数：h : HolderOnWith C r f s；hr : 0 < r；hd : 0 <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `HolderOnWith.ediam_image_le`：ediam_image_le (hf : HolderOnWith C r f s) 
: ediam (f '' s) <= (C : Real>=0∞) * ediam s ^ (r : Real)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure.congr_simp`：∀ {X : Type u_2} [ins
t : EMetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X] (d d_1 
: ℝ),   d = d_1 → MeasureTheory.Measure…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_singleton`：hausdorffMeasure_
zero_singleton (x : X) : μH[0] ({x} : Set X) = 1
· 使用定理 `MeasureTheory.Measure.one_le_hausdorffMeasure_zero_of_nonempty`：one_le_h
ausdorffMeasure_zero_of_nonempty {s : Set X} (h : s.Nonempty) : 1 <= μH[0] s
· 使用定理 `MeasureTheory.Measure.nullSingletonClass_hausdorff`：nullSingletonClass_h
ausdorff {d : Real} (hd : 0 < d) : NullSingletonClass (hausdorffMeasure d : Meas
ure X)
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : X → Y` is Hölder continuous on `s` with a positive exponent `r`, then
`μH[d] (f '' s) ≤ C ^ d * μH[r * d] s`.
-/
theorem hausdorffMeasure_image_le (h : HolderOnWith C r f s) (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (f '' s) ≤ (C : ℝ≥0∞) ^ d * μH[r * d] s := by
  -- We start with the trivial case `C = 0`
  rcases eq_zero_or_pos C with (rfl | hC0)
  · rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · simp only [measure_empty, nonpos_iff_eq_zero, mul_zero, image_empty]
    have : f '' s = {f x} :=
      have : (f '' s).Subsingleton := by simpa [ediam_eq_zero_iff] using h.ediam_image_le
      (subsingleton_iff_singleton (mem_image_of_mem f hx)).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul, mul_zero]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨x, hx⟩
    · have := nullSingletonClass_hausdorff Y h'd
      simp only [zero_le, measure_singleton]
  -- Now assume `C ≠ 0`
  · have hCd0 : (C : ℝ≥0∞) ^ d ≠ 0 := by simp [hC0.ne']
    have hCd : (C : ℝ≥0∞) ^ d ≠ ∞ := by simp [hd]
    simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hCd0 hCd,
      ← ENNReal.tsum_mul_left]
    refine iSup_le fun R => iSup_le fun hR => ?_
    have : Tendsto (fun d : ℝ≥0∞ => (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
      ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hr
    rcases ENNReal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR)) with
      ⟨δ, δ0, H⟩
    refine le_iSup₂_of_le δ δ0 <| iInf₂_mono' fun t hst ↦
      ⟨fun n => f '' (t n ∩ s), ?_, iInf_mono' fun htδ ↦
        ⟨fun n => (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le, ?_⟩⟩
    · grw [← image_iUnion, ← iUnion_inter, ← hst, inter_self]
    · refine ENNReal.tsum_le_tsum fun n => ?_
      simp only [iSup_le_iff, image_nonempty]
      intro hft
      simp only [Nonempty.mono ((t n).inter_subset_left) hft, ciSup_pos]
      rw [ENNReal.rpow_mul, ← ENNReal.mul_rpow_of_nonneg _ _ hd]
      gcongr
      exact h.ediam_image_inter_le _

end HolderOnWith

namespace LipschitzOnWith

open Submodule

variable {K : ℝ≥0} {f : X → Y} {s : Set X}

/-- If `f : X → Y` is `K`-Lipschitz on `s`, then `μH[d] (f '' s) ≤ K ^ d * μH[d] s`. -/
/-
**LipschitzOnWith.hausdorffMeasure_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Lipschitz
OnWith`。
形式化陈述：hausdorffMeasure_image_le (h : LipschitzOnWith K f s) {d : Real} (hd : 0 <
= d) : μH[d] (f '' s) <= (K : Real>=0∞) ^ d * μH[d] s
参数：h : LipschitzOnWith K f s；hd : 0 <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure.congr_simp`：∀ {X : Type u_2} [ins
t : EMetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X] (d d_1 
: ℝ),   d = d_1 → MeasureTheory.Measure…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HolderOnWith.hausdorffMeasure_image_le`：hausdorffMeasure_image_le (h : H
olderOnWith C r f s) (hr : 0 < r) {d : Real} (hd : 0 <= d) : μH[d] (f '' s) <= (
C : Real>=0∞) ^ d * μH[r * d…
· 使用定理 `LipschitzOnWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : Ps
eudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C : NNReal} {f : X → Y}   {
s : Set X}, Lipsch…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `f : X → Y` is `K`-Lipschitz on `s`, then `μH[d] (f '' s) ≤ K ^ d * μH[d] s`.
-/
theorem hausdorffMeasure_image_le (h : LipschitzOnWith K f s) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μH[d] s := by
  simpa only [NNReal.coe_one, one_mul] using h.holderOnWith.hausdorffMeasure_image_le zero_lt_one hd

end LipschitzOnWith

namespace LipschitzWith

variable {K : ℝ≥0} {f : X → Y}

/-- If `f` is a `K`-Lipschitz map, then it increases the Hausdorff `d`-measures of sets at most
by the factor of `K ^ d`. -/
/-
**LipschitzWith.hausdorffMeasure_image_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWi
th`。
形式化陈述：hausdorffMeasure_image_le (h : LipschitzWith K f) {d : Real} (hd : 0 <= d)
 (s : Set X) : μH[d] (f '' s) <= (K : Real>=0∞) ^ d * μH[d] s
参数：h : LipschitzWith K f；hd : 0 <= d；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.hausdorffMeasure_image_le`：hausdorffMeasure_image_le (h 
: LipschitzOnWith K f s) {d : Real} (hd : 0 <= d) : μH[d] (f '' s) <= (K : Real>
=0∞) ^ d * μH[d] s
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…

--- 原说明 ---
If `f` is a `K`-Lipschitz map, then it increases the Hausdorff `d`-measures of s
ets at most
by the factor of `K ^ d`.
-/
theorem hausdorffMeasure_image_le (h : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) (s : Set X) :
    μH[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μH[d] s :=
  h.lipschitzOnWith.hausdorffMeasure_image_le hd

end LipschitzWith

open scoped Pointwise

/-
**MeasureTheory.Measure.hausdorffMeasure_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MeasureTheory.Measure.hausdorffMeasure_smul₀ {𝕜 E : Type*} [NormedAddCommGroup E]
    [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {d : ℝ} (hd : 0 ≤ d) {r : 𝕜} (hr : r ≠ 0) (s : Set E) :
    μH[d] (r • s) = ‖r‖₊ ^ d • μH[d] s := by
  have {r : 𝕜} (s : Set E) : μH[d] (r • s) ≤ ‖r‖₊ ^ d • μH[d] s := by
    simpa [ENNReal.coe_rpow_of_nonneg, hd]
      using (lipschitzWith_smul r).hausdorffMeasure_image_le hd s
  refine le_antisymm (this s) ?_
  rw [← le_inv_smul_iff_of_pos]
  · dsimp
    rw [← NNReal.inv_rpow, ← nnnorm_inv]
    · refine Eq.trans_le ?_ (this (r • s))
      rw [inv_smul_smul₀ hr]
  · simp [pos_iff_ne_zero, hr]

/-!
### Antilipschitz maps do not decrease Hausdorff measures and dimension
-/

namespace AntilipschitzWith

variable {f : X → Y} {K : ℝ≥0} {d : ℝ}

/-
**AntilipschitzWith.hausdorffMeasure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `Anti
lipschitzWith`。
形式化陈述：hausdorffMeasure_preimage_le (hf : AntilipschitzWith K f) (hd : 0 <= d) (s
 : Set Y) : μH[d] (f ⁻¹' s) <= (K : Real>=0∞) ^ d * μH[d] s
参数：hf : AntilipschitzWith K f；hd : 0 <= d；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `AntilipschitzWith.subsingleton`：∀ {α : Type u_4} {β : Type u_5} [inst : 
EMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   AntilipschitzWith
 0 f → Subsingleton …
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Set.subsingleton_univ`：subsingleton_univ [Subsingleton α] : (univ : Set 
α).Subsingleton
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_singleton`：hausdorffMeasure_
zero_singleton (x : X) : μH[0] ({x} : Set X) = 1
· 使用定理 `MeasureTheory.Measure.one_le_hausdorffMeasure_zero_of_nonempty`：one_le_h
ausdorffMeasure_zero_of_nonempty {s : Set X} (h : s.Nonempty) : 1 <= μH[0] s
· 使用定理 `MeasureTheory.Measure.nullSingletonClass_hausdorff`：nullSingletonClass_h
ausdorff {d : Real} (hd : 0 < d) : NullSingletonClass (hausdorffMeasure d : Meas
ure X)
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
（共 60 条，此处仅展示前 30 条）
-/
theorem hausdorffMeasure_preimage_le (hf : AntilipschitzWith K f) (hd : 0 ≤ d) (s : Set Y) :
    μH[d] (f ⁻¹' s) ≤ (K : ℝ≥0∞) ^ d * μH[d] s := by
  rcases eq_or_ne K 0 with (rfl | h0)
  · rcases eq_empty_or_nonempty (f ⁻¹' s) with (hs | ⟨x, hx⟩)
    · simp only [hs, measure_empty, zero_le]
    have : f ⁻¹' s = {x} := by
      have : Subsingleton X := hf.subsingleton
      have : (f ⁻¹' s).Subsingleton := subsingleton_univ.anti (subset_univ _)
      exact (subsingleton_iff_singleton hx).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨f x, hx⟩
    · have := nullSingletonClass_hausdorff X h'd
      simp only [zero_le, measure_singleton]
  have hKd0 : (K : ℝ≥0∞) ^ d ≠ 0 := by simp [h0]
  have hKd : (K : ℝ≥0∞) ^ d ≠ ∞ := by simp [hd]
  simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hKd0 hKd,
    ← ENNReal.tsum_mul_left]
  refine iSup₂_le fun ε ε0 => ?_
  refine le_iSup₂_of_le (ε / K) (by simp [ε0.ne']) ?_
  refine le_iInf₂ fun t hst => le_iInf fun htε => ?_
  replace hst : f ⁻¹' s ⊆ _ := preimage_mono hst; rw [preimage_iUnion] at hst
  refine iInf₂_le_of_le _ hst (iInf_le_of_le (fun n => ?_) ?_)
  · exact (hf.ediam_preimage_le _).trans (ENNReal.mul_le_of_le_div' <| htε n)
  · refine ENNReal.tsum_le_tsum fun n => iSup_le_iff.2 fun hft => ?_
    simp only [nonempty_of_nonempty_preimage hft, ciSup_pos]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
    exact ENNReal.rpow_le_rpow (hf.ediam_preimage_le _) hd
/-
**AntilipschitzWith.le_hausdorffMeasure_image** 是 Mathlib 中的一个定理，位于命名空间 `Antilip
schitzWith`。
形式化陈述：le_hausdorffMeasure_image (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : 
Set X) : μH[d] s <= (K : Real>=0∞) ^ d * μH[d] (f '' s)
参数：hf : AntilipschitzWith K f；hd : 0 <= d；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `AntilipschitzWith.hausdorffMeasure_preimage_le`：hausdorffMeasure_preimag
e_le (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : Set Y) : μH[d] (f ⁻¹' s) <=
 (K : Real>=0∞) ^ d * μH[d] s
-/
theorem le_hausdorffMeasure_image (hf : AntilipschitzWith K f) (hd : 0 ≤ d) (s : Set X) :
    μH[d] s ≤ (K : ℝ≥0∞) ^ d * μH[d] (f '' s) :=
  calc
    μH[d] s ≤ μH[d] (f ⁻¹' f '' s) := measure_mono (subset_preimage_image _ _)
    _ ≤ (K : ℝ≥0∞) ^ d * μH[d] (f '' s) := hf.hausdorffMeasure_preimage_le hd (f '' s)

end AntilipschitzWith

/-!
### Isometries preserve the Hausdorff measure and Hausdorff dimension
-/


namespace Isometry

variable {f : X → Y} {d : ℝ}

/-
**Isometry.hausdorffMeasure_image** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：hausdorffMeasure_image (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) (s :
 Set X) : μH[d] (f '' s) = μH[d] s
参数：hf : Isometry f；hd : 0 <= d ∨ Surjective f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.OuterMeasure.isometry_comap_mkMetric`：isometry_comap_mkMet
ric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f) (H : Monotone m ∨ 
Surjective f) : comap f (mkMetric m) = m…
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `ENNReal.monotone_rpow_of_nonneg`：monotone_rpow_of_nonneg {z : Real} (h :
 0 <= z) : Monotone fun x : Real>=0∞ => x ^ z
-/
theorem hausdorffMeasure_image (hf : Isometry f) (hd : 0 ≤ d ∨ Surjective f) (s : Set X) :
    μH[d] (f '' s) = μH[d] s := by
  simp only [hausdorffMeasure, ← OuterMeasure.coe_mkMetric, ← OuterMeasure.comap_apply]
  rw [OuterMeasure.isometry_comap_mkMetric _ hf (hd.imp_left _)]
  exact ENNReal.monotone_rpow_of_nonneg
/-
**Isometry.hausdorffMeasure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：hausdorffMeasure_preimage (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) (
s : Set Y) : μH[d] (f ⁻¹' s) = μH[d] (s inter range f)
参数：hf : Isometry f；hd : 0 <= d ∨ Surjective f；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.hausdorffMeasure_image`：hausdorffMeasure_image (hf : Isometry f
) (hd : 0 <= d ∨ Surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem hausdorffMeasure_preimage (hf : Isometry f) (hd : 0 ≤ d ∨ Surjective f) (s : Set Y) :
    μH[d] (f ⁻¹' s) = μH[d] (s ∩ range f) := by
  rw [← hf.hausdorffMeasure_image hd, image_preimage_eq_inter_range]
/-
**Isometry.map_hausdorffMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：map_hausdorffMeasure (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) : Meas
ure.map f μH[d] = μH[d].restrict (range f)
参数：hf : Isometry f；hd : 0 <= d ∨ Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Isometry.hausdorffMeasure_preimage`：hausdorffMeasure_preimage (hf : Isom
etry f) (hd : 0 <= d ∨ Surjective f) (s : Set Y) : μH[d] (f ⁻¹' s) = μH[d] (s in
ter range f)
-/
theorem map_hausdorffMeasure (hf : Isometry f) (hd : 0 ≤ d ∨ Surjective f) :
    Measure.map f μH[d] = μH[d].restrict (range f) := by
  ext1 s hs
  rw [map_apply hf.continuous.measurable hs, Measure.restrict_apply hs,
    hf.hausdorffMeasure_preimage hd]

end Isometry

namespace IsometryEquiv

@[simp]
/-
**IsometryEquiv.hausdorffMeasure_image** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`
。
形式化陈述：hausdorffMeasure_image (e : X ≃ᵢ Y) (d : Real) (s : Set X) : μH[d] (e '' s
) = μH[d] s
参数：e : X ≃ᵢ Y；d : Real；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.hausdorffMeasure_image`：hausdorffMeasure_image (hf : Isometry f
) (hd : 0 <= d ∨ Surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.surjective`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β),   Function.Surjective 
⇑h
-/
theorem hausdorffMeasure_image (e : X ≃ᵢ Y) (d : ℝ) (s : Set X) : μH[d] (e '' s) = μH[d] s :=
  e.isometry.hausdorffMeasure_image (Or.inr e.surjective) s

@[simp]
/-
**IsometryEquiv.hausdorffMeasure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEqu
iv`。
形式化陈述：hausdorffMeasure_preimage (e : X ≃ᵢ Y) (d : Real) (s : Set Y) : μH[d] (e ⁻
¹' s) = μH[d] s
参数：e : X ≃ᵢ Y；d : Real；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.image_symm`：image_symm (h : α ≃ᵢ β) : image h.symm = preim
age h
· 使用定理 `IsometryEquiv.hausdorffMeasure_image`：hausdorffMeasure_image (e : X ≃ᵢ Y
) (d : Real) (s : Set X) : μH[d] (e '' s) = μH[d] s
-/
theorem hausdorffMeasure_preimage (e : X ≃ᵢ Y) (d : ℝ) (s : Set Y) : μH[d] (e ⁻¹' s) = μH[d] s := by
  rw [← e.image_symm, e.symm.hausdorffMeasure_image]

@[simp]
/-
**IsometryEquiv.map_hausdorffMeasure** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：map_hausdorffMeasure (e : X ≃ᵢ Y) (d : Real) : Measure.map e μH[d] = μH[d]
参数：e : X ≃ᵢ Y；d : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Isometry.map_hausdorffMeasure`：map_hausdorffMeasure (hf : Isometry f) (h
d : 0 <= d ∨ Surjective f) : Measure.map f μH[d] = μH[d].restrict (range f)
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.surjective`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β),   Function.Surjective 
⇑h
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem map_hausdorffMeasure (e : X ≃ᵢ Y) (d : ℝ) : Measure.map e μH[d] = μH[d] := by
  rw [e.isometry.map_hausdorffMeasure (Or.inr e.surjective), e.surjective.range_eq, restrict_univ]
/-
**IsometryEquiv.measurePreserving_hausdorffMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Is
ometryEquiv`。
形式化陈述：measurePreserving_hausdorffMeasure (e : X ≃ᵢ Y) (d : Real) : MeasurePreser
ving e μH[d] μH[d]
参数：e : X ≃ᵢ Y；d : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsometryEquiv.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Continuous ⇑h
· 使用定理 `IsometryEquiv.map_hausdorffMeasure`：map_hausdorffMeasure (e : X ≃ᵢ Y) (d
 : Real) : Measure.map e μH[d] = μH[d]
-/
theorem measurePreserving_hausdorffMeasure (e : X ≃ᵢ Y) (d : ℝ) : MeasurePreserving e μH[d] μH[d] :=
  ⟨e.continuous.measurable, map_hausdorffMeasure _ _⟩

end IsometryEquiv

namespace MeasureTheory

@[to_additive]
/-
**MeasureTheory.hausdorffMeasure_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hausdorffMeasure_smul {α : Type*} [SMul α X] [IsIsometricSMul α X] {d : Re
al} (c : α) (h : 0 <= d ∨ Surjective (c • · : X -> X)) (s : Set X) : μH[d] (c • 
s) = μH[d] s
参数：c : α；h : 0 <= d ∨ Surjective (c • · : X -> X)；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.hausdorffMeasure_image`：hausdorffMeasure_image (hf : Isometry f
) (hd : 0 <= d ∨ Surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem hausdorffMeasure_smul {α : Type*} [SMul α X] [IsIsometricSMul α X] {d : ℝ} (c : α)
    (h : 0 ≤ d ∨ Surjective (c • · : X → X)) (s : Set X) : μH[d] (c • s) = μH[d] s :=
  (isometry_smul X c).hausdorffMeasure_image h _

@[to_additive]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Group α] [MulAction α X] [IsIsometricSMul α X] {d : ℝ} :
    SMulInvariantMeasure α X μH[d] where
  measure_preimage_smul c _ _ := (IsometryEquiv.constSMul c).hausdorffMeasure_preimage _ _

@[to_additive]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {d : ℝ} [Group X] [IsIsometricSMul X X] : IsMulLeftInvariant (μH[d] : Measure X) where
  map_mul_left_eq_self x := (IsometryEquiv.constSMul x).map_hausdorffMeasure _

@[to_additive]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {d : ℝ} [Group X] [IsIsometricSMul Xᵐᵒᵖ X] : IsMulRightInvariant (μH[d] : Measure X) where
  map_mul_right_eq_self x := (IsometryEquiv.constSMul (MulOpposite.op x)).map_hausdorffMeasure _

/-!
### Hausdorff measure and Lebesgue measure
-/


/-- In the space `ι → ℝ`, the Hausdorff measure coincides exactly with the Lebesgue measure. -/
@[simp]
/-
**MeasureTheory.hausdorffMeasure_pi_real** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：hausdorffMeasure_pi_real {ι : Type*} [Fintype ι] : (μH[Fintype.card ι] : M
easure (ι -> Real)) = volume
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.pi_eq_generateFrom`：pi_eq_generateFrom {C : forall
 i, Set (Set (α i))} (hC : forall i, generateFrom (C i) = by apply_assumption) (
h2C : forall i, IsPiSystem (C …
· 使用定理 `Real.borel_eq_generateFrom_Ioo_rat`：borel_eq_generateFrom_Ioo_rat : bore
l Real = .generateFrom (⋃ (a : Rat) (b : Rat) (_ : a < b), {Ioo (a : Real) (b : 
Real)})
· 使用定理 `Real.isPiSystem_Ioo_rat`：isPiSystem_Ioo_rat : IsPiSystem (⋃ (a : Rat) (b
 : Rat) (_ : a < b), {Ioo (a : Real) (b : Real)})
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Metric.ediam_pi_le_of_le`：ediam_pi_le_of_le {ι : Type*} {X : ι -> Type*}
 [Fintype ι] [forall i, PseudoEMetricSpace (X i)] {s : forall i : ι, Set (X i)} 
{c : Real>=0∞}…
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
（共 162 条，此处仅展示前 30 条）

--- 原说明 ---
In the space `ι → ℝ`, the Hausdorff measure coincides exactly with the Lebesgue 
measure.
-/
theorem hausdorffMeasure_pi_real {ι : Type*} [Fintype ι] :
    (μH[Fintype.card ι] : Measure (ι → ℝ)) = volume := by
  classical
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine (pi_eq_generateFrom (fun _ => Real.borel_eq_generateFrom_Ioo_rat.symm)
    (fun _ => Real.isPiSystem_Ioo_rat) (fun _ => Real.finiteSpanningSetsInIooRat _) ?_).symm
  simp only [mem_iUnion, mem_singleton_iff]
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intro s hs
  choose a b H using hs
  obtain rfl : s = fun i => Ioo (α := ℝ) (a i) (b i) := funext fun i => (H i).2
  replace H := fun i => (H i).1
  apply le_antisymm _
  -- first check that `volume s ≤ μH s`
  · have Hle : volume ≤ (μH[Fintype.card ι] : Measure (ι → ℝ)) := by
      refine le_hausdorffMeasure _ _ ∞ ENNReal.coe_lt_top fun s _ => ?_
      rw [ENNReal.rpow_natCast]
      exact Real.volume_pi_le_diam_pow s
    rw [← volume_pi_pi fun i => Ioo (a i : ℝ) (b i)]
    exact Measure.le_iff'.1 Hle _
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
    `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
    `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : ∀ i, 0 ≤ (b i : ℝ) - a i := fun i => by
    simpa only [sub_nonneg, Rat.cast_le] using (H i).le
  let γ := fun n : ℕ => ∀ i : ι, Fin ⌈((b i : ℝ) - a i) * n⌉₊
  let t : ∀ n : ℕ, γ n → Set (ι → ℝ) := fun n f =>
    Set.pi univ fun i => Icc (a i + f i / n) (a i + (f i + 1) / n)
  have A : Tendsto (fun n : ℕ => 1 / (n : ℝ≥0∞)) atTop (𝓝 0) := by
    simp only [one_div, ENNReal.tendsto_inv_nat_nhds_zero]
  have B : ∀ᶠ n in atTop, ∀ i : γ n, ediam (t n i) ≤ 1 / n := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    intro f
    refine ediam_pi_le_of_le fun b => ?_
    simp only [Real.ediam_Icc, add_div, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), le_refl,
      add_sub_add_left_eq_sub, add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  have C : ∀ᶠ n in atTop, (Set.pi univ fun i : ι => Ioo (a i : ℝ) (b i)) ⊆ ⋃ i : γ n, t n i := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have npos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    intro x hx
    simp only [mem_Ioo, mem_univ_pi] at hx
    simp only [t, mem_iUnion, mem_univ_pi]
    let f : γ n := fun i =>
      ⟨⌊(x i - a i) * n⌋₊, by
        apply Nat.floor_lt_ceil_of_lt_of_pos
        · gcongr
          exact (hx i).right
        · refine mul_pos ?_ npos
          simpa only [Rat.cast_lt, sub_pos] using H i⟩
    refine ⟨f, fun i => ⟨?_, ?_⟩⟩
    · calc
        (a i : ℝ) + ⌊(x i - a i) * n⌋₊ / n ≤ (a i : ℝ) + (x i - a i) * n / n := by
          gcongr
          exact Nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le)
        _ = x i := by field
    · calc
        x i = (a i : ℝ) + (x i - a i) * n / n := by field
        _ ≤ (a i : ℝ) + (⌊(x i - a i) * n⌋₊ + 1) / n := by
          gcongr
          exact (Nat.lt_floor_add_one _).le
  calc
    μH[Fintype.card ι] (Set.pi univ fun i : ι => Ioo (a i : ℝ) (b i)) ≤
        liminf (fun n : ℕ => ∑ i : γ n, ediam (t n i) ^ ((Fintype.card ι) : ℝ)) atTop :=
      hausdorffMeasure_le_liminf_sum _ (Set.pi univ fun i => Ioo (a i : ℝ) (b i))
        (fun n : ℕ => 1 / (n : ℝ≥0∞)) A t B C
    _ ≤ liminf (fun n : ℕ => ∑ i : γ n, (1 / (n : ℝ≥0∞)) ^ Fintype.card ι) atTop := by
      refine liminf_le_liminf ?_ ?_
      · filter_upwards [B] with _ hn
        apply Finset.sum_le_sum fun i _ => _
        simp only [ENNReal.rpow_natCast]
        intro i _
        exact pow_le_pow_left' (hn i) _
      · isBoundedDefault
    _ = liminf (fun n : ℕ => ∏ i : ι, (⌈((b i : ℝ) - a i) * n⌉₊ : ℝ≥0∞) / n) atTop := by
      simp only [γ, Finset.card_univ, Nat.cast_prod, one_mul, Fintype.card_fin, Finset.sum_const,
        nsmul_eq_mul, Fintype.card_pi, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const]
    _ = ∏ i : ι, volume (Ioo (a i : ℝ) (b i)) := by
      simp only [Real.volume_Ioo]
      apply Tendsto.liminf_eq
      refine ENNReal.tendsto_finsetProd_of_ne_top _ (fun i _ => ?_) fun i _ => ?_
      · apply
          Tendsto.congr' _
            ((ENNReal.continuous_ofReal.tendsto _).comp
              ((tendsto_nat_ceil_mul_div_atTop (I i)).comp tendsto_natCast_atTop_atTop))
        apply eventually_atTop.2 ⟨1, fun n hn => _⟩
        intro n hn
        simp only [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), comp_apply,
          ENNReal.ofReal_natCast]
      · simp only [ENNReal.ofReal_ne_top, Ne, not_false_iff]
/-
**MeasureTheory.isAddHaarMeasure_hausdorffMeasure** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory`。
形式化陈述：isAddHaarMeasure_hausdorffMeasure {E : Type*} [NormedAddCommGroup E] [Norm
edSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] : 
IsAddHaarMeasure (G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `MeasureTheory.hausdorffMeasure_pi_real`：hausdorffMeasure_pi_real {ι : Ty
pe*} [Fintype ι] : (μH[Fintype.card ι] : Measure (ι -> Real)) = volume
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureOnCompactsForallVolumeOfSigmaFi
nite`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) →
 MeasureTheory.MeasureSpace (X i)]   [inst_2 : (i : ι) → Topologic…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
（共 54 条，此处仅展示前 30 条）
-/
instance isAddHaarMeasure_hausdorffMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    IsAddHaarMeasure (G := E) μH[finrank ℝ E] where
  lt_top_of_isCompact K hK := by
    set e : E ≃L[ℝ] Fin (finrank ℝ E) → ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices μH[finrank ℝ E] (e '' K) < ⊤ by
      rw [← e.symm_image_image K]
      apply lt_of_le_of_lt <| e.symm.lipschitz.hausdorffMeasure_image_le (by simp) (e '' K)
      rw [ENNReal.rpow_natCast]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) this
    conv_lhs => congr; congr; rw [← Fintype.card_fin (finrank ℝ E)]
    rw [hausdorffMeasure_pi_real]
    exact (hK.image e.continuous).measure_lt_top
  open_pos U hU hU' := by
    set e : E ≃L[ℝ] Fin (finrank ℝ E) → ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices 0 < μH[finrank ℝ E] (e '' U) from
      (ENNReal.mul_pos_iff.mp (lt_of_lt_of_le this <|
        e.lipschitz.hausdorffMeasure_image_le (by simp) _)).2.ne'
    conv_rhs => congr; congr; rw [← Fintype.card_fin (finrank ℝ E)]
    rw [hausdorffMeasure_pi_real]
    apply (e.isOpenMap U hU).measure_pos (μ := volume)
    simpa

variable (ι X)
/-
**MeasureTheory.hausdorffMeasure_measurePreserving_funUnique** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：hausdorffMeasure_measurePreserving_funUnique [Unique ι] (d : Real) : Measu
rePreserving (MeasurableEquiv.funUnique ι X) μH[d] μH[d]
参数：d : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.measurePreserving_hausdorffMeasure`：measurePreserving_haus
dorffMeasure (e : X ≃ᵢ Y) (d : Real) : MeasurePreserving e μH[d] μH[d]
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem hausdorffMeasure_measurePreserving_funUnique [Unique ι] (d : ℝ) :
    MeasurePreserving (MeasurableEquiv.funUnique ι X) μH[d] μH[d] :=
  (IsometryEquiv.funUnique ι X).measurePreserving_hausdorffMeasure _
/-
**MeasureTheory.hausdorffMeasure_measurePreserving_piFinTwo** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：hausdorffMeasure_measurePreserving_piFinTwo (α : Fin 2 -> Type*) [forall i
, MeasurableSpace (α i)] [forall i, EMetricSpace (α i)] [forall i, BorelSpace (α
 i)] [forall i, SecondCountableTopology (α i)] (d : Real) : MeasurePreserving (M
easurableEquiv.piFinTwo α) μH[d] μH[d]
参数：α : Fin 2 -> Type*；α i；α i；α i；α i；d : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.measurePreserving_hausdorffMeasure`：measurePreserving_haus
dorffMeasure (e : X ≃ᵢ Y) (d : Real) : MeasurePreserving e μH[d] μH[d]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
-/
theorem hausdorffMeasure_measurePreserving_piFinTwo (α : Fin 2 → Type*)
    [∀ i, MeasurableSpace (α i)] [∀ i, EMetricSpace (α i)] [∀ i, BorelSpace (α i)]
    [∀ i, SecondCountableTopology (α i)] (d : ℝ) :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) μH[d] μH[d] :=
  (IsometryEquiv.piFinTwo α).measurePreserving_hausdorffMeasure _

/-- In the space `ℝ`, the Hausdorff measure coincides exactly with the Lebesgue measure. -/
@[simp]
/-
**MeasureTheory.hausdorffMeasure_real** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hausdorffMeasure_real : (μH[1] : Measure Real) = volume
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.volume_preserving_funUnique`：volume_preserving_funUnique (
α : Type u) (β : Type v) [Unique α] [MeasureSpace β] : MeasurePreserving (Measur
ableEquiv.funUnique α β) volume…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MeasureTheory.hausdorffMeasure_measurePreserving_funUnique`：hausdorffMea
sure_measurePreserving_funUnique [Unique ι] (d : Real) : MeasurePreserving (Meas
urableEquiv.funUnique ι X) μH[d] μH[d]
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.hausdorffMeasure_pi_real`：hausdorffMeasure_pi_real {ι : Ty
pe*} [Fintype ι] : (μH[Fintype.card ι] : Measure (ι -> Real)) = volume
· 使用定理 `Fintype.card_unit`：Fintype.card_unit : Fintype.card Unit = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
In the space `ℝ`, the Hausdorff measure coincides exactly with the Lebesgue meas
ure.
-/
theorem hausdorffMeasure_real : (μH[1] : Measure ℝ) = volume := by
  rw [← (volume_preserving_funUnique Unit ℝ).map_eq,
    ← (hausdorffMeasure_measurePreserving_funUnique Unit ℝ 1).map_eq,
    ← hausdorffMeasure_pi_real, Fintype.card_unit, Nat.cast_one]

/-- In the space `ℝ × ℝ`, the Hausdorff measure coincides exactly with the Lebesgue measure. -/
@[simp]
/-
**MeasureTheory.hausdorffMeasure_prod_real** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：hausdorffMeasure_prod_real : (μH[2] : Measure (Real × Real)) = volume
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.volume_preserving_piFinTwo`：volume_preserving_piFinTwo (α 
: Fin 2 -> Type u) [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume
 : Measure (α i))] : MeasurePr…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `MeasureTheory.hausdorffMeasure_measurePreserving_piFinTwo`：hausdorffMeas
ure_measurePreserving_piFinTwo (α : Fin 2 -> Type*) [forall i, MeasurableSpace (
α i)] [forall i, EMetricSpace (α i)] [forall i,…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.hausdorffMeasure_pi_real`：hausdorffMeasure_pi_real {ι : Ty
pe*} [Fintype ι] : (μH[Fintype.card ι] : Measure (ι -> Real)) = volume
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)

--- 原说明 ---
In the space `ℝ × ℝ`, the Hausdorff measure coincides exactly with the Lebesgue 
measure.
-/
theorem hausdorffMeasure_prod_real : (μH[2] : Measure (ℝ × ℝ)) = volume := by
  rw [← (volume_preserving_piFinTwo fun _ => ℝ).map_eq,
    ← (hausdorffMeasure_measurePreserving_piFinTwo (fun _ => ℝ) _).map_eq,
    ← hausdorffMeasure_pi_real, Fintype.card_fin, Nat.cast_two]

/-! ### Geometric results in affine spaces -/

section Geometric

variable {𝕜 E P : Type*}

/-
**MeasureTheory.hausdorffMeasure_smul_right_image** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：hausdorffMeasure_smul_right_image [NormedAddCommGroup E] [NormedSpace Real
 E] [MeasurableSpace E] [BorelSpace E] (v : E) (s : Set Real) : μH[1] ((fun r =>
 r • v) '' s) = ‖v‖₊ • μH[1] s
参数：v : E；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MeasureTheory.Measure.nullSingletonClass_hausdorff`：nullSingletonClass_h
ausdorff {d : Real} (hd : 0 < d) : NullSingletonClass (hausdorffMeasure d : Meas
ure X)
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.hausdorffMeasure_real`：hausdorffMeasure_real : (μH[1] : Me
asure Real) = volume
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
（共 45 条，此处仅展示前 30 条）
-/
theorem hausdorffMeasure_smul_right_image [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (v : E) (s : Set ℝ) :
    μH[1] ((fun r => r • v) '' s) = ‖v‖₊ • μH[1] s := by
  obtain rfl | hv := eq_or_ne v 0
  · have := nullSingletonClass_hausdorff E one_pos
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [hs]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  -- break lineMap into pieces
  suffices
      μH[1] ((‖v‖ • ·) '' LinearMap.toSpanSingleton ℝ E (‖v‖⁻¹ • v) '' s) = ‖v‖₊ • μH[1] s by
    simpa only [Set.image_image, smul_comm (norm _), inv_smul_smul₀ hn,
      LinearMap.toSpanSingleton_apply] using this
  have iso_smul : Isometry (LinearMap.toSpanSingleton ℝ E (‖v‖⁻¹ • v)) := by
    refine AddMonoidHomClass.isometry_of_norm _ fun x => (norm_smul _ _).trans ?_
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn, mul_one, LinearMap.id_apply]
  rw [Set.image_smul, Measure.hausdorffMeasure_smul₀ zero_le_one hn, nnnorm_norm,
      NNReal.rpow_one, iso_smul.hausdorffMeasure_image (Or.inl <| zero_le_one' ℝ)]

section NormedFieldAffine

variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace P]
variable [MetricSpace P] [NormedAddTorsor E P] [BorelSpace P]

/-- Scaling by `c` around `x` scales the measure by `‖c‖₊ ^ d`. -/
/-
**MeasureTheory.hausdorffMeasure_homothety_image** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：hausdorffMeasure_homothety_image {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} 
(hc : c != 0) (s : Set P) : μH[d] (AffineMap.homothety x c '' s) = ‖c‖₊ ^ d • μH
[d] s
参数：hd : 0 <= d；x : P；hc : c != 0；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsometryEquiv.hausdorffMeasure_image`：hausdorffMeasure_image (e : X ≃ᵢ Y
) (d : Real) (s : Set X) : μH[d] (e '' s) = μH[d] s
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_smul₀`：MeasureTheory.Measure.haus
dorffMeasure_smul₀ {𝕜 E : Type*} [NormedAddCommGroup E] [NormedDivisionRing 𝕜] [
Module 𝕜 E] [NormSMulClass 𝕜 E] [M…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s

--- 原说明 ---
Scaling by `c` around `x` scales the measure by `‖c‖₊ ^ d`.
-/
theorem hausdorffMeasure_homothety_image {d : ℝ} (hd : 0 ≤ d) (x : P) {c : 𝕜} (hc : c ≠ 0)
    (s : Set P) : μH[d] (AffineMap.homothety x c '' s) = ‖c‖₊ ^ d • μH[d] s := by
  suffices
    μH[d] (IsometryEquiv.vaddConst x '' (c • ·) '' (IsometryEquiv.vaddConst x).symm '' s) =
      ‖c‖₊ ^ d • μH[d] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image, Set.image_smul, Measure.hausdorffMeasure_smul₀ hd hc,
    IsometryEquiv.hausdorffMeasure_image]
/-
**MeasureTheory.hausdorffMeasure_homothety_preimage** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：hausdorffMeasure_homothety_preimage {d : Real} (hd : 0 <= d) (x : P) {c : 
𝕜} (hc : c != 0) (s : Set P) : μH[d] (AffineMap.homothety x c ⁻¹' s) = ‖c‖₊⁻¹ ^ 
d • μH[d] s
参数：hd : 0 <= d；x : P；hc : c != 0；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.image_symm`：image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.sy
mm '' s = f ⁻¹' s
· 使用定理 `AffineEquiv.coe_homothetyUnitsMulHom_apply_symm`：coe_homothetyUnitsMulHo
m_apply_symm (p : P) (t : Rˣ) : ((homothetyUnitsMulHom p t).symm : P -> P) = Aff
ineMap.homothety p (↑t⁻¹ : R)
· 使用定理 `MeasureTheory.hausdorffMeasure_homothety_image`：hausdorffMeasure_homothe
ty_image {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0) (s : Set P) : μH
[d] (AffineMap.homothety x c '' s) =…
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
-/
theorem hausdorffMeasure_homothety_preimage {d : ℝ} (hd : 0 ≤ d) (x : P) {c : 𝕜} (hc : c ≠ 0)
    (s : Set P) : μH[d] (AffineMap.homothety x c ⁻¹' s) = ‖c‖₊⁻¹ ^ d • μH[d] s := by
  change μH[d] (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 c hc) ⁻¹' s) = _
  rw [← AffineEquiv.image_symm, AffineEquiv.coe_homothetyUnitsMulHom_apply_symm,
    hausdorffMeasure_homothety_image hd x (_ : 𝕜ˣ).isUnit.ne_zero, Units.val_inv_eq_inv_val,
    Units.val_mk0, nnnorm_inv]
/-
**MeasureTheory.map_homothety_hausdorffMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：map_homothety_hausdorffMeasure {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (h
c : c != 0) : Measure.map (AffineMap.homothety x c) μH[d] = ‖c‖₊⁻¹ ^ d • μH[d]
参数：hd : 0 <= d；x : P；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `AffineMap.homothety_continuous`：homothety_continuous (x : P) (t : R) : C
ontinuous homothety x t
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.hausdorffMeasure_homothety_preimage`：hausdorffMeasure_homo
thety_preimage {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0) (s : Set P
) : μH[d] (AffineMap.homothety x c ⁻¹' …
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
-/
theorem map_homothety_hausdorffMeasure {d : ℝ} (hd : 0 ≤ d) (x : P) {c : 𝕜} (hc : c ≠ 0) :
    Measure.map (AffineMap.homothety x c) μH[d] = ‖c‖₊⁻¹ ^ d • μH[d] := by
  ext s hs
  rw [Measure.map_apply (AffineMap.homothety_continuous x c).measurable hs,
    hausdorffMeasure_homothety_preimage hd x hc s, Measure.smul_apply]

end NormedFieldAffine

section RealAffine

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace P]
variable [MetricSpace P] [NormedAddTorsor E P] [BorelSpace P]

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping a set of reals along a line segment scales the measure by the length of a segment.

This is an auxiliary result used to prove `hausdorffMeasure_affineSegment`. -/
/-
**MeasureTheory.hausdorffMeasure_lineMap_image** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：hausdorffMeasure_lineMap_image (x y : P) (s : Set Real) : μH[1] (AffineMap
.lineMap x y '' s) = nndist x y • μH[1] s
参数：x y : P；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsometryEquiv.hausdorffMeasure_image`：hausdorffMeasure_image (e : X ≃ᵢ Y
) (d : Real) (s : Set X) : μH[d] (e '' s) = μH[d] s
· 使用定理 `MeasureTheory.hausdorffMeasure_smul_right_image`：hausdorffMeasure_smul_r
ight_image [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [Bore
lSpace E] (v : E) (s : Set Real) : μH…
· 使用定理 `nndist_eq_nnnorm_vsub'`：nndist_eq_nnnorm_vsub' (x y : P) : nndist x y = 
‖y -ᵥ x‖₊
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s

--- 原说明 ---
Mapping a set of reals along a line segment scales the measure by the length of 
a segment.

This is an auxiliary result used to prove `hausdorffMeasure_affineSegment`.
-/
theorem hausdorffMeasure_lineMap_image (x y : P) (s : Set ℝ) :
    μH[1] (AffineMap.lineMap x y '' s) = nndist x y • μH[1] s := by
  suffices μH[1] (IsometryEquiv.vaddConst x '' (· • (y -ᵥ x)) '' s) = nndist x y • μH[1] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image, hausdorffMeasure_smul_right_image,
    nndist_eq_nnnorm_vsub' E]

set_option backward.isDefEq.respectTransparency.types false in
/-- The measure of a segment is the distance between its endpoints. -/
@[simp]
/-
**MeasureTheory.hausdorffMeasure_affineSegment** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：hausdorffMeasure_affineSegment (x y : P) : μH[1] (affineSegment Real x y) 
= edist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSegment.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst
 : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root
_.Module…
· 使用定理 `MeasureTheory.hausdorffMeasure_lineMap_image`：hausdorffMeasure_lineMap_i
mage (x y : P) (s : Set Real) : μH[1] (AffineMap.lineMap x y '' s) = nndist x y 
• μH[1] s
· 使用定理 `MeasureTheory.hausdorffMeasure_real`：hausdorffMeasure_real : (μH[1] : Me
asure Real) = volume
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y

--- 原说明 ---
The measure of a segment is the distance between its endpoints.
-/
theorem hausdorffMeasure_affineSegment (x y : P) : μH[1] (affineSegment ℝ x y) = edist x y := by
  rw [affineSegment, hausdorffMeasure_lineMap_image, hausdorffMeasure_real, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one, ← Algebra.algebraMap_eq_smul_one]
  exact (edist_nndist _ _).symm

end RealAffine

/-- The measure of a segment is the distance between its endpoints. -/
@[simp]
/-
**MeasureTheory.hausdorffMeasure_segment** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：hausdorffMeasure_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace R
eal E] [MeasurableSpace E] [BorelSpace E] (x y : E) : μH[1] (segment Real x y) =
 edist x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSegment_eq_segment`：affineSegment_eq_segment (x y : V) : affineSeg
ment R x y = segment R x y
· 使用定理 `MeasureTheory.hausdorffMeasure_affineSegment`：hausdorffMeasure_affineSeg
ment (x y : P) : μH[1] (affineSegment Real x y) = edist x y

--- 原说明 ---
The measure of a segment is the distance between its endpoints.
-/
theorem hausdorffMeasure_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (x y : E) : μH[1] (segment ℝ x y) = edist x y := by
  rw [← affineSegment_eq_segment, hausdorffMeasure_affineSegment]

/--
Let `s` be a subset of `𝕜`-inner product space, and `K` a subspace. Then the `d`-dimensional
Hausdorff measure of the orthogonal projection of `s` onto `K` is less than or equal to the
`d`-dimensional Hausdorff measure of `s`.
-/
/-
**MeasureTheory.hausdorffMeasure_orthogonalProjectionOnto_le** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：hausdorffMeasure_orthogonalProjectionOnto_le [RCLike 𝕜] [NormedAddCommGrou
p E] [InnerProductSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E] (K : Submodule 𝕜
 E) [K.HasOrthogonalProjection] (d : Real) (s : Set E) (hs : 0 <= d) : μH[d] (K.
orthogonalProjectionOnto '' s) <= μH[d] s
参数：K : Submodule 𝕜 E；d : Real；s : Set E；hs : 0 <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LipschitzWith.hausdorffMeasure_image_le`：hausdorffMeasure_image_le (h : 
LipschitzWith K f) {d : Real} (hd : 0 <= d) (s : Set X) : μH[d] (f '' s) <= (K :
 Real>=0∞) ^ d * μH[d] s
· 使用定理 `Submodule.lipschitzWith_orthogonalProjectionOnto`：lipschitzWith_orthogon
alProjectionOnto : LipschitzWith 1 (orthogonalProjectionOnto K)

--- 原说明 ---
Let `s` be a subset of `𝕜`-inner product space, and `K` a subspace. Then the `d`
-dimensional
Hausdorff measure of the orthogonal projection of `s` onto `K` is less than or e
qual to the
`d`-dimensional Hausdorff measure of `s`.
-/
theorem hausdorffMeasure_orthogonalProjectionOnto_le [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (d : ℝ) (s : Set E) (hs : 0 ≤ d) :
    μH[d] (K.orthogonalProjectionOnto '' s) ≤ μH[d] s := by
  simpa using K.lipschitzWith_orthogonalProjectionOnto.hausdorffMeasure_image_le hs s

@[deprecated (since := "2026-05-05")] alias hausdorffMeasure_orthogonalProjection_le :=
  hausdorffMeasure_orthogonalProjectionOnto_le

end Geometric

end MeasureTheory

