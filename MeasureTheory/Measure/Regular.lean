/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Regular measures

A measure is `OuterRegular` if the measure of any measurable set `A` is the infimum of `μ U` over
all open sets `U` containing `A`.

A measure is `WeaklyRegular` if it satisfies the following properties:
* it is outer regular;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all closed sets `F` contained in `U`.

A measure is `Regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular;
* it is inner regular for open sets with respect to compact closed sets: the measure of any open
  set `U` is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `InnerRegular` if it is inner regular for measurable sets with respect to compact
sets: the measure of any measurable set `s` is the supremum of `μ K` over all compact
sets contained in `s`.

A measure is `InnerRegularCompactLTTop` if it is inner regular for measurable sets of finite
measure with respect to compact sets: the measure of any measurable set `s` is the supremum
of `μ K` over all compact sets contained in `s`.

There is a reason for this zoo of regularity classes:
* A finite measure on a metric space is always weakly regular. Therefore, in probability theory,
  weakly regular measures play a prominent role.
* In locally compact topological spaces, there are two competing notions of Radon measures: the
  ones that are regular, and the ones that are inner regular. For any of these two notions, there is
  a Riesz representation theorem, and an existence and uniqueness statement for the Haar measure in
  locally compact topological groups. The two notions coincide in sigma-compact spaces, but they
  differ in general, so it is worth having the two of them.
* Both notions of Haar measure satisfy the weaker notion `InnerRegularCompactLTTop`, so it is worth
  trying to express theorems using this weaker notion whenever possible, to make sure that it
  applies to both Haar measures simultaneously.

While traditional textbooks on measure theory on locally compact spaces emphasize regular measures,
more recent textbooks emphasize that inner regular Haar measures are better behaved than regular
Haar measures, so we will develop both notions.

The five conditions above are registered as typeclasses for a measure `μ`, and implications between
them are recorded as instances. For example, in a Hausdorff topological space, regularity implies
weak regularity. Also, regularity or inner regularity both imply `InnerRegularCompactLTTop`.
In a regular locally compact finite measure space, then regularity, inner regularity
and `InnerRegularCompactLTTop` are all equivalent.

In order to avoid code duplication, we also define a measure `μ` to be `InnerRegularWRT` for sets
satisfying a predicate `q` with respect to sets satisfying a predicate `p` if for any set
`U ∈ {U | q U}` and a number `r < μ U` there exists `F ⊆ U` such that `p F` and `r < μ F`.

There are two main nontrivial results in the development below:
* `InnerRegularWRT.measurableSet_of_isOpen` shows that, for an outer regular measure, inner
  regularity for open sets with respect to compact sets or closed sets implies inner regularity for
  all measurable sets of finite measure (with respect to compact sets or closed sets respectively).
* `InnerRegularWRT.weaklyRegular_of_finite` shows that a finite measure which is inner regular for
  open sets with respect to closed sets (for instance a finite measure on a metric space) is weakly
  regular.

All other results are deduced from these ones.

Here is an example showing how regularity and inner regularity may differ even on locally compact
spaces. Consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second
one the usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal
to Lebesgue measure on each vertical fiber. Let us consider the regular version of Haar measure.
Then the set `ℝ × {0}` has infinite measure (by outer regularity), but any compact set it contains
has zero measure (as it is finite). In fact, this set only contains subsets with measure zero or
infinity. The inner regular version of Haar measure, on the other hand, gives zero mass to the
set `ℝ × {0}`.

Another interesting example is the sum of the Dirac masses at rational points on the real line.
It is a σ-finite measure on a locally compact metric space, but it is not outer regular: for
outer regularity, one needs additional locally finite assumptions. On the other hand, it is
inner regular.

Several authors require both regularity and inner regularity for their measures. We have opted
for the more fine-grained definitions above as they apply more generally.

## Main definitions

* `MeasureTheory.Measure.OuterRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is outer regular.
* `MeasureTheory.Measure.Regular μ`: a typeclass registering that a measure `μ` on a topological
  space is regular.
* `MeasureTheory.Measure.WeaklyRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is weakly regular.
* `MeasureTheory.Measure.InnerRegularWRT μ p q`: a non-typeclass predicate saying that a measure `μ`
  is inner regular for sets satisfying `q` with respect to sets satisfying `p`.
* `MeasureTheory.Measure.InnerRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is inner regular for measurable sets with respect to compact sets.
* `MeasureTheory.Measure.InnerRegularCompactLTTop μ`: a typeclass registering that a measure `μ`
  on a topological space is inner regular for measurable sets of finite measure with respect to
  compact sets.

## Main results

### Outer regular measures

* `Set.measure_eq_iInf_isOpen` asserts that, when `μ` is outer regular, the measure of a
  set is the infimum of the measure of open sets containing it.
* `Set.exists_isOpen_lt_of_lt` asserts that, when `μ` is outer regular, for every set `s`
  and `r > μ s` there exists an open superset `U ⊇ s` of measure less than `r`.
* push forward of an outer regular measure is outer regular, and scalar multiplication of a regular
  measure by a finite number is outer regular.

### Weakly regular measures

* `IsOpen.measure_eq_iSup_isClosed` asserts that the measure of an open set is the supremum of
  the measure of closed sets it contains.
* `IsOpen.exists_lt_isClosed`: for an open set `U` and `r < μ U`, there exists a closed `F ⊆ U`
  of measure greater than `r`;
* `MeasurableSet.measure_eq_iSup_isClosed_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of closed sets it contains.
* `MeasurableSet.exists_lt_isClosed_of_ne_top` and `MeasurableSet.exists_isClosed_lt_add`:
  a measurable set of finite measure can be approximated by a closed subset (stated as
  `r < μ F` and `μ s < μ F + ε`, respectively).
* `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure` is an
  instance registering that a finite measure on a metric space is weakly regular (in fact, a
  pseudometrizable space is enough);
* `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite`
  is an instance registering that a locally finite measure on a second countable metric space (or
  even a pseudometrizable space) is weakly regular.

### Regular measures

* `IsOpen.measure_eq_iSup_isCompact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains.
* `IsOpen.exists_lt_isCompact`: for an open set `U` and `r < μ U`, there exists a compact `K ⊆ U`
  of measure greater than `r`;
* `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` is an
  instance registering that a locally finite measure on a `σ`-compact metric space is regular (in
  fact, an emetric space is enough).

### Inner regular measures

* `MeasurableSet.measure_eq_iSup_isCompact` asserts that the measure of a measurable set is the
  supremum of the measure of compact sets it contains.
* `MeasurableSet.exists_lt_isCompact`: for a measurable set `s` and `r < μ s`, there exists a
  compact `K ⊆ s` of measure greater than `r`;

### Inner regular measures for finite measure sets with respect to compact sets

* `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains.
* `MeasurableSet.exists_lt_isCompact_of_ne_top` and `MeasurableSet.exists_isCompact_lt_add`:
  a measurable set of finite measure can be approximated by a compact subset (stated as
  `r < μ K` and `μ s < μ K + ε`, respectively).

## Implementation notes

The main nontrivial statement is `MeasureTheory.Measure.InnerRegular.weaklyRegular_of_finite`,
expressing that in a finite measure space, if every open set can be approximated from inside by
closed sets, then the measure is in fact weakly regular. To prove that we show that any measurable
set can be approximated from inside by closed sets and from outside by open sets. This statement is
proved by measurable induction, starting from open sets and checking that it is stable by taking
complements (this is the point of this condition, being symmetrical between inside and outside) and
countable disjoint unions.

Once this statement is proved, one deduces results for `σ`-finite measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular, using
again the same statement).

For non-Hausdorff spaces, one may argue whether the right condition for inner regularity is with
respect to compact sets, or to compact closed sets. For instance,
[Fremlin, *Measure Theory* (volume 4, 411J)][fremlin_vol4] considers measures which are inner
regular with respect to compact closed sets (and calls them *tight*). However, since most of the
literature uses mere compact sets, we have chosen to follow this convention. It doesn't make a
difference in Hausdorff spaces, of course. In locally compact topological groups, the two
conditions coincide, since if a compact set `k` is contained in a measurable set `u`, then the
closure of `k` is a compact closed set still contained in `u`, see
`IsCompact.closure_subset_of_measurableSet_of_group`.

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]

[Bogachev, Measure Theory, volume 2, Theorem 7.11.1][bogachev2007]
-/

@[expose] public section

open Set Filter ENNReal NNReal TopologicalSpace
open scoped symmDiff Topology

namespace MeasureTheory

namespace Measure

/-- We say that a measure `μ` is *inner regular* with respect to predicates `p q : Set α → Prop`,
if for every `U` such that `q U` and `r < μ U`, there exists a subset `K ⊆ U` satisfying `p K`
of measure greater than `r`.

This definition is used to prove some facts about regular and weakly regular measures without
repeating the proofs. -/
/-
**MeasureTheory.Measure.InnerRegularWRT** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：InnerRegularWRT {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α -
> Prop)
参数：μ : Measure α；p q : Set α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a measure `μ` is *inner regular* with respect to predicates `p q : S
et α → Prop`,
if for every `U` such that `q U` and `r < μ U`, there exists a subset `K ⊆ U` sa
tisfying `p K`
of measure greater than `r`.

This definition is used to prove some facts about regular and weakly regular mea
sures without
repeating the proofs.
-/
def InnerRegularWRT {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α → Prop) :=
  ∀ ⦃U⦄, q U → ∀ r < μ U, ∃ K, K ⊆ U ∧ p K ∧ r < μ K

namespace InnerRegularWRT

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : Set α → Prop} {U : Set α}
  {ε : ℝ≥0∞}

/-
**MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：measure_eq_iSup (H : InnerRegularWRT μ p q) (hU : q U) : μ U = ⨆ (K) (_ : 
K subseteq U) (_ : p K), μ K
参数：H : InnerRegularWRT μ p q；hU : q U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
-/
theorem measure_eq_iSup (H : InnerRegularWRT μ p q) (hU : q U) :
    μ U = ⨆ (K) (_ : K ⊆ U) (_ : p K), μ K := by
  refine
    le_antisymm (le_of_forall_lt fun r hr => ?_) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr
/-
**MeasureTheory.Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：eq_of_innerRegularWRT_of_forall_eq {ν : Measure α} (hμ : μ.InnerRegularWRT
 p q) (hν : ν.InnerRegularWRT p q) (hμν : forall U, p U -> μ U = ν U) {U : Set α
} (hU : q U) : μ U = ν U
参数：hμ : μ.InnerRegularWRT p q；hν : ν.InnerRegularWRT p q；hμν : forall U, p U -> 
μ U = ν U；hU : q U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup`：measure_eq_iSup (
H : InnerRegularWRT μ p q) (hU : q U) : μ U = ⨆ (K) (_ : K subseteq U) (_ : p K)
, μ K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem eq_of_innerRegularWRT_of_forall_eq {ν : Measure α} (hμ : μ.InnerRegularWRT p q)
    (hν : ν.InnerRegularWRT p q) (hμν : ∀ U, p U → μ U = ν U)
    {U : Set α} (hU : q U) : μ U = ν U := by
  rw [hμ.measure_eq_iSup hU, hν.measure_eq_iSup hU]
  congr! 4 with t _ ht2
  exact hμν t ht2
/-
**MeasureTheory.Measure.InnerRegularWRT.exists_subset_lt_add** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：exists_subset_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμ
U : μ U != ∞) (hε : ε != 0) : exists K, K subseteq U ∧ p K ∧ μ U < μ K + ε
参数：H : InnerRegularWRT μ p q；h0 : p ∅；hU : q U；hμU : μ U != ∞；hε : ε != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `ENNReal.lt_add_of_sub_lt_right`：∀ {a b c : ENNReal}, a ≠ ⊤ ∨ c ≠ ⊤ → a -
 c < b → a < b + c
-/
theorem exists_subset_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞)
    (hε : ε ≠ 0) : ∃ K, K ⊆ U ∧ p K ∧ μ U < μ K + ε := by
  rcases eq_or_ne (μ U) 0 with h₀ | h₀
  · refine ⟨∅, empty_subset _, h0, ?_⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩
/-
**MeasureTheory.Measure.InnerRegularWRT.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.InnerRegularWRT`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {pa qa : Set α → Prop},   μ.InnerR
egularWRT pa qa →     ∀ {f : α → β},       AEMeasurable f μ →         ∀ {pb qb :
 Set β → Prop},           (∀ (U : Set β), qb U → qa (f ⁻¹' U)) →             (∀ 
(K : Set α), pa K → pb (f '' K)) →               (∀ (U : Set β), qb U → Measurab
leSet U) → (MeasureTheory.Measure.map f μ).InnerRegularWRT pb qb
参数：∀ (U : Set β), qb U → qa (f ⁻¹' U)；∀ (K : Set α), pa K → pb (f '' K)；∀ (U : S
et β), qb U → MeasurableSet U；MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.Measure.le_map_apply_image`：le_map_apply_image {f : α -> β
} (hf : AEMeasurable f μ) (s : Set α) : μ s <= μ.map f (f '' s)
-/
protected theorem map {α β} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {pa qa : Set α → Prop}
    (H : InnerRegularWRT μ pa qa) {f : α → β} (hf : AEMeasurable f μ) {pb qb : Set β → Prop}
    (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K))
    (hB₂ : ∀ U, qb U → MeasurableSet U) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [map_apply_of_aemeasurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  exact hK.trans_le (le_map_apply_image hf _)
/-
**MeasureTheory.Measure.InnerRegularWRT.map'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure.InnerRegularWRT`。
形式化陈述：map' {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa 
: Set α -> Prop} (H : InnerRegularWRT μ pa qa) (f : α ≃ᵐ β) {pb qb : Set β -> Pr
op} (hAB : forall U, qb U -> qa (f ⁻¹' U)) (hAB' : forall K, pa K -> pb (f '' K)
) : InnerRegularWRT (map f μ) pb qb
参数：H : InnerRegularWRT μ pa qa；f : α ≃ᵐ β；hAB : forall U, qb U -> qa (f ⁻¹' U)；h
AB' : forall K, pa K -> pb (f '' K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `MeasurableEquiv.preimage_image`：preimage_image (e : α ≃ᵐ β) (s : Set α) 
: e ⁻¹' e '' s = s
-/
theorem map' {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α → Prop}
    (H : InnerRegularWRT μ pa qa) (f : α ≃ᵐ β) {pb qb : Set β → Prop}
    (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K)) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [f.map_apply U] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  rwa [f.map_apply, f.preimage_image]
/-
**MeasureTheory.Measure.InnerRegularWRT.comap** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.InnerRegularWRT`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MeasurableSpace α] {mβ : Measurabl
eSpace β} {μ : MeasureTheory.Measure β}   {pa qa : Set α → Prop} {pb qb : Set β 
→ Prop},   μ.InnerRegularWRT pb qb →     ∀ {f : α → β},       MeasurableEmbeddin
g f →         (∀ (U : Set α), qa U → qb (f '' U)) →           (∀ K ⊆ Set.range f
, pb K → pa (f ⁻¹' K)) → (MeasureTheory.Measure.comap f μ).InnerRegularWRT pa qa
参数：∀ (U : Set α), qa U → qb (f '' U)；∀ K ⊆ Set.range f, pb K → pa (f ⁻¹' K)；Meas
ureTheory.Measure.comap f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
-/
protected theorem comap {α β} [MeasurableSpace α] {mβ : MeasurableSpace β}
    {μ : Measure β} {pa qa : Set α → Prop} {pb qb : Set β → Prop}
    (H : InnerRegularWRT μ pb qb) {f : α → β} (hf : MeasurableEmbedding f)
    (hAB : ∀ U, qa U → qb (f '' U)) (hAB' : ∀ K ⊆ range f, pb K → pa (f ⁻¹' K)) :
    (μ.comap f).InnerRegularWRT pa qa := by
  intro U hU r hr
  rw [hf.comap_apply] at hr
  obtain ⟨K, hKU, hK, hμU⟩ := H (hAB U hU) r hr
  have hKrange := hKU.trans (image_subset_range _ _)
  refine ⟨f ⁻¹' K, ?_, hAB' K hKrange hK, ?_⟩
  · rw [← hf.injective.preimage_image U]; exact preimage_mono hKU
  · rwa [hf.comap_apply, image_preimage_eq_iff.mpr hKrange]
/-
**MeasureTheory.Measure.InnerRegularWRT.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure.InnerRegularWRT`。
形式化陈述：smul (H : InnerRegularWRT μ p q) (c : Real>=0∞) : InnerRegularWRT (c • μ) 
p q
参数：H : InnerRegularWRT μ p q；c : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup`：measure_eq_iSup (
H : InnerRegularWRT μ p q) (hU : q U) : μ U = ⨆ (K) (_ : K subseteq U) (_ : p K)
, μ K
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
-/
theorem smul (H : InnerRegularWRT μ p q) (c : ℝ≥0∞) : InnerRegularWRT (c • μ) p q := by
  intro U hU r hr
  rw [smul_apply, H.measure_eq_iSup hU, smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using! hr
/-
**MeasureTheory.Measure.InnerRegularWRT.trans** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.InnerRegularWRT`。
形式化陈述：trans {q' : Set α -> Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularW
RT μ q q') : InnerRegularWRT μ p q'
参数：H : InnerRegularWRT μ p q；H' : InnerRegularWRT μ q q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem trans {q' : Set α → Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') :
    InnerRegularWRT μ p q' := by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩
/-
**MeasureTheory.Measure.InnerRegularWRT.rfl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.InnerRegularWRT`。
形式化陈述：rfl {p : Set α -> Prop} : InnerRegularWRT μ p p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem rfl {p : Set α → Prop} : InnerRegularWRT μ p p :=
  fun U hU _r hr ↦ ⟨U, Subset.rfl, hU, hr⟩
/-
**MeasureTheory.Measure.InnerRegularWRT.of_imp** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.InnerRegularWRT`。
形式化陈述：of_imp (h : forall s, q s -> p s) : InnerRegularWRT μ p q
参数：h : forall s, q s -> p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem of_imp (h : ∀ s, q s → p s) : InnerRegularWRT μ p q :=
  fun U hU _ hr ↦ ⟨U, Subset.rfl, h U hU, hr⟩
/-
**MeasureTheory.Measure.InnerRegularWRT.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure.InnerRegularWRT`。
形式化陈述：mono {p' q' : Set α -> Prop} (H : InnerRegularWRT μ p q) (h : forall s, q'
 s -> q s) (h' : forall s, p s -> p' s) : InnerRegularWRT μ p' q'
参数：H : InnerRegularWRT μ p q；h : forall s, q' s -> q s；h' : forall s, p s -> p' 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.trans`：trans {q' : Set α -> Prop} 
(H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') : InnerRegularWRT μ p 
q'
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.of_imp`：of_imp (h : forall s, q s 
-> p s) : InnerRegularWRT μ p q
-/
theorem mono {p' q' : Set α → Prop} (H : InnerRegularWRT μ p q)
    (h : ∀ s, q' s → q s) (h' : ∀ s, p s → p' s) : InnerRegularWRT μ p' q' :=
  of_imp h' |>.trans H |>.trans (of_imp h)

end InnerRegularWRT

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}

section Classes

variable [TopologicalSpace α]

/-- A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measurable set `A`.

This definition implies the same equality for any (not necessarily measurable) set, see
`Set.measure_eq_iInf_isOpen`. -/
/-
**MeasureTheory.Measure.OuterRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → [TopologicalSpace α] → Measu
reTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measura
ble set `A`.

This definition implies the same equality for any (not necessarily measurable) s
et, see
`Set.measure_eq_iInf_isOpen`.
-/
class OuterRegular (μ : Measure α) : Prop where
  protected outerRegular :
    ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r > μ A, ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < r

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open. -/
/-
**MeasureTheory.Measure.Regular** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → [TopologicalSpace α] → Measu
reTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open.
-/
class Regular (μ : Measure α) : Prop extends IsFiniteMeasureOnCompacts μ, OuterRegular μ where
  innerRegular : InnerRegularWRT μ IsCompact IsOpen

/-- A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U closed}` for `U` open. -/
/-
**MeasureTheory.Measure.WeaklyRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → [TopologicalSpace α] → Measu
reTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U closed}` for `U` open.
-/
class WeaklyRegular (μ : Measure α) : Prop extends OuterRegular μ where
  protected innerRegular : InnerRegularWRT μ IsClosed IsOpen

/-- A measure `μ` is inner regular if, for any measurable set `s`, then
`μ(s) = sup {μ(K) | K ⊆ s compact}`. -/
/-
**MeasureTheory.Measure.InnerRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → [TopologicalSpace α] → Measu
reTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is inner regular if, for any measurable set `s`, then
`μ(s) = sup {μ(K) | K ⊆ s compact}`.
-/
class InnerRegular (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact MeasurableSet

/-- A measure `μ` is inner regular for finite measure sets with respect to compact sets:
for any measurable set `s` with finite measure, then `μ(s) = sup {μ(K) | K ⊆ s compact}`.
The main interest of this class is that it is satisfied for both natural Haar measures (the
regular one and the inner regular one). -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop** 是 Mathlib 中的一个归纳类型，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → [TopologicalSpace α] → Measu
reTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is inner regular for finite measure sets with respect to compact s
ets:
for any measurable set `s` with finite measure, then `μ(s) = sup {μ(K) | K ⊆ s c
ompact}`.
The main interest of this class is that it is satisfied for both natural Haar me
asures (the
regular one and the inner regular one).
-/
class InnerRegularCompactLTTop (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞)

-- see Note [lower instance priority]
/-- A regular measure is weakly regular in an R₁ space. -/
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular measure is weakly regular in an R₁ space.
-/
instance (priority := 100) Regular.weaklyRegular [R1Space α] [Regular μ] :
    WeaklyRegular μ where
  innerRegular := fun _U hU r hr ↦
    let ⟨K, KU, K_comp, hK⟩ := Regular.innerRegular hU r hr
    ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
      hK.trans_le (measure_mono subset_closure)⟩

end Classes

namespace OuterRegular

variable [TopologicalSpace α]

/-
**MeasureTheory.Measure.OuterRegular.zero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure.OuterRegular`。
形式化陈述：zero : OuterRegular (0 : Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
instance zero : OuterRegular (0 : Measure α) :=
  ⟨fun A _ _r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩

/-- Given `r` larger than the measure of a set `A`, there exists an open superset of `A` with
measure less than `r`. -/
/-
**MeasureTheory.Measure.OuterRegular._root_.Set.exists_isOpen_lt_of_lt** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.Measure.OuterRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `r` larger than the measure of a set `A`, there exists an open superset of
 `A` with
measure less than `r`.
-/
theorem _root_.Set.exists_isOpen_lt_of_lt [OuterRegular μ] (A : Set α) (r : ℝ≥0∞) (hr : μ A < r) :
    ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < r := by
  rcases OuterRegular.outerRegular (measurableSet_toMeasurable μ A) r
      (by rwa [measure_toMeasurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_toMeasurable _ _).trans hAU, hUo, hU⟩

/-- For an outer regular measure, the measure of a set is the infimum of the measures of open sets
containing it. -/
/-
**MeasureTheory.Measure.OuterRegular._root_.Set.measure_eq_iInf_isOpen** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.Measure.OuterRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an outer regular measure, the measure of a set is the infimum of the measure
s of open sets
containing it.
-/
theorem _root_.Set.measure_eq_iInf_isOpen (A : Set α) (μ : Measure α) [OuterRegular μ] :
    μ A = ⨅ (U : Set α) (_ : A ⊆ U) (_ : IsOpen U), μ U := by
  refine le_antisymm (le_iInf₂ fun s hs => le_iInf fun _ => μ.mono hs) ?_
  refine le_of_forall_gt fun r hr => ?_
  simpa only [iInf_lt_iff, exists_prop] using A.exists_isOpen_lt_of_lt r hr
/-
**MeasureTheory.Measure.OuterRegular._root_.Set.exists_isOpen_lt_add** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure.OuterRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.exists_isOpen_lt_add [OuterRegular μ] (A : Set α) (hA : μ A ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < μ A + ε :=
  A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)
/-
**MeasureTheory.Measure.OuterRegular._root_.Set.exists_isOpen_le_add** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure.OuterRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.exists_isOpen_le_add (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U ≤ μ A + ε := by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_isOpen_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩
/-
**MeasureTheory.Measure.OuterRegular._root_.MeasurableSet.exists_isOpen_sdiff_lt
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.OuterRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableSet.exists_isOpen_sdiff_lt [OuterRegular μ] {A : Set α}
    (hA : MeasurableSet A) (hA' : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ A) < ε := by
  rcases A.exists_isOpen_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_sdiff_lt_of_lt_add hA.nullMeasurableSet hAU hA' hU

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isOpen_diff_lt := _root_.MeasurableSet.exists_isOpen_sdiff_lt
/-
**MeasureTheory.Measure.OuterRegular.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.OuterRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topol
ogicalSpace α] [OpensMeasurableSpace α]   [inst_3 : MeasurableSpace β] [inst_4 :
 TopologicalSpace β] [BorelSpace β] (f : α ≃ₜ β) (μ : MeasureTheory.Measure α)  
 [μ.OuterRegular], (MeasureTheory.Measure.map (⇑f) μ).OuterRegular
参数：f : α ≃ₜ β；μ : MeasureTheory.Measure α；MeasureTheory.Measure.map (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_isOpen_lt_of_lt`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRegular]   (
A : Set α) (r : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Homeomorph.measurable`：∀ {α : Type u_1} {γ : Type u_3} [inst : Topologic
alSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]   [inst_3 : Top
ologicalSpa…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Homeomorph.preimage_image`：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻
¹' h '' s = s
-/
protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) (μ : Measure α) [OuterRegular μ] :
    (Measure.map f μ).OuterRegular := by
  refine ⟨fun A hA r hr => ?_⟩
  rw [map_apply f.measurable hA, ← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, ?_⟩
  rwa [map_apply f.measurable this.measurableSet, f.preimage_symm, f.preimage_image]
/-
**MeasureTheory.Measure.OuterRegular.comap'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.OuterRegular`。
形式化陈述：comap' {mβ : MeasurableSpace β} [TopologicalSpace β] (μ : Measure β) [Oute
rRegular μ] {f : α -> β} (f_cont : Continuous f) (f_me : MeasurableEmbedding f) 
: (μ.comap f).OuterRegular where outerRegular A hA r hr
参数：μ : Measure β；f_cont : Continuous f；f_me : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.OuterRegular.outerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.OuterRegular] ⦃A : Set α…
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `ge_iff_le`：∀ {α : Type u_1} [inst : LE α] {x y : α}, x ≥ y ↔ y ≤ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem comap' {mβ : MeasurableSpace β} [TopologicalSpace β] (μ : Measure β) [OuterRegular μ]
    {f : α → β} (f_cont : Continuous f) (f_me : MeasurableEmbedding f) :
    (μ.comap f).OuterRegular where
  outerRegular A hA r hr := by
    rw [f_me.comap_apply] at hr
    obtain ⟨U, hUA, Uopen, hμU⟩ := OuterRegular.outerRegular (f_me.measurableSet_image' hA) r hr
    refine ⟨f ⁻¹' U, by rwa [ge_iff_le, ← image_subset_iff], Uopen.preimage f_cont, ?_⟩
    rw [f_me.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt hμU
/-
**MeasureTheory.Measure.OuterRegular.comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.OuterRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topol
ogicalSpace α] [BorelSpace α]   {mβ : MeasurableSpace β} [inst_3 : TopologicalSp
ace β] [BorelSpace β] (μ : MeasureTheory.Measure β) [μ.OuterRegular]   (f : α ≃ₜ
 β), (MeasureTheory.Measure.comap (⇑f) μ).OuterRegular
参数：μ : MeasureTheory.Measure β；f : α ≃ₜ β；MeasureTheory.Measure.comap (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.OuterRegular.comap'`：comap' {mβ : MeasurableSpace 
β} [TopologicalSpace β] (μ : Measure β) [OuterRegular μ] {f : α -> β} (f_cont : 
Continuous f) (f_me : Measurabl…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
-/
protected theorem comap [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
    (μ : Measure β) [OuterRegular μ] (f : α ≃ₜ β) : (μ.comap f).OuterRegular :=
  OuterRegular.comap' μ f.continuous f.measurableEmbedding
/-
**MeasureTheory.Measure.OuterRegular.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.OuterRegular`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] 
(μ : MeasureTheory.Measure α) [μ.OuterRegular]   {x : ENNReal}, x ≠ ⊤ → (x • μ).
OuterRegular
参数：μ : MeasureTheory.Measure α；x • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENNReal.mul_iInf_of_ne`：mul_iInf_of_ne (ha₀ : a != 0) (ha : a != ∞) : a 
* ⨅ i, f i = ⨅ i, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Set.measure_eq_iInf_isOpen`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
[inst_1 : TopologicalSpace α] (A : Set α) (μ : MeasureTheory.Measure α)   [μ.Out
erRegular], μ A …
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
-/
protected theorem smul (μ : Measure α) [OuterRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
    (x • μ).OuterRegular := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact OuterRegular.zero
  · refine ⟨fun A _ r hr => ?_⟩
    rw [smul_apply, A.measure_eq_iInf_isOpen, smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using! hr
/-
**MeasureTheory.Measure.OuterRegular.smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.Measure.OuterRegular`。
形式化陈述：smul_nnreal (μ : Measure α) [OuterRegular μ] (c : Real>=0) : OuterRegular 
(c • μ)
参数：μ : Measure α；c : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.OuterRegular.smul`：∀ {α : Type u_1} [inst : Measur
ableSpace α] [inst_1 : TopologicalSpace α] (μ : MeasureTheory.Measure α) [μ.Oute
rRegular]   {x : ENNReal}, x …
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
instance smul_nnreal (μ : Measure α) [OuterRegular μ] (c : ℝ≥0) :
    OuterRegular (c • μ) :=
  OuterRegular.smul μ coe_ne_top

open scoped Function in -- required for scoped `on` notation
/-- If the restrictions of a measure to countably many open sets covering the space are
outer regular, then the measure itself is outer regular. -/
/-
**MeasureTheory.Measure.OuterRegular.of_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure.OuterRegular`。
形式化陈述：of_restrict [OpensMeasurableSpace α] {μ : Measure α} {s : Nat -> Set α} (h
 : forall n, OuterRegular (μ.restrict (s n))) (h' : forall n, IsOpen (s n)) (h''
 : univ subseteq ⋃ n, s n) : OuterRegular μ
参数：h : forall n, OuterRegular (μ.restrict (s n))；h' : forall n, IsOpen (s n)；h''
 : univ subseteq ⋃ n, s n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `ENNReal.exists_pos_sum_of_countable'`：exists_pos_sum_of_countable' {ε : 
Real>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0∞, (forall i
, 0 < ε' i) ∧ ∑' i, ε' i <…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If the restrictions of a measure to countably many open sets covering the space 
are
outer regular, then the measure itself is outer regular.
-/
lemma of_restrict [OpensMeasurableSpace α] {μ : Measure α} {s : ℕ → Set α}
    (h : ∀ n, OuterRegular (μ.restrict (s n))) (h' : ∀ n, IsOpen (s n)) (h'' : univ ⊆ ⋃ n, s n) :
    OuterRegular μ := by
  refine ⟨fun A hA r hr => ?_⟩
  have HA : μ A < ∞ := lt_of_lt_of_le hr le_top
  have hm : ∀ n, MeasurableSet (s n) := fun n => (h' n).measurableSet
  -- Note that `A = ⋃ n, A ∩ disjointed s n`. We replace `A` with this sequence.
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    ∃ A' : ℕ → Set α,
      (∀ n, MeasurableSet (A' n)) ∧
        (∀ n, A' n ⊆ s n) ∧ Pairwise (Disjoint on A') ∧ A = ⋃ n, A' n := by
    refine
      ⟨fun n => A ∩ disjointed s n, fun n => hA.inter (MeasurableSet.disjointed hm _), fun n =>
        inter_subset_right.trans (disjointed_subset _ _),
        (disjoint_disjointed s).mono fun k l hkl => hkl.mono inf_le_right inf_le_right, ?_⟩
    rw [← inter_iUnion, iUnion_disjointed, univ_subset_iff.mp h'', inter_univ]
  rcases ENNReal.exists_pos_sum_of_countable' (tsub_pos_iff_lt.2 hr).ne' ℕ with ⟨δ, δ0, hδε⟩
  rw [lt_tsub_iff_right, add_comm] at hδε
  have : ∀ n, ∃ U ⊇ A n, IsOpen U ∧ μ U < μ (A n) + δ n := by
    intro n
    have H₁ : ∀ t, μ.restrict (s n) t = μ (t ∩ s n) := fun t => restrict_apply' (hm n)
    have Ht : μ.restrict (s n) (A n) ≠ ∞ := by
      rw [H₁]
      exact ((measure_mono (inter_subset_left.trans (subset_iUnion A n))).trans_lt HA).ne
    rcases (A n).exists_isOpen_lt_add Ht (δ0 n).ne' with ⟨U, hAU, hUo, hU⟩
    rw [H₁, H₁, inter_eq_self_of_subset_left (hAs _)] at hU
    exact ⟨U ∩ s n, subset_inter hAU (hAs _), hUo.inter (h' n), hU⟩
  choose U hAU hUo hU using this
  refine ⟨⋃ n, U n, iUnion_mono hAU, isOpen_iUnion hUo, ?_⟩
  calc
    μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_iUnion_le _
    _ ≤ ∑' n, (μ (A n) + δ n) := ENNReal.tsum_le_tsum fun n => (hU n).le
    _ = ∑' n, μ (A n) + ∑' n, δ n := ENNReal.tsum_add
    _ = μ (⋃ n, A n) + ∑' n, δ n := (congr_arg₂ (· + ·) (measure_iUnion hAd hAm).symm rfl)
    _ < r := hδε

/-- See also `IsCompact.measure_closure` for a version
that assumes the `σ`-algebra to be the Borel `σ`-algebra but makes no assumptions on `μ`. -/
/-
**MeasureTheory.Measure.OuterRegular.measure_closure_eq_of_isCompact** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.Measure.OuterRegular`。
形式化陈述：measure_closure_eq_of_isCompact [R1Space α] [OuterRegular μ] {k : Set α} (
hk : IsCompact k) : μ (closure k) = μ k
参数：hk : IsCompact k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.measure_eq_iInf_isOpen`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
[inst_1 : TopologicalSpace α] (A : Set α) (μ : MeasureTheory.Measure α)   [μ.Out
erRegular], μ A …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
See also `IsCompact.measure_closure` for a version
that assumes the `σ`-algebra to be the Borel `σ`-algebra but makes no assumption
s on `μ`.
-/
lemma measure_closure_eq_of_isCompact [R1Space α] [OuterRegular μ]
    {k : Set α} (hk : IsCompact k) : μ (closure k) = μ k := by
  apply le_antisymm ?_ (measure_mono subset_closure)
  simp only [measure_eq_iInf_isOpen k, le_iInf_iff]
  intro u ku u_open
  exact measure_mono (hk.closure_subset_of_isOpen u_open ku)

/-- Outer regular measures are determined by values on open sets. -/
/-
**MeasureTheory.Measure.OuterRegular.ext_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure.OuterRegular`。
形式化陈述：ext_isOpen {ν : Measure α} [OuterRegular μ] [OuterRegular ν] (hμν : forall
 U, IsOpen U -> μ U = ν U) : μ = ν
参数：hμν : forall U, IsOpen U -> μ U = ν U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.measure_eq_iInf_isOpen`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
[inst_1 : TopologicalSpace α] (A : Set α) (μ : MeasureTheory.Measure α)   [μ.Out
erRegular], μ A …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)

--- 原说明 ---
Outer regular measures are determined by values on open sets.
-/
theorem ext_isOpen {ν : Measure α} [OuterRegular μ] [OuterRegular ν]
    (hμν : ∀ U, IsOpen U → μ U = ν U) : μ = ν := by
  ext s ms
  rw [Set.measure_eq_iInf_isOpen, Set.measure_eq_iInf_isOpen]
  congr! 4 with t _ ht2
  exact hμν t ht2

/-- Outer regular measures are determined by values on bounded open sets. -/
/-
**MeasureTheory.Measure.OuterRegular.ext_isOpen_isBounded** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.OuterRegular`。
形式化陈述：ext_isOpen_isBounded {α : Type*} [PseudoMetricSpace α] {mα : MeasurableSpa
ce α} {μ ν : Measure α} [OuterRegular μ] [OuterRegular ν] (hμν : forall U, IsOpe
n U -> Bornology.IsBounded U -> μ U = ν U) : μ = ν
参数：hμν : forall U, IsOpen U -> Bornology.IsBounded U -> μ U = ν U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.OuterRegular.ext_isOpen`：ext_isOpen {ν : Measure α
} [OuterRegular μ] [OuterRegular ν] (hμν : forall U, IsOpen U -> μ U = ν U) : μ 
= ν
· 使用定理 `Metric.eq_countable_union_of_isBounded_of_isOpen`：eq_countable_union_of_
isBounded_of_isOpen {U : Set α} (hU : IsOpen U) : exists f : Nat -> Set α, Monot
one f ∧ ⋃ i, f i = U ∧ forall i, IsBou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Outer regular measures are determined by values on bounded open sets.
-/
theorem ext_isOpen_isBounded {α : Type*} [PseudoMetricSpace α] {mα : MeasurableSpace α}
    {μ ν : Measure α} [OuterRegular μ] [OuterRegular ν]
    (hμν : ∀ U, IsOpen U → Bornology.IsBounded U → μ U = ν U) : μ = ν := by
  refine ext_isOpen fun U hU ↦ ?_
  obtain ⟨f, hm, hu, hf⟩ := Metric.eq_countable_union_of_isBounded_of_isOpen hU
  rw [← hu, hm.measure_iUnion, hm.measure_iUnion]
  exact iSup_congr fun i ↦ hμν (f i) (hf i).2 (hf i).1

end OuterRegular

/-- If a measure `μ` admits finite spanning open sets such that the restriction of `μ` to each set
is outer regular, then the original measure is outer regular as well. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.outerRegular** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] 
[OpensMeasurableSpace α]   {μ : MeasureTheory.Measure α} (s : μ.FiniteSpanningSe
tsIn {U | IsOpen U ∧ (μ.restrict U).OuterRegular}),   μ.OuterRegular
参数：s : μ.FiniteSpanningSetsIn {U | IsOpen U ∧ (μ.restrict U).OuterRegular}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.OuterRegular.of_restrict`：of_restrict [OpensMeasur
ableSpace α] {μ : Measure α} {s : Nat -> Set α} (h : forall n, OuterRegular (μ.r
estrict (s n))) (h' : forall n, IsOp…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…

--- 原说明 ---
If a measure `μ` admits finite spanning open sets such that the restriction of `
μ` to each set
is outer regular, then the original measure is outer regular as well.
-/
protected theorem FiniteSpanningSetsIn.outerRegular
    [TopologicalSpace α] [OpensMeasurableSpace α] {μ : Measure α}
    (s : μ.FiniteSpanningSetsIn { U | IsOpen U ∧ OuterRegular (μ.restrict U) }) :
    OuterRegular μ :=
  OuterRegular.of_restrict (s := fun n ↦ s.set n) (fun n ↦ (s.set_mem n).2)
    (fun n ↦ (s.set_mem n).1) s.spanning.symm.subset

namespace InnerRegularWRT

variable {p : Set α → Prop}

/-- If the restrictions of a measure to a monotone sequence of sets covering the space are
inner regular for some property `p` and all measurable sets, then the measure itself is
inner regular. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.of_restrict** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure.InnerRegularWRT`。
形式化陈述：of_restrict {μ : Measure α} {s : Nat -> Set α} (h : forall n, InnerRegular
WRT (μ.restrict (s n)) p MeasurableSet) (hs : univ subseteq ⋃ n, s n) (hmono : M
onotone s) : InnerRegularWRT μ p MeasurableSet
参数：h : forall n, InnerRegularWRT (μ.restrict (s n)) p MeasurableSet；hs : univ su
bseteq ⋃ n, s n；hmono : Monotone s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `lt_iSup_iff`：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.Measure.restrict_apply_le`：restrict_apply_le (s t : Set α)
 : μ.restrict s t <= μ t

--- 原说明 ---
If the restrictions of a measure to a monotone sequence of sets covering the spa
ce are
inner regular for some property `p` and all measurable sets, then the measure it
self is
inner regular.
-/
lemma of_restrict {μ : Measure α} {s : ℕ → Set α}
    (h : ∀ n, InnerRegularWRT (μ.restrict (s n)) p MeasurableSet)
    (hs : univ ⊆ ⋃ n, s n) (hmono : Monotone s) : InnerRegularWRT μ p MeasurableSet := by
  intro F hF r hr
  have hBU : ⋃ n, F ∩ s n = F := by rw [← inter_iUnion, univ_subset_iff.mp hs, inter_univ]
  have : μ F = ⨆ n, μ (F ∩ s n) := by
    rw [← (monotone_const.inter hmono).measure_iUnion, hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  rw [← restrict_apply hF] at hn
  rcases h n hF _ hn with ⟨K, KF, hKp, hK⟩
  exact ⟨K, KF, hKp, hK.trans_le (restrict_apply_le _ _)⟩

/-- If `μ` is inner regular for measurable finite measure sets with respect to some class of sets,
then its restriction to any set is also inner regular for measurable finite measure sets, with
respect to the same class of sets. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.restrict** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure.InnerRegularWRT`。
形式化陈述：restrict (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)) (
A : Set α) : InnerRegularWRT (μ.restrict A) p (fun s => MeasurableSet s ∧ μ.rest
rict A s != ∞)
参数：h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)；A : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `MeasureTheory.Measure.restrict_toMeasurable`：restrict_toMeasurable (h : 
μ s != ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If `μ` is inner regular for measurable finite measure sets with respect to some 
class of sets,
then its restriction to any set is also inner regular for measurable finite meas
ure sets, with
respect to the same class of sets.
-/
lemma restrict (h : InnerRegularWRT μ p (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞)) (A : Set α) :
    InnerRegularWRT (μ.restrict A) p (fun s ↦ MeasurableSet s ∧ μ.restrict A s ≠ ∞) := by
  rintro s ⟨s_meas, hs⟩ r hr
  rw [restrict_apply s_meas] at hs
  obtain ⟨K, K_subs, pK, rK⟩ : ∃ K, K ⊆ (toMeasurable μ (s ∩ A)) ∩ s ∧ p K ∧ r < μ K := by
    have : r < μ ((toMeasurable μ (s ∩ A)) ∩ s) := by
      apply hr.trans_le
      rw [restrict_apply s_meas]
      exact measure_mono <| subset_inter (subset_toMeasurable μ (s ∩ A)) inter_subset_left
    refine h ⟨(measurableSet_toMeasurable _ _).inter s_meas, ?_⟩ _ this
    apply (lt_of_le_of_lt _ hs.lt_top).ne
    rw [← measure_toMeasurable (s ∩ A)]
    exact measure_mono inter_subset_left
  refine ⟨K, K_subs.trans inter_subset_right, pK, ?_⟩
  calc
  r < μ K := rK
  _ = μ.restrict (toMeasurable μ (s ∩ A)) K := by
    rw [restrict_apply' (measurableSet_toMeasurable μ (s ∩ A))]
    congr
    apply (inter_eq_left.2 ?_).symm
    exact K_subs.trans inter_subset_left
  _ = μ.restrict (s ∩ A) K := by rwa [restrict_toMeasurable]
  _ ≤ μ.restrict A K := Measure.le_iff'.1 (restrict_mono inter_subset_right le_rfl) K

/-- If `μ` is inner regular for measurable finite measure sets with respect to some class of sets,
then its restriction to any finite measure set is also inner regular for measurable sets with
respect to the same class of sets. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.restrict_of_measure_ne_top** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：restrict_of_measure_ne_top (h : InnerRegularWRT μ p (fun s => MeasurableSe
t s ∧ μ s != ∞)) {A : Set α} (hA : μ A != ∞) : InnerRegularWRT (μ.restrict A) p 
(fun s => MeasurableSet s)
参数：h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)；hA : μ A != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.trans`：trans {q' : Set α -> Prop} 
(H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') : InnerRegularWRT μ p 
q'
· 使用引理 `MeasureTheory.Measure.InnerRegularWRT.restrict`：restrict (h : InnerRegul
arWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)) (A : Set α) : InnerRegularWRT (
μ.restrict A) p (fun s => Measurable…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.of_imp`：of_imp (h : forall s, q s 
-> p s) : InnerRegularWRT μ p q
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…

--- 原说明 ---
If `μ` is inner regular for measurable finite measure sets with respect to some 
class of sets,
then its restriction to any finite measure set is also inner regular for measura
ble sets with
respect to the same class of sets.
-/
lemma restrict_of_measure_ne_top (h : InnerRegularWRT μ p (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞))
    {A : Set α} (hA : μ A ≠ ∞) :
    InnerRegularWRT (μ.restrict A) p (fun s ↦ MeasurableSet s) := by
  have : Fact (μ A < ∞) := ⟨hA.lt_top⟩
  exact (restrict h A).trans (of_imp (fun s hs ↦ ⟨hs, measure_ne_top _ _⟩))

/-- Given a σ-finite measure, any measurable set can be approximated from inside by a measurable
set of finite measure. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.of_sigmaFinite** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：of_sigmaFinite [SigmaFinite μ] : InnerRegularWRT μ (fun s => MeasurableSet
 s ∧ μ s != ∞) (fun s => MeasurableSet s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iSup_iff`：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞

--- 原说明 ---
Given a σ-finite measure, any measurable set can be approximated from inside by 
a measurable
set of finite measure.
-/
lemma of_sigmaFinite [SigmaFinite μ] :
    InnerRegularWRT μ (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞) (fun s ↦ MeasurableSet s) := by
  intro s hs r hr
  set B : ℕ → Set α := spanningSets μ
  have hBU : ⋃ n, s ∩ B n = s := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have : μ s = ⨆ n, μ (s ∩ B n) := by
    rw [← (monotone_const.inter (monotone_spanningSets μ)).measure_iUnion, hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  refine ⟨s ∩ B n, inter_subset_left, ⟨hs.inter (measurableSet_spanningSets μ n), ?_⟩, hn⟩
  exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne

variable [TopologicalSpace α]

/-- If a measure is inner regular (using closed or compact sets) for open sets, then every
measurable set of finite measure can be approximated by a (closed or compact) subset. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.measurableSet_of_isOpen** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：measurableSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen) 
(hd : forall ⦃s U⦄, p s -> IsOpen U -> p (s \ U)) : InnerRegularWRT μ p fun s =>
 MeasurableSet s ∧ μ s != ∞
参数：H : InnerRegularWRT μ p IsOpen；hd : forall ⦃s U⦄, p s -> IsOpen U -> p (s \ U
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_univ`：sdiff_univ (s : Set α) : s \ univ = ∅
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a
· 使用定理 `ENNReal.sub_sub_cancel`：sub_sub_cancel (h : a != ∞) (h2 : b <= a) : a - 
(a - b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MeasurableSet.exists_isOpen_sdiff_lt`：∀ {α : Type u_1} [inst : Measurabl
eSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRe
gular]   {A : Set α}, Meas…
· 使用定理 `Set.exists_isOpen_lt_of_lt`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRegular]   (
A : Set α) (r : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sdiff_subset_comm`：sdiff_subset_comm {s t u : Set α} : s \ t subsete
q u ↔ s \ u subseteq t
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
If a measure is inner regular (using closed or compact sets) for open sets, then
 every
measurable set of finite measure can be approximated by a (closed or compact) su
bset.
-/
theorem measurableSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen)
    (hd : ∀ ⦃s U⦄, p s → IsOpen U → p (s \ U)) :
    InnerRegularWRT μ p fun s => MeasurableSet s ∧ μ s ≠ ∞ := by
  rintro s ⟨hs, hμs⟩ r hr
  have h0 : p ∅ := by
    have : 0 < μ univ := (bot_le.trans_lt hr).trans_le (measure_mono (subset_univ _))
    obtain ⟨K, -, hK, -⟩ : ∃ K, K ⊆ univ ∧ p K ∧ 0 < μ K := H isOpen_univ _ this
    simpa using hd hK isOpen_univ
  obtain ⟨ε, hε, hεs, rfl⟩ : ∃ ε ≠ 0, ε + ε ≤ μ s ∧ r = μ s - (ε + ε) := by
    use (μ s - r) / 2
    simp [*, hr.le, ENNReal.add_halves, ENNReal.sub_sub_cancel, tsub_eq_zero_iff_le]
  rcases hs.exists_isOpen_sdiff_lt hμs hε with ⟨U, hsU, hUo, hUt, hμU⟩
  rcases (U \ s).exists_isOpen_lt_of_lt _ hμU with ⟨U', hsU', hU'o, hμU'⟩
  replace hsU' := sdiff_subset_comm.1 hsU'
  rcases H.exists_subset_lt_add h0 hUo hUt.ne hε with ⟨K, hKU, hKc, hKr⟩
  refine ⟨K \ U', fun x hx => hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, ENNReal.sub_lt_of_lt_add hεs ?_⟩
  calc
    μ s ≤ μ U := μ.mono hsU
    _ < μ K + ε := hKr
    _ ≤ μ (K \ U') + μ U' + ε := by grw [tsub_le_iff_right.1 le_measure_sdiff]
    _ ≤ μ (K \ U') + ε + ε := by gcongr
    _ = μ (K \ U') + (ε + ε) := add_assoc _ _ _

open Finset in
/-- In a finite measure space, assume that any open set can be approximated from inside by closed
sets. Then the measure is weakly regular. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.weaklyRegular_of_finite** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：weaklyRegular_of_finite [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
 (H : InnerRegularWRT μ IsClosed IsOpen) : WeaklyRegular μ
参数：μ : Measure α；H : InnerRegularWRT μ IsClosed IsOpen。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasurableSet.induction_on_open`：MeasurableSet.induction_on_open {C : fo
rall s : Set γ, MeasurableSet s -> Prop} (isOpen : forall U (hU : IsOpen U), C U
 hU.measurableSet) (c…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.exists_subset_lt_add`：exists_subse
t_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U != ∞) (hε 
: ε != 0) : exists K, K subseteq U ∧ p K ∧ μ U <…
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `ENNReal.exists_pos_sum_of_countable'`：exists_pos_sum_of_countable' {ε : 
Real>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0∞, (forall i
, 0 < ε' i) ∧ ∑' i, ε' i <…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
In a finite measure space, assume that any open set can be approximated from ins
ide by closed
sets. Then the measure is weakly regular.
-/
theorem weaklyRegular_of_finite [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : InnerRegularWRT μ IsClosed IsOpen) : WeaklyRegular μ := by
  have hfin : ∀ {s}, μ s ≠ ∞ := @(measure_ne_top μ)
  suffices ∀ s, MeasurableSet s → ∀ ε, ε ≠ 0 → ∃ F, F ⊆ s ∧ ∃ U, U ⊇ s ∧
      IsClosed F ∧ IsOpen U ∧ μ s ≤ μ F + ε ∧ μ U ≤ μ s + ε by
    refine
      { outerRegular := fun s hs r hr => ?_
        innerRegular := H }
    rcases exists_between hr with ⟨r', hsr', hr'r⟩
    rcases this s hs _ (tsub_pos_iff_lt.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩
    refine ⟨U, hsU, hUo, ?_⟩
    rw [add_tsub_cancel_of_le hsr'.le] at H
    exact H.trans_lt hr'r
  apply MeasurableSet.induction_on_open
  /- The proof is by measurable induction: we should check that the property is true for the empty
    set, for open sets, and is stable by taking the complement and by taking countable disjoint
    unions. The point of the property we are proving is that it is stable by taking complements
    (exchanging the roles of closed and open sets and thanks to the finiteness of the measure). -/
  -- check for open set
  · intro U hU ε hε
    rcases H.exists_subset_lt_add isClosed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩
    exact ⟨F, hsF, U, Subset.rfl, hFc, hU, hF.le, le_self_add⟩
  -- check for complements
  · rintro s hs H ε hε
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩
    refine
      ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs, hUo.isClosed_compl,
        hFc.isOpen_compl, ?_⟩
    simp only [measure_compl_le_add_iff, *, hUo.measurableSet, hFc.measurableSet, true_and]
  -- check for disjoint unions
  · intro s hsd hsm H ε ε0
    have ε0' : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
    rcases ENNReal.exists_pos_sum_of_countable' ε0' ℕ with ⟨δ, δ0, hδε⟩
    choose F hFs U hsU hFc hUo hF hU using fun n => H n (δ n) (δ0 n).ne'
    -- the approximating closed set is constructed by considering finitely many sets `s i`, which
    -- cover all the measure up to `ε/2`, approximating each of these by a closed set `F i`, and
    -- taking the union of these (finitely many) `F i`.
    have : Tendsto (fun t => (∑ k ∈ t, μ (s k)) + ε / 2) atTop (𝓝 <| μ (⋃ n, s n) + ε / 2) := by
      rw [measure_iUnion hsd hsm]
      exact Tendsto.add ENNReal.summable.hasSum tendsto_const_nhds
    rcases (this.eventually <| lt_mem_nhds <| ENNReal.lt_add_right hfin ε0').exists with ⟨t, ht⟩
    -- the approximating open set is constructed by taking for each `s n` an approximating open set
    -- `U n` with measure at most `μ (s n) + δ n` for a summable `δ`, and taking the union of these.
    refine
      ⟨⋃ k ∈ t, F k, iUnion_mono fun k => iUnion_subset fun _ => hFs _, ⋃ n, U n, iUnion_mono hsU,
        isClosed_biUnion_finset fun k _ => hFc k, isOpen_iUnion hUo, ht.le.trans ?_, ?_⟩
    · calc
        (∑ k ∈ t, μ (s k)) + ε / 2 ≤ ((∑ k ∈ t, μ (F k)) + ∑ k ∈ t, δ k) + ε / 2 := by
          rw [← sum_add_distrib]
          gcongr
          apply hF
        _ ≤ (∑ k ∈ t, μ (F k)) + ε / 2 + ε / 2 := by
          gcongr
          exact (ENNReal.sum_le_tsum _).trans hδε.le
        _ = μ (⋃ k ∈ t, F k) + ε := by
          rw [measure_biUnion_finset, add_assoc, ENNReal.add_halves]
          exacts [fun k _ n _ hkn => (hsd hkn).mono (hFs k) (hFs n),
            fun k _ => (hFc k).measurableSet]
    · calc
        μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_iUnion_le _
        _ ≤ ∑' n, (μ (s n) + δ n) := ENNReal.tsum_le_tsum hU
        _ = μ (⋃ n, s n) + ∑' n, δ n := by rw [measure_iUnion hsd hsm, ENNReal.tsum_add]
        _ ≤ μ (⋃ n, s n) + ε := by grw [hδε, ENNReal.half_le_self]

/-- In a metrizable space (or even a pseudometrizable space), an open set can be approximated from
inside by closed sets. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.of_pseudoMetrizableSpace** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：of_pseudoMetrizableSpace {X : Type*} [TopologicalSpace X] [PseudoMetrizabl
eSpace X] [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsClosed IsOpe
n
参数：μ : Measure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.exists_iUnion_isClosed`：∀ {α : Type u} [inst : PseudoEMetricSpace
 α] {U : Set α},   IsOpen U → ∃ F, (∀ (n : ℕ), IsClosed (F n)) ∧ (∀ (n : ℕ), F n
 ⊆ U) ∧ ⋃ n, F n = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iSup_iff`：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i

--- 原说明 ---
In a metrizable space (or even a pseudometrizable space), an open set can be app
roximated from
inside by closed sets.
-/
theorem of_pseudoMetrizableSpace {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsClosed IsOpen := by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  intro U hU r hr
  rcases hU.exists_iUnion_isClosed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [F_mono.measure_iUnion] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_iUnion _ _, F_closed n, hn⟩

/-- In a `σ`-compact space, any closed set can be approximated by a compact subset. -/
/-
**MeasureTheory.Measure.InnerRegularWRT.isCompact_isClosed** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.InnerRegularWRT`。
形式化陈述：isCompact_isClosed {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X] 
[MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsCompact IsClosed
参数：μ : Measure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_left`：IsCompact.inter_left (ht : IsCompact t) (hs : IsCl
osed s) : IsCompact (s inter t)
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `iUnion_compactCovering`：iUnion_compactCovering : ⋃ n, compactCovering X 
n = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
· 使用引理 `SigmaCompactSpace.exists_compact_covering`：SigmaCompactSpace.exists_comp
act_covering [h : SigmaCompactSpace X] : exists K : Nat -> Set X, (forall n, IsC
ompact (K n)) ∧ ⋃ n, K n = univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iSup_iff`：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
In a `σ`-compact space, any closed set can be approximated by a compact subset.
-/
theorem isCompact_isClosed {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsCompact IsClosed := by
  intro F hF r hr
  set B : ℕ → Set X := compactCovering X
  have hBc : ∀ n, IsCompact (F ∩ B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : ⋃ n, F ∩ B n = F := by rw [← inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F ∩ B n) := by
    rw [← Monotone.measure_iUnion, hBU]
    exact monotone_const.inter monotone_accumulate
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨_, inter_subset_left, hBc n, hn⟩

end InnerRegularWRT

namespace InnerRegular

variable [TopologicalSpace α]

/-- The measure of a measurable set is the supremum of the measures of compact sets it contains. -/
/-
**MeasureTheory.Measure.InnerRegular._root_.MeasurableSet.measure_eq_iSup_isComp
act** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure of a measurable set is the supremum of the measures of compact sets 
it contains.
-/
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : MeasurableSet U)
    (μ : Measure α) [InnerRegular μ] :
    μ U = ⨆ (K : Set α) (_ : K ⊆ U) (_ : IsCompact K), μ K :=
  InnerRegular.innerRegular.measure_eq_iSup hU
/-
**MeasureTheory.Measure.InnerRegular.zero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure.InnerRegular`。
形式化陈述：zero : InnerRegular (0 : Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
-/
instance zero : InnerRegular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩
/-
**MeasureTheory.Measure.InnerRegular.smul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure.InnerRegular`。
形式化陈述：smul [h : InnerRegular μ] (c : Real>=0∞) : InnerRegular (c • μ)
参数：c : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.smul`：smul (H : InnerRegularWRT μ 
p q) (c : Real>=0∞) : InnerRegularWRT (c • μ) p q
· 使用定理 `MeasureTheory.Measure.InnerRegular.innerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.InnerRegular], μ.InnerRe…
-/
instance smul [h : InnerRegular μ] (c : ℝ≥0∞) : InnerRegular (c • μ) :=
  ⟨InnerRegularWRT.smul h.innerRegular c⟩
/-
**MeasureTheory.Measure.InnerRegular.smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.Measure.InnerRegular`。
形式化陈述：smul_nnreal [InnerRegular μ] (c : Real>=0) : InnerRegular (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul_nnreal [InnerRegular μ] (c : ℝ≥0) : InnerRegular (c • μ) := smul (c : ℝ≥0∞)
/-
**MeasureTheory.Measure.InnerRegular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.M
easure.InnerRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [InnerRegular μ] : InnerRegularCompactLTTop μ :=
  ⟨fun _s hs r hr ↦ InnerRegular.innerRegular hs.1 r hr⟩
/-
**MeasureTheory.Measure.InnerRegular.innerRegularWRT_isClosed_isOpen** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.Measure.InnerRegular`。
形式化陈述：innerRegularWRT_isClosed_isOpen [R1Space α] [OpensMeasurableSpace α] [h : 
InnerRegular μ] : InnerRegularWRT μ IsClosed IsOpen
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.innerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.InnerRegular], μ.InnerRe…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma innerRegularWRT_isClosed_isOpen [R1Space α] [OpensMeasurableSpace α] [h : InnerRegular μ] :
    InnerRegularWRT μ IsClosed IsOpen := by
  intro U hU r hr
  rcases h.innerRegular hU.measurableSet r hr with ⟨K, KU, K_comp, hK⟩
  exact ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
    hK.trans_le (measure_mono subset_closure)⟩
/-
**MeasureTheory.Measure.InnerRegular.exists_isCompact_not_null** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure.InnerRegular`。
形式化陈述：exists_isCompact_not_null [InnerRegular μ] : (exists K, IsCompact K ∧ μ K 
!= 0) ↔ μ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSet.measure_eq_iSup_isCompact`：∀ {α : Type u_1} [inst : Measur
ableSpace α] [inst_1 : TopologicalSpace α] ⦃U : Set α⦄,   MeasurableSet U → ∀ (μ
 : MeasureTheory.Measure α) […
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_isCompact_not_null [InnerRegular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne, ← measure_univ_eq_zero, MeasurableSet.univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]
/-- If `μ` is inner regular, then any measurable set can be approximated by a compact subset.
See also `MeasurableSet.exists_isCompact_lt_add_of_ne_top`. -/
/-
**MeasureTheory.Measure.InnerRegular._root_.MeasurableSet.exists_lt_isCompact** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular, then any measurable set can be approximated by a compac
t subset.
See also `MeasurableSet.exists_isCompact_lt_add_of_ne_top`.
-/
theorem _root_.MeasurableSet.exists_lt_isCompact [InnerRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ r < μ K :=
  InnerRegular.innerRegular hA _ hr
/-
**MeasureTheory.Measure.InnerRegular.map_of_continuous** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.InnerRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [inst_3 : Measurab
leSpace β] [inst_4 : TopologicalSpace β] [BorelSpace β] [h : μ.InnerRegular]   {
f : α → β}, Continuous f → (MeasureTheory.Measure.map f μ).InnerRegular
参数：MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.map`：∀ {α : Type u_2} {β : Type u_
3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Me
asure α}   {pa qa : Set α → Pro…
· 使用定理 `MeasureTheory.Measure.InnerRegular.innerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.InnerRegular], μ.InnerRe…
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
-/
protected theorem map_of_continuous [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [h : InnerRegular μ] {f : α → β} (hf : Continuous f) :
    InnerRegular (Measure.map f μ) :=
  ⟨InnerRegularWRT.map h.innerRegular hf.aemeasurable (fun _s hs ↦ hf.measurable hs)
    (fun _K hK ↦ hK.image hf) (fun _s hs ↦ hs)⟩
/-
**MeasureTheory.Measure.InnerRegular.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.InnerRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [inst_3 : Measurab
leSpace β] [inst_4 : TopologicalSpace β] [BorelSpace β] [μ.InnerRegular]   (f : 
α ≃ₜ β), (MeasureTheory.Measure.map (⇑f) μ).InnerRegular
参数：f : α ≃ₜ β；MeasureTheory.Measure.map (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.map_of_continuous`：∀ {α : Type u_1} {
β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 :
 TopologicalSpace α]   [BorelSpace α] [ins…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
protected theorem map [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [InnerRegular μ] (f : α ≃ₜ β) : (Measure.map f μ).InnerRegular :=
  InnerRegular.map_of_continuous f.continuous
/-
**MeasureTheory.Measure.InnerRegular.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure.InnerRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [inst_3 : Measurab
leSpace β] [inst_4 : TopologicalSpace β] [BorelSpace β] (f : α ≃ₜ β),   (Measure
Theory.Measure.map (⇑f) μ).InnerRegular ↔ μ.InnerRegular
参数：f : α ≃ₜ β；MeasureTheory.Measure.map (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.symm_comp_self`：symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.InnerRegular.map`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSp
ace α]   [BorelSpace α] [ins…
-/
protected theorem map_iff [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) :
    InnerRegular (Measure.map f μ) ↔ InnerRegular μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp

open Topology in
/-
**MeasureTheory.Measure.InnerRegular.comap'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.InnerRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topol
ogicalSpace α] [BorelSpace α]   {mβ : MeasurableSpace β} [inst_3 : TopologicalSp
ace β] [BorelSpace β] (μ : MeasureTheory.Measure β)   [H : μ.InnerRegular] {f : 
α → β}, Topology.IsOpenEmbedding f → (MeasureTheory.Measure.comap f μ).InnerRegu
lar
参数：μ : MeasureTheory.Measure β；MeasureTheory.Measure.comap f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.comap`：∀ {α : Type u_2} {β : Type 
u_3} [inst : MeasurableSpace α] {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure β}   {pa qa : Set α → Prop} {…
· 使用定理 `MeasureTheory.Measure.InnerRegular.innerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.InnerRegular], μ.InnerRe…
· 使用定理 `Topology.IsOpenEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [mβ 
: TopologicalSpace β] [inst_2 : Me…
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用引理 `Topology.IsInducing.isCompact_preimage'`：Topology.IsInducing.isCompact_p
reimage' (hf : IsInducing f) {K : Set Y} (hK : IsCompact K) (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K)
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
-/
protected theorem comap' [BorelSpace α]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
    (μ : Measure β) [H : InnerRegular μ] {f : α → β} (hf : IsOpenEmbedding f) :
    (μ.comap f).InnerRegular where
  innerRegular :=
    H.innerRegular.comap hf.measurableEmbedding
    (fun _ hU ↦ hf.measurableEmbedding.measurableSet_image' hU)
    (fun _ hKrange hK ↦ hf.isInducing.isCompact_preimage' hK hKrange)
/-
**MeasureTheory.Measure.InnerRegular.comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.InnerRegular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topol
ogicalSpace α] [BorelSpace α]   {mβ : MeasurableSpace β} [inst_3 : TopologicalSp
ace β] [BorelSpace β] {μ : MeasureTheory.Measure β} [μ.InnerRegular]   (f : α ≃ₜ
 β), (MeasureTheory.Measure.comap (⇑f) μ).InnerRegular
参数：f : α ≃ₜ β；MeasureTheory.Measure.comap (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.comap'`：∀ {α : Type u_1} {β : Type u_
2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [BorelSpace α]   {mβ
 : MeasurableSpace β} [inst_3 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
protected theorem comap [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
    {μ : Measure β} [InnerRegular μ] (f : α ≃ₜ β) :
    (μ.comap f).InnerRegular :=
  InnerRegular.comap' μ f.isOpenEmbedding
/-
**MeasureTheory.Measure.InnerRegular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.M
easure.InnerRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {μ ν : Measure α} [InnerRegular μ] [InnerRegular ν] : InnerRegular (μ + ν) := by
  constructor
  intro s hs r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  rcases eq_or_ne (μ s) 0 with h | h
  · simp only [h, zero_add] at hr
    rcases MeasurableSet.exists_lt_isCompact hs hr with ⟨K, Ks, hK, h'K⟩
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases eq_or_ne (ν s) 0 with h' | h'
  · simp only [h', add_zero] at hr
    rcases MeasurableSet.exists_lt_isCompact hs hr with ⟨K, Ks, hK, h'K⟩
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases ENNReal.exists_lt_add_of_lt_add hr h h' with ⟨u, hu, v, hv, huv⟩
  rcases MeasurableSet.exists_lt_isCompact hs hu with ⟨K, Ks, hK, h'K⟩
  rcases MeasurableSet.exists_lt_isCompact hs hv with ⟨K', K's, hK', h'K'⟩
  refine ⟨K ∪ K', union_subset Ks K's, hK.union hK', huv.trans_le ?_⟩
  apply (add_le_add h'K.le h'K'.le).trans
  simp only [Measure.coe_add, Pi.add_apply]
  gcongr <;> simp
/-
**MeasureTheory.Measure.InnerRegular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.M
easure.InnerRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {μ : ι → Measure α} [∀ i, InnerRegular (μ i)] (a : Finset ι) :
    InnerRegular (∑ i ∈ a, μ i) := by
  classical
  induction a using Finset.induction with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | insert a s ha ih => simp only [ha, not_false_eq_true, Finset.sum_insert]; infer_instance
/-
**MeasureTheory.Measure.InnerRegular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.M
easure.InnerRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {μ : ι → Measure α} [∀ i, InnerRegular (μ i)] :
    InnerRegular (Measure.sum μ) := by
  constructor
  intro s hs r hr
  have : Tendsto (fun (a : Finset ι) ↦ ∑ i ∈ a, μ i s) atTop (𝓝 (Measure.sum μ s)) := by
    simp only [hs, Measure.sum_apply]
    exact ENNReal.summable.hasSum
  obtain ⟨a, ha⟩ : ∃ (a : Finset ι), r < (∑ i ∈ a, μ i) s := by
    simp only [coe_finsetSum, Finset.sum_apply]
    exact ((tendsto_order.1 this).1 r hr).exists
  rcases MeasurableSet.exists_lt_isCompact hs ha with ⟨K, Ks, hK, h'K⟩
  refine ⟨K, Ks, hK, h'K.trans_le ?_⟩
  simp only [coe_finsetSum, Finset.sum_apply]
  exact (ENNReal.sum_le_tsum _).trans (le_sum_apply _ _)

end InnerRegular

namespace InnerRegularCompactLTTop

variable [TopologicalSpace α]

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.exists_isC
ompact_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularCompa
ctLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_lt_isCompact_of_ne_top`.
-/
theorem _root_.MeasurableSet.exists_isCompact_lt_add [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ A < μ K + ε :=
  InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a compact closed subset.
Compared to `MeasurableSet.exists_isCompact_lt_add`,
this version additionally assumes that `α` is an R₁ space with Borel σ-algebra.
-/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.exists_isC
ompact_isClosed_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerReg
ularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a compact close
d subset.
Compared to `MeasurableSet.exists_isCompact_lt_add`,
this version additionally assumes that `α` is an R₁ space with Borel σ-algebra.
-/
theorem _root_.MeasurableSet.exists_isCompact_isClosed_lt_add
    [InnerRegularCompactLTTop μ] [R1Space α] [BorelSpace α]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ IsClosed K ∧ μ A < μ K + ε :=
  let ⟨K, hKA, hK, hμK⟩ := hA.exists_isCompact_lt_add h'A hε
  ⟨closure K, hK.closure_subset_measurableSet hA hKA, hK.closure, isClosed_closure,
    by rwa [hK.measure_closure]⟩

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.exists_isC
ompact_sdiff_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularCom
pactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`.
-/
theorem _root_.MeasurableSet.exists_isCompact_sdiff_lt [OpensMeasurableSpace α] [T2Space α]
    [InnerRegularCompactLTTop μ] ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact ⟨K, hKA, hKc, measure_sdiff_lt_of_lt_add hKc.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCompact_diff_lt :=
  _root_.MeasurableSet.exists_isCompact_sdiff_lt

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a compact closed subset.
Compared to `MeasurableSet.exists_isCompact_sdiff_lt`,
this lemma additionally assumes that `α` is an R₁ space with Borel σ-algebra. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.exists_isC
ompact_isClosed_sdiff_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerR
egularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a compact close
d subset.
Compared to `MeasurableSet.exists_isCompact_sdiff_lt`,
this lemma additionally assumes that `α` is an R₁ space with Borel σ-algebra.
-/
theorem _root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt [BorelSpace α] [R1Space α]
    [InnerRegularCompactLTTop μ] ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ IsClosed K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_isClosed_lt_add h'A hε with ⟨K, hKA, hKco, hKcl, hK⟩
  exact ⟨K, hKA, hKco, hKcl, measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCompact_isClosed_diff_lt :=
  _root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add`. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.exists_lt_
isCompact_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegula
rCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add`.
-/
theorem _root_.MeasurableSet.exists_lt_isCompact_of_ne_top [InnerRegularCompactLTTop μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ r < μ K :=
  InnerRegularCompactLTTop.innerRegular ⟨hA, h'A⟩ _ hr

/-- If `μ` is inner regular for finite measure sets with respect to compact sets,
any measurable set of finite mass can be approximated from inside by compact sets. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.measure_eq
_iSup_isCompact_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.Inner
RegularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets,
any measurable set of finite mass can be approximated from inside by compact set
s.
-/
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) :
    μ A = ⨆ (K) (_ : K ⊆ A) (_ : IsCompact K), μ K :=
  InnerRegularCompactLTTop.innerRegular.measure_eq_iSup ⟨hA, h'A⟩

/-- If `μ` is inner regular for finite measure sets with respect to compact sets, then its
restriction to any set also is. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.restrict** 是 Mathlib 中的一个实例，位于命
名空间 `MeasureTheory.Measure.InnerRegularCompactLTTop`。
形式化陈述：restrict [h : InnerRegularCompactLTTop μ] (A : Set α) : InnerRegularCompac
tLTTop (μ.restrict A)
参数：A : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.InnerRegularWRT.restrict`：restrict (h : InnerRegul
arWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)) (A : Set α) : InnerRegularWRT (
μ.restrict A) p (fun s => Measurable…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.innerRegular`：∀ {α : Type
 u_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheor
y.Measure α}   [self : μ.InnerRegularCompactLTTop…

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets, th
en its
restriction to any set also is.
-/
instance restrict [h : InnerRegularCompactLTTop μ] (A : Set α) :
    InnerRegularCompactLTTop (μ.restrict A) :=
  ⟨InnerRegularWRT.restrict h.innerRegular A⟩
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.Measure.InnerRegularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) [h : InnerRegularCompactLTTop μ] [IsFiniteMeasure μ] :
    InnerRegular μ := by
  constructor
  convert! h.innerRegular with s
  simp [measure_ne_top μ s]
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.Measure.InnerRegularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) [BorelSpace α] [R1Space α] [InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] : WeaklyRegular μ :=
  InnerRegular.innerRegularWRT_isClosed_isOpen.weaklyRegular_of_finite _
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.Measure.InnerRegularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) [BorelSpace α] [R1Space α] [h : InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] : Regular μ where
  innerRegular := InnerRegularWRT.trans h.innerRegular <|
    InnerRegularWRT.of_imp (fun U hU ↦ ⟨hU.measurableSet, measure_ne_top μ U⟩)
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.IsCompact.exists_isOpen_
lt_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure.InnerRegularCompactLTT
op`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.IsCompact.exists_isOpen_lt_of_lt [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α] {K : Set α}
    (hK : IsCompact K) (r : ℝ≥0∞) (hr : μ K < r) :
    ∃ U, K ⊆ U ∧ IsOpen U ∧ μ U < r := by
  rcases hK.exists_open_superset_measure_lt_top μ with ⟨V, hKV, hVo, hμV⟩
  have := Fact.mk hμV
  obtain ⟨U, hKU, hUo, hμU⟩ : ∃ U, K ⊆ U ∧ IsOpen U ∧ μ.restrict V U < r :=
    exists_isOpen_lt_of_lt K r <| (restrict_apply_le _ _).trans_lt hr
  refine ⟨U ∩ V, subset_inter hKU hKV, hUo.inter hVo, ?_⟩
  rwa [restrict_apply hUo.measurableSet] at hμU

/-- If `μ` is inner regular for finite measure sets with respect to compact sets
and is locally finite in an R₁ space,
then any compact set can be approximated from outside by open sets. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.IsCompact.measure_eq_iIn
f_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure.InnerRegularCompactLTT
op`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is inner regular for finite measure sets with respect to compact sets
and is locally finite in an R₁ space,
then any compact set can be approximated from outside by open sets.
-/
protected lemma _root_.IsCompact.measure_eq_iInf_isOpen [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α] {K : Set α} (hK : IsCompact K) :
    μ K = ⨅ (U : Set α) (_ : K ⊆ U) (_ : IsOpen U), μ U := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    exact fun U KU _ ↦ measure_mono KU
  · apply le_of_forall_gt
    simpa only [iInf_lt_iff, exists_prop, exists_and_left] using hK.exists_isOpen_lt_of_lt
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.IsCompact.exists_isOpen_
lt_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularCompactLTTop
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsCompact.exists_isOpen_lt_add [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {K : Set α} (hK : IsCompact K) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, K ⊆ U ∧ IsOpen U ∧ μ U < μ K + ε :=
  hK.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hK.measure_lt_top.ne hε)

/-- Let `μ` be a locally finite measure on an R₁ topological space with Borel σ-algebra.
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated in measure by an open set.
See also `Set.exists_isOpen_lt_of_lt` and `MeasurableSet.exists_isOpen_diff_lt`
for the case of an outer regular measure. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasurableSet.exists_isO
pen_symmDiff_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularCom
pactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `μ` be a locally finite measure on an R₁ topological space with Borel σ-alge
bra.
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any measurable set of finite measure can be approximated in measure by an o
pen set.
See also `Set.exists_isOpen_lt_of_lt` and `MeasurableSet.exists_isOpen_diff_lt`
for the case of an outer regular measure.
-/
protected theorem _root_.MeasurableSet.exists_isOpen_symmDiff_lt [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, IsOpen U ∧ μ U < ∞ ∧ μ (U ∆ s) < ε := by
  have : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_isClosed_sdiff_lt hμs this with ⟨K, hKs, hKco, hKcl, hμK⟩
  rcases hKco.exists_isOpen_lt_add (μ := μ) this with ⟨U, hKU, hUo, hμU⟩
  refine ⟨U, hUo, hμU.trans_le le_top, ?_⟩
  rw [← ENNReal.add_halves ε, measure_symmDiff_eq hUo.nullMeasurableSet hs.nullMeasurableSet]
  gcongr
  · calc
      μ (U \ s) ≤ μ (U \ K) := by gcongr
      _ < ε / 2 := by
        apply measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKU _ hμU
        exact ne_top_of_le_ne_top hμs (by gcongr)
  · exact lt_of_le_of_lt (by gcongr) hμK

/-- Let `μ` be a locally finite measure on an R₁ topological space with Borel σ-algebra.
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any null measurable set of finite measure can be approximated in measure by an open set.
See also `Set.exists_isOpen_lt_of_lt` and `MeasurableSet.exists_isOpen_diff_lt`
for the case of an outer regular measure. -/
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop._root_.MeasureTheory.NullMeasur
ableSet.exists_isOpen_symmDiff_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re.InnerRegularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `μ` be a locally finite measure on an R₁ topological space with Borel σ-alge
bra.
If `μ` is inner regular for finite measure sets with respect to compact sets,
then any null measurable set of finite measure can be approximated in measure by
 an open set.
See also `Set.exists_isOpen_lt_of_lt` and `MeasurableSet.exists_isOpen_diff_lt`
for the case of an outer regular measure.
-/
protected theorem _root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt
    [InnerRegularCompactLTTop μ] [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {s : Set α} (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, IsOpen U ∧ μ U < ∞ ∧ μ (U ∆ s) < ε := by
  rcases hs with ⟨t, htm, hst⟩
  rcases htm.exists_isOpen_symmDiff_lt (by rwa [← measure_congr hst]) hε with ⟨U, hUo, hμU, hUs⟩
  refine ⟨U, hUo, hμU, ?_⟩
  rwa [measure_congr <| (ae_eq_refl _).symmDiff hst]
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.smul** 是 Mathlib 中的一个实例，位于命名空间 
`MeasureTheory.Measure.InnerRegularCompactLTTop`。
形式化陈述：smul [h : InnerRegularCompactLTTop μ] (c : Real>=0∞) : InnerRegularCompact
LTTop (c • μ)
参数：c : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.smul`：smul (H : InnerRegularWRT μ 
p q) (c : Real>=0∞) : InnerRegularWRT (c • μ) p q
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.innerRegular`：∀ {α : Type
 u_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheor
y.Measure α}   [self : μ.InnerRegularCompactLTTop…
-/
instance smul [h : InnerRegularCompactLTTop μ] (c : ℝ≥0∞) : InnerRegularCompactLTTop (c • μ) := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]
    infer_instance
  by_cases h'c : c = ∞
  · constructor
    intro s hs r hr
    by_cases h's : μ s = 0
    · simp [h's] at hr
    · simp [h'c, h's] at hs
  · constructor
    convert! InnerRegularWRT.smul h.innerRegular c using 2 with s
    have : (c • μ) s ≠ ∞ ↔ μ s ≠ ∞ := by simp [ENNReal.mul_eq_top, hc, h'c]
    simp only [this]
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.smul_nnreal** 是 Mathlib 中的一个实例，
位于命名空间 `MeasureTheory.Measure.InnerRegularCompactLTTop`。
形式化陈述：smul_nnreal [InnerRegularCompactLTTop μ] (c : Real>=0) : InnerRegularCompa
ctLTTop (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul_nnreal [InnerRegularCompactLTTop μ] (c : ℝ≥0) :
    InnerRegularCompactLTTop (c • μ) :=
  inferInstanceAs (InnerRegularCompactLTTop ((c : ℝ≥0∞) • μ))
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.Measure.InnerRegularCompactLTTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) [InnerRegularCompactLTTop μ] [SigmaFinite μ] : InnerRegular μ :=
  ⟨InnerRegularCompactLTTop.innerRegular.trans InnerRegularWRT.of_sigmaFinite⟩
/-
**MeasureTheory.Measure.InnerRegularCompactLTTop.map_of_continuous** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure.InnerRegularCompactLTTop`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [inst_3 : Measurab
leSpace β] [inst_4 : TopologicalSpace β] [BorelSpace β]   [h : μ.InnerRegularCom
pactLTTop] {f : α → β}, Continuous f → (MeasureTheory.Measure.map f μ).InnerRegu
larCompactLTTop
参数：MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.map`：∀ {α : Type u_2} {β : Type u_
3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Me
asure α}   {pa qa : Set α → Pro…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.innerRegular`：∀ {α : Type
 u_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheor
y.Measure α}   [self : μ.InnerRegularCompactLTTop…
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
-/
protected theorem map_of_continuous [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [h : InnerRegularCompactLTTop μ] {f : α → β} (hf : Continuous f) :
    InnerRegularCompactLTTop (Measure.map f μ) := by
  constructor
  refine InnerRegularWRT.map h.innerRegular hf.aemeasurable ?_ (fun K hK ↦ hK.image hf) ?_
  · rintro s ⟨hs, h's⟩
    exact ⟨hf.measurable hs, by rwa [map_apply hf.measurable hs] at h's⟩
  · rintro s ⟨hs, -⟩
    exact hs

end InnerRegularCompactLTTop

-- Generalized and moved to another file

namespace WeaklyRegular

variable [TopologicalSpace α]

/-
**MeasureTheory.Measure.WeaklyRegular.zero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.Measure.WeaklyRegular`。
形式化陈述：zero : WeaklyRegular (0 : Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
-/
instance zero : WeaklyRegular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isClosed_empty, hr⟩⟩

/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
/-
**MeasureTheory.Measure.WeaklyRegular._root_.IsOpen.exists_lt_isClosed** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is a weakly regular measure, then any open set can be approximated by a c
losed subset.
-/
theorem _root_.IsOpen.exists_lt_isClosed [WeaklyRegular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ F, F ⊆ U ∧ IsClosed F ∧ r < μ F :=
  WeaklyRegular.innerRegular hU r hr

/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
/-
**MeasureTheory.Measure.WeaklyRegular._root_.IsOpen.measure_eq_iSup_isClosed** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is a weakly regular measure, then any open set can be approximated by a c
losed subset.
-/
theorem _root_.IsOpen.measure_eq_iSup_isClosed ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [WeaklyRegular μ] : μ U = ⨆ (F) (_ : F ⊆ U) (_ : IsClosed F), μ F :=
  WeaklyRegular.innerRegular.measure_eq_iSup hU
/-
**MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
形式化陈述：innerRegular_measurable [WeaklyRegular μ] : InnerRegularWRT μ IsClosed fun
 s => MeasurableSet s ∧ μ s != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.measurableSet_of_isOpen`：measurabl
eSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen) (hd : forall ⦃s
 U⦄, p s -> IsOpen U -> p (s \ U)) : InnerRegularWR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.innerRegular`：∀ {α : Type u_1} {inst
 : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α
}   [self : μ.WeaklyRegular], μ.InnerR…
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
-/
theorem innerRegular_measurable [WeaklyRegular μ] :
    InnerRegularWRT μ IsClosed fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  WeaklyRegular.innerRegular.measurableSet_of_isOpen (fun _ _ h₁ h₂ ↦ h₁.inter h₂.isClosed_compl)

/-- If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `ε` is a positive
number, then there exist a closed set `K ⊆ s` such that `μ s < μ K + ε`. -/
/-
**MeasureTheory.Measure.WeaklyRegular._root_.MeasurableSet.exists_isClosed_lt_ad
d** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `
ε` is a positive
number, then there exist a closed set `K ⊆ s` such that `μ s < μ K + ε`.
-/
theorem _root_.MeasurableSet.exists_isClosed_lt_add [WeaklyRegular μ] {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ s ∧ IsClosed K ∧ μ s < μ K + ε :=
  innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε
/-
**MeasureTheory.Measure.WeaklyRegular._root_.MeasurableSet.exists_isClosed_sdiff
_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableSet.exists_isClosed_sdiff_lt [OpensMeasurableSpace α] [WeaklyRegular μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ F, F ⊆ A ∧ IsClosed F ∧ μ (A \ F) < ε := by
  rcases hA.exists_isClosed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact ⟨F, hFA, hFc, measure_sdiff_lt_of_lt_add hFc.nullMeasurableSet hFA
    (ne_top_of_le_ne_top h'A <| measure_mono hFA) hF⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isClosed_diff_lt := _root_.MeasurableSet.exists_isClosed_sdiff_lt

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
/-
**MeasureTheory.Measure.WeaklyRegular._root_.MeasurableSet.exists_lt_isClosed_of
_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a weakly regular measure, any measurable set of finite mass can be approxi
mated from
inside by closed sets.
-/
theorem _root_.MeasurableSet.exists_lt_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsClosed K ∧ r < μ K :=
  innerRegular_measurable ⟨hA, h'A⟩ _ hr

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
/-
**MeasureTheory.Measure.WeaklyRegular._root_.MeasurableSet.measure_eq_iSup_isClo
sed_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a weakly regular measure, any measurable set of finite mass can be approxi
mated from
inside by closed sets.
-/
theorem _root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (_ : IsClosed K), μ K :=
  innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩

/-- The restriction of a weakly regular measure to a measurable set of finite measure is
weakly regular. -/
/-
**MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure.WeaklyRegular`。
形式化陈述：restrict_of_measure_ne_top [BorelSpace α] [WeaklyRegular μ] {A : Set α} (h
'A : μ A != ∞) : WeaklyRegular (μ.restrict A)
参数：h'A : μ A != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.weaklyRegular_of_finite`：weaklyReg
ular_of_finite [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ] (H : InnerRegu
larWRT μ IsClosed IsOpen) : WeaklyRegular μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用引理 `MeasureTheory.Measure.InnerRegularWRT.restrict_of_measure_ne_top`：restri
ct_of_measure_ne_top (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s !=
 ∞)) {A : Set α} (hA : μ A != ∞) : InnerRegularWRT (μ.…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable`：innerRegula
r_measurable [WeaklyRegular μ] : InnerRegularWRT μ IsClosed fun s => MeasurableS
et s ∧ μ s != ∞
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α

--- 原说明 ---
The restriction of a weakly regular measure to a measurable set of finite measur
e is
weakly regular.
-/
theorem restrict_of_measure_ne_top [BorelSpace α] [WeaklyRegular μ] {A : Set α}
    (h'A : μ A ≠ ∞) : WeaklyRegular (μ.restrict A) := by
  have : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine InnerRegularWRT.weaklyRegular_of_finite (μ.restrict A) (fun V V_open r hr ↦ ?_)
  have : InnerRegularWRT (μ.restrict A) IsClosed (fun s ↦ MeasurableSet s) :=
    InnerRegularWRT.restrict_of_measure_ne_top innerRegular_measurable h'A
  exact this V_open.measurableSet r hr

-- see Note [lower instance priority]
/-- Any finite measure on a metrizable space (or even a pseudometrizable space)
is weakly regular. -/
/-
**MeasureTheory.Measure.WeaklyRegular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any finite measure on a metrizable space (or even a pseudometrizable space)
is weakly regular.
-/
instance (priority := 100) of_pseudoMetrizableSpace_of_isFiniteMeasure {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    WeaklyRegular μ :=
  (InnerRegularWRT.of_pseudoMetrizableSpace μ).weaklyRegular_of_finite μ

-- see Note [lower instance priority]
/-- Any locally finite measure on a second countable metrizable space
(or even a pseudometrizable space) is weakly regular. -/
/-
**MeasureTheory.Measure.WeaklyRegular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
Measure.WeaklyRegular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any locally finite measure on a second countable metrizable space
(or even a pseudometrizable space) is weakly regular.
-/
instance (priority := 100) of_pseudoMetrizableSpace_secondCountable_of_locallyFinite {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : WeaklyRegular μ :=
  have : OuterRegular μ := by
    refine (μ.finiteSpanningSetsInOpen'.mono' fun U hU => ?_).outerRegular
    have : Fact (μ U < ∞) := ⟨hU.2⟩
    exact ⟨hU.1, inferInstance⟩
  ⟨InnerRegularWRT.of_pseudoMetrizableSpace μ⟩
/-
**MeasureTheory.Measure.WeaklyRegular.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.WeaklyRegular`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
[inst_1 : TopologicalSpace α]   [μ.WeaklyRegular] {x : ENNReal}, x ≠ ⊤ → (x • μ)
.WeaklyRegular
参数：x • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.OuterRegular.smul`：∀ {α : Type u_1} [inst : Measur
ableSpace α] [inst_1 : TopologicalSpace α] (μ : MeasureTheory.Measure α) [μ.Oute
rRegular]   {x : ENNReal}, x …
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.smul`：smul (H : InnerRegularWRT μ 
p q) (c : Real>=0∞) : InnerRegularWRT (c • μ) p q
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.innerRegular`：∀ {α : Type u_1} {inst
 : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α
}   [self : μ.WeaklyRegular], μ.InnerR…
-/
protected theorem smul [WeaklyRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).WeaklyRegular := by
  have := OuterRegular.smul μ hx
  exact ⟨WeaklyRegular.innerRegular.smul x⟩
/-
**MeasureTheory.Measure.WeaklyRegular.smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.Measure.WeaklyRegular`。
形式化陈述：smul_nnreal [WeaklyRegular μ] (c : Real>=0) : WeaklyRegular (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.smul`：∀ {α : Type u_1} [inst : Measu
rableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [μ.W
eaklyRegular] {x : ENNReal}, x…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
instance smul_nnreal [WeaklyRegular μ] (c : ℝ≥0) : WeaklyRegular (c • μ) :=
  WeaklyRegular.smul coe_ne_top

end WeaklyRegular

namespace Regular

variable [TopologicalSpace α]

/-
**MeasureTheory.Measure.Regular.zero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Me
asure.Regular`。
形式化陈述：zero : Regular (0 : Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
-/
instance zero : Regular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

/-- If `μ` is a regular measure, then any open set can be approximated by a compact subset. -/
/-
**MeasureTheory.Measure.Regular._root_.IsOpen.exists_lt_isCompact** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is a regular measure, then any open set can be approximated by a compact 
subset.
-/
theorem _root_.IsOpen.exists_lt_isCompact [Regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ K, K ⊆ U ∧ IsCompact K ∧ r < μ K :=
  Regular.innerRegular hU r hr

/-- The measure of an open set is the supremum of the measures of compact sets it contains. -/
/-
**MeasureTheory.Measure.Regular._root_.IsOpen.measure_eq_iSup_isCompact** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Measure.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure of an open set is the supremum of the measures of compact sets it co
ntains.
-/
theorem _root_.IsOpen.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [Regular μ] : μ U = ⨆ (K : Set α) (_ : K ⊆ U) (_ : IsCompact K), μ K :=
  Regular.innerRegular.measure_eq_iSup hU
/-
**MeasureTheory.Measure.Regular.exists_isCompact_not_null** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.Regular`。
形式化陈述：exists_isCompact_not_null [Regular μ] : (exists K, IsCompact K ∧ μ K != 0)
 ↔ μ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOpen.measure_eq_iSup_isCompact`：∀ {α : Type u_1} [inst : MeasurableSpa
ce α] [inst_1 : TopologicalSpace α] ⦃U : Set α⦄,   IsOpen U → ∀ (μ : MeasureTheo
ry.Measure α) [μ.Regul…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_isCompact_not_null [Regular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne, ← measure_univ_eq_zero, isOpen_univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
/-
**MeasureTheory.Measure.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measur
e.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is a regular measure, then any measurable set of finite measure can be ap
proximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`.
-/
instance (priority := 100) [Regular μ] : InnerRegularCompactLTTop μ :=
  ⟨Regular.innerRegular.measurableSet_of_isOpen (fun _ _ hs hU ↦ hs.diff hU)⟩
/-
**MeasureTheory.Measure.Regular.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure.Regular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [inst_3 : Measurab
leSpace β] [inst_4 : TopologicalSpace β] [BorelSpace β] [μ.Regular] (f : α ≃ₜ β)
,   (MeasureTheory.Measure.map (⇑f) μ).Regular
参数：f : α ≃ₜ β；MeasureTheory.Measure.map (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.OuterRegular.map`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasurableSpace α
]   [inst_3 : MeasurableSpac…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.Regular.toOuterRegular`：∀ {α : Type u_1} {inst : M
easurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   
[self : μ.Regular], μ.OuterRegular
· 使用定理 `MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map`：∀ {α : Type u_1} {β
 : Type u_2} [inst : TopologicalSpace α] {mα : MeasurableSpace α} [BorelSpace α]
   [mβ : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.map'`：map' {α β} [MeasurableSpace 
α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α -> Prop} (H : InnerRegular
WRT μ pa qa) (f : α ≃ᵐ β) {pb qb…
· 使用定理 `MeasureTheory.Measure.Regular.innerRegular`：∀ {α : Type u_1} {inst : Mea
surableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   [s
elf : μ.Regular], μ.InnerRegular…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
-/
protected theorem map [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [Regular μ] (f : α ≃ₜ β) : (Measure.map f μ).Regular := by
  have := OuterRegular.map f μ
  have := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨Regular.innerRegular.map' f.toMeasurableEquiv
        (fun U hU => hU.preimage f.continuous)
        (fun K hK => hK.image f.continuous)⟩
/-
**MeasureTheory.Measure.Regular.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.Regular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [inst_3 : Measurab
leSpace β] [inst_4 : TopologicalSpace β] [BorelSpace β] (f : α ≃ₜ β),   (Measure
Theory.Measure.map (⇑f) μ).Regular ↔ μ.Regular
参数：f : α ≃ₜ β；MeasureTheory.Measure.map (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.symm_comp_self`：symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
-/
protected theorem map_iff [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) :
    Regular (Measure.map f μ) ↔ Regular μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp

open Topology in
/-
**MeasureTheory.Measure.Regular.comap'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure.Regular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topol
ogicalSpace α] [BorelSpace α]   {mβ : MeasurableSpace β} [inst_3 : TopologicalSp
ace β] [BorelSpace β] (μ : MeasureTheory.Measure β) [μ.Regular]   {f : α → β}, T
opology.IsOpenEmbedding f → (MeasureTheory.Measure.comap f μ).Regular
参数：μ : MeasureTheory.Measure β；MeasureTheory.Measure.comap f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.OuterRegular.comap'`：comap' {mβ : MeasurableSpace 
β} [TopologicalSpace β] (μ : Measure β) [OuterRegular μ] {f : α -> β} (f_cont : 
Continuous f) (f_me : Measurabl…
· 使用定理 `MeasureTheory.Measure.Regular.toOuterRegular`：∀ {α : Type u_1} {inst : M
easurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   
[self : μ.Regular], μ.OuterRegular
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `Topology.IsOpenEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [mβ 
: TopologicalSpace β] [inst_2 : Me…
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.comap'`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : TopologicalSpa
ce α]   [inst_1 : TopologicalSpace β…
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.comap`：∀ {α : Type u_2} {β : Type 
u_3} [inst : MeasurableSpace α] {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure β}   {pa qa : Set α → Prop} {…
· 使用定理 `MeasureTheory.Measure.Regular.innerRegular`：∀ {α : Type u_1} {inst : Mea
surableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   [s
elf : μ.Regular], μ.InnerRegular…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   Topology.IsOpenEmbedding f → ∀ {s :…
· 使用引理 `Topology.IsInducing.isCompact_preimage'`：Topology.IsInducing.isCompact_p
reimage' (hf : IsInducing f) {K : Set Y} (hK : IsCompact K) (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K)
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
-/
protected theorem comap' [BorelSpace α]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β] (μ : Measure β) [Regular μ]
    {f : α → β} (hf : IsOpenEmbedding f) : (μ.comap f).Regular := by
  have := OuterRegular.comap' μ hf.continuous hf.measurableEmbedding
  have := IsFiniteMeasureOnCompacts.comap' μ hf.continuous hf.measurableEmbedding
  exact ⟨InnerRegularWRT.comap Regular.innerRegular hf.measurableEmbedding
    (fun _ hU ↦ hf.isOpen_iff_image_isOpen.mp hU)
    (fun _ hKrange hK ↦ hf.isInducing.isCompact_preimage' hK hKrange)⟩
/-
**MeasureTheory.Measure.Regular.comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure.Regular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topol
ogicalSpace α] [BorelSpace α]   {mβ : MeasurableSpace β} [inst_3 : TopologicalSp
ace β] [BorelSpace β] (μ : MeasureTheory.Measure β) [μ.Regular]   (f : α ≃ₜ β), 
(MeasureTheory.Measure.comap (⇑f) μ).Regular
参数：μ : MeasureTheory.Measure β；f : α ≃ₜ β；MeasureTheory.Measure.comap (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.Regular.comap'`：∀ {α : Type u_1} {β : Type u_2} [i
nst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [BorelSpace α]   {mβ : Me
asurableSpace β} [inst_3 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
protected theorem comap [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β]
    [BorelSpace β] (μ : Measure β) [Regular μ] (f : α ≃ₜ β) : (μ.comap f).Regular :=
  Regular.comap' μ f.isOpenEmbedding
/-
**MeasureTheory.Measure.Regular.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure.Regular`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
[inst_1 : TopologicalSpace α] [μ.Regular]   {x : ENNReal}, x ≠ ⊤ → (x • μ).Regul
ar
参数：x • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.OuterRegular.smul`：∀ {α : Type u_1} [inst : Measur
ableSpace α] [inst_1 : TopologicalSpace α] (μ : MeasureTheory.Measure α) [μ.Oute
rRegular]   {x : ENNReal}, x …
· 使用定理 `MeasureTheory.Measure.Regular.toOuterRegular`：∀ {α : Type u_1} {inst : M
easurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   
[self : μ.Regular], μ.OuterRegular
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.smul`：∀ {α : Type u_1} {m0 : Mea
surableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [Mea
sureTheory.IsFiniteMeasureOnCompac…
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.smul`：smul (H : InnerRegularWRT μ 
p q) (c : Real>=0∞) : InnerRegularWRT (c • μ) p q
· 使用定理 `MeasureTheory.Measure.Regular.innerRegular`：∀ {α : Type u_1} {inst : Mea
surableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   [s
elf : μ.Regular], μ.InnerRegular…
-/
protected theorem smul [Regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).Regular := by
  have := OuterRegular.smul μ hx
  have := IsFiniteMeasureOnCompacts.smul μ hx
  exact ⟨Regular.innerRegular.smul x⟩
/-
**MeasureTheory.Measure.Regular.smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Measure.Regular`。
形式化陈述：smul_nnreal [Regular μ] (c : Real>=0) : Regular (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.Regular.smul`：∀ {α : Type u_1} [inst : MeasurableS
pace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.Regular] 
  {x : ENNReal}, x ≠ ⊤ →…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
instance smul_nnreal [Regular μ] (c : ℝ≥0) : Regular (c • μ) := Regular.smul coe_ne_top

/-- The restriction of a regular measure to a set of finite measure is regular. -/
/-
**MeasureTheory.Measure.Regular.restrict_of_measure_ne_top** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.Regular`。
形式化陈述：restrict_of_measure_ne_top [R1Space α] [BorelSpace α] [Regular μ] {A : Set
 α} (h'A : μ A != ∞) : Regular (μ.restrict A)
参数：h'A : μ A != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top`：restrict
_of_measure_ne_top [BorelSpace α] [WeaklyRegular μ] {A : Set α} (h'A : μ A != ∞)
 : WeaklyRegular (μ.restrict A)
· 使用定理 `MeasureTheory.Measure.Regular.weaklyRegular`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [R1
Space α]   [μ.Regular], μ.WeaklyR…
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasurableSet.exists_lt_isCompact_of_ne_top`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [
μ.InnerRegularCompactLTTop] ⦃A : …
· 使用定理 `MeasureTheory.Measure.Regular.instInnerRegularCompactLTTop`：∀ {α : Type 
u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologi
calSpace α] [μ.Regular],   μ.InnerRegularCompact…

--- 原说明 ---
The restriction of a regular measure to a set of finite measure is regular.
-/
theorem restrict_of_measure_ne_top [R1Space α] [BorelSpace α] [Regular μ]
    {A : Set α} (h'A : μ A ≠ ∞) : Regular (μ.restrict A) := by
  have : WeaklyRegular (μ.restrict A) := WeaklyRegular.restrict_of_measure_ne_top h'A
  constructor
  intro V hV r hr
  have R : restrict μ A V ≠ ∞ := by
    rw [restrict_apply hV.measurableSet]
    exact ((measure_mono inter_subset_right).trans_lt h'A.lt_top).ne
  exact MeasurableSet.exists_lt_isCompact_of_ne_top hV.measurableSet R hr

end Regular

/-
**MeasureTheory.Measure.Regular.domSMul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.Regular`。
形式化陈述：∀ {G : Type u_3} {A : Type u_4} [inst : Group G] [inst_1 : AddCommGroup A]
 [inst_2 : DistribMulAction G A]   [inst_3 : MeasurableSpace A] [inst_4 : Topolo
gicalSpace A] [inst_5 : BorelSpace A] [inst_6 : ContinuousConstSMul G A]   {μ : 
MeasureTheory.Measure A} (g : Gᵈᵐᵃ) [μ.Regular], (g • μ).Regular
参数：g : Gᵈᵐᵃ；g • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Regular.domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [ContinuousConstSMul G A]
    {μ : Measure A} (g : Gᵈᵐᵃ) [Regular μ] : Regular (g • μ) :=
  .map <| .smul ((DomMulAct.mk.symm g : G)⁻¹)

-- see Note [lower instance priority]
/-- Any locally finite measure on a `σ`-compact pseudometrizable space is regular. -/
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any locally finite measure on a `σ`-compact pseudometrizable space is regular.
-/
instance (priority := 100) Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : Regular μ := by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact ⟨(InnerRegularWRT.isCompact_isClosed μ).trans (InnerRegularWRT.of_pseudoMetrizableSpace μ)⟩

/-- Any sigma finite measure on a `σ`-compact pseudometrizable space is inner regular. -/
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any sigma finite measure on a `σ`-compact pseudometrizable space is inner regula
r.
-/
instance (priority := 100) {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [SigmaFinite μ] : InnerRegular μ := by
  refine ⟨(InnerRegularWRT.isCompact_isClosed μ).trans ?_⟩
  refine InnerRegularWRT.of_restrict (fun n ↦ ?_) (iUnion_spanningSets μ).superset
    (monotone_spanningSets μ)
  have : Fact (μ (spanningSets μ n) < ∞) := ⟨measure_spanningSets_lt_top μ n⟩
  exact WeaklyRegular.innerRegular_measurable.trans InnerRegularWRT.of_sigmaFinite

end Measure

end MeasureTheory

