/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Tactic.NormNum

/-!
# Filters with a cardinal intersection property

In this file we define `CardinalInterFilter l c` to be the class of filters with the following
property: for any collection of sets `s ∈ l` with cardinality strictly less than `c`,
their intersection belongs to `l` as well.

## Main results
* `Filter.cardinalInterFilter_aleph0` establishes that every filter `l` is a
    `CardinalInterFilter l ℵ₀`
* `CardinalInterFilter.toCountableInterFilter` establishes that every `CardinalInterFilter l c` with
    `c > ℵ₀` is a `CountableInterFilter`.
* `CountableInterFilter.toCardinalInterFilter` establishes that every `CountableInterFilter l` is a
    `CardinalInterFilter l ℵ₁`.
* `CardinalInterFilter.of_cardinalInterFilter_of_lt` establishes that we have
  `CardinalInterFilter l c` → `CardinalInterFilter l a` for all `a < c`.

## Tags
filter, cardinal
-/

@[expose] public section


open Set Filter Cardinal

universe u
variable {ι : Type u} {α β : Type u} {c : Cardinal.{u}}

/--
Definition of `CardinalInterFilter` / `CardinalInterFilter` 的定义

English:
class CardinalInterFilter
  parameters: (l : Filter α) (c : Cardinal.{u})
  axioms and operations (1):
    - cardinal_sInter_mem : forall S : Set (Set α), (#S < c) -> (forall s in S, s in l) -> ⋂₀ S in l

中文:
类 Cardinal整数erFilter
  参数: (l : 滤子 α) (c : 基数.{u})
  公理与运算 (1 个):
    - cardinal_sInter_mem : 对任意 S : 集合 (集合 α), (#S < c) -> (对任意 s in S, s in l) -> ⋂₀ S in l

Depends on / 依赖: UniqueFactorizationMonoid, to_uniqueFactorizationMonoid
-/
class CardinalInterFilter (l : Filter α) (c : Cardinal.{u}) : Prop where
  /-- For a collection of sets `s ∈ l` with cardinality below c,
  their intersection belongs to `l` as well. -/
  cardinal_sInter_mem : forall S : Set (Set α), (#S < c) -> (forall s in S, s in l) -> ⋂₀ S in l

variable {l : Filter α}

/--
theorem `cardinal_sInter_mem` / 定理 `cardinal_sInter_mem`

English:
theorem cardinal_sInter_mem
  given: {S : Set (Set α)} [CardinalInterFilter l c] (hSc : #S < c)
  proof: ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ hSc⟩

中文:
定理 cardinal_s整数er_mem
  条件: {S : 集合 (集合 α)} [Cardinal整数erFilter l c] (hSc : #S < c)
  证明: ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ hSc⟩

Depends on / 依赖: mem_of_superset, sInter_subset_of_mem
-/
theorem cardinal_sInter_mem {S : Set (Set α)} [CardinalInterFilter l c] (hSc : #S < c) :
    ⋂₀ S in l ↔ forall s in S, s in l := ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ hSc⟩

/--
theorem `_root_.Filter.cardinalInterFilter_aleph0` / 定理 `_root_.Filter.cardinalInterFilter_aleph0`

English:
theorem _root_.Filter.cardinalInterFilter_aleph0
  given: (l : Filter α)
  statement: CardinalInterFilter l ℵ₀ where
  proof: by
    simp_all only [lt_aleph0_iff_subtype_finite, ofPred_mem_eq, sInter_mem,
      implies_true]

中文:
定理 _root_.滤子.cardinal整数erFilter_aleph0
  条件: (l : 滤子 α)
  结论: Cardinal整数erFilter l ℵ₀ where
  证明: by
    simp_all only [lt_aleph0_iff_subtype_finite, ofPred_mem_eq, sInter_mem,
      implies_true]

Depends on / 依赖: implies_true, lt_aleph0_iff_subtype_finite, ofPred_mem_eq, sInter_mem
-/
theorem _root_.Filter.cardinalInterFilter_aleph0 (l : Filter α) : CardinalInterFilter l ℵ₀ where
  cardinal_sInter_mem := by
    simp_all only [lt_aleph0_iff_subtype_finite, ofPred_mem_eq, sInter_mem,
      implies_true]

/--
theorem `CardinalInterFilter.toCountableInterFilter` / 定理 `CardinalInterFilter.toCountableInterFilter`

English:
theorem CardinalInterFilter.toCountableInterFilter
  statement: (l : Filter α) [CardinalInterFilter l c]
  proof: CardinalInterFilter.cardinal_sInter_mem S (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

中文:
定理 Cardinal整数erFilter.toCountable整数erFilter
  结论: (l : 滤子 α) [Cardinal整数erFilter l c]
  证明: CardinalInterFilter.cardinal_sInter_mem S (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

Depends on / 依赖: CardinalInterFilter, CardinalInterFilter.cardinal_sInter_mem, Countable, Set.Countable.le_aleph0, cardinal_sInter_mem, le_aleph0, lt_of_le_of_lt
-/
theorem CardinalInterFilter.toCountableInterFilter (l : Filter α) [CardinalInterFilter l c]
    (hc : ℵ₀ < c) : CountableInterFilter l where
  countable_sInter_mem S hS a :=
    CardinalInterFilter.cardinal_sInter_mem S (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

/--
Instance `CountableInterFilter.toCardinalInterFilter` / 实例 `CountableInterFilter.toCardinalInterFilter`

English:
instance CountableInterFilter.toCardinalInterFilter
  signature: (l : Filter α) [CountableInterFilter l]
  body: by
    apply CountableInterFilter.countable_sInter_mem S _ a
    rwa [← le_aleph0_iff_set_countable, ← lt_aleph_one_iff]

中文:
实例 余untable整数erFilter.toCardinal整数erFilter
  签名: (l : 滤子 α) [余untable整数erFilter l]
  定义体: by
    apply CountableInterFilter.countable_sInter_mem S _ a
    rwa [← le_aleph0_iff_set_countable, ← lt_aleph_one_iff]

Depends on / 依赖: CountableInterFilter, CountableInterFilter.countable_sInter_mem, countable_sInter_mem, le_aleph0_iff_set_countable, lt_aleph_one_iff
-/
instance CountableInterFilter.toCardinalInterFilter (l : Filter α) [CountableInterFilter l] :
    CardinalInterFilter l ℵ₁ where
  cardinal_sInter_mem S hS a := by
    apply CountableInterFilter.countable_sInter_mem S _ a
    rwa [← le_aleph0_iff_set_countable, ← lt_aleph_one_iff]

/--
theorem `cardinalInterFilter_aleph_one_iff` / 定理 `cardinalInterFilter_aleph_one_iff`

English:
theorem cardinalInterFilter_aleph_one_iff
  statement: CardinalInterFilter l ℵ₁ ↔ CountableInterFilter l where
  proof: CountableInterFilter.toCardinalInterFilter l
  mp _ := by
    refine ⟨fun S h a => CardinalInterFilter.cardinal_sInter_mem (c := ℵ₁) S ?_ a⟩
    rwa [lt_aleph_one_iff, le_aleph0_iff_set_countable]

中文:
定理 cardinal整数erFilter_aleph_one_iff
  结论: Cardinal整数erFilter l ℵ₁ ↔ 余untable整数erFilter l where
  证明: CountableInterFilter.toCardinalInterFilter l
  mp _ := by
    refine ⟨fun S h a => CardinalInterFilter.cardinal_sInter_mem (c := ℵ₁) S ?_ a⟩
    rwa [lt_aleph_one_iff, le_aleph0_iff_set_countable]

Depends on / 依赖: CountableInterFilter, CountableInterFilter.toCardinalInterFilter, toCardinalInterFilter
-/
theorem cardinalInterFilter_aleph_one_iff : CardinalInterFilter l ℵ₁ ↔ CountableInterFilter l where
  mpr _ := CountableInterFilter.toCardinalInterFilter l
  mp _ := by
    refine ⟨fun S h a => CardinalInterFilter.cardinal_sInter_mem (c := ℵ₁) S ?_ a⟩
    rwa [lt_aleph_one_iff, le_aleph0_iff_set_countable]

/--
theorem `CardinalInterFilter.of_cardinalInterFilter_of_le` / 定理 `CardinalInterFilter.of_cardinalInterFilter_of_le`

English:
theorem CardinalInterFilter.of_cardinalInterFilter_of_le
  statement: (l : Filter α) [CardinalInterFilter l c]
  proof: CardinalInterFilter.cardinal_sInter_mem S (lt_of_lt_of_le hS hac) a

中文:
定理 Cardinal整数erFilter.of_cardinal整数erFilter_of_le
  结论: (l : 滤子 α) [Cardinal整数erFilter l c]
  证明: CardinalInterFilter.cardinal_sInter_mem S (lt_of_lt_of_le hS hac) a

Depends on / 依赖: CardinalInterFilter, CardinalInterFilter.cardinal_sInter_mem, cardinal_sInter_mem, lt_of_lt_of_le
-/
theorem CardinalInterFilter.of_cardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a <= c) :
    CardinalInterFilter l a where
  cardinal_sInter_mem S hS a :=
    CardinalInterFilter.cardinal_sInter_mem S (lt_of_lt_of_le hS hac) a

/--
theorem `CardinalInterFilter.of_cardinalInterFilter_of_lt` / 定理 `CardinalInterFilter.of_cardinalInterFilter_of_lt`

English:
theorem CardinalInterFilter.of_cardinalInterFilter_of_lt
  statement: (l : Filter α) [CardinalInterFilter l c]
  proof: CardinalInterFilter.of_cardinalInterFilter_of_le l (hac.le)

中文:
定理 Cardinal整数erFilter.of_cardinal整数erFilter_of_lt
  结论: (l : 滤子 α) [Cardinal整数erFilter l c]
  证明: CardinalInterFilter.of_cardinalInterFilter_of_le l (hac.le)

Depends on / 依赖: CardinalInterFilter, CardinalInterFilter.of_cardinalInterFilter_of_le, hac.le, of_cardinalInterFilter_of_le
-/
theorem CardinalInterFilter.of_cardinalInterFilter_of_lt (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a < c) : CardinalInterFilter l a :=
  CardinalInterFilter.of_cardinalInterFilter_of_le l (hac.le)

namespace Filter

variable [CardinalInterFilter l c]

/--
theorem `cardinal_iInter_mem` / 定理 `cardinal_iInter_mem`

English:
theorem cardinal_iInter_mem
  given: {s : ι -> Set α} (hic : #ι < c)
  proof: by
  rw [← sInter_range _]
  apply (cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)).trans
  exact forall_mem_range

中文:
定理 cardinal_i整数er_mem
  条件: {s : ι -> 集合 α} (hic : #ι < c)
  证明: by
  rw [← sInter_range _]
  apply (cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)).trans
  exact forall_mem_range

Depends on / 依赖: Cardinal, Cardinal.mk_range_le, cardinal_sInter_mem, forall_mem_range, lt_of_le_of_lt, mk_range_le, sInter_range
-/
theorem cardinal_iInter_mem {s : ι -> Set α} (hic : #ι < c) :
    (⋂ i, s i) in l ↔ forall i, s i in l := by
  rw [← sInter_range _]
  apply (cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)).trans
  exact forall_mem_range

/--
theorem `cardinal_bInter_mem` / 定理 `cardinal_bInter_mem`

English:
theorem cardinal_bInter_mem
  statement: {S : Set ι} (hS : #S < c)
  proof: by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall

中文:
定理 cardinal_b整数er_mem
  结论: {S : 集合 ι} (hS : #S < c)
  证明: by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall, biInter_eq_iInter, cardinal_iInter_mem
-/
theorem cardinal_bInter_mem {S : Set ι} (hS : #S < c)
    {s : forall i in S, Set α} :
    (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ forall i, forall hi : i in S, s i ‹_› in l := by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall

/--
theorem `eventually_cardinal_forall` / 定理 `eventually_cardinal_forall`

English:
theorem eventually_cardinal_forall
  given: {p : α -> ι -> Prop} (hic : #ι < c)
  proof: by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_iInter_mem hic

中文:
定理 eventually_cardinal_对任意
  条件: {p : α -> ι -> 命题} (hic : #ι < c)
  证明: by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_iInter_mem hic

Depends on / 依赖: Eventually, Filter, Filter.Eventually, cardinal_iInter_mem, ofPred_forall
-/
theorem eventually_cardinal_forall {p : α -> ι -> Prop} (hic : #ι < c) :
    (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in l, p x i := by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_iInter_mem hic

/--
theorem `eventually_cardinal_ball` / 定理 `eventually_cardinal_ball`

English:
theorem eventually_cardinal_ball
  statement: {S : Set ι} (hS : #S < c)
  proof: by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_bInter_mem hS

中文:
定理 eventually_cardinal_ball
  结论: {S : 集合 ι} (hS : #S < c)
  证明: by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_bInter_mem hS

Depends on / 依赖: Eventually, Filter, Filter.Eventually, cardinal_bInter_mem, ofPred_forall
-/
theorem eventually_cardinal_ball {S : Set ι} (hS : #S < c)
    {p : α -> forall i in S, Prop} :
    (forallᶠ x in l, forall i hi, p x i hi) ↔ forall i hi, forallᶠ x in l, p x i hi := by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_bInter_mem hS

/--
theorem `EventuallyLE.cardinal_iUnion` / 定理 `EventuallyLE.cardinal_iUnion`

English:
theorem EventuallyLE.cardinal_iUnion
  statement: {s t : ι -> Set α} (hic : #ι < c)
  proof: ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2
    (mem_iUnion.1 hs).imp hst

中文:
定理 EventuallyLE.cardinal_iUnion
  结论: {s t : ι -> 集合 α} (hic : #ι < c)
  证明: ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2
    (mem_iUnion.1 hs).imp hst

Depends on / 依赖: eventually_cardinal_forall, mem_iUnion
-/
theorem EventuallyLE.cardinal_iUnion {s t : ι -> Set α} (hic : #ι < c)
    (h : forall i, s i <=ᶠ[l] t i) : ⋃ i, s i <=ᶠ[l] ⋃ i, t i :=
((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2
    (mem_iUnion.1 hs).imp hst

/--
theorem `EventuallyEq.cardinal_iUnion` / 定理 `EventuallyEq.cardinal_iUnion`

English:
theorem EventuallyEq.cardinal_iUnion
  statement: {s t : ι -> Set α} (hic : #ι < c)
  proof: (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)

中文:
定理 EventuallyEq.cardinal_iUnion
  结论: {s t : ι -> 集合 α} (hic : #ι < c)
  证明: (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)

Depends on / 依赖: EventuallyLE, EventuallyLE.cardinal_iUnion, antisymm, cardinal_iUnion, symm.le
-/
theorem EventuallyEq.cardinal_iUnion {s t : ι -> Set α} (hic : #ι < c)
    (h : forall i, s i =ᶠ[l] t i) : ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)

/--
theorem `EventuallyLE.cardinal_bUnion` / 定理 `EventuallyLE.cardinal_bUnion`

English:
theorem EventuallyLE.cardinal_bUnion
  statement: {S : Set ι} (hS : #S < c)
  proof: by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2

中文:
定理 EventuallyLE.cardinal_bUnion
  结论: {S : 集合 ι} (hS : #S < c)
  证明: by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2

Depends on / 依赖: EventuallyLE, EventuallyLE.cardinal_iUnion, biUnion_eq_iUnion, cardinal_iUnion
-/
theorem EventuallyLE.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi <=ᶠ[l] t i hi) :
    ⋃ i in S, s i ‹_› <=ᶠ[l] ⋃ i in S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2

/--
theorem `EventuallyEq.cardinal_bUnion` / 定理 `EventuallyEq.cardinal_bUnion`

English:
theorem EventuallyEq.cardinal_bUnion
  statement: {S : Set ι} (hS : #S < c)
  proof: (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)

中文:
定理 EventuallyEq.cardinal_bUnion
  结论: {S : 集合 ι} (hS : #S < c)
  证明: (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)

Depends on / 依赖: EventuallyLE, EventuallyLE.cardinal_bUnion, antisymm, cardinal_bUnion, symm.le
-/
theorem EventuallyEq.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i in S, s i ‹_› =ᶠ[l] ⋃ i in S, t i ‹_› :=
  (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)

/--
theorem `EventuallyLE.cardinal_iInter` / 定理 `EventuallyLE.cardinal_iInter`

English:
theorem EventuallyLE.cardinal_iInter
  statement: {s t : ι -> Set α} (hic : #ι < c)
  proof: ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

中文:
定理 EventuallyLE.cardinal_i整数er
  结论: {s t : ι -> 集合 α} (hic : #ι < c)
  证明: ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

Depends on / 依赖: eventually_cardinal_forall, mem_iInter
-/
theorem EventuallyLE.cardinal_iInter {s t : ι -> Set α} (hic : #ι < c)
    (h : forall i, s i <=ᶠ[l] t i) : ⋂ i, s i <=ᶠ[l] ⋂ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

/--
theorem `EventuallyEq.cardinal_iInter` / 定理 `EventuallyEq.cardinal_iInter`

English:
theorem EventuallyEq.cardinal_iInter
  statement: {s t : ι -> Set α} (hic : #ι < c)
  proof: (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)

中文:
定理 EventuallyEq.cardinal_i整数er
  结论: {s t : ι -> 集合 α} (hic : #ι < c)
  证明: (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)

Depends on / 依赖: EventuallyLE, EventuallyLE.cardinal_iInter, antisymm, cardinal_iInter, symm.le
-/
theorem EventuallyEq.cardinal_iInter {s t : ι -> Set α} (hic : #ι < c)
    (h : forall i, s i =ᶠ[l] t i) : ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)

/--
theorem `EventuallyLE.cardinal_bInter` / 定理 `EventuallyLE.cardinal_bInter`

English:
theorem EventuallyLE.cardinal_bInter
  statement: {S : Set ι} (hS : #S < c)
  proof: by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2

中文:
定理 EventuallyLE.cardinal_b整数er
  结论: {S : 集合 ι} (hS : #S < c)
  证明: by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2

Depends on / 依赖: EventuallyLE, EventuallyLE.cardinal_iInter, biInter_eq_iInter, cardinal_iInter
-/
theorem EventuallyLE.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi <=ᶠ[l] t i hi) :
    ⋂ i in S, s i ‹_› <=ᶠ[l] ⋂ i in S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2

/--
theorem `EventuallyEq.cardinal_bInter` / 定理 `EventuallyEq.cardinal_bInter`

English:
theorem EventuallyEq.cardinal_bInter
  statement: {S : Set ι} (hS : #S < c)
  proof: (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)

中文:
定理 EventuallyEq.cardinal_b整数er
  结论: {S : 集合 ι} (hS : #S < c)
  证明: (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)

Depends on / 依赖: EventuallyLE, EventuallyLE.cardinal_bInter, antisymm, cardinal_bInter, coprime_iff_not_dvd, hp.irreducible.coprime_iff_not_dvd, irreducible, symm.le
-/
theorem EventuallyEq.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i in S, s i ‹_› =ᶠ[l] ⋂ i in S, t i ‹_› :=
  (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)

/--
Definition of `ofCardinalInter` / `ofCardinalInter` 的定义

English:
definition ofCardinalInter
  signature: (l : Set (Set α)) (hc : 2 < c)
  body: l
  univ_sets :=
    sInter_empty ▸ hl ∅ (mk_eq_zero (∅ : Set (Set α)) ▸ lt_trans zero_lt_two hc) (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸ by
    apply hl _ (?_) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
    have : #({s, t} : Set (Set α)) <= 2 := by
      calc
      _ <= #({t} : Set (Set α)) + 1 := Cardinal.mk_insert_le
      _ = 2 := by norm_num
    exact lt_of_le_of_lt this hc

中文:
定义 ofCardinal整数er
  签名: (l : 集合 (集合 α)) (hc : 2 < c)
  定义体: l
  univ_sets :=
    sInter_empty ▸ hl ∅ (mk_eq_zero (∅ : Set (Set α)) ▸ lt_trans zero_lt_two hc) (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸ by
    apply hl _ (?_) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
    have : #({s, t} : Set (Set α)) <= 2 := by
      calc
      _ <= #({t} : Set (Set α)) + 1 := Cardinal.mk_insert_le
      _ = 2 := by norm_num
    exact lt_of_le_of_lt this hc
-/
def ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hl : forall S : Set (Set α), (#S < c) -> S subseteq l -> ⋂₀ S in l)
    (h_mono : forall s t, s in l -> s subseteq t -> t in l) : Filter α where
  sets := l
  univ_sets :=
    sInter_empty ▸ hl ∅ (mk_eq_zero (∅ : Set (Set α)) ▸ lt_trans zero_lt_two hc) (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸ by
    apply hl _ (?_) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
    have : #({s, t} : Set (Set α)) <= 2 := by
      calc
      _ <= #({t} : Set (Set α)) + 1 := Cardinal.mk_insert_le
      _ = 2 := by norm_num
    exact lt_of_le_of_lt this hc

/--
Instance `cardinalInter_ofCardinalInter` / 实例 `cardinalInter_ofCardinalInter`

English:
instance cardinalInter_ofCardinalInter
  signature: (l : Set (Set α)) (hc : 2 < c)
  body: ⟨hl⟩

@[simp]

中文:
实例 cardinal整数er_ofCardinal整数er
  签名: (l : 集合 (集合 α)) (hc : 2 < c)
  定义体: ⟨hl⟩

@[simp]
-/
instance cardinalInter_ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hl : forall S : Set (Set α), (#S < c) -> S subseteq l -> ⋂₀ S in l)
    (h_mono : forall s t, s in l -> s subseteq t -> t in l) :
    CardinalInterFilter (Filter.ofCardinalInter l hc hl h_mono) c :=
  ⟨hl⟩

@[simp]
/--
theorem `mem_ofCardinalInter` / 定理 `mem_ofCardinalInter`

English:
theorem mem_ofCardinalInter
  statement: {l : Set (Set α)} (hc : 2 < c)
  proof: Iff.rfl

中文:
定理 mem_ofCardinal整数er
  结论: {l : 集合 (集合 α)} (hc : 2 < c)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofCardinalInter {l : Set (Set α)} (hc : 2 < c)
    (hl : forall S : Set (Set α), (#S < c) -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> s subseteq t -> t in l)
    {s : Set α} : s in Filter.ofCardinalInter l hc hl h_mono ↔ s in l :=
  Iff.rfl

/--
Definition of `ofCardinalUnion` / `ofCardinalUnion` 的定义

English:
definition ofCardinalUnion
  signature: (l : Set (Set α)) (hc : 2 < c)
  body: by
  refine .ofCardinalInter {s | sᶜ in l} hc (fun S hSc hSp => ?_) fun s t ht hsub => ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (lt_of_le_of_lt mk_image_le hSc)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

中文:
定义 ofCardinalUnion
  签名: (l : 集合 (集合 α)) (hc : 2 < c)
  定义体: by
  refine .ofCardinalInter {s | sᶜ in l} hc (fun S hSc hSp => ?_) fun s t ht hsub => ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (lt_of_le_of_lt mk_image_le hSc)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

Depends on / 依赖: compl_sInter, compl_subset_compl, hUnion, lt_of_le_of_lt, mem_image, mem_ofPred_eq, mk_image_le, ofCardinalInter
-/
def ofCardinalUnion (l : Set (Set α)) (hc : 2 < c)
    (hUnion : forall S : Set (Set α), (#S < c) -> (forall s in S, s in l) -> ⋃₀ S in l)
    (hmono : forall t in l, forall s subseteq t, s in l) : Filter α := by
  refine .ofCardinalInter {s | sᶜ in l} hc (fun S hSc hSp => ?_) fun s t ht hsub => ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (lt_of_le_of_lt mk_image_le hSc)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

/--
Instance `cardinalInter_ofCardinalUnion` / 实例 `cardinalInter_ofCardinalUnion`

English:
instance cardinalInter_ofCardinalUnion
  signature: (l : Set (Set α)) (hc : 2 < c) (h₁ h₂)
  body: cardinalInter_ofCardinalInter ..

@[simp]

中文:
实例 cardinal整数er_ofCardinalUnion
  签名: (l : 集合 (集合 α)) (hc : 2 < c) (h₁ h₂)
  定义体: cardinalInter_ofCardinalInter ..

@[simp]

Depends on / 依赖: cardinalInter_ofCardinalInter
-/
instance cardinalInter_ofCardinalUnion (l : Set (Set α)) (hc : 2 < c) (h₁ h₂) :
    CardinalInterFilter (Filter.ofCardinalUnion l hc h₁ h₂) c :=
  cardinalInter_ofCardinalInter ..

@[simp]
/--
theorem `mem_ofCardinalUnion` / 定理 `mem_ofCardinalUnion`

English:
theorem mem_ofCardinalUnion
  given: {l : Set (Set α)} (hc : 2 < c) {hunion hmono s}
  proof: Iff.rfl

中文:
定理 mem_ofCardinalUnion
  条件: {l : 集合 (集合 α)} (hc : 2 < c) {hunion hmono s}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofCardinalUnion {l : Set (Set α)} (hc : 2 < c) {hunion hmono s} :
    s in ofCardinalUnion l hc hunion hmono ↔ l sᶜ :=
  Iff.rfl

/--
Instance `cardinalInterFilter_principal` / 实例 `cardinalInterFilter_principal`

English:
instance cardinalInterFilter_principal
  signature: (s : Set α)
  body: ⟨fun _ _ hS => subset_sInter hS⟩

中文:
实例 cardinal整数erFilter_principal
  签名: (s : 集合 α)
  定义体: ⟨fun _ _ hS => subset_sInter hS⟩

Depends on / 依赖: subset_sInter
-/
instance cardinalInterFilter_principal (s : Set α) : CardinalInterFilter (𝓟 s) c :=
  ⟨fun _ _ hS => subset_sInter hS⟩

/--
Instance `cardinalInterFilter_bot` / 实例 `cardinalInterFilter_bot`

English:
instance cardinalInterFilter_bot
  signature: : CardinalInterFilter (⊥ : Filter α) c
  body: by
  rw [← principal_empty]
  apply cardinalInterFilter_principal

中文:
实例 cardinal整数erFilter_bot
  签名: : Cardinal整数erFilter (⊥ : 滤子 α) c
  定义体: by
  rw [← principal_empty]
  apply cardinalInterFilter_principal

Depends on / 依赖: cardinalInterFilter_principal, principal_empty
-/
instance cardinalInterFilter_bot : CardinalInterFilter (⊥ : Filter α) c := by
  rw [← principal_empty]
  apply cardinalInterFilter_principal

/--
Instance `cardinalInterFilter_top` / 实例 `cardinalInterFilter_top`

English:
instance cardinalInterFilter_top
  signature: : CardinalInterFilter (⊤ : Filter α) c
  body: by
  rw [← principal_univ]
  apply cardinalInterFilter_principal

中文:
实例 cardinal整数erFilter_top
  签名: : Cardinal整数erFilter (⊤ : 滤子 α) c
  定义体: by
  rw [← principal_univ]
  apply cardinalInterFilter_principal

Depends on / 依赖: cardinalInterFilter_principal, principal_univ
-/
instance cardinalInterFilter_top : CardinalInterFilter (⊤ : Filter α) c := by
  rw [← principal_univ]
  apply cardinalInterFilter_principal

instance (l : Filter β) [CardinalInterFilter l c] (f : α -> β) :
    CardinalInterFilter (comap f l) c := by
  refine ⟨fun S hSc hS => ?_⟩
  choose! t htl ht using hS
  refine ⟨_, (cardinal_bInter_mem hSc).2 htl, ?_⟩
  simpa [preimage_iInter] using iInter₂_mono ht

instance (l : Filter α) [CardinalInterFilter l c] (f : α -> β) :
    CardinalInterFilter (map f l) c := by
  refine ⟨fun S hSc hS => ?_⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (cardinal_bInter_mem hSc).2 hS

/--
Instance `cardinalInterFilter_inf_eq` / 实例 `cardinalInterFilter_inf_eq`

English:
instance cardinalInterFilter_inf_eq
  signature: (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
  body: by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i in S, s i ‹_›) in l₁ := (cardinal_bInter_mem hSc).2 hs
  replace ht : (⋂ i in S, t i ‹_›) in l₂ := (cardinal_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

中文:
实例 cardinal整数erFilter_inf_eq
  签名: (l₁ l₂ : 滤子 α) [Cardinal整数erFilter l₁ c]
  定义体: by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i in S, s i ‹_›) in l₁ := (cardinal_bInter_mem hSc).2 hs
  replace ht : (⋂ i in S, t i ‹_›) in l₂ := (cardinal_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

Depends on / 依赖: cardinal_bInter_mem, iInter_subset, iInter_subset_of_subset, inter_mem_inf, inter_subset_inter, mem_of_superset, replace, subset_sInter
-/
instance cardinalInterFilter_inf_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊓ l₂) c := by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i in S, s i ‹_›) in l₁ := (cardinal_bInter_mem hSc).2 hs
  replace ht : (⋂ i in S, t i ‹_›) in l₂ := (cardinal_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

/--
Instance `cardinalInterFilter_inf` / 实例 `cardinalInterFilter_inf`

English:
instance cardinalInterFilter_inf
  signature: (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
  body: by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_inf_eq _ _

中文:
实例 cardinal整数erFilter_inf
  签名: (l₁ l₂ : 滤子 α) {c₁ c₂ : 基数.{u}}
  定义体: by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_inf_eq _ _

Depends on / 依赖: CardinalInterFilter, CardinalInterFilter.of_cardinalInterFilter_of_le, cardinalInterFilter_inf_eq, inf_le_left, inf_le_right, of_cardinalInterFilter_of_le
-/
instance cardinalInterFilter_inf (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] : CardinalInterFilter (l₁ ⊓ l₂)
    (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_inf_eq _ _

/--
Instance `cardinalInterFilter_sup_eq` / 实例 `cardinalInterFilter_sup_eq`

English:
instance cardinalInterFilter_sup_eq
  signature: (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
  body: by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (cardinal_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

中文:
实例 cardinal整数erFilter_sup_eq
  签名: (l₁ l₂ : 滤子 α) [Cardinal整数erFilter l₁ c]
  定义体: by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (cardinal_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

Depends on / 依赖: cardinal_sInter_mem, exacts
-/
instance cardinalInterFilter_sup_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊔ l₂) c := by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (cardinal_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

/--
Instance `cardinalInterFilter_sup` / 实例 `cardinalInterFilter_sup`

English:
instance cardinalInterFilter_sup
  signature: (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
  body: by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_sup_eq _ _

中文:
实例 cardinal整数erFilter_sup
  签名: (l₁ l₂ : 滤子 α) {c₁ c₂ : 基数.{u}}
  定义体: by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_sup_eq _ _

Depends on / 依赖: CardinalInterFilter, CardinalInterFilter.of_cardinalInterFilter_of_le, cardinalInterFilter_sup_eq, inf_le_left, inf_le_right, of_cardinalInterFilter_of_le
-/
instance cardinalInterFilter_sup (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] :
    CardinalInterFilter (l₁ ⊔ l₂) (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_sup_eq _ _

variable (g : Set (Set α))

/--
Inductive type `CardinalGenerateSets` / 归纳类型 `CardinalGenerateSets`

English:
inductive CardinalGenerateSets
  parameters: : Set α -> Prop
  constructors (4):
    - basic: {s : Set α} : s in g -> CardinalGenerateSets s
    - univ: CardinalGenerateSets univ
    - superset: {s t : Set α} : CardinalGenerateSets s -> s subseteq t -> CardinalGenerateSets t
    - sInter: {S : Set (Set α)} : (#S < c) -> (forall s in S, CardinalGenerateSets s) -> CardinalGenerateSets (⋂₀ S)

中文:
归纳类型 CardinalGenerateSets
  参数: : 集合 α -> 命题
  构造子 (4 个):
    - basic: {s : 集合 α} : s in g -> CardinalGenerateSets s
    - univ: CardinalGenerateSets univ
    - superset: {s t : 集合 α} : CardinalGenerateSets s -> s subseteq t -> CardinalGenerateSets t
    - sInter: {S : 集合 (集合 α)} : (#S < c) -> (对任意 s in S, CardinalGenerateSets s) -> CardinalGenerateSets (⋂₀ S)
-/
inductive CardinalGenerateSets : Set α -> Prop
  | basic {s : Set α} : s in g -> CardinalGenerateSets s
  | univ : CardinalGenerateSets univ
  | superset {s t : Set α} : CardinalGenerateSets s -> s subseteq t -> CardinalGenerateSets t
  | sInter {S : Set (Set α)} :
    (#S < c) -> (forall s in S, CardinalGenerateSets s) -> CardinalGenerateSets (⋂₀ S)

/--
Definition of `cardinalGenerate` / `cardinalGenerate` 的定义

English:
definition cardinalGenerate
  signature: (hc : 2 < c)
  body: ofCardinalInter {s | CardinalGenerateSets g s} hc (fun _ => .sInter) fun _ _ => .superset

中文:
定义 cardinalGenerate
  签名: (hc : 2 < c)
  定义体: ofCardinalInter {s | CardinalGenerateSets g s} hc (fun _ => .sInter) fun _ _ => .superset

Depends on / 依赖: CardinalGenerateSets, ofCardinalInter, sInter, superset
-/
def cardinalGenerate (hc : 2 < c) : Filter α :=
  ofCardinalInter {s | CardinalGenerateSets g s} hc (fun _ => .sInter) fun _ _ => .superset

/--
lemma `cardinalInter_ofCardinalGenerate` / 引理 `cardinalInter_ofCardinalGenerate`

English:
lemma cardinalInter_ofCardinalGenerate
  given: (hc : 2 < c)
  proof: by
  delta cardinalGenerate
  apply cardinalInter_ofCardinalInter _ _ _

中文:
引理 cardinal整数er_ofCardinalGenerate
  条件: (hc : 2 < c)
  证明: by
  delta cardinalGenerate
  apply cardinalInter_ofCardinalInter _ _ _

Depends on / 依赖: cardinalGenerate, cardinalInter_ofCardinalInter
-/
lemma cardinalInter_ofCardinalGenerate (hc : 2 < c) :
    CardinalInterFilter (cardinalGenerate g hc) c := by
  delta cardinalGenerate
  apply cardinalInter_ofCardinalInter _ _ _

variable {g}

/--
theorem `mem_cardinalGenerate_iff` / 定理 `mem_cardinalGenerate_iff`

English:
theorem mem_cardinalGenerate_iff
  given: {s : Set α} {hreg : c.IsRegular}
  proof: by
  constructor <;> intro h
  · induction h with
    | @basic s hs =>
      refine ⟨{s}, singleton_subset_iff.mpr hs, ?_⟩
      simpa [subset_refl] using IsRegular.nat_lt hreg 1
    | univ =>
      exact ⟨∅, ⟨empty_subset g, mk_eq_zero (∅ : Set <| Set α) ▸ IsRegular.nat_lt hreg 0, by simp⟩⟩
    | superset _ _ ih => exact Exists.imp (by tauto) ih
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s in S), T s H, by simpa,
        (Cardinal.card_biUnion_lt_iff_forall_of_isRegular hreg Sct).2 Tct, ?_⟩
      apply subset_sInter
      apply fun s H => subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  have : CardinalInterFilter (cardinalGenerate g (IsRegular.nat_lt hreg 2)) c :=
    cardinalInter_ofCardinalGenerate _ _
  exact mem_of_superset ((cardinal_sInter_mem Sct).mpr
    (fun s H => CardinalGenerateSets.basic (Sg H))) hS

中文:
定理 mem_cardinalGenerate_iff
  条件: {s : 集合 α} {hreg : c.是正则}
  证明: by
  constructor <;> intro h
  · induction h with
    | @basic s hs =>
      refine ⟨{s}, singleton_subset_iff.mpr hs, ?_⟩
      simpa [subset_refl] using IsRegular.nat_lt hreg 1
    | univ =>
      exact ⟨∅, ⟨empty_subset g, mk_eq_zero (∅ : Set <| Set α) ▸ IsRegular.nat_lt hreg 0, by simp⟩⟩
    | superset _ _ ih => exact Exists.imp (by tauto) ih
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s in S), T s H, by simpa,
        (Cardinal.card_biUnion_lt_iff_forall_of_isRegular hreg Sct).2 Tct, ?_⟩
      apply subset_sInter
      apply fun s H => subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  have : CardinalInterFilter (cardinalGenerate g (IsRegular.nat_lt hreg 2)) c :=
    cardinalInter_ofCardinalGenerate _ _
  exact mem_of_superset ((cardinal_sInter_mem Sct).mpr
    (fun s H => CardinalGenerateSets.basic (Sg H))) hS

Depends on / 依赖: Cardinal, Cardinal.card_biUnion_lt_iff_forall_of_isRegular, Exists, Exists.imp, IsRegular, IsRegular.nat_lt, card_biUnion_lt_iff_forall_of_isRegular, empty_subset, mk_eq_zero, nat_lt, sInter, singleton_subset_iff, singleton_subset_iff.mpr, subset_refl, subset_sInt, superset
-/
theorem mem_cardinalGenerate_iff {s : Set α} {hreg : c.IsRegular} :
    s in cardinalGenerate g (IsRegular.nat_lt hreg 2) ↔
    exists S : Set (Set α), S subseteq g ∧ (#S < c) ∧ ⋂₀ S subseteq s := by
  constructor <;> intro h
  · induction h with
    | @basic s hs =>
      refine ⟨{s}, singleton_subset_iff.mpr hs, ?_⟩
      simpa [subset_refl] using IsRegular.nat_lt hreg 1
    | univ =>
      exact ⟨∅, ⟨empty_subset g, mk_eq_zero (∅ : Set <| Set α) ▸ IsRegular.nat_lt hreg 0, by simp⟩⟩
    | superset _ _ ih => exact Exists.imp (by tauto) ih
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s in S), T s H, by simpa,
        (Cardinal.card_biUnion_lt_iff_forall_of_isRegular hreg Sct).2 Tct, ?_⟩
      apply subset_sInter
      apply fun s H => subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  have : CardinalInterFilter (cardinalGenerate g (IsRegular.nat_lt hreg 2)) c :=
    cardinalInter_ofCardinalGenerate _ _
  exact mem_of_superset ((cardinal_sInter_mem Sct).mpr
    (fun s H => CardinalGenerateSets.basic (Sg H))) hS

/--
theorem `le_cardinalGenerate_iff_of_cardinalInterFilter` / 定理 `le_cardinalGenerate_iff_of_cardinalInterFilter`

English:
theorem le_cardinalGenerate_iff_of_cardinalInterFilter
  statement: {f : Filter α} [CardinalInterFilter f c]
  proof: by
  constructor <;> intro h
  · exact subset_trans (fun s => CardinalGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (cardinal_sInter_mem Sct).mpr ih

中文:
定理 le_cardinalGenerate_iff_of_cardinal整数erFilter
  结论: {f : 滤子 α} [Cardinal整数erFilter f c]
  证明: by
  constructor <;> intro h
  · exact subset_trans (fun s => CardinalGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (cardinal_sInter_mem Sct).mpr ih

Depends on / 依赖: CardinalGenerateSets, CardinalGenerateSets.basic, cardinal_sInter_mem, mem_of_superset, sInter, subset_trans, superset, univ_mem
-/
theorem le_cardinalGenerate_iff_of_cardinalInterFilter {f : Filter α} [CardinalInterFilter f c]
    (hc : 2 < c) : f <= cardinalGenerate g hc ↔ g subseteq f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CardinalGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (cardinal_sInter_mem Sct).mpr ih

/--
theorem `cardinalGenerate_isGreatest` / 定理 `cardinalGenerate_isGreatest`

English:
theorem cardinalGenerate_isGreatest
  given: (hc : 2 < c)
  proof: by
  refine ⟨⟨cardinalInter_ofCardinalGenerate _ _, fun s => CardinalGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [le_cardinalGenerate_iff_of_cardinalInterFilter]

中文:
定理 cardinalGenerate_isGreatest
  条件: (hc : 2 < c)
  证明: by
  refine ⟨⟨cardinalInter_ofCardinalGenerate _ _, fun s => CardinalGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [le_cardinalGenerate_iff_of_cardinalInterFilter]

Depends on / 依赖: CardinalGenerateSets, CardinalGenerateSets.basic, cardinalInter_ofCardinalGenerate, le_cardinalGenerate_iff_of_cardinalInterFilter
-/
theorem cardinalGenerate_isGreatest (hc : 2 < c) :
    IsGreatest { f : Filter α | CardinalInterFilter f c ∧ g subseteq f.sets } (cardinalGenerate g hc) := by
  refine ⟨⟨cardinalInter_ofCardinalGenerate _ _, fun s => CardinalGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [le_cardinalGenerate_iff_of_cardinalInterFilter]

end Filter
