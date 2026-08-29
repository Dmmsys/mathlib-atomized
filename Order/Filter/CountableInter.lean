/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Curry
public import Mathlib.Data.Set.Countable

/-!
# Filters with countable intersection property

In this file we define `CountableInterFilter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `Mathlib/Topology/GDelta/Basic.lean` and
the `MeasureTheory.ae` filter defined in `Mathlib/MeasureTheory/OuterMeasure/AE.lean`.

We reformulate the definition in terms of indexed intersection and in terms of `Filter.Eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `Filter.principal`, `Filter.map`,
`Filter.comap`, `Inf.inf`). We also provide a custom constructor `Filter.ofCountableInter`
that deduces two axioms of a `Filter` from the countable intersection property.

Note that there also exists a typeclass `CardinalInterFilter`, and thus an alternative spelling of
`CountableInterFilter` as `CardinalInterFilter l ℵ₁`. The former (defined here) is the
preferred spelling; it has the advantage of not requiring the user to import the theory of ordinals.

## Tags
filter, countable
-/

@[expose] public section


open Set Filter

variable {ι : Sort*} {α β : Type*}

/--
Definition of `CountableInterFilter` / `CountableInterFilter` 的定义

English:
class CountableInterFilter
  parameters: (l : Filter α)
  axioms and operations (1):
    - countable_sInter_mem : forall S : Set (Set α), S.Countable -> (forall s in S, s in l) -> ⋂₀ S in l

中文:
类 CountableInterFilter
  参数: (l : Filter α)
  公理与运算 (1 个):
    - countable_sInter_mem : 对任意 S : Set (Set α), S.Countable -> (对任意 s in S, s in l) -> ⋂₀ S in l
-/
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : forall S : Set (Set α), S.Countable -> (forall s in S, s in l) -> ⋂₀ S in l

variable {l : Filter α} [CountableInterFilter l]

/--
theorem `countable_sInter_mem` / 定理 `countable_sInter_mem`

English:
theorem countable_sInter_mem
  given: {S : Set (Set α)} (hSc : S.Countable)
  statement: ⋂₀ S in l ↔ forall s in S, s in l
  proof: ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩

中文:
定理 countable_sInter_mem
  条件: {S : Set (Set α)} (hSc : S.Countable)
  结论: ⋂₀ S in l ↔ 对任意 s in S, s in l
  证明: ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩

Depends on / 依赖: CountableInterFilter, CountableInterFilter.countable_sInter_mem, countable_sInter_mem, mem_of_superset, sInter_subset_of_mem
-/
theorem countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S in l ↔ forall s in S, s in l :=
  ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩

/--
theorem `countable_iInter_mem` / 定理 `countable_iInter_mem`

English:
theorem countable_iInter_mem
  given: [Countable ι] {s : ι -> Set α}
  statement: (⋂ i, s i) in l ↔ forall i, s i in l
  proof: sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_mem_range

中文:
定理 countable_iInter_mem
  条件: [Countable ι] {s : ι -> Set α}
  结论: (⋂ i, s i) in l ↔ 对任意 i, s i in l
  证明: sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_mem_range

Depends on / 依赖: countable_range, countable_sInter_mem, forall_mem_range, sInter_range
-/
theorem countable_iInter_mem [Countable ι] {s : ι -> Set α} : (⋂ i, s i) in l ↔ forall i, s i in l :=
  sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_mem_range

/--
theorem `countable_bInter_mem` / 定理 `countable_bInter_mem`

English:
theorem countable_bInter_mem
  given: {ι : Type*} {S : Set ι} (hS : S.Countable) {s : forall i in S, Set α}
  proof: by
  rw [biInter_eq_iInter]
  have := hS.toEncodable
  exact countable_iInter_mem.trans Subtype.forall

中文:
定理 countable_bInter_mem
  条件: {ι : 类型} {S : Set ι} (hS : S.Countable) {s : 对任意 i in S, Set α}
  证明: by
  rw [biInter_eq_iInter]
  have := hS.toEncodable
  exact countable_iInter_mem.trans Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall, biInter_eq_iInter, countable_iInter_mem, countable_iInter_mem.trans, hS.toEncodable, toEncodable
-/
theorem countable_bInter_mem {ι : Type*} {S : Set ι} (hS : S.Countable) {s : forall i in S, Set α} :
    (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ forall i, forall hi : i in S, s i ‹_› in l := by
  rw [biInter_eq_iInter]
  have := hS.toEncodable
  exact countable_iInter_mem.trans Subtype.forall

/--
theorem `eventually_countable_forall` / 定理 `eventually_countable_forall`

English:
theorem eventually_countable_forall
  given: [Countable ι] {p : α -> ι -> Prop}
  proof: by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }

中文:
定理 eventually_countable_forall
  条件: [Countable ι] {p : α -> ι -> 命题}
  证明: by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }

Depends on / 依赖: Eventually, Filter, Filter.Eventually, countable_iInter_mem, ofPred_forall
-/
theorem eventually_countable_forall [Countable ι] {p : α -> ι -> Prop} :
    (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in l, p x i := by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }

/--
theorem `eventually_countable_ball` / 定理 `eventually_countable_ball`

English:
theorem eventually_countable_ball
  statement: {ι : Type*} {S : Set ι} (hS : S.Countable)
  proof: by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }

中文:
定理 eventually_countable_ball
  结论: {ι : 类型} {S : Set ι} (hS : S.Countable)
  证明: by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }

Depends on / 依赖: Eventually, Filter, Filter.Eventually, countable_bInter_mem, ofPred_forall
-/
theorem eventually_countable_ball {ι : Type*} {S : Set ι} (hS : S.Countable)
    {p : α -> forall i in S, Prop} :
    (forallᶠ x in l, forall i hi, p x i hi) ↔ forall i hi, forallᶠ x in l, p x i hi := by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }

/--
theorem `eventually_finset_ball` / 定理 `eventually_finset_ball`

English:
theorem eventually_finset_ball
  given: {ι : Type*} {S : Finset ι} {p : α -> forall i in S, Prop}
  proof: eventually_countable_ball S.countable_toSet

中文:
定理 eventually_finset_ball
  条件: {ι : 类型} {S : Finset ι} {p : α -> 对任意 i in S, 命题}
  证明: eventually_countable_ball S.countable_toSet

Depends on / 依赖: S.countable_toSet, countable_toSet, eventually_countable_ball
-/
theorem eventually_finset_ball {ι : Type*} {S : Finset ι} {p : α -> forall i in S, Prop} :
    (forallᶠ x in l, forall i hi, p x i hi) ↔ forall i hi, forallᶠ x in l, p x i hi :=
  eventually_countable_ball S.countable_toSet

namespace Filter

/--
theorem `EventuallyLE.countable_iUnion` / 定理 `EventuallyLE.countable_iUnion`

English:
theorem EventuallyLE.countable_iUnion
  given: [Countable ι] {s t : ι -> Set α} (h : forall i, s i <=ᶠ[l] t i)
  proof: (eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 (mem_iUnion.1 hs).imp hst

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iUnion :=
  EventuallyLE.countable_iUnion

中文:
定理 EventuallyLE.countable_iUnion
  条件: [Countable ι] {s t : ι -> Set α} (h : 对任意 i, s i <=ᶠ[l] t i)
  证明: (eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 (mem_iUnion.1 hs).imp hst

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iUnion :=
  EventuallyLE.countable_iUnion

Depends on / 依赖: eventually_countable_forall, mem_iUnion
-/
theorem EventuallyLE.countable_iUnion [Countable ι] {s t : ι -> Set α} (h : forall i, s i <=ᶠ[l] t i) :
    ⋃ i, s i <=ᶠ[l] ⋃ i, t i :=
(eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 (mem_iUnion.1 hs).imp hst

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iUnion :=
  EventuallyLE.countable_iUnion

/--
theorem `EventuallyEq.countable_iUnion` / 定理 `EventuallyEq.countable_iUnion`

English:
theorem EventuallyEq.countable_iUnion
  given: [Countable ι] {s t : ι -> Set α} (h : forall i, s i =ᶠ[l] t i)
  proof: (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iUnion :=
  EventuallyEq.countable_iUnion

中文:
定理 EventuallyEq.countable_iUnion
  条件: [Countable ι] {s t : ι -> Set α} (h : 对任意 i, s i =ᶠ[l] t i)
  证明: (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iUnion :=
  EventuallyEq.countable_iUnion

Depends on / 依赖: EventuallyLE, EventuallyLE.countable_iUnion, antisymm, countable_iUnion, symm.le
-/
theorem EventuallyEq.countable_iUnion [Countable ι] {s t : ι -> Set α} (h : forall i, s i =ᶠ[l] t i) :
    ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iUnion :=
  EventuallyEq.countable_iUnion

/--
theorem `EventuallyLE.countable_bUnion` / 定理 `EventuallyLE.countable_bUnion`

English:
theorem EventuallyLE.countable_bUnion
  statement: {ι : Type*} {S : Set ι} (hS : S.Countable)
  proof: by
  simp only [biUnion_eq_iUnion]
  have := hS.toEncodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bUnion :=
  EventuallyLE.countable_bUnion

中文:
定理 EventuallyLE.countable_bUnion
  结论: {ι : 类型} {S : Set ι} (hS : S.Countable)
  证明: by
  simp only [biUnion_eq_iUnion]
  have := hS.toEncodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bUnion :=
  EventuallyLE.countable_bUnion

Depends on / 依赖: EventuallyLE, EventuallyLE.countable_iUnion, biUnion_eq_iUnion, countable_iUnion, hS.toEncodable, toEncodable
-/
theorem EventuallyLE.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi <=ᶠ[l] t i hi) :
    ⋃ i in S, s i ‹_› <=ᶠ[l] ⋃ i in S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  have := hS.toEncodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bUnion :=
  EventuallyLE.countable_bUnion

/--
theorem `EventuallyEq.countable_bUnion` / 定理 `EventuallyEq.countable_bUnion`

English:
theorem EventuallyEq.countable_bUnion
  statement: {ι : Type*} {S : Set ι} (hS : S.Countable)
  proof: (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bUnion :=
  EventuallyEq.countable_bUnion

中文:
定理 EventuallyEq.countable_bUnion
  结论: {ι : 类型} {S : Set ι} (hS : S.Countable)
  证明: (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bUnion :=
  EventuallyEq.countable_bUnion

Depends on / 依赖: EventuallyLE, EventuallyLE.countable_bUnion, antisymm, countable_bUnion, symm.le
-/
theorem EventuallyEq.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i in S, s i ‹_› =ᶠ[l] ⋃ i in S, t i ‹_› :=
  (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bUnion :=
  EventuallyEq.countable_bUnion

/--
theorem `EventuallyLE.countable_iInter` / 定理 `EventuallyLE.countable_iInter`

English:
theorem EventuallyLE.countable_iInter
  given: [Countable ι] {s t : ι -> Set α} (h : forall i, s i <=ᶠ[l] t i)
  proof: (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iInter :=
  EventuallyLE.countable_iInter

中文:
定理 EventuallyLE.countable_iInter
  条件: [Countable ι] {s t : ι -> Set α} (h : 对任意 i, s i <=ᶠ[l] t i)
  证明: (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iInter :=
  EventuallyLE.countable_iInter

Depends on / 依赖: eventually_countable_forall, mem_iInter
-/
theorem EventuallyLE.countable_iInter [Countable ι] {s t : ι -> Set α} (h : forall i, s i <=ᶠ[l] t i) :
    ⋂ i, s i <=ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iInter :=
  EventuallyLE.countable_iInter

/--
theorem `EventuallyEq.countable_iInter` / 定理 `EventuallyEq.countable_iInter`

English:
theorem EventuallyEq.countable_iInter
  given: [Countable ι] {s t : ι -> Set α} (h : forall i, s i =ᶠ[l] t i)
  proof: (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iInter :=
  EventuallyEq.countable_iInter

中文:
定理 EventuallyEq.countable_iInter
  条件: [Countable ι] {s t : ι -> Set α} (h : 对任意 i, s i =ᶠ[l] t i)
  证明: (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iInter :=
  EventuallyEq.countable_iInter

Depends on / 依赖: EventuallyLE, EventuallyLE.countable_iInter, antisymm, countable_iInter, symm.le
-/
theorem EventuallyEq.countable_iInter [Countable ι] {s t : ι -> Set α} (h : forall i, s i =ᶠ[l] t i) :
    ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iInter :=
  EventuallyEq.countable_iInter

/--
theorem `EventuallyLE.countable_bInter` / 定理 `EventuallyLE.countable_bInter`

English:
theorem EventuallyLE.countable_bInter
  statement: {ι : Type*} {S : Set ι} (hS : S.Countable)
  proof: by
  simp only [biInter_eq_iInter]
  have := hS.toEncodable
  exact EventuallyLE.countable_iInter fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bInter :=
  EventuallyLE.countable_bInter

中文:
定理 EventuallyLE.countable_bInter
  结论: {ι : 类型} {S : Set ι} (hS : S.Countable)
  证明: by
  simp only [biInter_eq_iInter]
  have := hS.toEncodable
  exact EventuallyLE.countable_iInter fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bInter :=
  EventuallyLE.countable_bInter

Depends on / 依赖: EventuallyLE, EventuallyLE.countable_iInter, biInter_eq_iInter, countable_iInter, hS.toEncodable, toEncodable
-/
theorem EventuallyLE.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi <=ᶠ[l] t i hi) :
    ⋂ i in S, s i ‹_› <=ᶠ[l] ⋂ i in S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  have := hS.toEncodable
  exact EventuallyLE.countable_iInter fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bInter :=
  EventuallyLE.countable_bInter

/--
theorem `EventuallyEq.countable_bInter` / 定理 `EventuallyEq.countable_bInter`

English:
theorem EventuallyEq.countable_bInter
  statement: {ι : Type*} {S : Set ι} (hS : S.Countable)
  proof: (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bInter :=
  EventuallyEq.countable_bInter

中文:
定理 EventuallyEq.countable_bInter
  结论: {ι : 类型} {S : Set ι} (hS : S.Countable)
  证明: (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bInter :=
  EventuallyEq.countable_bInter

Depends on / 依赖: EventuallyLE, EventuallyLE.countable_bInter, antisymm, countable_bInter, symm.le
-/
theorem EventuallyEq.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : forall i in S, Set α} (h : forall i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i in S, s i ‹_› =ᶠ[l] ⋂ i in S, t i ‹_› :=
  (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bInter :=
  EventuallyEq.countable_bInter

/--
Definition of `ofCountableInter` / `ofCountableInter` 的定义

English:
definition ofCountableInter
  signature: (l : Set (Set α))
  body: l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)

中文:
定义 ofCountableInter
  签名: (l : Set (Set α))
  定义体: l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
-/
def ofCountableInter (l : Set (Set α))
    (hl : forall S : Set (Set α), S.Countable -> S subseteq l -> ⋂₀ S in l)
    (h_mono : forall s t, s in l -> s subseteq t -> t in l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)

/--
Instance `countableInter_ofCountableInter` / 实例 `countableInter_ofCountableInter`

English:
instance countableInter_ofCountableInter
  signature: (l : Set (Set α))
  body: ⟨hl⟩

@[simp]

中文:
实例 countableInter_ofCountableInter
  签名: (l : Set (Set α))
  定义体: ⟨hl⟩

@[simp]
-/
instance countableInter_ofCountableInter (l : Set (Set α))
    (hl : forall S : Set (Set α), S.Countable -> S subseteq l -> ⋂₀ S in l)
    (h_mono : forall s t, s in l -> s subseteq t -> t in l) :
    CountableInterFilter (Filter.ofCountableInter l hl h_mono) :=
  ⟨hl⟩

@[simp]
/--
theorem `mem_ofCountableInter` / 定理 `mem_ofCountableInter`

English:
theorem mem_ofCountableInter
  statement: {l : Set (Set α)}
  proof: Iff.rfl

中文:
定理 mem_ofCountableInter
  结论: {l : Set (Set α)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofCountableInter {l : Set (Set α)}
    (hl : forall S : Set (Set α), S.Countable -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> s subseteq t -> t in l)
    {s : Set α} : s in Filter.ofCountableInter l hl h_mono ↔ s in l :=
  Iff.rfl

/--
Definition of `ofCountableUnion` / `ofCountableUnion` 的定义

English:
definition ofCountableUnion
  signature: (l : Set (Set α))
  body: by
  refine .ofCountableInter {s | sᶜ in l} (fun S hSc hSp => ?_) fun s t ht hsub => ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_sub

中文:
定义 ofCountableUnion
  签名: (l : Set (Set α))
  定义体: by
  refine .ofCountableInter {s | sᶜ in l} (fun S hSc hSp => ?_) fun s t ht hsub => ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_sub

Depends on / 依赖: compl_sInter, compl_subset_compl, hSc.image, hUnion, mem_image, mem_ofPred_eq, ofCountableInter
-/
def ofCountableUnion (l : Set (Set α))
    (hUnion : forall S : Set (Set α), S.Countable -> (forall s in S, s in l) -> ⋃₀ S in l)
    (hmono : forall t in l, forall s subseteq t, s in l) : Filter α := by
  refine .ofCountableInter {s | sᶜ in l} (fun S hSc hSp => ?_) fun s t ht hsub => ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

/--
Instance `countableInter_ofCountableUnion` / 实例 `countableInter_ofCountableUnion`

English:
instance countableInter_ofCountableUnion
  signature: (l : Set (Set α)) (h₁ h₂)
  body: countableInter_ofCountableInter ..

@[simp]

中文:
实例 countableInter_ofCountableUnion
  签名: (l : Set (Set α)) (h₁ h₂)
  定义体: countableInter_ofCountableInter ..

@[simp]

Depends on / 依赖: countableInter_ofCountableInter
-/
instance countableInter_ofCountableUnion (l : Set (Set α)) (h₁ h₂) :
    CountableInterFilter (Filter.ofCountableUnion l h₁ h₂) :=
  countableInter_ofCountableInter ..

@[simp]
/--
theorem `mem_ofCountableUnion` / 定理 `mem_ofCountableUnion`

English:
theorem mem_ofCountableUnion
  given: {l : Set (Set α)} {hunion hmono s}
  proof: Iff.rfl

中文:
定理 mem_ofCountableUnion
  条件: {l : Set (Set α)} {hunion hmono s}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofCountableUnion {l : Set (Set α)} {hunion hmono s} :
    s in ofCountableUnion l hunion hmono ↔ sᶜ in l :=
  Iff.rfl

end Filter

/--
Instance `countableInterFilter_principal` / 实例 `countableInterFilter_principal`

English:
instance countableInterFilter_principal
  signature: (s : Set α)
  body: ⟨fun _ _ hS => subset_sInter hS⟩

中文:
实例 countableInterFilter_principal
  签名: (s : Set α)
  定义体: ⟨fun _ _ hS => subset_sInter hS⟩

Depends on / 依赖: subset_sInter
-/
instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun _ _ hS => subset_sInter hS⟩

/--
Instance `countableInterFilter_bot` / 实例 `countableInterFilter_bot`

English:
instance countableInterFilter_bot
  signature: : CountableInterFilter (⊥ : Filter α)
  body: by
  rw [← principal_empty]
  apply countableInterFilter_principal

中文:
实例 countableInterFilter_bot
  签名: : Countable整数erFilter (⊥ : Filter α)
  定义体: by
  rw [← principal_empty]
  apply countableInterFilter_principal

Depends on / 依赖: countableInterFilter_principal, principal_empty
-/
instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) := by
  rw [← principal_empty]
  apply countableInterFilter_principal

/--
Instance `countableInterFilter_top` / 实例 `countableInterFilter_top`

English:
instance countableInterFilter_top
  signature: : CountableInterFilter (⊤ : Filter α)
  body: by
  rw [← principal_univ]
  apply countableInterFilter_principal

中文:
实例 countableInterFilter_top
  签名: : Countable整数erFilter (⊤ : Filter α)
  定义体: by
  rw [← principal_univ]
  apply countableInterFilter_principal

Depends on / 依赖: countableInterFilter_principal, principal_univ
-/
instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) := by
  rw [← principal_univ]
  apply countableInterFilter_principal

instance (l : Filter β) [CountableInterFilter l] (f : α -> β) :
    CountableInterFilter (comap f l) := by
  refine ⟨fun S hSc hS => ?_⟩
  choose! t htl ht using hS
  have : (⋂ s in S, t s) in l := (countable_bInter_mem hSc).2 htl
  refine ⟨_, this, ?_⟩
  simpa [preimage_iInter] using iInter₂_mono ht

instance (l : Filter α) [CountableInterFilter l] (f : α -> β) : CountableInterFilter (map f l) := by
  refine ⟨fun S hSc hS => ?_⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (countable_bInter_mem hSc).2 hS

/--
Instance `countableInterFilter_inf` / 实例 `countableInterFilter_inf`

English:
instance countableInterFilter_inf
  signature: (l₁ l₂ : Filter α) [CountableInterFilter l₁]
  body: by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i in S, s i ‹_›) in l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i in S, t i ‹_›) in l₂ := (countable_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw 

中文:
实例 countableInterFilter_inf
  签名: (l₁ l₂ : Filter α) [Countable整数erFilter l₁]
  定义体: by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i in S, s i ‹_›) in l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i in S, t i ‹_›) in l₂ := (countable_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw 

Depends on / 依赖: countable_bInter_mem, iInter_subset, iInter_subset_of_subset, inter_mem_inf, inter_subset_inter, mem_of_superset, replace, subset_sInter
-/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) := by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i in S, s i ‹_›) in l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i in S, t i ‹_›) in l₂ := (countable_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

/--
Instance `countableInterFilter_sup` / 实例 `countableInterFilter_sup`

English:
instance countableInterFilter_sup
  signature: (l₁ l₂ : Filter α) [CountableInterFilter l₁]
  body: by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (countable_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

中文:
实例 countableInterFilter_sup
  签名: (l₁ l₂ : Filter α) [Countable整数erFilter l₁]
  定义体: by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (countable_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

Depends on / 依赖: countable_sInter_mem, exacts
-/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) := by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (countable_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

/--
Instance `CountableInterFilter.curry` / 实例 `CountableInterFilter.curry`

English:
instance CountableInterFilter.curry
  signature: {α β : Type*} {l : Filter α} {m : Filter β}
  body: ⟨by
  intro S Sct hS
  simp_rw [mem_curry_iff, mem_sInter, eventually_countable_ball (p := fun _ _ _ => (_, _) in _) Sct,
    eventually_countable_ball (p := fun _ _ _ => forallᶠ (_ : β) in m, _) Sct, ← mem_curry_iff]
  exact hS⟩

中文:
实例 CountableInterFilter.curry
  签名: {α β : 类型} {l : Filter α} {m : Filter β}
  定义体: ⟨by
  intro S Sct hS
  simp_rw [mem_curry_iff, mem_sInter, eventually_countable_ball (p := fun _ _ _ => (_, _) in _) Sct,
    eventually_countable_ball (p := fun _ _ _ => forallᶠ (_ : β) in m, _) Sct, ← mem_curry_iff]
  exact hS⟩

Depends on / 依赖: eventually_countable_ball, mem_curry_iff, mem_sInter, simp_rw
-/
instance CountableInterFilter.curry {α β : Type*} {l : Filter α} {m : Filter β}
    [CountableInterFilter l] [CountableInterFilter m] : CountableInterFilter (l.curry m) := ⟨by
  intro S Sct hS
  simp_rw [mem_curry_iff, mem_sInter, eventually_countable_ball (p := fun _ _ _ => (_, _) in _) Sct,
    eventually_countable_ball (p := fun _ _ _ => forallᶠ (_ : β) in m, _) Sct, ← mem_curry_iff]
  exact hS⟩

namespace Filter

variable (g : Set (Set α))

/--
Inductive type `CountableGenerateSets` / 归纳类型 `CountableGenerateSets`

English:
inductive CountableGenerateSets
  parameters: : Set α -> Prop
  constructors (4):
    - basic: {s : Set α} : s in g -> CountableGenerateSets s
    - univ: CountableGenerateSets univ
    - superset: {s t : Set α} : CountableGenerateSets s -> s subseteq t -> CountableGenerateSets t
    - sInter: {S : Set (Set α)} : S.Countable -> (forall s in S, CountableGenerateSets s) -> CountableGenerateSets (⋂₀ S)

中文:
归纳类型 CountableGenerateSets
  参数: : Set α -> 命题
  构造子 (4 个):
    - basic: {s : Set α} : s in g -> CountableGenerateSets s
    - univ: CountableGenerateSets univ
    - superset: {s t : Set α} : CountableGenerateSets s -> s subseteq t -> CountableGenerateSets t
    - sInter: {S : Set (Set α)} : S.Countable -> (对任意 s in S, CountableGenerateSets s) -> CountableGenerateSets (⋂₀ S)
-/
inductive CountableGenerateSets : Set α -> Prop
  | basic {s : Set α} : s in g -> CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s -> s subseteq t -> CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable -> (forall s in S, CountableGenerateSets s) -> CountableGenerateSets (⋂₀ S)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `countableGenerate` / `countableGenerate` 的定义

English:
definition countableGenerate
  signature: : Filter α
  body: ofCountableInter {s | CountableGenerateSets g s} (fun _ => .sInter) fun _ _ => .superset
deriving CountableInterFilter

中文:
定义 countableGenerate
  签名: : Filter α
  定义体: ofCountableInter {s | CountableGenerateSets g s} (fun _ => .sInter) fun _ _ => .superset
deriving CountableInterFilter

Depends on / 依赖: CountableGenerateSets, ofCountableInter, sInter, superset
-/
def countableGenerate : Filter α :=
  ofCountableInter {s | CountableGenerateSets g s} (fun _ => .sInter) fun _ _ => .superset
deriving CountableInterFilter

variable {g}

/--
theorem `mem_countableGenerate_iff` / 定理 `mem_countableGenerate_iff`

English:
theorem mem_countableGenerate_iff
  given: {s : Set α}
  proof: by
  constructor <;> intro h
  · induction h with
    | @basic s hs => exact ⟨{s}, by simp [hs]⟩
    | univ => exact ⟨∅, by simp⟩
    | superset _ _ ih => refine Exists.imp (fun S => ?_) ih; tauto
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s in S), T s H, 

中文:
定理 mem_countableGenerate_iff
  条件: {s : Set α}
  证明: by
  constructor <;> intro h
  · induction h with
    | @basic s hs => exact ⟨{s}, by simp [hs]⟩
    | univ => exact ⟨∅, by simp⟩
    | superset _ _ ih => refine Exists.imp (fun S => ?_) ih; tauto
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s in S), T s H, 

Depends on / 依赖: Exists, Exists.imp, Sct.biUnion, biUnion, countable_sInter_mem, mem_of_superset, sInter, sInter_subset_sInter, subset_sInter, subset_trans, superset
-/
theorem mem_countableGenerate_iff {s : Set α} :
    s in countableGenerate g ↔ exists S : Set (Set α), S subseteq g ∧ S.Countable ∧ ⋂₀ S subseteq s := by
  constructor <;> intro h
  · induction h with
    | @basic s hs => exact ⟨{s}, by simp [hs]⟩
    | univ => exact ⟨∅, by simp⟩
    | superset _ _ ih => refine Exists.imp (fun S => ?_) ih; tauto
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s in S), T s H, by simpa, Sct.biUnion Tct, ?_⟩
      apply subset_sInter
      intro s H
      exact subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  refine mem_of_superset ((countable_sInter_mem Sct).mpr ?_) hS
  intro s H
  exact CountableGenerateSets.basic (Sg H)

/--
theorem `le_countableGenerate_iff_of_countableInterFilter` / 定理 `le_countableGenerate_iff_of_countableInterFilter`

English:
theorem le_countableGenerate_iff_of_countableInterFilter
  given: {f : Filter α} [CountableInterFilter f]
  proof: by
  constructor <;> intro h
  · exact subset_trans (fun s => CountableGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (countable_sInter_mem Sct).mpr ih

中文:
定理 le_countableGenerate_iff_of_countableInterFilter
  条件: {f : Filter α} [Countable整数erFilter f]
  证明: by
  constructor <;> intro h
  · exact subset_trans (fun s => CountableGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (countable_sInter_mem Sct).mpr ih

Depends on / 依赖: CountableGenerateSets, CountableGenerateSets.basic, countable_sInter_mem, mem_of_superset, sInter, subset_trans, superset, univ_mem
-/
theorem le_countableGenerate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] :
    f <= countableGenerate g ↔ g subseteq f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CountableGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (countable_sInter_mem Sct).mpr ih

variable (g)

/--
theorem `countableGenerate_isGreatest` / 定理 `countableGenerate_isGreatest`

English:
theorem countableGenerate_isGreatest
  proof: by
  refine ⟨⟨inferInstance, fun s => CountableGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_countableGenerate_iff_of_countableInterFilter _ _ _ fct]

中文:
定理 countableGenerate_isGreatest
  证明: by
  refine ⟨⟨inferInstance, fun s => CountableGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_countableGenerate_iff_of_countableInterFilter _ _ _ fct]

Depends on / 依赖: CountableGenerateSets, CountableGenerateSets.basic, le_countableGenerate_iff_of_countableInterFilter
-/
theorem countableGenerate_isGreatest :
    IsGreatest { f : Filter α | CountableInterFilter f ∧ g subseteq f.sets } (countableGenerate g) := by
  refine ⟨⟨inferInstance, fun s => CountableGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_countableGenerate_iff_of_countableInterFilter _ _ _ fct]

end Filter
