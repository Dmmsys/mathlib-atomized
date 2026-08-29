/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Vitali families

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
  `Besicovitch.vitaliFamily`, and by the Vitali covering theorem, in `Vitali.vitaliFamily`.
* The main theorem on differentiation of measures along a Vitali family is proved in
  `VitaliFamily.ae_tendsto_rnDeriv`.

## Main definitions

* `VitaliFamily μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
  one can extract an almost everywhere disjoint covering from any subfamily containing sets of
  arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.FineSubfamilyOn` describes the subfamilies of `v` from which one can extract almost
  everywhere disjoint coverings. This property, called
  `v.FineSubfamilyOn.exists_disjoint_covering_ae`, is essentially a restatement of the definition
  of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filterAt x` is a filter on sets of `X`, such that convergence with respect to this filter
  means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996]
  (Vitali families are called Vitali relations there)
-/

@[expose] public section


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

/--
Definition of `VitaliFamily` / `VitaliFamily` 的定义

English:
structure VitaliFamily
  parameters: {m : MeasurableSpace X} (μ : Measure X)
  axioms and operations (5):
    - setsAt : X -> Set (Set X)
    - measurableSet : forall x : X, forall s in setsAt x, MeasurableSet s
    - nonempty_interior : forall x : X, forall s in setsAt x, (interior s).Nonempty
    - nontrivial : forall (x : X), forall ε > (0 : Real), exists s in setsAt x, s subseteq closedBall x ε
    - covering : forall (s : Set X) (f : X -> Set (Set X)), (forall x in s, f x subseteq setsAt x) -> (forall x in s, forall ε > (0 : Real), exists t in f x, t subseteq closedBall x ε) -> exists t : Set (X × Set X), (forall p in t, p.1 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (forall p in t, p.2 in f p.1) ∧ μ (s \ ⋃ p in t, p.2) = 0

中文:
结构 Vitali族
  参数: {m : 可测空间 X} (μ : 测度 X)
  公理与运算 (5 个):
    - setsAt : X -> 集合 (集合 X)
    - measurableSet : 对任意 x : X, 对任意 s in setsAt x, 可测集 s
    - nonempty_interior : 对任意 x : X, 对任意 s in setsAt x, (interior s).非空
    - nontrivial : 对任意 (x : X), 对任意 ε > (0 : 实数), 存在 s in setsAt x, s subseteq closedBall x ε
    - covering : 对任意 (s : 集合 X) (f : X -> 集合 (集合 X)), (对任意 x in s, f x subseteq setsAt x) -> (对任意 x in s, 对任意 ε > (0 : 实数), 存在 t in f x, t subseteq closedBall x ε) -> 存在 t : 集合 (X × 集合 X), (对任意 p in t, p.1 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (对任意 p in t, p.2 in f p.1) ∧ μ (s \ ⋃ p in t, p.2) = 0
-/
structure VitaliFamily {m : MeasurableSpace X} (μ : Measure X) where
  /-- Sets of the family "centered" at a given point. -/
  setsAt : X -> Set (Set X)
  /-- All sets of the family are measurable. -/
  measurableSet : forall x : X, forall s in setsAt x, MeasurableSet s
  /-- All sets of the family have nonempty interior. -/
  nonempty_interior : forall x : X, forall s in setsAt x, (interior s).Nonempty
  /-- For any closed ball around `x`, there exists a set of the family contained in this ball. -/
  nontrivial : forall (x : X), forall ε > (0 : Real), exists s in setsAt x, s subseteq closedBall x ε
  /-- Consider a (possibly non-measurable) set `s`,
  and for any `x` in `s` a subfamily `f x` of `setsAt x`
  containing sets of arbitrarily small diameter.
  Then one can extract a disjoint subfamily covering almost all `s`. -/
  covering : forall (s : Set X) (f : X -> Set (Set X)),
    (forall x in s, f x subseteq setsAt x) -> (forall x in s, forall ε > (0 : Real), exists t in f x, t subseteq closedBall x ε) ->
    exists t : Set (X × Set X), (forall p in t, p.1 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧
      (forall p in t, p.2 in f p.1) ∧ μ (s \ ⋃ p in t, p.2) = 0

namespace VitaliFamily

variable {m0 : MeasurableSpace X} {μ : Measure X}

/--
Definition of `mono` / `mono` 的定义

English:
definition mono
  signature: (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ)
  body: v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩

中文:
定义 mono
  签名: (v : Vitali族 μ) (ν : 测度 X) (hν : ν ≪ μ)
  定义体: v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩
-/
def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩

/--
Definition of `FineSubfamilyOn` / `FineSubfamilyOn` 的定义

English:
definition FineSubfamilyOn
  signature: (v : VitaliFamily μ) (f : X -> Set (Set X)) (s : Set X)
  body: forall x in s, forall ε > 0, exists t in v.setsAt x inter f x, t subseteq closedBall x ε

中文:
定义 FineSubfamilyOn
  签名: (v : Vitali族 μ) (f : X -> 集合 (集合 X)) (s : 集合 X)
  定义体: forall x in s, forall ε > 0, exists t in v.setsAt x inter f x, t subseteq closedBall x ε

Depends on / 依赖: closedBall, setsAt, subseteq, v.setsAt
-/
def FineSubfamilyOn (v : VitaliFamily μ) (f : X -> Set (Set X)) (s : Set X) : Prop :=
  forall x in s, forall ε > 0, exists t in v.setsAt x inter f x, t subseteq closedBall x ε

namespace FineSubfamilyOn

variable {v : VitaliFamily μ} {f : X -> Set (Set X)} {s : Set X} (h : v.FineSubfamilyOn f s)
include h

/--
theorem `exists_disjoint_covering_ae` / 定理 `exists_disjoint_covering_ae`

English:
theorem exists_disjoint_covering_ae
  proof: v.covering s (fun x => v.setsAt x inter f x) (fun _ _ => inter_subset_left) h

中文:
定理 存在_disjoint_covering_ae
  证明: v.covering s (fun x => v.setsAt x inter f x) (fun _ _ => inter_subset_left) h

Depends on / 依赖: covering, inter_subset_left, setsAt, v.covering, v.setsAt
-/
theorem exists_disjoint_covering_ae :
    exists t : Set (X × Set X),
      (forall p : X × Set X, p in t -> p.1 in s) ∧
      (t.PairwiseDisjoint fun p => p.2) ∧
      (forall p : X × Set X, p in t -> p.2 in v.setsAt p.1 inter f p.1) ∧
      μ (s \ ⋃ (p : X × Set X) (_ : p in t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x inter f x) (fun _ _ => inter_subset_left) h

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def index
  body: h.exists_disjoint_covering_ae.choose

中文:
定义 noncomputable
  签名: def index
  定义体: h.exists_disjoint_covering_ae.choose
-/
protected noncomputable def index : Set (X × Set X) :=
  h.exists_disjoint_covering_ae.choose

/-- Given `h : v.FineSubfamilyOn f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
@[nolint unusedArguments]
/--
Definition of `covering` / `covering` 的定义

English:
definition covering
  signature: (_h : FineSubfamilyOn v f s)
  body: fun p => p.2

中文:
定义 covering
  签名: (_h : FineSubfamilyOn v f s)
  定义体: fun p => p.2
-/
protected def covering (_h : FineSubfamilyOn v f s) : X × Set X -> Set X :=
  fun p => p.2

/--
theorem `index_subset` / 定理 `index_subset`

English:
theorem index_subset
  statement: forall p : X × Set X, p in h.index -> p.1 in s
  proof: h.exists_disjoint_covering_ae.choose_spec.1

中文:
定理 index_subset
  结论: 对任意 p : X × 集合 X, p in h.index -> p.1 in s
  证明: h.exists_disjoint_covering_ae.choose_spec.1

Depends on / 依赖: choose_spec, exists_disjoint_covering_ae, h.exists_disjoint_covering_ae.choose_spec
-/
theorem index_subset : forall p : X × Set X, p in h.index -> p.1 in s :=
  h.exists_disjoint_covering_ae.choose_spec.1

/--
theorem `covering_disjoint` / 定理 `covering_disjoint`

English:
theorem covering_disjoint
  statement: h.index.PairwiseDisjoint h.covering
  proof: h.exists_disjoint_covering_ae.choose_spec.2.1

中文:
定理 covering_disjoint
  结论: h.index.PairwiseDisjoint h.covering
  证明: h.exists_disjoint_covering_ae.choose_spec.2.1

Depends on / 依赖: choose_spec, exists_disjoint_covering_ae, h.exists_disjoint_covering_ae.choose_spec
-/
theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
  h.exists_disjoint_covering_ae.choose_spec.2.1

open scoped Function in -- required for scoped `on` notation
/--
theorem `covering_disjoint_subtype` / 定理 `covering_disjoint_subtype`

English:
theorem covering_disjoint_subtype
  statement: Pairwise (Disjoint on fun x : h.index => h.covering x)
  proof: (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

中文:
定理 covering_disjoint_subtype
  结论: 两两 (Disjoint on fun x : h.index => h.covering x)
  证明: (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

Depends on / 依赖: covering_disjoint, h.covering_disjoint, pairwise_subtype_iff_pairwise_set
-/
theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
  (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

/--
theorem `covering_mem` / 定理 `covering_mem`

English:
theorem covering_mem
  given: {p : X × Set X} (hp : p in h.index)
  statement: h.covering p in f p.1
  proof: (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2

中文:
定理 covering_mem
  条件: {p : X × 集合 X} (hp : p in h.index)
  结论: h.covering p in f p.1
  证明: (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2

Depends on / 依赖: choose_spec, exists_disjoint_covering_ae, h.exists_disjoint_covering_ae.choose_spec
-/
theorem covering_mem {p : X × Set X} (hp : p in h.index) : h.covering p in f p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2

/--
theorem `covering_mem_family` / 定理 `covering_mem_family`

English:
theorem covering_mem_family
  given: {p : X × Set X} (hp : p in h.index)
  statement: h.covering p in v.setsAt p.1
  proof: (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1

中文:
定理 covering_mem_family
  条件: {p : X × 集合 X} (hp : p in h.index)
  结论: h.covering p in v.setsAt p.1
  证明: (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1

Depends on / 依赖: choose_spec, exists_disjoint_covering_ae, h.exists_disjoint_covering_ae.choose_spec
-/
theorem covering_mem_family {p : X × Set X} (hp : p in h.index) : h.covering p in v.setsAt p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1

/--
theorem `measure_sdiff_biUnion` / 定理 `measure_sdiff_biUnion`

English:
theorem measure_sdiff_biUnion
  statement: μ (s \ ⋃ p in h.index, h.covering p) = 0
  proof: h.exists_disjoint_covering_ae.choose_spec.2.2.2

@[deprecated (since := "2026-06-03")] alias measure_diff_biUnion := measure_sdiff_biUnion

中文:
定理 measure_sdiff_biUnion
  结论: μ (s \ ⋃ p in h.index, h.covering p) = 0
  证明: h.exists_disjoint_covering_ae.choose_spec.2.2.2

@[deprecated (since := "2026-06-03")] alias measure_diff_biUnion := measure_sdiff_biUnion

Depends on / 依赖: choose_spec, exists_disjoint_covering_ae, h.exists_disjoint_covering_ae.choose_spec
-/
theorem measure_sdiff_biUnion : μ (s \ ⋃ p in h.index, h.covering p) = 0 :=
  h.exists_disjoint_covering_ae.choose_spec.2.2.2

@[deprecated (since := "2026-06-03")] alias measure_diff_biUnion := measure_sdiff_biUnion

/--
theorem `index_countable` / 定理 `index_countable`

English:
theorem index_countable
  given: [SecondCountableTopology X]
  statement: h.index.Countable
  proof: h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)

中文:
定理 index_countable
  条件: [第二可数拓扑 X]
  结论: h.index.可数
  证明: h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)

Depends on / 依赖: countable_of_nonempty_interior, covering_disjoint, covering_mem_family, h.covering_disjoint.countable_of_nonempty_interior, h.covering_mem_family, nonempty_interior, v.nonempty_interior
-/
theorem index_countable [SecondCountableTopology X] : h.index.Countable :=
  h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)

/--
theorem `measurableSet_u` / 定理 `measurableSet_u`

English:
theorem measurableSet_u
  given: {p : X × Set X} (hp : p in h.index)
  proof: v.measurableSet p.1 _ (h.covering_mem_family hp)

中文:
定理 measurableSet_u
  条件: {p : X × 集合 X} (hp : p in h.index)
  证明: v.measurableSet p.1 _ (h.covering_mem_family hp)
-/
protected theorem measurableSet_u {p : X × Set X} (hp : p in h.index) :
    MeasurableSet (h.covering p) :=
  v.measurableSet p.1 _ (h.covering_mem_family hp)

/--
theorem `measure_le_tsum_of_absolutelyContinuous` / 定理 `measure_le_tsum_of_absolutelyContinuous`

English:
theorem measure_le_tsum_of_absolutelyContinuous
  statement: [SecondCountableTopology X] {ρ : Measure X}
  proof: calc
    ρ s <= ρ ((s \ ⋃ p in h.index, h.covering p) union ⋃ p in h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, sdiff_union_self])
    _ <= ρ (s \ ⋃ p in h.index, h.covering p) + ρ (⋃ p in h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_sdiff_biUnion]; rw [zero_add]; rw [measure_biUnion h.index_countable h.covering_disjoint fun x hx => h.measurableSet_u hx]

中文:
定理 measure_le_tsum_of_absolutelyContinuous
  结论: [第二可数拓扑 X] {ρ : 测度 X}
  证明: calc
    ρ s <= ρ ((s \ ⋃ p in h.index, h.covering p) union ⋃ p in h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, sdiff_union_self])
    _ <= ρ (s \ ⋃ p in h.index, h.covering p) + ρ (⋃ p in h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_sdiff_biUnion]; rw [zero_add]; rw [measure_biUnion h.index_countable h.covering_disjoint fun x hx => h.measurableSet_u hx]

Depends on / 依赖: covering, covering_disjoint, h.covering, h.covering_disjoint, h.index, h.index_countable, h.measurableSet_u, h.measure_sdiff_biUnion, index_countable, measurableSet_u, measure_biUnion, measure_mono, measure_sdiff_biUnion, measure_union_le, sdiff_union_self, subset_union_left, zero_add
-/
theorem measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : Measure X}
    (hρ : ρ ≪ μ) : ρ s <= ∑' p : h.index, ρ (h.covering p) :=
  calc
    ρ s <= ρ ((s \ ⋃ p in h.index, h.covering p) union ⋃ p in h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, sdiff_union_self])
    _ <= ρ (s \ ⋃ p in h.index, h.covering p) + ρ (⋃ p in h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_sdiff_biUnion]; rw [zero_add]; rw [measure_biUnion h.index_countable h.covering_disjoint fun x hx => h.measurableSet_u hx]

/--
theorem `measure_le_tsum` / 定理 `measure_le_tsum`

English:
theorem measure_le_tsum
  given: [SecondCountableTopology X]
  statement: μ s <= ∑' x : h.index, μ (h.covering x)
  proof: h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl

中文:
定理 measure_le_tsum
  条件: [第二可数拓扑 X]
  结论: μ s <= ∑' x : h.index, μ (h.covering x)
  证明: h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl, h.measure_le_tsum_of_absolutelyContinuous, measure_le_tsum_of_absolutelyContinuous
-/
theorem measure_le_tsum [SecondCountableTopology X] : μ s <= ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl

end FineSubfamilyOn

/--
Definition of `enlarge` / `enlarge` 的定义

English:
definition enlarge
  signature: (v : VitaliFamily μ) (δ : Real) (δpos : 0 < δ)
  body: v.setsAt x union {s | MeasurableSet s ∧ (interior s).Nonempty ∧ ¬s subseteq closedBall x δ}
  measurableSet := by
    rintro x s (hs | hs)
    exacts [v.measurableSet _ _ hs, hs.1]
  nonempty_interior := by
    rintro x s (hs | hs)
    exacts [v.nonempty_interior _ _ hs, hs.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨s, hs, h's⟩
    exact ⟨s, mem_union_left _ hs, h's⟩
  covering := by
    intro s f fset ffine
    let g : X -> Set (Set X) := fun x => f x inter v.setsAt x
    have : forall x in s, forall ε : Real, ε > 0 -> exists t in g x, t subseteq closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨t, tf, ht⟩ : exists t in f x, t subseteq closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx tf with (h't | h't)
      · exact ⟨t, ⟨tf, h't⟩, ht.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h't.2.2 ?_)
        exact ht.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩

中文:
定义 enlarge
  签名: (v : Vitali族 μ) (δ : 实数) (δpos : 0 < δ)
  定义体: v.setsAt x union {s | MeasurableSet s ∧ (interior s).Nonempty ∧ ¬s subseteq closedBall x δ}
  measurableSet := by
    rintro x s (hs | hs)
    exacts [v.measurableSet _ _ hs, hs.1]
  nonempty_interior := by
    rintro x s (hs | hs)
    exacts [v.nonempty_interior _ _ hs, hs.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨s, hs, h's⟩
    exact ⟨s, mem_union_left _ hs, h's⟩
  covering := by
    intro s f fset ffine
    let g : X -> Set (Set X) := fun x => f x inter v.setsAt x
    have : forall x in s, forall ε : Real, ε > 0 -> exists t in g x, t subseteq closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨t, tf, ht⟩ : exists t in f x, t subseteq closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx tf with (h't | h't)
      · exact ⟨t, ⟨tf, h't⟩, ht.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h't.2.2 ?_)
        exact ht.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩

Depends on / 依赖: MeasurableSet, Nonempty, closedBall, interior, setsAt, subseteq, v.setsAt
-/
def enlarge (v : VitaliFamily μ) (δ : Real) (δpos : 0 < δ) : VitaliFamily μ where
  setsAt x := v.setsAt x union {s | MeasurableSet s ∧ (interior s).Nonempty ∧ ¬s subseteq closedBall x δ}
  measurableSet := by
    rintro x s (hs | hs)
    exacts [v.measurableSet _ _ hs, hs.1]
  nonempty_interior := by
    rintro x s (hs | hs)
    exacts [v.nonempty_interior _ _ hs, hs.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨s, hs, h's⟩
    exact ⟨s, mem_union_left _ hs, h's⟩
  covering := by
    intro s f fset ffine
    let g : X -> Set (Set X) := fun x => f x inter v.setsAt x
    have : forall x in s, forall ε : Real, ε > 0 -> exists t in g x, t subseteq closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨t, tf, ht⟩ : exists t in f x, t subseteq closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx tf with (h't | h't)
      · exact ⟨t, ⟨tf, h't⟩, ht.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h't.2.2 ?_)
        exact ht.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩

variable (v : VitaliFamily μ)

/--
Definition of `filterAt` / `filterAt` 的定义

English:
definition filterAt
  signature: (x : X)
  body: (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)

中文:
定义 filterAt
  签名: (x : X)
  定义体: (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)

Depends on / 依赖: setsAt, smallSets, v.setsAt
-/
def filterAt (x : X) : Filter (Set X) := (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)

/--
theorem `_root_.Filter.HasBasis.vitaliFamily` / 定理 `_root_.Filter.HasBasis.vitaliFamily`

English:
theorem _root_.Filter.HasBasis.vitaliFamily
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {x : X}
  proof: by
  simpa only [← Set.ofPred_inter_eq_sep] using! h.smallSets.inf_principal _

中文:
定理 _root_.滤子.有基.vitaliFamily
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 X} {x : X}
  证明: by
  simpa only [← Set.ofPred_inter_eq_sep] using! h.smallSets.inf_principal _

Depends on / 依赖: Set.ofPred_inter_eq_sep, h.smallSets.inf_principal, inf_principal, ofPred_inter_eq_sep, smallSets
-/
theorem _root_.Filter.HasBasis.vitaliFamily {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : (v.filterAt x).HasBasis p (fun i => {t in v.setsAt x | t subseteq s i}) := by
  simpa only [← Set.ofPred_inter_eq_sep] using! h.smallSets.inf_principal _

/--
theorem `filterAt_basis_closedBall` / 定理 `filterAt_basis_closedBall`

English:
theorem filterAt_basis_closedBall
  given: (x : X)
  proof: nhds_basis_closedBall.vitaliFamily v

中文:
定理 filterAt_basis_closedBall
  条件: (x : X)
  证明: nhds_basis_closedBall.vitaliFamily v

Depends on / 依赖: nhds_basis_closedBall, nhds_basis_closedBall.vitaliFamily, vitaliFamily
-/
theorem filterAt_basis_closedBall (x : X) :
    (v.filterAt x).HasBasis (0 < ·) ({t in v.setsAt x | t subseteq closedBall x ·}) :=
  nhds_basis_closedBall.vitaliFamily v

/--
theorem `mem_filterAt_iff` / 定理 `mem_filterAt_iff`

English:
theorem mem_filterAt_iff
  given: {x : X} {s : Set (Set X)}
  proof: by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_ofPred]

中文:
定理 mem_filterAt_iff
  条件: {x : X} {s : 集合 (集合 X)}
  证明: by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_ofPred]

Depends on / 依赖: and_imp, filterAt_basis_closedBall, mem_iff, mem_ofPred, subset_def, v.filterAt_basis_closedBall
-/
theorem mem_filterAt_iff {x : X} {s : Set (Set X)} :
    s in v.filterAt x ↔ exists ε > (0 : Real), forall t in v.setsAt x, t subseteq closedBall x ε -> t in s := by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_ofPred]

/--
Instance `filterAt_neBot` / 实例 `filterAt_neBot`

English:
instance filterAt_neBot
  signature: (x : X)
  body: (v.filterAt_basis_closedBall x).neBot_iff.2 v.nontrivial _ _

中文:
实例 filterAt_neBot
  签名: (x : X)
  定义体: (v.filterAt_basis_closedBall x).neBot_iff.2 v.nontrivial _ _

Depends on / 依赖: filterAt_basis_closedBall, neBot_iff, nontrivial, v.filterAt_basis_closedBall, v.nontrivial
-/
instance filterAt_neBot (x : X) : (v.filterAt x).NeBot :=
(v.filterAt_basis_closedBall x).neBot_iff.2 v.nontrivial _ _

/--
theorem `eventually_filterAt_iff` / 定理 `eventually_filterAt_iff`

English:
theorem eventually_filterAt_iff
  given: {x : X} {P : Set X -> Prop}
  proof: v.mem_filterAt_iff

中文:
定理 eventually_filterAt_iff
  条件: {x : X} {P : 集合 X -> 命题}
  证明: v.mem_filterAt_iff

Depends on / 依赖: mem_filterAt_iff, v.mem_filterAt_iff
-/
theorem eventually_filterAt_iff {x : X} {P : Set X -> Prop} :
    (forallᶠ t in v.filterAt x, P t) ↔ exists ε > (0 : Real), forall t in v.setsAt x, t subseteq closedBall x ε -> P t :=
  v.mem_filterAt_iff

/--
theorem `tendsto_filterAt_iff` / 定理 `tendsto_filterAt_iff`

English:
theorem tendsto_filterAt_iff
  given: {ι : Type*} {l : Filter ι} {f : ι -> Set X} {x : X}
  proof: by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]

中文:
定理 tendsto_filterAt_iff
  条件: {ι : 类型} {l : 滤子 ι} {f : ι -> 集合 X} {x : X}
  证明: by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]

Depends on / 依赖: and_comm, filterAt, mem_powerset_iff, nhds_basis_closedBall, nhds_basis_closedBall.smallSets.tendsto_right_iff, smallSets, tendsto_inf, tendsto_principal, tendsto_right_iff
-/
theorem tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι -> Set X} {x : X} :
    Tendsto f l (v.filterAt x) ↔
      (forallᶠ i in l, f i in v.setsAt x) ∧ forall ε > (0 : Real), forallᶠ i in l, f i subseteq closedBall x ε := by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]

/--
theorem `eventually_filterAt_mem_setsAt` / 定理 `eventually_filterAt_mem_setsAt`

English:
theorem eventually_filterAt_mem_setsAt
  given: (x : X)
  statement: forallᶠ t in v.filterAt x, t in v.setsAt x
  proof: (v.tendsto_filterAt_iff.mp tendsto_id).1

中文:
定理 eventually_filterAt_mem_setsAt
  条件: (x : X)
  结论: 对任意ᶠ t in v.filterAt x, t in v.setsAt x
  证明: (v.tendsto_filterAt_iff.mp tendsto_id).1

Depends on / 依赖: tendsto_filterAt_iff, tendsto_id, v.tendsto_filterAt_iff.mp
-/
theorem eventually_filterAt_mem_setsAt (x : X) : forallᶠ t in v.filterAt x, t in v.setsAt x :=
  (v.tendsto_filterAt_iff.mp tendsto_id).1

/--
theorem `eventually_filterAt_subset_closedBall` / 定理 `eventually_filterAt_subset_closedBall`

English:
theorem eventually_filterAt_subset_closedBall
  given: (x : X) {ε : Real} (hε : 0 < ε)
  proof: (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε

中文:
定理 eventually_filterAt_subset_closedBall
  条件: (x : X) {ε : 实数} (hε : 0 < ε)
  证明: (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε

Depends on / 依赖: tendsto_filterAt_iff, tendsto_id, v.tendsto_filterAt_iff.mp
-/
theorem eventually_filterAt_subset_closedBall (x : X) {ε : Real} (hε : 0 < ε) :
    forallᶠ t : Set X in v.filterAt x, t subseteq closedBall x ε :=
  (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε

/--
theorem `eventually_filterAt_measurableSet` / 定理 `eventually_filterAt_measurableSet`

English:
theorem eventually_filterAt_measurableSet
  given: (x : X)
  statement: forallᶠ t in v.filterAt x, MeasurableSet t
  proof: by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha

中文:
定理 eventually_filterAt_measurableSet
  条件: (x : X)
  结论: 对任意ᶠ t in v.filterAt x, 可测集 t
  证明: by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha

Depends on / 依赖: eventually_filterAt_mem_setsAt, filter_upwards, measurableSet, v.eventually_filterAt_mem_setsAt, v.measurableSet
-/
theorem eventually_filterAt_measurableSet (x : X) : forallᶠ t in v.filterAt x, MeasurableSet t := by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha

/--
theorem `frequently_filterAt_iff` / 定理 `frequently_filterAt_iff`

English:
theorem frequently_filterAt_iff
  given: {x : X} {P : Set X -> Prop}
  proof: by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_ofPred]

中文:
定理 frequently_filterAt_iff
  条件: {x : X} {P : 集合 X -> 命题}
  证明: by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_ofPred]

Depends on / 依赖: and_assoc, filterAt_basis_closedBall, frequently_iff, mem_ofPred, subset_def, v.filterAt_basis_closedBall
-/
theorem frequently_filterAt_iff {x : X} {P : Set X -> Prop} :
    (existsᶠ t in v.filterAt x, P t) ↔ forall ε > (0 : Real), exists t in v.setsAt x, t subseteq closedBall x ε ∧ P t := by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_ofPred]

/--
theorem `eventually_filterAt_subset_of_nhds` / 定理 `eventually_filterAt_subset_of_nhds`

English:
theorem eventually_filterAt_subset_of_nhds
  given: {x : X} {o : Set X} (hx : o in 𝓝 x)
  proof: (eventually_smallSets_subset.2 hx).filter_mono inf_le_left

@[simp]

中文:
定理 eventually_filterAt_subset_of_nhds
  条件: {x : X} {o : 集合 X} (hx : o in 𝓝 x)
  证明: (eventually_smallSets_subset.2 hx).filter_mono inf_le_left

@[simp]

Depends on / 依赖: eventually_smallSets_subset, filter_mono, inf_le_left
-/
theorem eventually_filterAt_subset_of_nhds {x : X} {o : Set X} (hx : o in 𝓝 x) :
    forallᶠ t in v.filterAt x, t subseteq o :=
  (eventually_smallSets_subset.2 hx).filter_mono inf_le_left

@[simp]
/--
theorem `filterAt_enlarge` / 定理 `filterAt_enlarge`

English:
theorem filterAt_enlarge
  given: (v : VitaliFamily μ) {δ : Real} (δpos : 0 < δ)
  proof: by
  ext1 x
  suffices {t | MeasurableSet t -> (interior t).Nonempty -> ¬t subseteq closedBall x δ ->
      t in v.setsAt x} in (𝓝 x).smallSets by
    simpa [VitaliFamily.filterAt, VitaliFamily.enlarge, ← sup_principal, inf_sup_left,
      mem_inf_principal]
  filter_upwards [eventually_smallSets_subset.mpr (closedBall_mem_nhds _ δpos)]
  simp +contextual

中文:
定理 filterAt_enlarge
  条件: (v : Vitali族 μ) {δ : 实数} (δpos : 0 < δ)
  证明: by
  ext1 x
  suffices {t | MeasurableSet t -> (interior t).Nonempty -> ¬t subseteq closedBall x δ ->
      t in v.setsAt x} in (𝓝 x).smallSets by
    simpa [VitaliFamily.filterAt, VitaliFamily.enlarge, ← sup_principal, inf_sup_left,
      mem_inf_principal]
  filter_upwards [eventually_smallSets_subset.mpr (closedBall_mem_nhds _ δpos)]
  simp +contextual

Depends on / 依赖: MeasurableSet, Nonempty, VitaliFamily, VitaliFamily.enlarge, VitaliFamily.filterAt, closedBall, closedBall_mem_nhds, contextual, enlarge, eventually_smallSets_subset, eventually_smallSets_subset.mpr, filterAt, filter_upwards, inf_sup_left, interior, mem_inf_principal, setsAt, smallSets, subseteq, sup_principal
-/
theorem filterAt_enlarge (v : VitaliFamily μ) {δ : Real} (δpos : 0 < δ) :
    (v.enlarge δ δpos).filterAt = v.filterAt := by
  ext1 x
  suffices {t | MeasurableSet t -> (interior t).Nonempty -> ¬t subseteq closedBall x δ ->
      t in v.setsAt x} in (𝓝 x).smallSets by
    simpa [VitaliFamily.filterAt, VitaliFamily.enlarge, ← sup_principal, inf_sup_left,
      mem_inf_principal]
  filter_upwards [eventually_smallSets_subset.mpr (closedBall_mem_nhds _ δpos)]
  simp +contextual

/--
theorem `fineSubfamilyOn_iff_frequently` / 定理 `fineSubfamilyOn_iff_frequently`

English:
theorem fineSubfamilyOn_iff_frequently
  given: (v : VitaliFamily μ) {f : X -> Set (Set X)} {s : Set X}
  proof: by
  refine forall₂_congr fun x hx => ?_
  simp [frequently_filterAt_iff, ← and_assoc, and_right_comm]

中文:
定理 fineSubfamilyOn_iff_frequently
  条件: (v : Vitali族 μ) {f : X -> 集合 (集合 X)} {s : 集合 X}
  证明: by
  refine forall₂_congr fun x hx => ?_
  simp [frequently_filterAt_iff, ← and_assoc, and_right_comm]

Depends on / 依赖: and_assoc, and_right_comm, frequently_filterAt_iff
-/
theorem fineSubfamilyOn_iff_frequently (v : VitaliFamily μ) {f : X -> Set (Set X)} {s : Set X} :
    v.FineSubfamilyOn f s ↔ forall x in s, existsᶠ t in v.filterAt x, t in f x := by
  refine forall₂_congr fun x hx => ?_
  simp [frequently_filterAt_iff, ← and_assoc, and_right_comm]

/--
theorem `fineSubfamilyOn_of_frequently` / 定理 `fineSubfamilyOn_of_frequently`

English:
theorem fineSubfamilyOn_of_frequently
  statement: (v : VitaliFamily μ) (f : X -> Set (Set X)) (s : Set X)
  proof: by
  rwa [fineSubfamilyOn_iff_frequently]

中文:
定理 fineSubfamilyOn_of_frequently
  结论: (v : Vitali族 μ) (f : X -> 集合 (集合 X)) (s : 集合 X)
  证明: by
  rwa [fineSubfamilyOn_iff_frequently]

Depends on / 依赖: fineSubfamilyOn_iff_frequently
-/
theorem fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : X -> Set (Set X)) (s : Set X)
    (h : forall x in s, existsᶠ t in v.filterAt x, t in f x) : v.FineSubfamilyOn f s := by
  rwa [fineSubfamilyOn_iff_frequently]

end VitaliFamily
