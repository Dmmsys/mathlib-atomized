/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.WithTop

/-!
# Lemmas around weak (pseudo) extended metric spaces.

In this file we show that whenever `some : α → Option α` is an open embedding and `α` is a
`WeakPseudoEMetricSpace`, then `Option α` is as well in a natural manner. We then use this to prove
`ℝ≥0` and `EReal` are weak extended metric spaces.

## Main statements

* `Option.weakPseudoEMetricSpace_of_isOpenEmbedding`: states that under a weak condition, if `α` is
  a weak pseudo extended space, so is `Option α`.
* `instWeakPseudoEMetricSpaceOnePoint`: The one point compactification of a weak pseudo extended
  metric space is a weak pseudo extended metric space.
* `instWeakEMetricSpaceENNReal`: `ℝ≥0∞` is a weak extended metric space.
* `instWeakEMetricSpaceEReal`: `EReal` is a weak extended metric space.

TODO: Some lemmas around order topologies can likely be generalised from linear orders to pre-
or partial orders.

-/

@[expose] public section

open Set Filter Topology WithTop WithBot

open scoped Uniformity Topology NNReal ENNReal Pointwise

universe u

variable {α : Type u} [t : TopologicalSpace α]

section

namespace Option

/-- Given some (extended) distance function on `α`, it can be extended to a distance function on
`Option α` by defining `edist none a = 0` if `a = none` and `∞` otherwise. -/
instance (priority := low) toEDist {α : Type u} [EDist α] : EDist (Option α) where
  edist
  | none, (x : α) => ∞
  | none, none => 0
  | (x : α), none => ∞
  | (x : α), (y : α) => edist x y

variable [m : WeakPseudoEMetricSpace α]

@[simp]
/--
theorem `edist_none_none` / 定理 `edist_none_none`

English:
theorem edist_none_none
  statement: edist (self := Option.toEDist (α := α))
  proof: rfl

@[simp]

中文:
定理 edist_none_none
  结论: edist (self := 选项类型.toEDist (α := α))
  证明: rfl

@[simp]

Depends on / 依赖: Option.toEDist, toEDist
-/
theorem edist_none_none : edist (self := Option.toEDist (α := α))
    none none = 0 := rfl

@[simp]
/--
theorem `edist_none_some` / 定理 `edist_none_some`

English:
theorem edist_none_some
  given: {a : α}
  proof: rfl

@[simp]

中文:
定理 edist_none_some
  条件: {a : α}
  证明: rfl

@[simp]

Depends on / 依赖: Option.toEDist, toEDist
-/
theorem edist_none_some {a : α} :
    edist (self := Option.toEDist (α := α)) none a = ⊤ := rfl

@[simp]
/--
theorem `edist_some_none` / 定理 `edist_some_none`

English:
theorem edist_some_none
  given: {a : α}
  proof: rfl

@[simp]

中文:
定理 edist_some_none
  条件: {a : α}
  证明: rfl

@[simp]

Depends on / 依赖: Option.toEDist, toEDist
-/
theorem edist_some_none {a : α} :
    edist (self := Option.toEDist (α := α)) a none = ⊤ := rfl

@[simp]
/--
theorem `edist_some_some` / 定理 `edist_some_some`

English:
theorem edist_some_some
  given: {a b : α}
  proof: rfl

中文:
定理 edist_some_some
  条件: {a b : α}
  证明: rfl

Depends on / 依赖: Option.toEDist, toEDist
-/
theorem edist_some_some {a b : α} :
    edist (self := Option.toEDist (α := α)) a b = edist a b := rfl

/--
theorem `some_eball` / 定理 `some_eball`

English:
theorem some_eball
  given: (a : α) (r : ENNReal)
  proof: by
  ext x
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | none => simp at h
  | (y : α) =>
    exact ⟨y, h, rfl⟩

中文:
定理 some_eball
  条件: (a : α) (r : 广义非负实数)
  证明: by
  ext x
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | none => simp at h
  | (y : α) =>
    exact ⟨y, h, rfl⟩
-/
theorem some_eball (a : α) (r : ENNReal) :
    Option.some '' Metric.eball a r = Metric.eball (α := Option α) a r := by
  ext x
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | none => simp at h
  | (y : α) =>
    exact ⟨y, h, rfl⟩

/--
lemma `edist_self'` / 引理 `edist_self'`

English:
lemma edist_self'
  given: {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α)

中文:
引理 edist_self'
  条件: {α : 类型u} [拓扑空间 α] (m : WeakPseudoEMetric空间 α)
-/
lemma edist_self' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    forall x : Option α, edist x x = 0
  | (_ : α) => by simp [m.edist_self]
  | none => rfl

/--
lemma `edist_comm'` / 引理 `edist_comm'`

English:
lemma edist_comm'
  given: {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α)

中文:
引理 edist_comm'
  条件: {α : 类型u} [拓扑空间 α] (m : WeakPseudoEMetric空间 α)
-/
lemma edist_comm' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    forall x y : Option α, edist x y = edist y x
  | (_ : α), (_ : α) => by simp [m.edist_comm]
  | (_ : α), none => by simp
  | none, (_ : α) => by simp
  | none, none => by simp

/--
lemma `edist_triangle'` / 引理 `edist_triangle'`

English:
lemma edist_triangle'
  given: {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α)

中文:
引理 edist_triangle'
  条件: {α : 类型u} [拓扑空间 α] (m : WeakPseudoEMetric空间 α)
-/
lemma edist_triangle' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    forall x y z : Option α, edist x z <= edist x y + edist y z
  | (_ : α), (_ : α), (_ : α) => by simp [m.edist_triangle]
  | none, (_ : α), (_ : α) => by simp
  | (_ : α), none, (_ : α) => by simp
  | none, none, (_ : α) => by simp
  | (_ : α), (_ : α), none => by simp
  | none, (_ : α), none => by simp
  | (_ : α), none, none => by simp
  | none, none, none => by simp

/--
theorem `ball_infty_of_pos` / 定理 `ball_infty_of_pos`

English:
theorem ball_infty_of_pos
  given: {r : ENNReal} (hr : 0 < r)
  proof: by
  refine eq_singleton_iff_unique_mem.mpr ⟨Metric.mem_eball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | none => tauto

中文:
定理 ball_infty_of_pos
  条件: {r : 广义非负实数} (hr : 0 < r)
  证明: by
  refine eq_singleton_iff_unique_mem.mpr ⟨Metric.mem_eball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | none => tauto

Depends on / 依赖: Metric, Metric.mem_eball.mpr, eq_singleton_iff_unique_mem, eq_singleton_iff_unique_mem.mpr, mem_eball
-/
theorem ball_infty_of_pos {r : ENNReal} (hr : 0 < r) :
    Metric.eball (none : Option α) r = {none} := by
  refine eq_singleton_iff_unique_mem.mpr ⟨Metric.mem_eball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | none => tauto

/--
Definition of `WeakPseudoEMetricSpace.OfIsOpenEmbedding` / `WeakPseudoEMetricSpace.OfIsOpenEmbedding` 的定义

English:
abbreviation WeakPseudoEMetricSpace.OfIsOpenEmbedding
  signature: {α : Type u} [t : TopologicalSpace α]
  body: edist
  edist_self := h_edist ▸ edist_self' m
  edist_comm := h_edist ▸ edist_comm' m
  edist_triangle := h_edist ▸ edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (Option α) (PseudoEMetricSpace.ofEDist edist
      (h_edist ▸ edist_self' m) (h_edist ▸ edist_comm' m) (h_edist ▸ edist_triangle' m))).mpr
    intro x xs
    suffices exists ε > 0, @Metric.eball (Option α) Option.toEDist x ε subseteq s by rwa [← h_edist] at this
    match x with
    | none =>
      exact ⟨1, by norm_num, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, some_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    rw [h_edist]
    match x with
    | (x : α) =>
      obtain ⟨s', s'o, s's⟩ := m.topology_eq_on_restrict x r
      refine ⟨some '' s', ?_, ?_⟩
      · exact (IsOpenEmbedding.isOpen_iff_image_isOpen h).mp s'o
      ext ⟨y, yh⟩
      match y with
      | none => contradiction
      | (z : α) =>
        apply Set.ext_iff.mp at s's
        simp only [mem_preimage, Subtype.forall, Metric.mem_eball, mem_image] at s's ⊢ yh
        specialize s's z yh
        refine ⟨fun ⟨r, rh, rh'⟩ => ?_, fun _ => ⟨z, by tauto⟩⟩
exact s's.1 h.injective rh' ▸ rh
    | none =>
      apply discreteTopology_iff_forall_isOpen.mp
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

中文:
缩写 WeakPseudoEMetric空间.OfIsOpenEmbedding
  签名: {α : 类型u} [t : 拓扑空间 α]
  定义体: edist
  edist_self := h_edist ▸ edist_self' m
  edist_comm := h_edist ▸ edist_comm' m
  edist_triangle := h_edist ▸ edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (Option α) (PseudoEMetricSpace.ofEDist edist
      (h_edist ▸ edist_self' m) (h_edist ▸ edist_comm' m) (h_edist ▸ edist_triangle' m))).mpr
    intro x xs
    suffices exists ε > 0, @Metric.eball (Option α) Option.toEDist x ε subseteq s by rwa [← h_edist] at this
    match x with
    | none =>
      exact ⟨1, by norm_num, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, some_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    rw [h_edist]
    match x with
    | (x : α) =>
      obtain ⟨s', s'o, s's⟩ := m.topology_eq_on_restrict x r
      refine ⟨some '' s', ?_, ?_⟩
      · exact (IsOpenEmbedding.isOpen_iff_image_isOpen h).mp s'o
      ext ⟨y, yh⟩
      match y with
      | none => contradiction
      | (z : α) =>
        apply Set.ext_iff.mp at s's
        simp only [mem_preimage, Subtype.forall, Metric.mem_eball, mem_image] at s's ⊢ yh
        specialize s's z yh
        refine ⟨fun ⟨r, rh, rh'⟩ => ?_, fun _ => ⟨z, by tauto⟩⟩
exact s's.1 h.injective rh' ▸ rh
    | none =>
      apply discreteTopology_iff_forall_isOpen.mp
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology
-/
abbrev WeakPseudoEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakPseudoEMetricSpace α] [inst : EDist (Option α)]
    (h_edist : inst = Option.toEDist) (h : IsOpenEmbedding (some (α := α))) :
    WeakPseudoEMetricSpace (Option α) where
  edist := edist
  edist_self := h_edist ▸ edist_self' m
  edist_comm := h_edist ▸ edist_comm' m
  edist_triangle := h_edist ▸ edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (Option α) (PseudoEMetricSpace.ofEDist edist
      (h_edist ▸ edist_self' m) (h_edist ▸ edist_comm' m) (h_edist ▸ edist_triangle' m))).mpr
    intro x xs
    suffices exists ε > 0, @Metric.eball (Option α) Option.toEDist x ε subseteq s by rwa [← h_edist] at this
    match x with
    | none =>
      exact ⟨1, by norm_num, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, some_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    rw [h_edist]
    match x with
    | (x : α) =>
      obtain ⟨s', s'o, s's⟩ := m.topology_eq_on_restrict x r
      refine ⟨some '' s', ?_, ?_⟩
      · exact (IsOpenEmbedding.isOpen_iff_image_isOpen h).mp s'o
      ext ⟨y, yh⟩
      match y with
      | none => contradiction
      | (z : α) =>
        apply Set.ext_iff.mp at s's
        simp only [mem_preimage, Subtype.forall, Metric.mem_eball, mem_image] at s's ⊢ yh
        specialize s's z yh
        refine ⟨fun ⟨r, rh, rh'⟩ => ?_, fun _ => ⟨z, by tauto⟩⟩
exact s's.1 h.injective rh' ▸ rh
    | none =>
      apply discreteTopology_iff_forall_isOpen.mp
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

/--
Definition of `WeakEMetricSpace.OfIsOpenEmbedding` / `WeakEMetricSpace.OfIsOpenEmbedding` 的定义

English:
abbreviation WeakEMetricSpace.OfIsOpenEmbedding
  signature: {α : Type u} [t : TopologicalSpace α]
  body: { toWeakPseudoEMetricSpace := WeakPseudoEMetricSpace.OfIsOpenEmbedding h_edist h,
    eq_of_edist_eq_zero {x y} xy := by
      rw [congr(@edist _ $h_edist x y)] at xy
      cases x <;> cases y
      · rfl
      · simp at xy
      · simp at xy
      rw [m.eq_of_edist_eq_zero xy]
    }

中文:
缩写 WeakEMetric空间.OfIsOpenEmbedding
  签名: {α : 类型u} [t : 拓扑空间 α]
  定义体: { toWeakPseudoEMetricSpace := WeakPseudoEMetricSpace.OfIsOpenEmbedding h_edist h,
    eq_of_edist_eq_zero {x y} xy := by
      rw [congr(@edist _ $h_edist x y)] at xy
      cases x <;> cases y
      · rfl
      · simp at xy
      · simp at xy
      rw [m.eq_of_edist_eq_zero xy]
    }
-/
abbrev WeakEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakEMetricSpace α] [inst : EDist (Option α)]
    (h_edist : inst = Option.toEDist) (h : IsOpenEmbedding (some (α := α))) :
    WeakEMetricSpace (Option α) :=
  { toWeakPseudoEMetricSpace := WeakPseudoEMetricSpace.OfIsOpenEmbedding h_edist h,
    eq_of_edist_eq_zero {x y} xy := by
      rw [congr(@edist _ $h_edist x y)] at xy
      cases x <;> cases y
      · rfl
      · simp at xy
      · simp at xy
      rw [m.eq_of_edist_eq_zero xy]
    }

end Option

variable [LinearOrder α] [OrderTopology α]

/-- If `α` has a linear order topology, `some : α → WithTop α` is an open embedding with respect to
the order topologies. -/
@[to_dual]
/--
theorem `WithTop.isOpenEmbedding_some` / 定理 `WithTop.isOpenEmbedding_some`

English:
theorem WithTop.isOpenEmbedding_some
  statement: IsOpenEmbedding (some (α := α))
  proof: ⟨WithTop.coe_strictMono.isEmbedding_of_ordConnected (range_coe (α := α) ▸ ordConnected_Iio),
   range_coe (α := α) ▸ isOpen_Iio' ⊤⟩

@[to_dual]

中文:
定理 WithTop.isOpenEmbedding_some
  结论: 是开嵌入 (some (α := α))
  证明: ⟨WithTop.coe_strictMono.isEmbedding_of_ordConnected (range_coe (α := α) ▸ ordConnected_Iio),
   range_coe (α := α) ▸ isOpen_Iio' ⊤⟩

@[to_dual]
-/
theorem WithTop.isOpenEmbedding_some : IsOpenEmbedding (some (α := α)) :=
  ⟨WithTop.coe_strictMono.isEmbedding_of_ordConnected (range_coe (α := α) ▸ ordConnected_Iio),
   range_coe (α := α) ▸ isOpen_Iio' ⊤⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EDist
  signature: α] : EDist (WithTop α) where

中文:
实例 [EDist
  签名: α] : EDist (WithTop α) where
-/
instance [EDist α] : EDist (WithTop α) where
  edist
  | ⊤, (x : α) => ∞
  | ⊤, ⊤ => 0
  | (x : α), ⊤ => ∞
  | (x : α), (y : α) => edist x y

/-- If `α` has a topology induced by a linear order and is a weak pseudo extended metric space,
so is `WithTop α` -/
@[to_dual]
/--
Instance `instWeakPseudoEMetricSpaceWithTop` / 实例 `instWeakPseudoEMetricSpaceWithTop`

English:
instance instWeakPseudoEMetricSpaceWithTop
  signature: [m : WeakPseudoEMetricSpace α]
  body: letI : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  letI : WeakPseudoEMetricSpace (Option α) :=
    Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding (inst := instEDistWithTop) rfl
    WithTop.isOpenEmbedding_some
inferInstanceAs WeakPseudoEMetricSpace (Option α)

中文:
实例 instWeakPseudoEMetricSpaceWithTop
  签名: [m : WeakPseudoEMetric空间 α]
  定义体: letI : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  letI : WeakPseudoEMetricSpace (Option α) :=
    Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding (inst := instEDistWithTop) rfl
    WithTop.isOpenEmbedding_some
inferInstanceAs WeakPseudoEMetricSpace (Option α)

Depends on / 依赖: OfIsOpenEmbedding, Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding, TopologicalSpace, TopologicalSpace.instWithTopOfOrderTopology, WeakPseudoEMetricSpace, WithTop, WithTop.isOpenEmbedding_some, instEDistWithTop, instWithTopOfOrderTopology, isOpenEmbedding_some
-/
instance instWeakPseudoEMetricSpaceWithTop [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (WithTop α) :=
  letI : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  letI : WeakPseudoEMetricSpace (Option α) :=
    Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding (inst := instEDistWithTop) rfl
    WithTop.isOpenEmbedding_some
inferInstanceAs WeakPseudoEMetricSpace (Option α)

/-- If `α` has a topology induced by a linear order and is a weak extended metric space,
so is `WithTop α` -/
@[to_dual]
/--
Instance `instWeakEMetricSpaceWithTop` / 实例 `instWeakEMetricSpaceWithTop`

English:
instance instWeakEMetricSpaceWithTop
  signature: [m : WeakEMetricSpace α]
  body: let : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistWithTop) rfl WithTop.isOpenEmbedding_some
inferInstanceAs WeakEMetricSpace (Option α)

中文:
实例 instWeakEMetricSpaceWithTop
  签名: [m : WeakEMetric空间 α]
  定义体: let : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistWithTop) rfl WithTop.isOpenEmbedding_some
inferInstanceAs WeakEMetricSpace (Option α)

Depends on / 依赖: OfIsOpenEmbedding, Option.WeakEMetricSpace.OfIsOpenEmbedding, TopologicalSpace, TopologicalSpace.instWithTopOfOrderTopology, WeakEMetricSpace, WithTop, WithTop.isOpenEmbedding_some, instEDistWithTop, instWithTopOfOrderTopology, isOpenEmbedding_some
-/
instance instWeakEMetricSpaceWithTop [m : WeakEMetricSpace α] : WeakEMetricSpace (WithTop α) :=
  let : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistWithTop) rfl WithTop.isOpenEmbedding_some
inferInstanceAs WeakEMetricSpace (Option α)

open scoped OnePoint in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EDist
  signature: α] : EDist (OnePoint α) where

中文:
实例 [EDist
  签名: α] : EDist (OnePoint α) where
-/
instance [EDist α] : EDist (OnePoint α) where
  edist
  | ∞, (x : α) => none
  | ∞, ∞ => 0
  | (x : α), ∞ => none
  | (x : α), (y : α) => edist x y

/--
Instance `instWeakPseudoEMetricSpaceOnePoint` / 实例 `instWeakPseudoEMetricSpaceOnePoint`

English:
instance instWeakPseudoEMetricSpaceOnePoint
  signature: [m : WeakPseudoEMetricSpace α]
  body: let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakPseudoEMetricSpace (Option α) := Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
inferInstanceAs WeakPseudoEMetricSpace (Option α)

中文:
实例 instWeakPseudoEMetricSpaceOnePoint
  签名: [m : WeakPseudoEMetric空间 α]
  定义体: let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakPseudoEMetricSpace (Option α) := Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
inferInstanceAs WeakPseudoEMetricSpace (Option α)

Depends on / 依赖: OfIsOpenEmbedding, OnePoint, OnePoint.instTopologicalSpace, OnePoint.isOpenEmbedding_coe, Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding, TopologicalSpace, WeakPseudoEMetricSpace, instEDistOnePoint, instTopologicalSpace, isOpenEmbedding_coe
-/
instance instWeakPseudoEMetricSpaceOnePoint [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakPseudoEMetricSpace (Option α) := Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
inferInstanceAs WeakPseudoEMetricSpace (Option α)

/--
Instance `instWeakEMetricSpaceOnePoint` / 实例 `instWeakEMetricSpaceOnePoint`

English:
instance instWeakEMetricSpaceOnePoint
  signature: [m : WeakEMetricSpace α]
  body: let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
inferInstanceAs WeakEMetricSpace (Option α)

中文:
实例 instWeakEMetricSpaceOnePoint
  签名: [m : WeakEMetric空间 α]
  定义体: let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
inferInstanceAs WeakEMetricSpace (Option α)

Depends on / 依赖: OfIsOpenEmbedding, OnePoint, OnePoint.instTopologicalSpace, OnePoint.isOpenEmbedding_coe, Option.WeakEMetricSpace.OfIsOpenEmbedding, TopologicalSpace, WeakEMetricSpace, instEDistOnePoint, instTopologicalSpace, isOpenEmbedding_coe
-/
instance instWeakEMetricSpaceOnePoint [m : WeakEMetricSpace α] :
    WeakEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
inferInstanceAs WeakEMetricSpace (Option α)

/--
Instance `instWeakEMetricSpaceENNReal` / 实例 `instWeakEMetricSpaceENNReal`

English:
instance instWeakEMetricSpaceENNReal
  signature: : WeakEMetricSpace Real>=0∞
  body: inferInstanceAs WeakEMetricSpace (WithTop Real>=0)

中文:
实例 instWeakEMetricSpaceENN实数
  签名: : WeakEMetric空间 实数>=0∞
  定义体: inferInstanceAs WeakEMetricSpace (WithTop Real>=0)

Depends on / 依赖: WeakEMetricSpace, WithTop
-/
noncomputable instance instWeakEMetricSpaceENNReal : WeakEMetricSpace Real>=0∞ :=
inferInstanceAs WeakEMetricSpace (WithTop Real>=0)

/--
Instance `instWeakEMetricSpaceEReal` / 实例 `instWeakEMetricSpaceEReal`

English:
instance instWeakEMetricSpaceEReal
  signature: : WeakEMetricSpace EReal
  body: inferInstanceAs WeakEMetricSpace (WithBot (WithTop Real))

中文:
实例 instWeakEMetricSpaceE实数
  签名: : WeakEMetric空间 E实数
  定义体: inferInstanceAs WeakEMetricSpace (WithBot (WithTop Real))

Depends on / 依赖: WeakEMetricSpace, WithBot, WithTop
-/
noncomputable instance instWeakEMetricSpaceEReal : WeakEMetricSpace EReal :=
inferInstanceAs WeakEMetricSpace (WithBot (WithTop Real))

/--
Instance `instWeakEMetricSpaceENat` / 实例 `instWeakEMetricSpaceENat`

English:
instance instWeakEMetricSpaceENat
  signature: : WeakEMetricSpace Nat∞
  body: inferInstanceAs WeakEMetricSpace (WithTop Nat)

中文:
实例 instWeakEMetricSpaceE自然数
  签名: : WeakEMetric空间 自然数∞
  定义体: inferInstanceAs WeakEMetricSpace (WithTop Nat)

Depends on / 依赖: WeakEMetricSpace, WithTop
-/
noncomputable instance instWeakEMetricSpaceENat : WeakEMetricSpace Nat∞ :=
inferInstanceAs WeakEMetricSpace (WithTop Nat)

/--
theorem `ENNReal.edist_eq_top_iff` / 定理 `ENNReal.edist_eq_top_iff`

English:
theorem ENNReal.edist_eq_top_iff
  given: (a b : Real>=0∞)
  statement: edist a b = ∞ ↔ a != b ∧ (a = ∞ ∨ b = ∞)
  proof: by
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, or_self, and_true, iff_false,
    top_ne_coe, not_false_eq_true, coe_ne_top, or_false, and_self, or_true, and_self, iff_true,
    coe_inj, and_false, iff_false]
  · exact zero_ne_top
  · rfl
  · rfl
  · exact edist_ne_top _ _

中文:
定理 广义非负实数.edist_eq_top_iff
  条件: (a b : 实数>=0∞)
  结论: edist a b = ∞ ↔ a != b ∧ (a = ∞ ∨ b = ∞)
  证明: by
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, or_self, and_true, iff_false,
    top_ne_coe, not_false_eq_true, coe_ne_top, or_false, and_self, or_true, and_self, iff_true,
    coe_inj, and_false, iff_false]
  · exact zero_ne_top
  · rfl
  · rfl
  · exact edist_ne_top _ _

Depends on / 依赖: and_false, and_self, and_true, coe_inj, coe_ne_top, edist_ne_top, iff_false, iff_true, ne_eq, not_false_eq_true, not_true_eq_false, or_false, or_self, or_true, top_ne_coe, zero_ne_top
-/
theorem ENNReal.edist_eq_top_iff (a b : Real>=0∞) : edist a b = ∞ ↔ a != b ∧ (a = ∞ ∨ b = ∞) := by
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, or_self, and_true, iff_false,
    top_ne_coe, not_false_eq_true, coe_ne_top, or_false, and_self, or_true, and_self, iff_true,
    coe_inj, and_false, iff_false]
  · exact zero_ne_top
  · rfl
  · rfl
  · exact edist_ne_top _ _

--TODO: Many more lemmas around `edist` on `ℝ≥0∞` etc. to add
