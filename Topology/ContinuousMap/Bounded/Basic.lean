/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Bornology.BoundedOperation
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with the uniform distance.
-/

@[expose] public section

assert_not_exists CStarRing

noncomputable section

open Topology Bornology NNReal UniformConvergence

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

/--
Definition of `BoundedContinuousFunction` / `BoundedContinuousFunction` 的定义

English:
structure BoundedContinuousFunction
  parameters: (α : Type u) (β : Type v) [TopologicalSpace α]
  extends: ContinuousMap α β
  axioms and operations (1):
    - map_bounded' : exists C, forall x y, dist (toFun x) (toFun y) <= C

中文:
结构 有界连续函数
  参数: (α : 类型u) (β : 类型v) [拓扑空间 α]
  继承: 连续映射 α β
  公理与运算 (1 个):
    - map_bounded' : 存在 C, 对任意 x y, dist (toFun x) (toFun y) <= C
-/
structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α]
    [PseudoMetricSpace β] : Type max u v extends ContinuousMap α β where
  map_bounded' : exists C, forall x y, dist (toFun x) (toFun y) <= C

@[inherit_doc] scoped[BoundedContinuousFunction] infixr:25 " ->ᵇ " => BoundedContinuousFunction

section

/--
Definition of `BoundedContinuousMapClass` / `BoundedContinuousMapClass` 的定义

English:
class BoundedContinuousMapClass
  parameters: (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  extends: ContinuousMapClass F α β
  axioms and operations (1):
    - map_bounded((f : F)) : exists C, forall x y, dist (f x) (f y) <= C

中文:
类 BoundedContinuous映射类
  参数: (F : 类型) (α β : outParam 类型) [拓扑空间 α]
  继承: 连续映射类 F α β
  公理与运算 (1 个):
    - map_bounded((f : F)) : 存在 C, 对任意 x y, dist (f x) (f y) <= C
-/
class BoundedContinuousMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
    [PseudoMetricSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  map_bounded (f : F) : exists C, forall x y, dist (f x) (f y) <= C

end

export BoundedContinuousMapClass (map_bounded)

namespace BoundedContinuousFunction

section Basics

variable [TopologicalSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {f g : α ->ᵇ β} {x : α} {C : Real}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (α ->ᵇ β) α β where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : 函数状 (α ->ᵇ β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (α ->ᵇ β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `instBoundedContinuousMapClass` / 实例 `instBoundedContinuousMapClass`

English:
instance instBoundedContinuousMapClass
  signature: : BoundedContinuousMapClass (α ->ᵇ β) α β where
  body: f.continuous_toFun
  map_bounded f := f.map_bounded'

中文:
实例 instBoundedContinuousMapClass
  签名: : BoundedContinuous映射类 (α ->ᵇ β) α β where
  定义体: f.continuous_toFun
  map_bounded f := f.map_bounded'

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance instBoundedContinuousMapClass : BoundedContinuousMapClass (α ->ᵇ β) α β where
  map_continuous f := f.continuous_toFun
  map_bounded f := f.map_bounded'

/--
Instance `instCoeTC` / 实例 `instCoeTC`

English:
instance instCoeTC
  signature: [FunLike F α β] [BoundedContinuousMapClass F α β]
  body: ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      map_bounded' := map_bounded f }⟩

@[simp]

中文:
实例 instCoeTC
  签名: [函数状 F α β] [BoundedContinuous映射类 F α β]
  定义体: ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      map_bounded' := map_bounded f }⟩

@[simp]

Depends on / 依赖: continuous_toFun, map_bounded, map_continuous
-/
instance instCoeTC [FunLike F α β] [BoundedContinuousMapClass F α β] : CoeTC F (α ->ᵇ β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      map_bounded' := map_bounded f }⟩

@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: (f : α ->ᵇ β)
  statement: (f.toContinuousMap : α -> β) = f
  proof: rfl

中文:
定理 coe_toContinuousMap
  条件: (f : α ->ᵇ β)
  结论: (f.toContinuousMap : α -> β) = f
  证明: rfl
-/
theorem coe_toContinuousMap (f : α ->ᵇ β) : (f.toContinuousMap : α -> β) = f := rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : α ->ᵇ β)
  body: h

initialize_simps_projections BoundedContinuousFunction (toFun -> apply)

中文:
定义 Simps.apply
  签名: (h : α ->ᵇ β)
  定义体: h

initialize_simps_projections BoundedContinuousFunction (toFun -> apply)
-/
def Simps.apply (h : α ->ᵇ β) : α -> β := h

initialize_simps_projections BoundedContinuousFunction (toFun -> apply)

/--
theorem `bounded` / 定理 `bounded`

English:
theorem bounded
  given: (f : α ->ᵇ β)
  statement: exists C, forall x y : α, dist (f x) (f y) <= C
  proof: f.map_bounded'

中文:
定理 bounded
  条件: (f : α ->ᵇ β)
  结论: 存在 C, 对任意 x y : α, dist (f x) (f y) <= C
  证明: f.map_bounded'
-/
protected theorem bounded (f : α ->ᵇ β) : exists C, forall x y : α, dist (f x) (f y) <= C :=
  f.map_bounded'

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : α ->ᵇ β)
  statement: Continuous f
  proof: f.toContinuousMap.continuous

@[ext]

中文:
定理 continuous
  条件: (f : α ->ᵇ β)
  结论: 连续 f
  证明: f.toContinuousMap.continuous

@[ext]
-/
protected theorem continuous (f : α ->ᵇ β) : Continuous f :=
  f.toContinuousMap.continuous

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

@[simp]

中文:
定理 ext
  条件: (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α -> β) (h : _) (h' : _)
  proof: rfl

中文:
定理 coe_mk
  条件: (f : α -> β) (h : _) (h' : _)
  证明: rfl
-/
theorem coe_mk (f : α -> β) (h : _) (h' : _) :
    BoundedContinuousFunction.mk ⟨f, h⟩ h' = f :=
  rfl

/--
theorem `isBounded_range` / 定理 `isBounded_range`

English:
theorem isBounded_range
  given: (f : α ->ᵇ β)
  statement: IsBounded (range f)
  proof: isBounded_range_iff.2 f.bounded

中文:
定理 isBounded_range
  条件: (f : α ->ᵇ β)
  结论: IsBounded (range f)
  证明: isBounded_range_iff.2 f.bounded

Depends on / 依赖: bounded, f.bounded, isBounded_range_iff
-/
theorem isBounded_range (f : α ->ᵇ β) : IsBounded (range f) :=
  isBounded_range_iff.2 f.bounded

/--
theorem `isBounded_image` / 定理 `isBounded_image`

English:
theorem isBounded_image
  given: (f : α ->ᵇ β) (s : Set α)
  statement: IsBounded (f '' s)
  proof: f.isBounded_range.subset image_subset_range _ _

中文:
定理 isBounded_image
  条件: (f : α ->ᵇ β) (s : 集合 α)
  结论: IsBounded (f '' s)
  证明: f.isBounded_range.subset image_subset_range _ _

Depends on / 依赖: f.isBounded_range.subset, image_subset_range, isBounded_range, subset
-/
theorem isBounded_image (f : α ->ᵇ β) (s : Set α) : IsBounded (f '' s) :=
f.isBounded_range.subset image_subset_range _ _

/--
theorem `eq_of_empty` / 定理 `eq_of_empty`

English:
theorem eq_of_empty
  given: [h : IsEmpty α] (f g : α ->ᵇ β)
  statement: f = g
  proof: ext h.elim

中文:
定理 eq_of_empty
  条件: [h : 是空 α] (f g : α ->ᵇ β)
  结论: f = g
  证明: ext h.elim

Depends on / 依赖: h.elim
-/
theorem eq_of_empty [h : IsEmpty α] (f g : α ->ᵇ β) : f = g :=
ext h.elim

/--
Definition of `mkOfBound` / `mkOfBound` 的定义

English:
definition mkOfBound
  signature: (f : C(α, β)) (C : Real) (h : forall x y : α, dist (f x) (f y) <= C)
  body: ⟨f, ⟨C, h⟩⟩

@[simp]

中文:
定义 mkOfBound
  签名: (f : C(α, β)) (C : 实数) (h : 对任意 x y : α, dist (f x) (f y) <= C)
  定义体: ⟨f, ⟨C, h⟩⟩

@[simp]
-/
def mkOfBound (f : C(α, β)) (C : Real) (h : forall x y : α, dist (f x) (f y) <= C) : α ->ᵇ β :=
  ⟨f, ⟨C, h⟩⟩

@[simp]
/--
theorem `mkOfBound_coe` / 定理 `mkOfBound_coe`

English:
theorem mkOfBound_coe
  given: {f} {C} {h}
  statement: (mkOfBound f C h : α -> β) = (f : α -> β)
  proof: rfl

中文:
定理 mkOfBound_coe
  条件: {f} {C} {h}
  结论: (mkOfBound f C h : α -> β) = (f : α -> β)
  证明: rfl
-/
theorem mkOfBound_coe {f} {C} {h} : (mkOfBound f C h : α -> β) = (f : α -> β) := rfl

/--
Definition of `mkOfCompact` / `mkOfCompact` 的定义

English:
definition mkOfCompact
  signature: [CompactSpace α] (f : C(α, β))
  body: ⟨f, isBounded_range_iff.1 (isCompact_range f.continuous).isBounded⟩

@[simp]

中文:
定义 mkOfCompact
  签名: [紧空间 α] (f : C(α, β))
  定义体: ⟨f, isBounded_range_iff.1 (isCompact_range f.continuous).isBounded⟩

@[simp]

Depends on / 依赖: continuous, f.continuous, isBounded, isBounded_range_iff, isCompact_range
-/
def mkOfCompact [CompactSpace α] (f : C(α, β)) : α ->ᵇ β :=
  ⟨f, isBounded_range_iff.1 (isCompact_range f.continuous).isBounded⟩

@[simp]
/--
theorem `mkOfCompact_apply` / 定理 `mkOfCompact_apply`

English:
theorem mkOfCompact_apply
  given: [CompactSpace α] (f : C(α, β)) (a : α)
  statement: mkOfCompact f a = f a
  proof: rfl

中文:
定理 mkOfCompact_apply
  条件: [紧空间 α] (f : C(α, β)) (a : α)
  结论: mkOfCompact f a = f a
  证明: rfl
-/
theorem mkOfCompact_apply [CompactSpace α] (f : C(α, β)) (a : α) : mkOfCompact f a = f a := rfl

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions. -/
@[simps]
/--
Definition of `mkOfDiscrete` / `mkOfDiscrete` 的定义

English:
definition mkOfDiscrete
  signature: [DiscreteTopology α] (f : α -> β) (C : Real) (h : forall x y : α, dist (f x) (f y) <= C)
  body: ⟨⟨f, continuous_of_discreteTopology⟩, ⟨C, h⟩⟩

中文:
定义 mkOfDiscrete
  签名: [离散拓扑 α] (f : α -> β) (C : 实数) (h : 对任意 x y : α, dist (f x) (f y) <= C)
  定义体: ⟨⟨f, continuous_of_discreteTopology⟩, ⟨C, h⟩⟩

Depends on / 依赖: continuous_of_discreteTopology
-/
def mkOfDiscrete [DiscreteTopology α] (f : α -> β) (C : Real) (h : forall x y : α, dist (f x) (f y) <= C) :
    α ->ᵇ β :=
  ⟨⟨f, continuous_of_discreteTopology⟩, ⟨C, h⟩⟩

/--
Instance `instDist` / 实例 `instDist`

English:
instance instDist
  signature: : Dist (α ->ᵇ β)
  body: ⟨fun f g => sInf { C | 0 <= C ∧ forall x : α, dist (f x) (g x) <= C }⟩

中文:
实例 instDist
  签名: : Dist (α ->ᵇ β)
  定义体: ⟨fun f g => sInf { C | 0 <= C ∧ forall x : α, dist (f x) (g x) <= C }⟩
-/
instance instDist : Dist (α ->ᵇ β) :=
  ⟨fun f g => sInf { C | 0 <= C ∧ forall x : α, dist (f x) (g x) <= C }⟩

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  statement: dist f g = sInf { C | 0 <= C ∧ forall x : α, dist (f x) (g x) <= C }
  proof: rfl

中文:
定理 dist_eq
  结论: dist f g = sInf { C | 0 <= C ∧ 对任意 x : α, dist (f x) (g x) <= C }
  证明: rfl
-/
theorem dist_eq : dist f g = sInf { C | 0 <= C ∧ forall x : α, dist (f x) (g x) <= C } := rfl

/--
theorem `dist_set_exists` / 定理 `dist_set_exists`

English:
theorem dist_set_exists
  statement: exists C, 0 <= C ∧ forall x : α, dist (f x) (g x) <= C
  proof: by
  rcases isBounded_iff.1 (f.isBounded_range.union g.isBounded_range) with ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left _ _, fun x => (hC ?_ ?_).trans (le_max_right _ _)⟩
    <;> [left; right]
    <;> apply mem_range_self

中文:
定理 dist_set_存在
  结论: 存在 C, 0 <= C ∧ 对任意 x : α, dist (f x) (g x) <= C
  证明: by
  rcases isBounded_iff.1 (f.isBounded_range.union g.isBounded_range) with ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left _ _, fun x => (hC ?_ ?_).trans (le_max_right _ _)⟩
    <;> [left; right]
    <;> apply mem_range_self

Depends on / 依赖: f.isBounded_range.union, g.isBounded_range, isBounded_iff, isBounded_range, le_max_left, le_max_right, mem_range_self
-/
theorem dist_set_exists : exists C, 0 <= C ∧ forall x : α, dist (f x) (g x) <= C := by
  rcases isBounded_iff.1 (f.isBounded_range.union g.isBounded_range) with ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left _ _, fun x => (hC ?_ ?_).trans (le_max_right _ _)⟩
    <;> [left; right]
    <;> apply mem_range_self

/--
theorem `dist_coe_le_dist` / 定理 `dist_coe_le_dist`

English:
theorem dist_coe_le_dist
  given: (x : α)
  statement: dist (f x) (g x) <= dist f g
  proof: le_csInf dist_set_exists fun _ hb => hb.2 x

中文:
定理 dist_coe_le_dist
  条件: (x : α)
  结论: dist (f x) (g x) <= dist f g
  证明: le_csInf dist_set_exists fun _ hb => hb.2 x

Depends on / 依赖: dist_set_exists, le_csInf
-/
theorem dist_coe_le_dist (x : α) : dist (f x) (g x) <= dist f g :=
  le_csInf dist_set_exists fun _ hb => hb.2 x

/- This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superseded by the general result that the distance is nonnegative
in metric spaces. -/

set_option backward.privateInPublic true in
/--
theorem `dist_nonneg'` / 定理 `dist_nonneg'`

English:
theorem dist_nonneg'
  statement: 0 <= dist f g
  proof: le_csInf dist_set_exists fun _ => And.left

中文:
定理 dist_nonneg'
  结论: 0 <= dist f g
  证明: le_csInf dist_set_exists fun _ => And.left
-/
private theorem dist_nonneg' : 0 <= dist f g :=
  le_csInf dist_set_exists fun _ => And.left

/--
theorem `dist_le` / 定理 `dist_le`

English:
theorem dist_le
  given: (C0 : (0 : Real) <= C)
  statement: dist f g <= C ↔ forall x : α, dist (f x) (g x) <= C
  proof: ⟨fun h x => le_trans (dist_coe_le_dist x) h, fun H => csInf_le ⟨0, fun _ => And.left⟩ ⟨C0, H⟩⟩

中文:
定理 dist_le
  条件: (C0 : (0 : 实数) <= C)
  结论: dist f g <= C ↔ 对任意 x : α, dist (f x) (g x) <= C
  证明: ⟨fun h x => le_trans (dist_coe_le_dist x) h, fun H => csInf_le ⟨0, fun _ => And.left⟩ ⟨C0, H⟩⟩

Depends on / 依赖: And.left, csInf_le, dist_coe_le_dist, le_trans
-/
theorem dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ forall x : α, dist (f x) (g x) <= C :=
  ⟨fun h x => le_trans (dist_coe_le_dist x) h, fun H => csInf_le ⟨0, fun _ => And.left⟩ ⟨C0, H⟩⟩

/--
theorem `dist_le_iff_of_nonempty` / 定理 `dist_le_iff_of_nonempty`

English:
theorem dist_le_iff_of_nonempty
  given: [Nonempty α]
  statement: dist f g <= C ↔ forall x, dist (f x) (g x) <= C
  proof: ⟨fun h x => le_trans (dist_coe_le_dist x) h,
    fun w => (dist_le (le_trans dist_nonneg (w (Nonempty.some ‹_›)))).mpr w⟩

中文:
定理 dist_le_iff_of_nonempty
  条件: [非空 α]
  结论: dist f g <= C ↔ 对任意 x, dist (f x) (g x) <= C
  证明: ⟨fun h x => le_trans (dist_coe_le_dist x) h,
    fun w => (dist_le (le_trans dist_nonneg (w (Nonempty.some ‹_›)))).mpr w⟩

Depends on / 依赖: Nonempty, Nonempty.some, dist_coe_le_dist, dist_le, dist_nonneg, le_trans
-/
theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x) (g x) <= C :=
  ⟨fun h x => le_trans (dist_coe_le_dist x) h,
    fun w => (dist_le (le_trans dist_nonneg (w (Nonempty.some ‹_›)))).mpr w⟩

/--
theorem `dist_lt_of_nonempty_compact` / 定理 `dist_lt_of_nonempty_compact`

English:
theorem dist_lt_of_nonempty_compact
  statement: [Nonempty α] [CompactSpace α]
  proof: by
  have c : Continuous fun x => dist (f x) (g x) := by fun_prop
  obtain ⟨x, -, le⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty (Continuous.continuousOn c)
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr fun y => le trivial) (w x)

中文:
定理 dist_lt_of_nonempty_compact
  结论: [非空 α] [紧空间 α]
  证明: by
  have c : Continuous fun x => dist (f x) (g x) := by fun_prop
  obtain ⟨x, -, le⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty (Continuous.continuousOn c)
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr fun y => le trivial) (w x)

Depends on / 依赖: Continuous, Continuous.continuousOn, IsCompact, IsCompact.exists_isMaxOn, Set.univ_nonempty, continuousOn, dist_le_iff_of_nonempty, dist_le_iff_of_nonempty.mpr, exists_isMaxOn, fun_prop, isCompact_univ, lt_of_le_of_lt, univ_nonempty
-/
theorem dist_lt_of_nonempty_compact [Nonempty α] [CompactSpace α]
    (w : forall x : α, dist (f x) (g x) < C) : dist f g < C := by
  have c : Continuous fun x => dist (f x) (g x) := by fun_prop
  obtain ⟨x, -, le⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty (Continuous.continuousOn c)
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr fun y => le trivial) (w x)

/--
theorem `dist_lt_iff_of_compact` / 定理 `dist_lt_iff_of_compact`

English:
theorem dist_lt_iff_of_compact
  given: [CompactSpace α] (C0 : (0 : Real) < C)
  proof: by
  fconstructor
  · intro w x
    exact lt_of_le_of_lt (dist_coe_le_dist x) w
  · by_cases h : Nonempty α
    · exact dist_lt_of_nonempty_compact
    · rintro -
      convert! C0
      apply le_antisymm _ dist_nonneg'
      rw [dist_eq]
      exact csInf_le ⟨0, fun C => And.left⟩ ⟨le_rfl, fun x => False.elim (h (Nonempty.intro x))⟩

中文:
定理 dist_lt_iff_of_compact
  条件: [紧空间 α] (C0 : (0 : 实数) < C)
  证明: by
  fconstructor
  · intro w x
    exact lt_of_le_of_lt (dist_coe_le_dist x) w
  · by_cases h : Nonempty α
    · exact dist_lt_of_nonempty_compact
    · rintro -
      convert! C0
      apply le_antisymm _ dist_nonneg'
      rw [dist_eq]
      exact csInf_le ⟨0, fun C => And.left⟩ ⟨le_rfl, fun x => False.elim (h (Nonempty.intro x))⟩

Depends on / 依赖: And.left, False.elim, Nonempty, Nonempty.intro, convert, csInf_le, dist_coe_le_dist, dist_eq, dist_lt_of_nonempty_compact, dist_nonneg, fconstructor, le_antisymm, le_rfl, lt_of_le_of_lt
-/
theorem dist_lt_iff_of_compact [CompactSpace α] (C0 : (0 : Real) < C) :
    dist f g < C ↔ forall x : α, dist (f x) (g x) < C := by
  fconstructor
  · intro w x
    exact lt_of_le_of_lt (dist_coe_le_dist x) w
  · by_cases h : Nonempty α
    · exact dist_lt_of_nonempty_compact
    · rintro -
      convert! C0
      apply le_antisymm _ dist_nonneg'
      rw [dist_eq]
      exact csInf_le ⟨0, fun C => And.left⟩ ⟨le_rfl, fun x => False.elim (h (Nonempty.intro x))⟩

/--
theorem `dist_lt_iff_of_nonempty_compact` / 定理 `dist_lt_iff_of_nonempty_compact`

English:
theorem dist_lt_iff_of_nonempty_compact
  given: [Nonempty α] [CompactSpace α]
  proof: ⟨fun w x => lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

中文:
定理 dist_lt_iff_of_nonempty_compact
  条件: [非空 α] [紧空间 α]
  证明: ⟨fun w x => lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

Depends on / 依赖: dist_coe_le_dist, dist_lt_of_nonempty_compact, lt_of_le_of_lt
-/
theorem dist_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] :
    dist f g < C ↔ forall x : α, dist (f x) (g x) < C :=
  ⟨fun w x => lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instPseudoMetricSpace` / 实例 `instPseudoMetricSpace`

English:
instance instPseudoMetricSpace
  signature: : PseudoMetricSpace (α ->ᵇ β) where
  body: le_antisymm ((dist_le le_rfl).2 fun x => by simp) dist_nonneg'
  dist_comm f g := by simp [dist_eq, dist_comm]
  dist_triangle _ _ _ := (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2
    fun _ => le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _))

中文:
实例 instPseudoMetricSpace
  签名: : 伪度量空间 (α ->ᵇ β) where
  定义体: le_antisymm ((dist_le le_rfl).2 fun x => by simp) dist_nonneg'
  dist_comm f g := by simp [dist_eq, dist_comm]
  dist_triangle _ _ _ := (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2
    fun _ => le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _))

Depends on / 依赖: dist_le, dist_nonneg, le_antisymm, le_rfl
-/
instance instPseudoMetricSpace : PseudoMetricSpace (α ->ᵇ β) where
  dist_self f := le_antisymm ((dist_le le_rfl).2 fun x => by simp) dist_nonneg'
  dist_comm f g := by simp [dist_eq, dist_comm]
  dist_triangle _ _ _ := (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2
    fun _ => le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _))

/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: {β} [MetricSpace β]
  body: by
    ext x
    exact eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg)

中文:
实例 instMetricSpace
  签名: {β} [度量空间 β]
  定义体: by
    ext x
    exact eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg)

Depends on / 依赖: dist_coe_le_dist, dist_nonneg, eq_of_dist_eq_zero, le_antisymm
-/
instance instMetricSpace {β} [MetricSpace β] : MetricSpace (α ->ᵇ β) where
  eq_of_dist_eq_zero hfg := by
    ext x
    exact eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg)

/--
theorem `nndist_eq` / 定理 `nndist_eq`

English:
theorem nndist_eq
  statement: nndist f g = sInf { C | forall x : α, nndist (f x) (g x) <= C }
  proof: Subtype.ext dist_eq.trans by
    rw [val_eq_coe]; rw [coe_sInf]; rw [coe_image]
    simp_rw [mem_ofPred_eq, ← NNReal.coe_le_coe, NNReal.coe_mk, exists_prop, coe_nndist]

中文:
定理 nndist_eq
  结论: nndist f g = sInf { C | 对任意 x : α, nndist (f x) (g x) <= C }
  证明: Subtype.ext dist_eq.trans by
    rw [val_eq_coe]; rw [coe_sInf]; rw [coe_image]
    simp_rw [mem_ofPred_eq, ← NNReal.coe_le_coe, NNReal.coe_mk, exists_prop, coe_nndist]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_mk, Subtype, Subtype.ext, coe_image, coe_le_coe, coe_mk, coe_nndist, coe_sInf, dist_eq, dist_eq.trans, exists_prop, mem_ofPred_eq, simp_rw, val_eq_coe
-/
theorem nndist_eq : nndist f g = sInf { C | forall x : α, nndist (f x) (g x) <= C } :=
Subtype.ext dist_eq.trans by
    rw [val_eq_coe]; rw [coe_sInf]; rw [coe_image]
    simp_rw [mem_ofPred_eq, ← NNReal.coe_le_coe, NNReal.coe_mk, exists_prop, coe_nndist]

/--
theorem `nndist_set_exists` / 定理 `nndist_set_exists`

English:
theorem nndist_set_exists
  statement: exists C, forall x : α, nndist (f x) (g x) <= C
  proof: Subtype.exists.mpr dist_set_exists.imp fun _ ⟨ha, h⟩ => ⟨ha, h⟩

中文:
定理 nndist_set_存在
  结论: 存在 C, 对任意 x : α, nndist (f x) (g x) <= C
  证明: Subtype.exists.mpr dist_set_exists.imp fun _ ⟨ha, h⟩ => ⟨ha, h⟩

Depends on / 依赖: Subtype, Subtype.exists.mpr, dist_set_exists, dist_set_exists.imp
-/
theorem nndist_set_exists : exists C, forall x : α, nndist (f x) (g x) <= C :=
Subtype.exists.mpr dist_set_exists.imp fun _ ⟨ha, h⟩ => ⟨ha, h⟩

/--
theorem `nndist_coe_le_nndist` / 定理 `nndist_coe_le_nndist`

English:
theorem nndist_coe_le_nndist
  given: (x : α)
  statement: nndist (f x) (g x) <= nndist f g
  proof: dist_coe_le_dist x

中文:
定理 nndist_coe_le_nndist
  条件: (x : α)
  结论: nndist (f x) (g x) <= nndist f g
  证明: dist_coe_le_dist x

Depends on / 依赖: dist_coe_le_dist
-/
theorem nndist_coe_le_nndist (x : α) : nndist (f x) (g x) <= nndist f g :=
  dist_coe_le_dist x

/--
theorem `dist_zero_of_empty` / 定理 `dist_zero_of_empty`

English:
theorem dist_zero_of_empty
  given: [IsEmpty α]
  statement: dist f g = 0
  proof: by
  rw [(ext isEmptyElim : f = g)]; rw [dist_self]

中文:
定理 dist_zero_of_empty
  条件: [是空 α]
  结论: dist f g = 0
  证明: by
  rw [(ext isEmptyElim : f = g)]; rw [dist_self]

Depends on / 依赖: dist_self, isEmptyElim
-/
theorem dist_zero_of_empty [IsEmpty α] : dist f g = 0 := by
  rw [(ext isEmptyElim : f = g)]; rw [dist_self]

/--
theorem `dist_eq_iSup` / 定理 `dist_eq_iSup`

English:
theorem dist_eq_iSup
  statement: dist f g = ⨆ x : α, dist (f x) (g x)
  proof: by
  cases isEmpty_or_nonempty α
  · rw [iSup_of_empty', Real.sSup_empty, dist_zero_of_empty]
  refine (dist_le_iff_of_nonempty.mpr <| le_ciSup ?_).antisymm (ciSup_le dist_coe_le_dist)
  exact dist_set_exists.imp fun C hC => forall_mem_range.2 hC.2

中文:
定理 dist_eq_iSup
  结论: dist f g = ⨆ x : α, dist (f x) (g x)
  证明: by
  cases isEmpty_or_nonempty α
  · rw [iSup_of_empty', Real.sSup_empty, dist_zero_of_empty]
  refine (dist_le_iff_of_nonempty.mpr <| le_ciSup ?_).antisymm (ciSup_le dist_coe_le_dist)
  exact dist_set_exists.imp fun C hC => forall_mem_range.2 hC.2

Depends on / 依赖: Real.sSup_empty, antisymm, ciSup_le, dist_coe_le_dist, dist_le_iff_of_nonempty, dist_le_iff_of_nonempty.mpr, dist_set_exists, dist_set_exists.imp, dist_zero_of_empty, forall_mem_range, iSup_of_empty, isEmpty_or_nonempty, le_ciSup, sSup_empty
-/
theorem dist_eq_iSup : dist f g = ⨆ x : α, dist (f x) (g x) := by
  cases isEmpty_or_nonempty α
  · rw [iSup_of_empty', Real.sSup_empty, dist_zero_of_empty]
  refine (dist_le_iff_of_nonempty.mpr <| le_ciSup ?_).antisymm (ciSup_le dist_coe_le_dist)
  exact dist_set_exists.imp fun C hC => forall_mem_range.2 hC.2

/--
theorem `nndist_eq_iSup` / 定理 `nndist_eq_iSup`

English:
theorem nndist_eq_iSup
  statement: nndist f g = ⨆ x : α, nndist (f x) (g x)
  proof: Subtype.ext dist_eq_iSup.trans by simp_rw [val_eq_coe, coe_iSup, coe_nndist]

中文:
定理 nndist_eq_iSup
  结论: nndist f g = ⨆ x : α, nndist (f x) (g x)
  证明: Subtype.ext dist_eq_iSup.trans by simp_rw [val_eq_coe, coe_iSup, coe_nndist]

Depends on / 依赖: Subtype, Subtype.ext, coe_iSup, coe_nndist, dist_eq_iSup, dist_eq_iSup.trans, simp_rw, val_eq_coe
-/
theorem nndist_eq_iSup : nndist f g = ⨆ x : α, nndist (f x) (g x) :=
Subtype.ext dist_eq_iSup.trans by simp_rw [val_eq_coe, coe_iSup, coe_nndist]

/--
theorem `edist_eq_iSup` / 定理 `edist_eq_iSup`

English:
theorem edist_eq_iSup
  statement: edist f g = ⨆ x, edist (f x) (g x)
  proof: by
  simp_rw [edist_nndist, nndist_eq_iSup]
  refine ENNReal.coe_iSup ⟨nndist f g, ?_⟩
  rintro - ⟨x, hx, rfl⟩
  exact nndist_coe_le_nndist x

中文:
定理 edist_eq_iSup
  结论: edist f g = ⨆ x, edist (f x) (g x)
  证明: by
  simp_rw [edist_nndist, nndist_eq_iSup]
  refine ENNReal.coe_iSup ⟨nndist f g, ?_⟩
  rintro - ⟨x, hx, rfl⟩
  exact nndist_coe_le_nndist x

Depends on / 依赖: ENNReal, ENNReal.coe_iSup, coe_iSup, edist_nndist, nndist, nndist_coe_le_nndist, nndist_eq_iSup, simp_rw
-/
theorem edist_eq_iSup : edist f g = ⨆ x, edist (f x) (g x) := by
  simp_rw [edist_nndist, nndist_eq_iSup]
  refine ENNReal.coe_iSup ⟨nndist f g, ?_⟩
  rintro - ⟨x, hx, rfl⟩
  exact nndist_coe_le_nndist x

/--
theorem `tendsto_iff_tendstoUniformly` / 定理 `tendsto_iff_tendstoUniformly`

English:
theorem tendsto_iff_tendstoUniformly
  given: {ι : Type*} {F : ι -> α ->ᵇ β} {f : α ->ᵇ β} {l : Filter ι}
  proof: Iff.intro
    (fun h =>
      tendstoUniformly_iff.2 fun ε ε0 =>
        (Metric.tendsto_nhds.mp h ε ε0).mp
          (Eventually.of_forall fun n hn x =>
            lt_of_le_of_lt (dist_coe_le_dist x) (dist_comm (F n) f ▸ hn)))
    fun h =>
    Metric.tendsto_nhds.mpr fun _ ε_pos =>
      (h _ (dist_mem_uniformity <| half_pos ε_pos)).mp
        (Eventually.of_forall fun n hn =>
          lt_of_le_of_lt
            ((dist_le (half_pos ε_pos).le).mpr fun x => dist_comm (f x) (F n x) ▸ le_of_lt (hn x))
            (half_lt_self ε_pos))

中文:
定理 tendsto_iff_tendstoUniformly
  条件: {ι : 类型} {F : ι -> α ->ᵇ β} {f : α ->ᵇ β} {l : 滤子 ι}
  证明: Iff.intro
    (fun h =>
      tendstoUniformly_iff.2 fun ε ε0 =>
        (Metric.tendsto_nhds.mp h ε ε0).mp
          (Eventually.of_forall fun n hn x =>
            lt_of_le_of_lt (dist_coe_le_dist x) (dist_comm (F n) f ▸ hn)))
    fun h =>
    Metric.tendsto_nhds.mpr fun _ ε_pos =>
      (h _ (dist_mem_uniformity <| half_pos ε_pos)).mp
        (Eventually.of_forall fun n hn =>
          lt_of_le_of_lt
            ((dist_le (half_pos ε_pos).le).mpr fun x => dist_comm (f x) (F n x) ▸ le_of_lt (hn x))
            (half_lt_self ε_pos))

Depends on / 依赖: Eventually, Eventually.of_forall, Iff.intro, Metric, Metric.tendsto_nhds.mp, Metric.tendsto_nhds.mpr, dist_coe_le_dist, dist_comm, dist_le, dist_mem_uniformity, half_lt_self, half_pos, le_of_lt, lt_of_le_of_lt, of_forall, tendstoUniformly_iff, tendsto_nhds
-/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι -> α ->ᵇ β} {f : α ->ᵇ β} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l :=
  Iff.intro
    (fun h =>
      tendstoUniformly_iff.2 fun ε ε0 =>
        (Metric.tendsto_nhds.mp h ε ε0).mp
          (Eventually.of_forall fun n hn x =>
            lt_of_le_of_lt (dist_coe_le_dist x) (dist_comm (F n) f ▸ hn)))
    fun h =>
    Metric.tendsto_nhds.mpr fun _ ε_pos =>
      (h _ (dist_mem_uniformity <| half_pos ε_pos)).mp
        (Eventually.of_forall fun n hn =>
          lt_of_le_of_lt
            ((dist_le (half_pos ε_pos).le).mpr fun x => dist_comm (f x) (F n x) ▸ le_of_lt (hn x))
            (half_lt_self ε_pos))

/--
theorem `isInducing_coeFn` / 定理 `isInducing_coeFn`

English:
theorem isInducing_coeFn
  statement: IsInducing (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β)
  proof: by
  rw [isInducing_iff_nhds]
  refine fun f => eq_of_forall_le_iff fun l => ?_
  rw [← tendsto_iff_comap]; rw [← tendsto_id']; rw [tendsto_iff_tendstoUniformly]; rw [UniformFun.tendsto_iff_tendstoUniformly]
  simp [comp_def]

中文:
定理 isInducing_coeFn
  结论: 是Inducing (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β)
  证明: by
  rw [isInducing_iff_nhds]
  refine fun f => eq_of_forall_le_iff fun l => ?_
  rw [← tendsto_iff_comap]; rw [← tendsto_id']; rw [tendsto_iff_tendstoUniformly]; rw [UniformFun.tendsto_iff_tendstoUniformly]
  simp [comp_def]

Depends on / 依赖: UniformFun, UniformFun.tendsto_iff_tendstoUniformly, comp_def, eq_of_forall_le_iff, isInducing_iff_nhds, tendsto_id, tendsto_iff_comap, tendsto_iff_tendstoUniformly
-/
theorem isInducing_coeFn : IsInducing (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β) := by
  rw [isInducing_iff_nhds]
  refine fun f => eq_of_forall_le_iff fun l => ?_
  rw [← tendsto_iff_comap]; rw [← tendsto_id']; rw [tendsto_iff_tendstoUniformly]; rw [UniformFun.tendsto_iff_tendstoUniformly]
  simp [comp_def]

-- TODO: upgrade to `IsUniformEmbedding`
/--
theorem `isEmbedding_coeFn` / 定理 `isEmbedding_coeFn`

English:
theorem isEmbedding_coeFn
  statement: IsEmbedding (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β)
  proof: ⟨isInducing_coeFn, fun _ _ h => ext fun x => congr_fun h x⟩

中文:
定理 isEmbedding_coeFn
  结论: 是嵌入 (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β)
  证明: ⟨isInducing_coeFn, fun _ _ h => ext fun x => congr_fun h x⟩

Depends on / 依赖: congr_fun, isInducing_coeFn
-/
theorem isEmbedding_coeFn : IsEmbedding (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β) :=
  ⟨isInducing_coeFn, fun _ _ h => ext fun x => congr_fun h x⟩

variable (α) in
/-- Constant as a continuous bounded function. -/
@[simps! -fullyApplied]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (b : β)
  body: ⟨ContinuousMap.const α b, 0, by simp⟩

中文:
定义 const
  签名: (b : β)
  定义体: ⟨ContinuousMap.const α b, 0, by simp⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.const
-/
def const (b : β) : α ->ᵇ β :=
  ⟨ContinuousMap.const α b, 0, by simp⟩

/--
theorem `const_apply'` / 定理 `const_apply'`

English:
theorem const_apply'
  given: (a : α) (b : β)
  statement: (const α b : α -> β) a = b
  proof: rfl

中文:
定理 const_apply'
  条件: (a : α) (b : β)
  结论: (const α b : α -> β) a = b
  证明: rfl
-/
theorem const_apply' (a : α) (b : β) : (const α b : α -> β) a = b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: β] : Inhabited (α ->ᵇ β)
  body: ⟨const α default⟩

中文:
实例 [可居
  签名: β] : 可居 (α ->ᵇ β)
  定义体: ⟨const α default⟩
-/
instance [Inhabited β] : Inhabited (α ->ᵇ β) :=
  ⟨const α default⟩

/--
theorem `lipschitz_eval_const` / 定理 `lipschitz_eval_const`

English:
theorem lipschitz_eval_const
  given: (x : α)
  statement: LipschitzWith 1 fun f : α ->ᵇ β => f x
  proof: LipschitzWith.mk_one fun _ _ => dist_coe_le_dist x

@[fun_prop]

中文:
定理 lipschitz_eval_const
  条件: (x : α)
  结论: LipschitzWith 1 fun f : α ->ᵇ β => f x
  证明: LipschitzWith.mk_one fun _ _ => dist_coe_le_dist x

@[fun_prop]

Depends on / 依赖: LipschitzWith, LipschitzWith.mk_one, dist_coe_le_dist, mk_one
-/
theorem lipschitz_eval_const (x : α) : LipschitzWith 1 fun f : α ->ᵇ β => f x :=
  LipschitzWith.mk_one fun _ _ => dist_coe_le_dist x

@[fun_prop]
/--
theorem `uniformContinuous_coe` / 定理 `uniformContinuous_coe`

English:
theorem uniformContinuous_coe
  statement: @UniformContinuous (α ->ᵇ β) (α -> β) _ _ (⇑)
  proof: uniformContinuous_pi.2 fun x => (lipschitz_eval_const x).uniformContinuous

中文:
定理 uniformContinuous_coe
  结论: @一致连续 (α ->ᵇ β) (α -> β) _ _ (⇑)
  证明: uniformContinuous_pi.2 fun x => (lipschitz_eval_const x).uniformContinuous

Depends on / 依赖: lipschitz_eval_const, uniformContinuous, uniformContinuous_pi
-/
theorem uniformContinuous_coe : @UniformContinuous (α ->ᵇ β) (α -> β) _ _ (⇑) :=
  uniformContinuous_pi.2 fun x => (lipschitz_eval_const x).uniformContinuous

/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous fun (f : α ->ᵇ β) x => f x
  proof: UniformContinuous.continuous uniformContinuous_coe

中文:
定理 continuous_coe
  结论: 连续 fun (f : α ->ᵇ β) x => f x
  证明: UniformContinuous.continuous uniformContinuous_coe

Depends on / 依赖: UniformContinuous, UniformContinuous.continuous, continuous, uniformContinuous_coe
-/
theorem continuous_coe : Continuous fun (f : α ->ᵇ β) x => f x :=
  UniformContinuous.continuous uniformContinuous_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEval (α ->ᵇ β) α β
  body: continuous_prod_of_continuous_lipschitzWith _ 1
    (fun f => f.continuous) lipschitz_eval_const

中文:
实例 :
  签名: 余ntinuousEval (α ->ᵇ β) α β
  定义体: continuous_prod_of_continuous_lipschitzWith _ 1
    (fun f => f.continuous) lipschitz_eval_const

Depends on / 依赖: continuous_prod_of_continuous_lipschitzWith
-/
instance : ContinuousEval (α ->ᵇ β) α β where
  continuous_eval := continuous_prod_of_continuous_lipschitzWith _ 1
    (fun f => f.continuous) lipschitz_eval_const

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEvalConst (α ->ᵇ β) α β
  body: inferInstance

中文:
实例 :
  签名: 余ntinuousEvalConst (α ->ᵇ β) α β
  定义体: inferInstance
-/
instance : ContinuousEvalConst (α ->ᵇ β) α β := inferInstance

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace β]
  body: complete_of_cauchySeq_tendsto fun (f : Nat -> α ->ᵇ β) (hf : CauchySeq f) => by
    /- We have to show that `f n` converges to a bounded continuous function.
      For this, we prove pointwise convergence to define the limit, then check
      it is a continuous bounded function, and then check the norm convergence. -/
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have f_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist x) (b_bound n m N hn hm)
    have fx_cau : forall x, CauchySeq fun n => f n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x => cauchySeq_tendsto_of_complete (fx_cau x)
    /- `F : α → β`, `hF : ∀ (x : α), Tendsto (fun n ↦ ↑(f n) x) atTop (𝓝 (F x))`
      `F` is the desired limit function. Check that it is uniformly approximated by `f N`. -/
    have fF_bdd : forall x N, dist (f N x) (F x) <= b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hF x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => f_bdd x N n N (le_refl N) hn⟩)
    refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
    · -- Check that `F` is continuous, as a uniform limit of continuous functions
      have : TendstoUniformly (fun n x => f n x) F atTop := by
        refine Metric.tendstoUniformly_iff.2 fun ε ε0 => ?_
        refine ((tendsto_order.1 b_lim).2 ε ε0).mono fun n hn x => ?_
        rw [dist_comm]
        exact lt_of_le_of_lt (fF_bdd x n) hn
      exact this.continuous (Frequently.of_forall fun N => (f N).continuous)
    · -- Check that `F` is bounded
      rcases (f 0).bounded with ⟨C, hC⟩
      refine ⟨C + (b 0 + b 0), fun x y => ?_⟩
      calc
        dist (F x) (F y) <= dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :=
          dist_triangle4_left _ _ _ _
        _ <= C + (b 0 + b 0) := add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))
    · -- Check that `F` is close to `f N` in distance terms
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) ?_ b_lim)
      exact fun N => (dist_le (b0 _)).2 fun x => fF_bdd x N

中文:
实例 instCompleteSpace
  签名: [完备空间 β]
  定义体: complete_of_cauchySeq_tendsto fun (f : Nat -> α ->ᵇ β) (hf : CauchySeq f) => by
    /- We have to show that `f n` converges to a bounded continuous function.
      For this, we prove pointwise convergence to define the limit, then check
      it is a continuous bounded function, and then check the norm convergence. -/
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have f_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist x) (b_bound n m N hn hm)
    have fx_cau : forall x, CauchySeq fun n => f n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x => cauchySeq_tendsto_of_complete (fx_cau x)
    /- `F : α → β`, `hF : ∀ (x : α), Tendsto (fun n ↦ ↑(f n) x) atTop (𝓝 (F x))`
      `F` is the desired limit function. Check that it is uniformly approximated by `f N`. -/
    have fF_bdd : forall x N, dist (f N x) (F x) <= b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hF x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => f_bdd x N n N (le_refl N) hn⟩)
    refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
    · -- Check that `F` is continuous, as a uniform limit of continuous functions
      have : TendstoUniformly (fun n x => f n x) F atTop := by
        refine Metric.tendstoUniformly_iff.2 fun ε ε0 => ?_
        refine ((tendsto_order.1 b_lim).2 ε ε0).mono fun n hn x => ?_
        rw [dist_comm]
        exact lt_of_le_of_lt (fF_bdd x n) hn
      exact this.continuous (Frequently.of_forall fun N => (f N).continuous)
    · -- Check that `F` is bounded
      rcases (f 0).bounded with ⟨C, hC⟩
      refine ⟨C + (b 0 + b 0), fun x y => ?_⟩
      calc
        dist (F x) (F y) <= dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :=
          dist_triangle4_left _ _ _ _
        _ <= C + (b 0 + b 0) := add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))
    · -- Check that `F` is close to `f N` in distance terms
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) ?_ b_lim)
      exact fun N => (dist_le (b0 _)).2 fun x => fF_bdd x N

Depends on / 依赖: CauchySeq, complete_of_cauchySeq_tendsto
-/
instance instCompleteSpace [CompleteSpace β] : CompleteSpace (α ->ᵇ β) :=
  complete_of_cauchySeq_tendsto fun (f : Nat -> α ->ᵇ β) (hf : CauchySeq f) => by
    /- We have to show that `f n` converges to a bounded continuous function.
      For this, we prove pointwise convergence to define the limit, then check
      it is a continuous bounded function, and then check the norm convergence. -/
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have f_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist x) (b_bound n m N hn hm)
    have fx_cau : forall x, CauchySeq fun n => f n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x => cauchySeq_tendsto_of_complete (fx_cau x)
    /- `F : α → β`, `hF : ∀ (x : α), Tendsto (fun n ↦ ↑(f n) x) atTop (𝓝 (F x))`
      `F` is the desired limit function. Check that it is uniformly approximated by `f N`. -/
    have fF_bdd : forall x N, dist (f N x) (F x) <= b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hF x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => f_bdd x N n N (le_refl N) hn⟩)
    refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
    · -- Check that `F` is continuous, as a uniform limit of continuous functions
      have : TendstoUniformly (fun n x => f n x) F atTop := by
        refine Metric.tendstoUniformly_iff.2 fun ε ε0 => ?_
        refine ((tendsto_order.1 b_lim).2 ε ε0).mono fun n hn x => ?_
        rw [dist_comm]
        exact lt_of_le_of_lt (fF_bdd x n) hn
      exact this.continuous (Frequently.of_forall fun N => (f N).continuous)
    · -- Check that `F` is bounded
      rcases (f 0).bounded with ⟨C, hC⟩
      refine ⟨C + (b 0 + b 0), fun x y => ?_⟩
      calc
        dist (F x) (F y) <= dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :=
          dist_triangle4_left _ _ _ _
        _ <= C + (b 0 + b 0) := add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))
    · -- Check that `F` is close to `f N` in distance terms
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) ?_ b_lim)
      exact fun N => (dist_le (b0 _)).2 fun x => fF_bdd x N

/--
Definition of `compContinuous` / `compContinuous` 的定义

English:
definition compContinuous
  signature: {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α))
  body: f.1.comp g
  map_bounded' := f.map_bounded'.imp fun _ hC _ _ => hC _ _

@[simp]

中文:
定义 compContinuous
  签名: {δ : 类型} [拓扑空间 δ] (f : α ->ᵇ β) (g : C(δ, α))
  定义体: f.1.comp g
  map_bounded' := f.map_bounded'.imp fun _ hC _ _ => hC _ _

@[simp]
-/
def compContinuous {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α)) : δ ->ᵇ β where
  toContinuousMap := f.1.comp g
  map_bounded' := f.map_bounded'.imp fun _ hC _ _ => hC _ _

@[simp]
/--
theorem `coe_compContinuous` / 定理 `coe_compContinuous`

English:
theorem coe_compContinuous
  given: {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α))
  proof: rfl

@[simp]

中文:
定理 coe_compContinuous
  条件: {δ : 类型} [拓扑空间 δ] (f : α ->ᵇ β) (g : C(δ, α))
  证明: rfl

@[simp]
-/
theorem coe_compContinuous {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α)) :
    ⇑(f.compContinuous g) = f ∘ g := rfl

@[simp]
/--
theorem `compContinuous_apply` / 定理 `compContinuous_apply`

English:
theorem compContinuous_apply
  given: {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α)) (x : δ)
  proof: rfl

中文:
定理 compContinuous_apply
  条件: {δ : 类型} [拓扑空间 δ] (f : α ->ᵇ β) (g : C(δ, α)) (x : δ)
  证明: rfl
-/
theorem compContinuous_apply {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α)) (x : δ) :
    f.compContinuous g x = f (g x) := rfl

/--
theorem `lipschitz_compContinuous` / 定理 `lipschitz_compContinuous`

English:
theorem lipschitz_compContinuous
  given: {δ : Type*} [TopologicalSpace δ] (g : C(δ, α))
  proof: LipschitzWith.mk_one fun _ _ => (dist_le dist_nonneg).2 fun x => dist_coe_le_dist (g x)

中文:
定理 lipschitz_compContinuous
  条件: {δ : 类型} [拓扑空间 δ] (g : C(δ, α))
  证明: LipschitzWith.mk_one fun _ _ => (dist_le dist_nonneg).2 fun x => dist_coe_le_dist (g x)

Depends on / 依赖: LipschitzWith, LipschitzWith.mk_one, dist_coe_le_dist, dist_le, dist_nonneg, mk_one
-/
theorem lipschitz_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
    LipschitzWith 1 fun f : α ->ᵇ β => f.compContinuous g :=
  LipschitzWith.mk_one fun _ _ => (dist_le dist_nonneg).2 fun x => dist_coe_le_dist (g x)

/--
theorem `continuous_compContinuous` / 定理 `continuous_compContinuous`

English:
theorem continuous_compContinuous
  given: {δ : Type*} [TopologicalSpace δ] (g : C(δ, α))
  proof: (lipschitz_compContinuous g).continuous

中文:
定理 continuous_compContinuous
  条件: {δ : 类型} [拓扑空间 δ] (g : C(δ, α))
  证明: (lipschitz_compContinuous g).continuous

Depends on / 依赖: continuous, lipschitz_compContinuous
-/
theorem continuous_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
    Continuous fun f : α ->ᵇ β => f.compContinuous g :=
  (lipschitz_compContinuous g).continuous

/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : α ->ᵇ β) (s : Set α)
  body: f.compContinuous (ContinuousMap.id _).restrict s

@[simp]

中文:
定义 domRestrict
  签名: (f : α ->ᵇ β) (s : 集合 α)
  定义体: f.compContinuous (ContinuousMap.id _).restrict s

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.id, compContinuous, f.compContinuous, restrict
-/
def domRestrict (f : α ->ᵇ β) (s : Set α) : s ->ᵇ β :=
f.compContinuous (ContinuousMap.id _).restrict s

@[simp]
/--
theorem `coe_domRestrict` / 定理 `coe_domRestrict`

English:
theorem coe_domRestrict
  given: (f : α ->ᵇ β) (s : Set α)
  statement: ⇑(f.domRestrict s) = f ∘ (↑)
  proof: rfl

@[simp]

中文:
定理 coe_domRestrict
  条件: (f : α ->ᵇ β) (s : 集合 α)
  结论: ⇑(f.domRestrict s) = f ∘ (↑)
  证明: rfl

@[simp]
-/
theorem coe_domRestrict (f : α ->ᵇ β) (s : Set α) : ⇑(f.domRestrict s) = f ∘ (↑) := rfl

@[simp]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  given: (f : α ->ᵇ β) (s : Set α) (x : s)
  statement: f.domRestrict s x = f x
  proof: rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias coe_restrict := coe_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

中文:
定理 domRestrict_apply
  条件: (f : α ->ᵇ β) (s : 集合 α) (x : s)
  结论: f.domRestrict s x = f x
  证明: rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias coe_restrict := coe_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
-/
theorem domRestrict_apply (f : α ->ᵇ β) (s : Set α) (x : s) : f.domRestrict s x = f x := rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias coe_restrict := coe_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (G : β -> γ) {C : Real>=0} (H : LipschitzWith C G) (f : α ->ᵇ β)
  body: ⟨⟨fun x => G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0 * D, fun x y =>
      calc
        dist (G (f x)) (G (f y)) <= C * dist (f x) (f y) := H.dist_le_mul _ _
        _ <= max C 0 * dist (f x) (f y) := by gcongr; apply le_max_left
        _ <= max C 0 * D := by gcongr; apply hD
        ⟩⟩

@[simp]

中文:
定义 comp
  签名: (G : β -> γ) {C : 实数>=0} (H : LipschitzWith C G) (f : α ->ᵇ β)
  定义体: ⟨⟨fun x => G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0 * D, fun x y =>
      calc
        dist (G (f x)) (G (f y)) <= C * dist (f x) (f y) := H.dist_le_mul _ _
        _ <= max C 0 * dist (f x) (f y) := by gcongr; apply le_max_left
        _ <= max C 0 * D := by gcongr; apply hD
        ⟩⟩

@[simp]

Depends on / 依赖: H.continuous.comp, H.dist_le_mul, bounded, continuous, dist_le_mul, f.bounded, f.continuous, le_max_left
-/
def comp (G : β -> γ) {C : Real>=0} (H : LipschitzWith C G) (f : α ->ᵇ β) : α ->ᵇ γ :=
  ⟨⟨fun x => G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0 * D, fun x y =>
      calc
        dist (G (f x)) (G (f y)) <= C * dist (f x) (f y) := H.dist_le_mul _ _
        _ <= max C 0 * dist (f x) (f y) := by gcongr; apply le_max_left
        _ <= max C 0 * D := by gcongr; apply hD
        ⟩⟩

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (G : β -> γ) {C : Real>=0} (H : LipschitzWith C G) (f : α ->ᵇ β) (a : α)
  proof: rfl

中文:
定理 comp_apply
  条件: (G : β -> γ) {C : 实数>=0} (H : LipschitzWith C G) (f : α ->ᵇ β) (a : α)
  证明: rfl
-/
theorem comp_apply (G : β -> γ) {C : Real>=0} (H : LipschitzWith C G) (f : α ->ᵇ β) (a : α) :
    (f.comp G H) a = G (f a) := rfl

/--
theorem `lipschitz_comp` / 定理 `lipschitz_comp`

English:
theorem lipschitz_comp
  given: {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G)
  proof: LipschitzWith.of_dist_le_mul fun f g =>
    (dist_le (mul_nonneg C.2 dist_nonneg)).2 fun x =>
      calc
        dist (G (f x)) (G (g x)) <= C * dist (f x) (g x) := H.dist_le_mul _ _
        _ <= C * dist f g := by gcongr; apply dist_coe_le_dist

中文:
定理 lipschitz_comp
  条件: {G : β -> γ} {C : 实数>=0} (H : LipschitzWith C G)
  证明: LipschitzWith.of_dist_le_mul fun f g =>
    (dist_le (mul_nonneg C.2 dist_nonneg)).2 fun x =>
      calc
        dist (G (f x)) (G (g x)) <= C * dist (f x) (g x) := H.dist_le_mul _ _
        _ <= C * dist f g := by gcongr; apply dist_coe_le_dist

Depends on / 依赖: H.dist_le_mul, LipschitzWith, LipschitzWith.of_dist_le_mul, dist_coe_le_dist, dist_le, dist_le_mul, dist_nonneg, mul_nonneg, of_dist_le_mul
-/
theorem lipschitz_comp {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G) :
    LipschitzWith C (comp G H : (α ->ᵇ β) -> α ->ᵇ γ) :=
  LipschitzWith.of_dist_le_mul fun f g =>
    (dist_le (mul_nonneg C.2 dist_nonneg)).2 fun x =>
      calc
        dist (G (f x)) (G (g x)) <= C * dist (f x) (g x) := H.dist_le_mul _ _
        _ <= C * dist f g := by gcongr; apply dist_coe_le_dist

/-- The composition operator (in the target) with a Lipschitz map is uniformly continuous. -/
@[fun_prop]
/--
theorem `uniformContinuous_comp` / 定理 `uniformContinuous_comp`

English:
theorem uniformContinuous_comp
  given: {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G)
  proof: (lipschitz_comp H).uniformContinuous

中文:
定理 uniformContinuous_comp
  条件: {G : β -> γ} {C : 实数>=0} (H : LipschitzWith C G)
  证明: (lipschitz_comp H).uniformContinuous

Depends on / 依赖: lipschitz_comp, uniformContinuous
-/
theorem uniformContinuous_comp {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G) :
    UniformContinuous (comp G H : (α ->ᵇ β) -> α ->ᵇ γ) :=
  (lipschitz_comp H).uniformContinuous

/--
theorem `continuous_comp` / 定理 `continuous_comp`

English:
theorem continuous_comp
  given: {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G)
  proof: (lipschitz_comp H).continuous

中文:
定理 continuous_comp
  条件: {G : β -> γ} {C : 实数>=0} (H : LipschitzWith C G)
  证明: (lipschitz_comp H).continuous

Depends on / 依赖: continuous, lipschitz_comp
-/
theorem continuous_comp {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G) :
    Continuous (comp G H : (α ->ᵇ β) -> α ->ᵇ γ) :=
  (lipschitz_comp H).continuous

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (s : Set β) (f : α ->ᵇ β) (H : forall x, f x in s)
  body: ⟨⟨s.codRestrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩

中文:
定义 codRestrict
  签名: (s : 集合 β) (f : α ->ᵇ β) (H : 对任意 x, f x in s)
  定义体: ⟨⟨s.codRestrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩

Depends on / 依赖: bounded, codRestrict, continuous, f.bounded, f.continuous.subtype_mk, s.codRestrict, subtype_mk
-/
def codRestrict (s : Set β) (f : α ->ᵇ β) (H : forall x, f x in s) : α ->ᵇ s :=
  ⟨⟨s.codRestrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩

section Extend

variable {δ : Type*} [TopologicalSpace δ] [DiscreteTopology δ]

/-- A version of `Function.extend` for bounded continuous maps. We assume that the domain has
discrete topology, so we only need to verify boundedness. -/
nonrec def extend (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) : δ ->ᵇ β where
  toFun := extend f g h
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    rw [← isBounded_range_iff]; rw [range_extend f.injective]
    exact g.isBounded_range.union (h.isBounded_image _)

@[simp]
/--
theorem `extend_apply` / 定理 `extend_apply`

English:
theorem extend_apply
  given: (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) (x : α)
  statement: extend f g h (f x) = g x
  proof: f.injective.extend_apply _ _ _

@[simp]
nonrec theorem extend_comp (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) : extend f g h ∘ f = g :=
  extend_comp f.injective _ _

nonrec theorem extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α ->ᵇ β) (h : δ ->ᵇ β) :
    extend f g h x = h x :=
  extend_apply' _ _ _ hx

中文:
定理 extend_apply
  条件: (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) (x : α)
  结论: extend f g h (f x) = g x
  证明: f.injective.extend_apply _ _ _

@[simp]
nonrec theorem extend_comp (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) : extend f g h ∘ f = g :=
  extend_comp f.injective _ _

nonrec theorem extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α ->ᵇ β) (h : δ ->ᵇ β) :
    extend f g h x = h x :=
  extend_apply' _ _ _ hx

Depends on / 依赖: extend_apply, f.injective.extend_apply, injective
-/
theorem extend_apply (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) (x : α) : extend f g h (f x) = g x :=
  f.injective.extend_apply _ _ _

@[simp]
nonrec theorem extend_comp (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) : extend f g h ∘ f = g :=
  extend_comp f.injective _ _

nonrec theorem extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α ->ᵇ β) (h : δ ->ᵇ β) :
    extend f g h x = h x :=
  extend_apply' _ _ _ hx

/--
theorem `extend_of_empty` / 定理 `extend_of_empty`

English:
theorem extend_of_empty
  given: [IsEmpty α] (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β)
  statement: extend f g h = h
  proof: DFunLike.coe_injective Function.extend_of_isEmpty f g h

@[simp]

中文:
定理 extend_of_empty
  条件: [是空 α] (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β)
  结论: extend f g h = h
  证明: DFunLike.coe_injective Function.extend_of_isEmpty f g h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.extend_of_isEmpty, coe_injective, extend_of_isEmpty
-/
theorem extend_of_empty [IsEmpty α] (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) : extend f g h = h :=
DFunLike.coe_injective Function.extend_of_isEmpty f g h

@[simp]
/--
theorem `dist_extend_extend` / 定理 `dist_extend_extend`

English:
theorem dist_extend_extend
  given: (f : α ↪ δ) (g₁ g₂ : α ->ᵇ β) (h₁ h₂ : δ ->ᵇ β)
  proof: by
  refine le_antisymm ((dist_le <| le_max_iff.2 <| Or.inl dist_nonneg).2 fun x => ?_) (max_le ?_ ?_)
  · rcases em (exists y, f y = x) with (⟨x, rfl⟩ | hx)
    · simp only [extend_apply]
      exact (dist_coe_le_dist x).trans (le_max_left _ _)
    · simp only [extend_apply' hx]
      lift x to ((range f)ᶜ : Set δ) using hx
      calc
        dist (h₁ x) (h₂ x) = dist (h₁.domRestrict (range f)ᶜ x) (h₂.domRestrict (range f)ᶜ x) := rfl
        _ <= dist (h₁.domRestrict (range f)ᶜ) (h₂.domRestrict (range f)ᶜ) := dist_coe_le_dist x
        _ <= _ := le_max_right _ _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    rw [← extend_apply f g₁ h₁]; rw [← extend_apply f g₂ h₂]
    exact dist_coe_le_dist _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    calc
      dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) := by
        rw [extend_apply' x.coe_prop]; rw [extend_apply' x.coe_prop]
      _ <= _ := dist_coe_le_dist _

中文:
定理 dist_extend_extend
  条件: (f : α ↪ δ) (g₁ g₂ : α ->ᵇ β) (h₁ h₂ : δ ->ᵇ β)
  证明: by
  refine le_antisymm ((dist_le <| le_max_iff.2 <| Or.inl dist_nonneg).2 fun x => ?_) (max_le ?_ ?_)
  · rcases em (exists y, f y = x) with (⟨x, rfl⟩ | hx)
    · simp only [extend_apply]
      exact (dist_coe_le_dist x).trans (le_max_left _ _)
    · simp only [extend_apply' hx]
      lift x to ((range f)ᶜ : Set δ) using hx
      calc
        dist (h₁ x) (h₂ x) = dist (h₁.domRestrict (range f)ᶜ x) (h₂.domRestrict (range f)ᶜ x) := rfl
        _ <= dist (h₁.domRestrict (range f)ᶜ) (h₂.domRestrict (range f)ᶜ) := dist_coe_le_dist x
        _ <= _ := le_max_right _ _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    rw [← extend_apply f g₁ h₁]; rw [← extend_apply f g₂ h₂]
    exact dist_coe_le_dist _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    calc
      dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) := by
        rw [extend_apply' x.coe_prop]; rw [extend_apply' x.coe_prop]
      _ <= _ := dist_coe_le_dist _

Depends on / 依赖: Or.inl, dist_coe_le_dist, dist_le, dist_nonneg, domRestrict, extend_apply, le_antisymm, le_max_iff, le_max_left, max_le
-/
theorem dist_extend_extend (f : α ↪ δ) (g₁ g₂ : α ->ᵇ β) (h₁ h₂ : δ ->ᵇ β) :
    dist (g₁.extend f h₁) (g₂.extend f h₂) =
      max (dist g₁ g₂) (dist (h₁.domRestrict (range f)ᶜ) (h₂.domRestrict (range f)ᶜ)) := by
  refine le_antisymm ((dist_le <| le_max_iff.2 <| Or.inl dist_nonneg).2 fun x => ?_) (max_le ?_ ?_)
  · rcases em (exists y, f y = x) with (⟨x, rfl⟩ | hx)
    · simp only [extend_apply]
      exact (dist_coe_le_dist x).trans (le_max_left _ _)
    · simp only [extend_apply' hx]
      lift x to ((range f)ᶜ : Set δ) using hx
      calc
        dist (h₁ x) (h₂ x) = dist (h₁.domRestrict (range f)ᶜ x) (h₂.domRestrict (range f)ᶜ x) := rfl
        _ <= dist (h₁.domRestrict (range f)ᶜ) (h₂.domRestrict (range f)ᶜ) := dist_coe_le_dist x
        _ <= _ := le_max_right _ _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    rw [← extend_apply f g₁ h₁]; rw [← extend_apply f g₂ h₂]
    exact dist_coe_le_dist _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    calc
      dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) := by
        rw [extend_apply' x.coe_prop]; rw [extend_apply' x.coe_prop]
      _ <= _ := dist_coe_le_dist _

/--
theorem `isometry_extend` / 定理 `isometry_extend`

English:
theorem isometry_extend
  given: (f : α ↪ δ) (h : δ ->ᵇ β)
  statement: Isometry fun g : α ->ᵇ β => extend f g h
  proof: Isometry.of_dist_eq fun g₁ g₂ => by simp

中文:
定理 isometry_extend
  条件: (f : α ↪ δ) (h : δ ->ᵇ β)
  结论: 等距 fun g : α ->ᵇ β => extend f g h
  证明: Isometry.of_dist_eq fun g₁ g₂ => by simp

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem isometry_extend (f : α ↪ δ) (h : δ ->ᵇ β) : Isometry fun g : α ->ᵇ β => extend f g h :=
  Isometry.of_dist_eq fun g₁ g₂ => by simp

end Extend

/-- The indicator function of a clopen set, as a bounded continuous function. -/
@[simps]
/--
Definition of `indicator` / `indicator` 的定义

English:
definition indicator
  signature: (s : Set α) (hs : IsClopen s)
  body: s.indicator 1
continuous_toFun := continuous_indicator (by simp [hs]) continuous_const.continuousOn
  map_bounded' := ⟨1, fun x y => by by_cases hx : x in s <;> by_cases hy : y in s <;> simp [hx, hy]⟩

中文:
定义 indicator
  签名: (s : 集合 α) (hs : IsClopen s)
  定义体: s.indicator 1
continuous_toFun := continuous_indicator (by simp [hs]) continuous_const.continuousOn
  map_bounded' := ⟨1, fun x y => by by_cases hx : x in s <;> by_cases hy : y in s <;> simp [hx, hy]⟩

Depends on / 依赖: indicator, s.indicator
-/
noncomputable def indicator (s : Set α) (hs : IsClopen s) : BoundedContinuousFunction α Real where
  toFun := s.indicator 1
continuous_toFun := continuous_indicator (by simp [hs]) continuous_const.continuousOn
  map_bounded' := ⟨1, fun x y => by by_cases hx : x in s <;> by_cases hy : y in s <;> simp [hx, hy]⟩

end Basics

section One

variable [TopologicalSpace α] [PseudoMetricSpace β] [One β]

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (α ->ᵇ β)
  body: ⟨const α 1⟩

@[to_additive (attr := simp)]

中文:
实例 instOne
  签名: : 幺 (α ->ᵇ β)
  定义体: ⟨const α 1⟩

@[to_additive (attr := simp)]
-/
@[to_additive] instance instOne : One (α ->ᵇ β) := ⟨const α 1⟩

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : α ->ᵇ β) : α -> β) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_one
  结论: ((1 : α ->ᵇ β) : α -> β) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_one : ((1 : α ->ᵇ β) : α -> β) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `mkOfCompact_one` / 定理 `mkOfCompact_one`

English:
theorem mkOfCompact_one
  given: [CompactSpace α]
  statement: mkOfCompact (1 : C(α, β)) = 1
  proof: rfl

@[to_additive]

中文:
定理 mkOfCompact_one
  条件: [紧空间 α]
  结论: mkOfCompact (1 : C(α, β)) = 1
  证明: rfl

@[to_additive]
-/
theorem mkOfCompact_one [CompactSpace α] : mkOfCompact (1 : C(α, β)) = 1 := rfl

@[to_additive]
/--
theorem `forall_coe_one_iff_one` / 定理 `forall_coe_one_iff_one`

English:
theorem forall_coe_one_iff_one
  given: (f : α ->ᵇ β)
  statement: (forall x, f x = 1) ↔ f = 1
  proof: (@DFunLike.ext_iff _ _ _ _ f 1).symm

@[to_additive (attr := simp)]

中文:
定理 对任意_coe_one_iff_one
  条件: (f : α ->ᵇ β)
  结论: (对任意 x, f x = 1) ↔ f = 1
  证明: (@DFunLike.ext_iff _ _ _ _ f 1).symm

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
theorem forall_coe_one_iff_one (f : α ->ᵇ β) : (forall x, f x = 1) ↔ f = 1 :=
  (@DFunLike.ext_iff _ _ _ _ f 1).symm

@[to_additive (attr := simp)]
/--
theorem `one_compContinuous` / 定理 `one_compContinuous`

English:
theorem one_compContinuous
  given: [TopologicalSpace γ] (f : C(γ, α))
  statement: (1 : α ->ᵇ β).compContinuous f = 1
  proof: rfl

中文:
定理 one_compContinuous
  条件: [拓扑空间 γ] (f : C(γ, α))
  结论: (1 : α ->ᵇ β).compContinuous f = 1
  证明: rfl
-/
theorem one_compContinuous [TopologicalSpace γ] (f : C(γ, α)) : (1 : α ->ᵇ β).compContinuous f = 1 :=
  rfl

end One

section mul

variable {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul R] [BoundedMul R] [ContinuousMul R]
  body: { toFun := fun x => f x * g x
      continuous_toFun := f.continuous.mul g.continuous
      map_bounded' := mul_bounded_of_bounded_of_bounded (map_bounded f) (map_bounded g) }

@[to_additive (attr := simp)]

中文:
实例 instMul
  签名: [乘法 R] [有界乘法 R] [连续乘法 R]
  定义体: { toFun := fun x => f x * g x
      continuous_toFun := f.continuous.mul g.continuous
      map_bounded' := mul_bounded_of_bounded_of_bounded (map_bounded f) (map_bounded g) }

@[to_additive (attr := simp)]

Depends on / 依赖: continuous, continuous_toFun, f.continuous.mul, g.continuous, map_bounded, mul_bounded_of_bounded_of_bounded
-/
instance instMul [Mul R] [BoundedMul R] [ContinuousMul R] :
    Mul (α ->ᵇ R) where
  mul f g :=
    { toFun := fun x => f x * g x
      continuous_toFun := f.continuous.mul g.continuous
      map_bounded' := mul_bounded_of_bounded_of_bounded (map_bounded f) (map_bounded g) }

@[to_additive (attr := simp)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α ->ᵇ R)
  statement: ⇑(f * g) = f * g
  proof: rfl

@[to_additive]

中文:
定理 coe_mul
  条件: [乘法 R] [有界乘法 R] [连续乘法 R] (f g : α ->ᵇ R)
  结论: ⇑(f * g) = f * g
  证明: rfl

@[to_additive]
-/
theorem coe_mul [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α ->ᵇ R) : ⇑(f * g) = f * g := rfl

@[to_additive]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α ->ᵇ R) (x : α)
  proof: rfl

@[deprecated "dont use `nsmulRec` directly" (since := "2026-03-06")]

中文:
定理 mul_apply
  条件: [乘法 R] [有界乘法 R] [连续乘法 R] (f g : α ->ᵇ R) (x : α)
  证明: rfl

@[deprecated "dont use `nsmulRec` directly" (since := "2026-03-06")]
-/
theorem mul_apply [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α ->ᵇ R) (x : α) :
    (f * g) x = f x * g x := rfl

@[deprecated "dont use `nsmulRec` directly" (since := "2026-03-06")]
/--
theorem `coe_nsmulRec` / 定理 `coe_nsmulRec`

English:
theorem coe_nsmulRec
  statement: [PseudoMetricSpace β] [AddMonoid β] [BoundedAdd β] [ContinuousAdd β]

中文:
定理 coe_nsmulRec
  结论: [伪度量空间 β] [加法幺半群 β] [有界加法 β] [连续加法 β]
-/
theorem coe_nsmulRec [PseudoMetricSpace β] [AddMonoid β] [BoundedAdd β] [ContinuousAdd β]
    (f : α ->ᵇ β) : forall n, ⇑(nsmulRec n f) = n • ⇑f
  | 0 => by rw [nsmulRec, zero_smul, coe_zero]
  | n + 1 => by rw [nsmulRec, succ_nsmul, coe_add, coe_nsmulRec _ n]

@[to_additive]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: [Monoid R] [BoundedMul R] [ContinuousMul R]
  body: { toFun := fun x => (f x) ^ n
      continuous_toFun := f.continuous.pow n
      map_bounded' := by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp isBounded_pow (isBounded_range f) n
        exact ⟨C, fun x y => hC (by simp) (by simp)⟩ }

@[to_additive]

中文:
实例 instPow
  签名: [幺半群 R] [有界乘法 R] [连续乘法 R]
  定义体: { toFun := fun x => (f x) ^ n
      continuous_toFun := f.continuous.pow n
      map_bounded' := by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp isBounded_pow (isBounded_range f) n
        exact ⟨C, fun x y => hC (by simp) (by simp)⟩ }

@[to_additive]

Depends on / 依赖: Metric, Metric.isBounded_iff.mp, continuous, continuous_toFun, f.continuous.pow, isBounded_iff, isBounded_pow, isBounded_range, map_bounded
-/
instance instPow [Monoid R] [BoundedMul R] [ContinuousMul R] : Pow (α ->ᵇ R) Nat where
  pow f n :=
    { toFun := fun x => (f x) ^ n
      continuous_toFun := f.continuous.pow n
      map_bounded' := by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp isBounded_pow (isBounded_range f) n
        exact ⟨C, fun x y => hC (by simp) (by simp)⟩ }

@[to_additive]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: [Monoid R] [BoundedMul R] [ContinuousMul R] (n : Nat) (f : α ->ᵇ R)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_pow
  条件: [幺半群 R] [有界乘法 R] [连续乘法 R] (n : 自然数) (f : α ->ᵇ R)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_pow [Monoid R] [BoundedMul R] [ContinuousMul R] (n : Nat) (f : α ->ᵇ R) :
    ⇑(f ^ n) = (⇑f) ^ n := rfl

@[to_additive (attr := simp)]
/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: [Monoid R] [BoundedMul R] [ContinuousMul R] (n : Nat) (f : α ->ᵇ R) (x : α)
  proof: rfl

@[to_additive]

中文:
定理 pow_apply
  条件: [幺半群 R] [有界乘法 R] [连续乘法 R] (n : 自然数) (f : α ->ᵇ R) (x : α)
  证明: rfl

@[to_additive]
-/
theorem pow_apply [Monoid R] [BoundedMul R] [ContinuousMul R] (n : Nat) (f : α ->ᵇ R) (x : α) :
    (f ^ n) x = f x ^ n := rfl

@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid R] [BoundedMul R] [ContinuousMul R]
  body: fast_instance%
  Injective.monoid _ DFunLike.coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 instMonoid
  签名: [幺半群 R] [有界乘法 R] [连续乘法 R]
  定义体: fast_instance%
  Injective.monoid _ DFunLike.coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance instMonoid [Monoid R] [BoundedMul R] [ContinuousMul R] :
    Monoid (α ->ᵇ R) := fast_instance%
  Injective.monoid _ DFunLike.coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid R] [BoundedMul R] [ContinuousMul R]
  body: fast_instance%
  Injective.commMonoid _ DFunLike.coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instCommMonoid
  签名: [交换幺半群 R] [有界乘法 R] [连续乘法 R]
  定义体: fast_instance%
  Injective.commMonoid _ DFunLike.coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: fast_instance
-/
instance instCommMonoid [CommMonoid R] [BoundedMul R] [ContinuousMul R] :
    CommMonoid (α ->ᵇ R) := fast_instance%
  Injective.commMonoid _ DFunLike.coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Coercion of a `BoundedContinuousFunction` is a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps) /-- Coercion of a `BoundedContinuousFunction` is an `AddMonoidHom`.
Similar to `AddMonoidHom.coeFn`. -/]
/--
Definition of `coeFnMonoidHom` / `coeFnMonoidHom` 的定义

English:
definition coeFnMonoidHom
  signature: [Monoid R] [BoundedMul R] [ContinuousMul R]
  body: (⇑)
  map_one' := coe_one
  map_mul' := coe_mul

中文:
定义 coeFnMonoidHom
  签名: [幺半群 R] [有界乘法 R] [连续乘法 R]
  定义体: (⇑)
  map_one' := coe_one
  map_mul' := coe_mul
-/
def coeFnMonoidHom [Monoid R] [BoundedMul R] [ContinuousMul R] : (α ->ᵇ R) ->* α -> R where
  toFun := (⇑)
  map_one' := coe_one
  map_mul' := coe_mul

variable (α R) in
/-- The multiplicative map forgetting that a bounded continuous function is bounded. -/
@[to_additive (attr := simps) /-- The additive map forgetting that a bounded continuous
function is bounded.-/]
/--
Definition of `toContinuousMapMonoidHom` / `toContinuousMapMonoidHom` 的定义

English:
definition toContinuousMapMonoidHom
  signature: [Monoid R] [BoundedMul R] [ContinuousMul R]
  body: toContinuousMap
  map_one' := rfl
  map_mul' := by
    intros
    ext
    simp

@[to_additive (attr := simp)]

中文:
定义 toContinuousMapMonoidHom
  签名: [幺半群 R] [有界乘法 R] [连续乘法 R]
  定义体: toContinuousMap
  map_one' := rfl
  map_mul' := by
    intros
    ext
    simp

@[to_additive (attr := simp)]

Depends on / 依赖: toContinuousMap
-/
def toContinuousMapMonoidHom [Monoid R] [BoundedMul R] [ContinuousMul R] : (α ->ᵇ R) ->* C(α, R) where
  toFun := toContinuousMap
  map_one' := rfl
  map_mul' := by
    intros
    ext
    simp

@[to_additive (attr := simp)]
/--
lemma `coe_prod` / 引理 `coe_prod`

English:
lemma coe_prod
  statement: {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [ContinuousMul R]
  proof: map_prod coeFnMonoidHom f s

@[to_additive]

中文:
引理 coe_prod
  结论: {ι : 类型} (s : 有限集 ι) [交换幺半群 R] [有界乘法 R] [连续乘法 R]
  证明: map_prod coeFnMonoidHom f s

@[to_additive]

Depends on / 依赖: coeFnMonoidHom, map_prod
-/
lemma coe_prod {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [ContinuousMul R]
    (f : ι -> α ->ᵇ R) :
    ⇑(∏ i in s, f i) = ∏ i in s, ⇑(f i) := map_prod coeFnMonoidHom f s

@[to_additive]
/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  statement: {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [ContinuousMul R]
  proof: by simp

@[to_additive]

中文:
引理 prod_apply
  结论: {ι : 类型} (s : 有限集 ι) [交换幺半群 R] [有界乘法 R] [连续乘法 R]
  证明: by simp

@[to_additive]
-/
lemma prod_apply {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [ContinuousMul R]
    (f : ι -> α ->ᵇ R) (a : α) :
    (∏ i in s, f i) a = ∏ i in s, f i a := by simp

@[to_additive]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [MulOneClass R] [BoundedMul R] [ContinuousMul R]
  body: fast_instance% DFunLike.coe_injective.mulOneClass _ coe_one coe_mul

中文:
实例 instMulOneClass
  签名: [MulOne类 R] [有界乘法 R] [连续乘法 R]
  定义体: fast_instance% DFunLike.coe_injective.mulOneClass _ coe_one coe_mul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulOneClass, coe_injective, coe_mul, coe_one, fast_instance, mulOneClass
-/
instance instMulOneClass [MulOneClass R] [BoundedMul R] [ContinuousMul R] : MulOneClass (α ->ᵇ R) :=
  fast_instance% DFunLike.coe_injective.mulOneClass _ coe_one coe_mul

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological monoids, as a
`MonoidHom`. Similar to `MonoidHom.compLeftContinuous`. -/
@[to_additive (attr := simps)
/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological `AddMonoid`s,
as a `AddMonoidHom`. Similar to `AddMonoidHom.compLeftContinuous`. -/]
/--
Definition of `_root_.MonoidHom.compLeftContinuousBounded` / `_root_.MonoidHom.compLeftContinuousBounded` 的定义

English:
definition _root_.MonoidHom.compLeftContinuousBounded
  signature: (α : Type*)
  body: f.comp g hg
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

中文:
定义 _root_.幺半群态射.compLeftContinuousBounded
  签名: (α : 类型)
  定义体: f.comp g hg
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _
-/
protected def _root_.MonoidHom.compLeftContinuousBounded (α : Type*)
    [TopologicalSpace α] [PseudoMetricSpace β] [Monoid β] [BoundedMul β] [ContinuousMul β]
    [PseudoMetricSpace γ] [Monoid γ] [BoundedMul γ] [ContinuousMul γ]
    (g : β ->* γ) {C : NNReal} (hg : LipschitzWith C g) :
    (α ->ᵇ β) ->* (α ->ᵇ γ) where
  toFun f := f.comp g hg
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

end mul

section add

variable [TopologicalSpace α] [PseudoMetricSpace β]
variable {C : Real}

@[simp]
/--
theorem `mkOfCompact_add` / 定理 `mkOfCompact_add`

English:
theorem mkOfCompact_add
  given: [CompactSpace α] [Add β] [BoundedAdd β] [ContinuousAdd β] (f g : C(α, β))
  proof: rfl

中文:
定理 mkOfCompact_add
  条件: [紧空间 α] [加法 β] [有界加法 β] [连续加法 β] (f g : C(α, β))
  证明: rfl
-/
theorem mkOfCompact_add [CompactSpace α] [Add β] [BoundedAdd β] [ContinuousAdd β] (f g : C(α, β)) :
    mkOfCompact (f + g) = mkOfCompact f + mkOfCompact g := rfl

/--
theorem `add_compContinuous` / 定理 `add_compContinuous`

English:
theorem add_compContinuous
  statement: [Add β] [BoundedAdd β] [ContinuousAdd β] [TopologicalSpace γ]
  proof: rfl

中文:
定理 add_compContinuous
  结论: [加法 β] [有界加法 β] [连续加法 β] [拓扑空间 γ]
  证明: rfl
-/
theorem add_compContinuous [Add β] [BoundedAdd β] [ContinuousAdd β] [TopologicalSpace γ]
    (f g : α ->ᵇ β) (h : C(γ, α)) :
    (g + f).compContinuous h = g.compContinuous h + f.compContinuous h := rfl

end add

section LipschitzAdd

/- In this section, if `β` is an `AddMonoid` whose addition operation is Lipschitz, then we show
that the space of bounded continuous functions from `α` to `β` inherits a topological `AddMonoid`
structure, by using pointwise operations and checking that they are compatible with the uniform
distance.

Implementation note: The material in this section could have been written for `LipschitzMul`
and transported by `@[to_additive]`. We choose not to do this because this causes a few lemma
names (for example, `coe_mul`) to conflict with later lemma names for normed rings; this is only a
trivial inconvenience, but in any case there are no obvious applications of the multiplicative
version. -/

variable [TopologicalSpace α] [PseudoMetricSpace β] [AddMonoid β] [LipschitzAdd β]
variable (f g : α ->ᵇ β) {x : α} {C : Real}

/--
Instance `instLipschitzAdd` / 实例 `instLipschitzAdd`

English:
instance instLipschitzAdd
  signature: : LipschitzAdd (α ->ᵇ β) where
  body: ⟨LipschitzAdd.C β, by
      have C_nonneg := (LipschitzAdd.C β).coe_nonneg
      rw [lipschitzWith_iff_dist_le_mul]
      rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      rw [dist_le (mul_nonneg C_nonneg dist_nonneg)]
      intro x
      refine le_trans (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) ?_
      gcongr
      apply max_le_max <;> exact dist_coe_le_dist x⟩

中文:
实例 instLipschitzAdd
  签名: : Lipschitz加法 (α ->ᵇ β) where
  定义体: ⟨LipschitzAdd.C β, by
      have C_nonneg := (LipschitzAdd.C β).coe_nonneg
      rw [lipschitzWith_iff_dist_le_mul]
      rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      rw [dist_le (mul_nonneg C_nonneg dist_nonneg)]
      intro x
      refine le_trans (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) ?_
      gcongr
      apply max_le_max <;> exact dist_coe_le_dist x⟩

Depends on / 依赖: C_nonneg, LipschitzAdd, LipschitzAdd.C, coe_nonneg, dist_coe_le_dist, dist_le, dist_nonneg, le_trans, lipschitzWith_iff_dist_le_mul, lipschitz_with_lipschitz_const_add, max_le_max, mul_nonneg
-/
instance instLipschitzAdd : LipschitzAdd (α ->ᵇ β) where
  lipschitz_add :=
    ⟨LipschitzAdd.C β, by
      have C_nonneg := (LipschitzAdd.C β).coe_nonneg
      rw [lipschitzWith_iff_dist_le_mul]
      rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      rw [dist_le (mul_nonneg C_nonneg dist_nonneg)]
      intro x
      refine le_trans (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) ?_
      gcongr
      apply max_le_max <;> exact dist_coe_le_dist x⟩

end LipschitzAdd

section sub

variable [TopologicalSpace α]
variable {R : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R] [ContinuousSub R]
variable (f g : α ->ᵇ R)

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (α ->ᵇ R) where
  body: { toFun := fun x => (f x - g x),
      map_bounded' := sub_bounded_of_bounded_of_bounded f.map_bounded' g.map_bounded' }

中文:
实例 instSub
  签名: : 减法 (α ->ᵇ R) where
  定义体: { toFun := fun x => (f x - g x),
      map_bounded' := sub_bounded_of_bounded_of_bounded f.map_bounded' g.map_bounded' }

Depends on / 依赖: f.map_bounded, g.map_bounded, map_bounded, sub_bounded_of_bounded_of_bounded
-/
instance instSub : Sub (α ->ᵇ R) where
  sub f g :=
    { toFun := fun x => (f x - g x),
      map_bounded' := sub_bounded_of_bounded_of_bounded f.map_bounded' g.map_bounded' }

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: {x : α}
  statement: (f - g) x = f x - g x
  proof: rfl

@[simp]

中文:
定理 sub_apply
  条件: {x : α}
  结论: (f - g) x = f x - g x
  证明: rfl

@[simp]
-/
theorem sub_apply {x : α} : (f - g) x = f x - g x := rfl

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ⇑(f - g) = f - g
  proof: rfl

中文:
定理 coe_sub
  结论: ⇑(f - g) = f - g
  证明: rfl
-/
theorem coe_sub : ⇑(f - g) = f - g := rfl

end sub

section casts

variable [TopologicalSpace α] {β : Type*} [PseudoMetricSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NatCast
  signature: β] : NatCast (α ->ᵇ β)
  body: ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp]

中文:
实例 [自然数嵌入
  签名: β] : 自然数嵌入 (α ->ᵇ β)
  定义体: ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.const
-/
instance [NatCast β] : NatCast (α ->ᵇ β) := ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp]
/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: [NatCast β] (n : Nat) (x : α)
  statement: (n : α ->ᵇ β) x = n
  proof: rfl

中文:
定理 natCast_apply
  条件: [自然数嵌入 β] (n : 自然数) (x : α)
  结论: (n : α ->ᵇ β) x = n
  证明: rfl
-/
theorem natCast_apply [NatCast β] (n : Nat) (x : α) : (n : α ->ᵇ β) x = n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IntCast
  signature: β] : IntCast (α ->ᵇ β)
  body: ⟨fun m => BoundedContinuousFunction.const _ m⟩

@[simp]

中文:
实例 [整数嵌入
  签名: β] : 整数嵌入 (α ->ᵇ β)
  定义体: ⟨fun m => BoundedContinuousFunction.const _ m⟩

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.const
-/
instance [IntCast β] : IntCast (α ->ᵇ β) := ⟨fun m => BoundedContinuousFunction.const _ m⟩

@[simp]
/--
theorem `intCast_apply` / 定理 `intCast_apply`

English:
theorem intCast_apply
  given: [IntCast β] (m : Int) (x : α)
  statement: (m : α ->ᵇ β) x = m
  proof: rfl

中文:
定理 intCast_apply
  条件: [整数嵌入 β] (m : 整数) (x : α)
  结论: (m : α ->ᵇ β) x = m
  证明: rfl
-/
theorem intCast_apply [IntCast β] (m : Int) (x : α) : (m : α ->ᵇ β) x = m := rfl

end casts

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]
  body: fast_instance%
  Injective.semiring _ DFunLike.coe_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

中文:
实例 instSemiring
  签名: {R : 类型} [拓扑空间 α] [伪度量空间 R]
  定义体: fast_instance%
  Injective.semiring _ DFunLike.coe_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

Depends on / 依赖: fast_instance
-/
instance instSemiring {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]
    [Semiring R] [BoundedMul R] [ContinuousMul R] [BoundedAdd R] [ContinuousAdd R] :
    Semiring (α ->ᵇ R) := fast_instance%
  Injective.semiring _ DFunLike.coe_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

section IsBoundedSMul

/-!
### `IsBoundedSMul` (in particular, topological module) structure

In this section, if `β` is a metric space and a `𝕜`-module whose addition and scalar multiplication
are compatible with the metric structure, then we show that the space of bounded continuous
functions from `α` to `β` inherits a so-called `IsBoundedSMul` structure (in particular, a
`ContinuousMul` structure, which is the mathlib formulation of being a topological module), by
using pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [PseudoMetricSpace β]

section SMul

variable [Zero 𝕜] [Zero β] [SMul 𝕜 β] [IsBoundedSMul 𝕜 β]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul 𝕜 (α ->ᵇ β) where
  body: { toContinuousMap := c • f.toContinuousMap
      map_bounded' :=
        let ⟨b, hb⟩ := f.bounded
        ⟨dist c 0 * b, fun x y => by
          refine (dist_smul_pair c (f x) (f y)).trans ?_
          gcongr
          apply hb⟩ }

@[simp]

中文:
实例 instSMul
  签名: : 标量乘法 𝕜 (α ->ᵇ β) where
  定义体: { toContinuousMap := c • f.toContinuousMap
      map_bounded' :=
        let ⟨b, hb⟩ := f.bounded
        ⟨dist c 0 * b, fun x y => by
          refine (dist_smul_pair c (f x) (f y)).trans ?_
          gcongr
          apply hb⟩ }

@[simp]

Depends on / 依赖: bounded, dist_smul_pair, f.bounded, f.toContinuousMap, map_bounded, toContinuousMap
-/
instance instSMul : SMul 𝕜 (α ->ᵇ β) where
  smul c f :=
    { toContinuousMap := c • f.toContinuousMap
      map_bounded' :=
        let ⟨b, hb⟩ := f.bounded
        ⟨dist c 0 * b, fun x y => by
          refine (dist_smul_pair c (f x) (f y)).trans ?_
          gcongr
          apply hb⟩ }

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (c : 𝕜) (f : α ->ᵇ β)
  statement: ⇑(c • f) = fun x => c • f x
  proof: rfl

中文:
定理 coe_smul
  条件: (c : 𝕜) (f : α ->ᵇ β)
  结论: ⇑(c • f) = fun x => c • f x
  证明: rfl
-/
theorem coe_smul (c : 𝕜) (f : α ->ᵇ β) : ⇑(c • f) = fun x => c • f x := rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (c : 𝕜) (f : α ->ᵇ β) (x : α)
  statement: (c • f) x = c • f x
  proof: rfl

中文:
定理 smul_apply
  条件: (c : 𝕜) (f : α ->ᵇ β) (x : α)
  结论: (c • f) x = c • f x
  证明: rfl
-/
theorem smul_apply (c : 𝕜) (f : α ->ᵇ β) (x : α) : (c • f) x = c • f x := rfl

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
  body: ext fun _ => smul_assoc ..

中文:
实例 instIsScalarTower
  签名: {𝕜' : 类型} [伪度量空间 𝕜'] [零 𝕜'] [标量乘法 𝕜' β]
  定义体: ext fun _ => smul_assoc ..

Depends on / 依赖: smul_assoc
-/
instance instIsScalarTower {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
    [IsBoundedSMul 𝕜' β] [SMul 𝕜' 𝕜] [IsScalarTower 𝕜' 𝕜 β] :
    IsScalarTower 𝕜' 𝕜 (α ->ᵇ β) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc ..

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
  body: ext fun _ => smul_comm ..

中文:
实例 instSMulCommClass
  签名: {𝕜' : 类型} [伪度量空间 𝕜'] [零 𝕜'] [标量乘法 𝕜' β]
  定义体: ext fun _ => smul_comm ..

Depends on / 依赖: smul_comm
-/
instance instSMulCommClass {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
    [IsBoundedSMul 𝕜' β] [SMulCommClass 𝕜' 𝕜 β] :
    SMulCommClass 𝕜' 𝕜 (α ->ᵇ β) where
  smul_comm _ _ _ := ext fun _ => smul_comm ..

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul 𝕜ᵐᵒᵖ β] [IsCentralScalar 𝕜 β]
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 instIsCentralScalar
  签名: [标量乘法 𝕜ᵐᵒᵖ β] [中心标量 𝕜 β]
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ β] [IsCentralScalar 𝕜 β] : IsCentralScalar 𝕜 (α ->ᵇ β) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
Instance `instIsBoundedSMul` / 实例 `instIsBoundedSMul`

English:
instance instIsBoundedSMul
  signature: : IsBoundedSMul 𝕜 (α ->ᵇ β) where
  body: by
    rw [dist_le (mul_nonneg dist_nonneg dist_nonneg)]
    intro x
    refine (dist_smul_pair c (f₁ x) (f₂ x)).trans ?_
    gcongr
    apply dist_coe_le_dist
  dist_pair_smul' c₁ c₂ f := by
    rw [dist_le (by positivity)]
    intro x
    refine (dist_pair_smul c₁ c₂ (f x)).trans ?_
    gcongr
    apply dist_coe_le_dist (g := 0)

中文:
实例 instIsBoundedSMul
  签名: : 是BoundedSMul 𝕜 (α ->ᵇ β) where
  定义体: by
    rw [dist_le (mul_nonneg dist_nonneg dist_nonneg)]
    intro x
    refine (dist_smul_pair c (f₁ x) (f₂ x)).trans ?_
    gcongr
    apply dist_coe_le_dist
  dist_pair_smul' c₁ c₂ f := by
    rw [dist_le (by positivity)]
    intro x
    refine (dist_pair_smul c₁ c₂ (f x)).trans ?_
    gcongr
    apply dist_coe_le_dist (g := 0)

Depends on / 依赖: dist_coe_le_dist, dist_le, dist_nonneg, dist_pair_smul, dist_smul_pair, mul_nonneg
-/
instance instIsBoundedSMul : IsBoundedSMul 𝕜 (α ->ᵇ β) where
  dist_smul_pair' c f₁ f₂ := by
    rw [dist_le (mul_nonneg dist_nonneg dist_nonneg)]
    intro x
    refine (dist_smul_pair c (f₁ x) (f₂ x)).trans ?_
    gcongr
    apply dist_coe_le_dist
  dist_pair_smul' c₁ c₂ f := by
    rw [dist_le (by positivity)]
    intro x
    refine (dist_pair_smul c₁ c₂ (f x)).trans ?_
    gcongr
    apply dist_coe_le_dist (g := 0)

end SMul

section MulAction

variable [MonoidWithZero 𝕜] [Zero β] [MulAction 𝕜 β] [IsBoundedSMul 𝕜 β]

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: : MulAction 𝕜 (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.mulAction _ coe_smul

中文:
实例 instMulAction
  签名: : 乘法作用 𝕜 (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.mulAction _ coe_smul

Depends on / 依赖: fast_instance
-/
instance instMulAction : MulAction 𝕜 (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.mulAction _ coe_smul

end MulAction

section DistribMulAction

variable [MonoidWithZero 𝕜] [AddMonoid β] [DistribMulAction 𝕜 β] [IsBoundedSMul 𝕜 β]
variable [BoundedAdd β] [ContinuousAdd β]

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: : DistribMulAction 𝕜 (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

中文:
实例 instDistribMulAction
  签名: : 分配乘法作用 𝕜 (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

Depends on / 依赖: fast_instance
-/
instance instDistribMulAction : DistribMulAction 𝕜 (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

end DistribMulAction

section Module

variable [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
variable {f g : α ->ᵇ β} {x : α} {C : Real}
variable [BoundedAdd β] [ContinuousAdd β]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module 𝕜 (α ->ᵇ β)
  body: fast_instance%
  DFunLike.coe_injective.module _ ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

中文:
实例 instModule
  签名: : 模 𝕜 (α ->ᵇ β)
  定义体: fast_instance%
  DFunLike.coe_injective.module _ ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

Depends on / 依赖: fast_instance
-/
instance instModule : Module 𝕜 (α ->ᵇ β) := fast_instance%
  DFunLike.coe_injective.module _ ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

variable (𝕜)

/-- The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`. -/
@[simps]
/--
Definition of `evalCLM` / `evalCLM` 的定义

English:
definition evalCLM
  signature: (x : α)
  body: f x
  map_add' _ _ := add_apply _ _ _
  map_smul' _ _ := smul_apply _ _ _

中文:
定义 evalCLM
  签名: (x : α)
  定义体: f x
  map_add' _ _ := add_apply _ _ _
  map_smul' _ _ := smul_apply _ _ _
-/
def evalCLM (x : α) : (α ->ᵇ β) ->L[𝕜] β where
  toFun f := f x
  map_add' _ _ := add_apply _ _ _
  map_smul' _ _ := smul_apply _ _ _

variable (α β)

/-- The linear map forgetting that a bounded continuous function is bounded. -/
@[simps]
/--
Definition of `toContinuousMapLinearMap` / `toContinuousMapLinearMap` 的定义

English:
definition toContinuousMapLinearMap
  signature: : (α ->ᵇ β) ->ₗ[𝕜] C(α, β) where
  body: toContinuousMap
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 toContinuousMapLinearMap
  签名: : (α ->ᵇ β) ->ₗ[𝕜] C(α, β) where
  定义体: toContinuousMap
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: toContinuousMap
-/
def toContinuousMapLinearMap : (α ->ᵇ β) ->ₗ[𝕜] C(α, β) where
  toFun := toContinuousMap
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

end Module

end IsBoundedSMul

/--
theorem `NNReal.upper_bound` / 定理 `NNReal.upper_bound`

English:
theorem NNReal.upper_bound
  given: {α : Type*} [TopologicalSpace α] (f : α ->ᵇ Real>=0) (x : α)
  proof: by
  have key : nndist (f x) ((0 : α ->ᵇ Real>=0) x) <= nndist f 0 := @dist_coe_le_dist α Real>=0 _ _ f 0 x
  simp only [coe_zero, Pi.zero_apply] at key
  rwa [NNReal.nndist_zero_eq_val' (f x)] at key

中文:
定理 非负实数.upper_bound
  条件: {α : 类型} [拓扑空间 α] (f : α ->ᵇ 实数>=0) (x : α)
  证明: by
  have key : nndist (f x) ((0 : α ->ᵇ Real>=0) x) <= nndist f 0 := @dist_coe_le_dist α Real>=0 _ _ f 0 x
  simp only [coe_zero, Pi.zero_apply] at key
  rwa [NNReal.nndist_zero_eq_val' (f x)] at key

Depends on / 依赖: NNReal, NNReal.nndist_zero_eq_val, Pi.zero_apply, coe_zero, dist_coe_le_dist, nndist, nndist_zero_eq_val, zero_apply
-/
theorem NNReal.upper_bound {α : Type*} [TopologicalSpace α] (f : α ->ᵇ Real>=0) (x : α) :
    f x <= nndist f 0 := by
  have key : nndist (f x) ((0 : α ->ᵇ Real>=0) x) <= nndist f 0 := @dist_coe_le_dist α Real>=0 _ _ f 0 x
  simp only [coe_zero, Pi.zero_apply] at key
  rwa [NNReal.nndist_zero_eq_val' (f x)] at key

end BoundedContinuousFunction
