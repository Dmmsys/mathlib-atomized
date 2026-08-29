/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Filter.Bases.Finite
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological groups

This file defines the following typeclasses:

* `IsTopologicalGroup`, `IsTopologicalAddGroup`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `ContinuousSub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `ContinuousSub` from `IsTopologicalGroup` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `Homeomorph` versions of several `Equiv`s: `Homeomorph.mulLeft`,
`Homeomorph.mulRight`, `Homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

@[expose] public section

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

/--
lemma `Set.isClosed_centralizer` / 引理 `Set.isClosed_centralizer`

English:
lemma Set.isClosed_centralizer
  statement: {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
  proof: by
  rw [centralizer]; rw [ofPred_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
refine isClosed_imp (by simp) isClosed_eq ?_ ?_
  all_goals fun_prop

中文:
引理 集合.isClosed_centralizer
  结论: {M : 类型} (s : 集合 M) [乘法 M] [拓扑空间 M]
  证明: by
  rw [centralizer]; rw [ofPred_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
refine isClosed_imp (by simp) isClosed_eq ?_ ?_
  all_goals fun_prop

Depends on / 依赖: all_goals, centralizer, fun_prop, isClosed_eq, isClosed_imp, isClosed_sInter, ofPred_forall
-/
lemma Set.isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer]; rw [ofPred_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
refine isClosed_imp (by simp) isClosed_eq ?_ ?_
  all_goals fun_prop

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Group G] [SeparatelyContinuousMul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive /-- Addition from the left in a topological additive group as a homeomorphism. -/]
/--
Definition of `Homeomorph.mulLeft` / `Homeomorph.mulLeft` 的定义

English:
definition Homeomorph.mulLeft
  signature: (a : G)
  body: { Equiv.mulLeft a with }

@[to_additive (attr := simp)]

中文:
定义 同胚.mulLeft
  签名: (a : G)
  定义体: { Equiv.mulLeft a with }

@[to_additive (attr := simp)]
-/
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with }

@[to_additive (attr := simp)]
/--
theorem `Homeomorph.coe_mulLeft` / 定理 `Homeomorph.coe_mulLeft`

English:
theorem Homeomorph.coe_mulLeft
  given: (a : G)
  statement: ⇑(Homeomorph.mulLeft a) = (a * ·)
  proof: rfl

@[to_additive]

中文:
定理 同胚.coe_mulLeft
  条件: (a : G)
  结论: ⇑(同胚.mulLeft a) = (a * ·)
  证明: rfl

@[to_additive]
-/
theorem Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (a * ·) :=
  rfl

@[to_additive]
/--
theorem `Homeomorph.mulLeft_symm` / 定理 `Homeomorph.mulLeft_symm`

English:
theorem Homeomorph.mulLeft_symm
  given: (a : G)
  statement: (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹
  proof: by
  ext
  rfl

@[to_additive]

中文:
定理 同胚.mulLeft_symm
  条件: (a : G)
  结论: (同胚.mulLeft a).symm = 同胚.mulLeft a⁻¹
  证明: by
  ext
  rfl

@[to_additive]
-/
theorem Homeomorph.mulLeft_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ := by
  ext
  rfl

@[to_additive]
/--
lemma `isOpenMap_mul_left` / 引理 `isOpenMap_mul_left`

English:
lemma isOpenMap_mul_left
  given: (a : G)
  statement: IsOpenMap (a * ·)
  proof: (Homeomorph.mulLeft a).isOpenMap

@[to_additive IsOpen.left_addCoset]

中文:
引理 isOpenMap_mul_left
  条件: (a : G)
  结论: 是开映射 (a * ·)
  证明: (Homeomorph.mulLeft a).isOpenMap

@[to_additive IsOpen.left_addCoset]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, isOpenMap, mulLeft
-/
lemma isOpenMap_mul_left (a : G) : IsOpenMap (a * ·) := (Homeomorph.mulLeft a).isOpenMap

@[to_additive IsOpen.left_addCoset]
/--
theorem `IsOpen.leftCoset` / 定理 `IsOpen.leftCoset`

English:
theorem IsOpen.leftCoset
  given: {U : Set G} (h : IsOpen U) (x : G)
  statement: IsOpen (x • U)
  proof: isOpenMap_mul_left x _ h

@[to_additive]

中文:
定理 是开集.leftCoset
  条件: {U : 集合 G} (h : 是开集 U) (x : G)
  结论: 是开集 (x • U)
  证明: isOpenMap_mul_left x _ h

@[to_additive]

Depends on / 依赖: isOpenMap_mul_left
-/
theorem IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (x • U) :=
  isOpenMap_mul_left x _ h

@[to_additive]
/--
lemma `isClosedMap_mul_left` / 引理 `isClosedMap_mul_left`

English:
lemma isClosedMap_mul_left
  given: (a : G)
  statement: IsClosedMap (a * ·)
  proof: (Homeomorph.mulLeft a).isClosedMap

@[to_additive IsClosed.left_addCoset]

中文:
引理 isClosedMap_mul_left
  条件: (a : G)
  结论: 是闭映射 (a * ·)
  证明: (Homeomorph.mulLeft a).isClosedMap

@[to_additive IsClosed.left_addCoset]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, isClosedMap, mulLeft
-/
lemma isClosedMap_mul_left (a : G) : IsClosedMap (a * ·) := (Homeomorph.mulLeft a).isClosedMap

@[to_additive IsClosed.left_addCoset]
/--
theorem `IsClosed.leftCoset` / 定理 `IsClosed.leftCoset`

English:
theorem IsClosed.leftCoset
  given: {U : Set G} (h : IsClosed U) (x : G)
  statement: IsClosed (x • U)
  proof: isClosedMap_mul_left x _ h

@[to_additive (attr := simp)]

中文:
定理 是闭集.leftCoset
  条件: {U : 集合 G} (h : 是闭集 U) (x : G)
  结论: 是闭集 (x • U)
  证明: isClosedMap_mul_left x _ h

@[to_additive (attr := simp)]

Depends on / 依赖: isClosedMap_mul_left
-/
theorem IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (x • U) :=
  isClosedMap_mul_left x _ h

@[to_additive (attr := simp)]
/--
theorem `Filter.map_mul_left_nhdsNE` / 定理 `Filter.map_mul_left_nhdsNE`

English:
theorem Filter.map_mul_left_nhdsNE
  given: {c a : G}
  proof: by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

中文:
定理 滤子.map_mul_left_nhdsNE
  条件: {c a : G}
  证明: by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq, mulLeft
-/
theorem Filter.map_mul_left_nhdsNE {c a : G} :
    map (c * ·) (𝓝[!=] a) = (𝓝[!=] (c * a)) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive /-- Addition from the right in a topological additive group as a homeomorphism. -/]
/--
Definition of `Homeomorph.mulRight` / `Homeomorph.mulRight` 的定义

English:
definition Homeomorph.mulRight
  signature: (a : G)
  body: { Equiv.mulRight a with }

@[to_additive (attr := simp)]

中文:
定义 同胚.mulRight
  签名: (a : G)
  定义体: { Equiv.mulRight a with }

@[to_additive (attr := simp)]
-/
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with }

@[to_additive (attr := simp)]
/--
lemma `Homeomorph.coe_mulRight` / 引理 `Homeomorph.coe_mulRight`

English:
lemma Homeomorph.coe_mulRight
  given: (a : G)
  statement: ⇑(Homeomorph.mulRight a) = (· * a)
  proof: rfl

@[to_additive]

中文:
引理 同胚.coe_mulRight
  条件: (a : G)
  结论: ⇑(同胚.mulRight a) = (· * a)
  证明: rfl

@[to_additive]
-/
lemma Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = (· * a) := rfl

@[to_additive]
/--
theorem `Homeomorph.mulRight_symm` / 定理 `Homeomorph.mulRight_symm`

English:
theorem Homeomorph.mulRight_symm
  given: (a : G)
  proof: by
  ext
  rfl

@[to_additive]

中文:
定理 同胚.mulRight_symm
  条件: (a : G)
  证明: by
  ext
  rfl

@[to_additive]
-/
theorem Homeomorph.mulRight_symm (a : G) :
    (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ := by
  ext
  rfl

@[to_additive]
/--
theorem `isOpenMap_mul_right` / 定理 `isOpenMap_mul_right`

English:
theorem isOpenMap_mul_right
  given: (a : G)
  statement: IsOpenMap (· * a)
  proof: (Homeomorph.mulRight a).isOpenMap

@[to_additive IsOpen.right_addCoset]

中文:
定理 isOpenMap_mul_right
  条件: (a : G)
  结论: 是开映射 (· * a)
  证明: (Homeomorph.mulRight a).isOpenMap

@[to_additive IsOpen.right_addCoset]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, isOpenMap, mulRight
-/
theorem isOpenMap_mul_right (a : G) : IsOpenMap (· * a) :=
  (Homeomorph.mulRight a).isOpenMap

@[to_additive IsOpen.right_addCoset]
/--
theorem `IsOpen.rightCoset` / 定理 `IsOpen.rightCoset`

English:
theorem IsOpen.rightCoset
  given: {U : Set G} (h : IsOpen U) (x : G)
  statement: IsOpen (op x • U)
  proof: isOpenMap_mul_right x _ h

@[to_additive]

中文:
定理 是开集.rightCoset
  条件: {U : 集合 G} (h : 是开集 U) (x : G)
  结论: 是开集 (op x • U)
  证明: isOpenMap_mul_right x _ h

@[to_additive]

Depends on / 依赖: isOpenMap_mul_right
-/
theorem IsOpen.rightCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (op x • U) :=
  isOpenMap_mul_right x _ h

@[to_additive]
/--
theorem `isClosedMap_mul_right` / 定理 `isClosedMap_mul_right`

English:
theorem isClosedMap_mul_right
  given: (a : G)
  statement: IsClosedMap (· * a)
  proof: (Homeomorph.mulRight a).isClosedMap

@[to_additive IsClosed.right_addCoset]

中文:
定理 isClosedMap_mul_right
  条件: (a : G)
  结论: 是闭映射 (· * a)
  证明: (Homeomorph.mulRight a).isClosedMap

@[to_additive IsClosed.right_addCoset]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, isClosedMap, mulRight
-/
theorem isClosedMap_mul_right (a : G) : IsClosedMap (· * a) :=
  (Homeomorph.mulRight a).isClosedMap

@[to_additive IsClosed.right_addCoset]
/--
theorem `IsClosed.rightCoset` / 定理 `IsClosed.rightCoset`

English:
theorem IsClosed.rightCoset
  given: {U : Set G} (h : IsClosed U) (x : G)
  statement: IsClosed (op x • U)
  proof: isClosedMap_mul_right x _ h

@[to_additive (attr := simp)]

中文:
定理 是闭集.rightCoset
  条件: {U : 集合 G} (h : 是闭集 U) (x : G)
  结论: 是闭集 (op x • U)
  证明: isClosedMap_mul_right x _ h

@[to_additive (attr := simp)]

Depends on / 依赖: isClosedMap_mul_right
-/
theorem IsClosed.rightCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (op x • U) :=
  isClosedMap_mul_right x _ h

@[to_additive (attr := simp)]
/--
theorem `Filter.map_mul_right_nhdsNE` / 定理 `Filter.map_mul_right_nhdsNE`

English:
theorem Filter.map_mul_right_nhdsNE
  given: {c a : G}
  proof: by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]

中文:
定理 滤子.map_mul_right_nhdsNE
  条件: {c a : G}
  证明: by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq, mulRight
-/
theorem Filter.map_mul_right_nhdsNE {c a : G} :
    map (· * c) (𝓝[!=] a) = (𝓝[!=] (a * c)) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
/--
theorem `discreteTopology_iff_isOpen_singleton_one` / 定理 `discreteTopology_iff_isOpen_singleton_one`

English:
theorem discreteTopology_iff_isOpen_singleton_one
  statement: DiscreteTopology G ↔ IsOpen ({1} : Set G)
  proof: MulAction.IsPretransitive.discreteTopology_iff G 1

@[to_additive]

中文:
定理 discreteTopology_iff_isOpen_singleton_one
  结论: 离散拓扑 G ↔ 是开集 ({1} : 集合 G)
  证明: MulAction.IsPretransitive.discreteTopology_iff G 1

@[to_additive]

Depends on / 依赖: IsPretransitive, MulAction, MulAction.IsPretransitive.discreteTopology_iff, discreteTopology_iff
-/
theorem discreteTopology_iff_isOpen_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  MulAction.IsPretransitive.discreteTopology_iff G 1

@[to_additive]
/--
theorem `discreteTopology_of_isOpen_singleton_one` / 定理 `discreteTopology_of_isOpen_singleton_one`

English:
theorem discreteTopology_of_isOpen_singleton_one
  given: (h : IsOpen ({1} : Set G))
  proof: discreteTopology_iff_isOpen_singleton_one.mpr h

@[to_additive]

中文:
定理 discreteTopology_of_isOpen_singleton_one
  条件: (h : 是开集 ({1} : 集合 G))
  证明: discreteTopology_iff_isOpen_singleton_one.mpr h

@[to_additive]

Depends on / 依赖: discreteTopology_iff_isOpen_singleton_one, discreteTopology_iff_isOpen_singleton_one.mpr
-/
theorem discreteTopology_of_isOpen_singleton_one (h : IsOpen ({1} : Set G)) :
    DiscreteTopology G :=
  discreteTopology_iff_isOpen_singleton_one.mpr h

@[to_additive]
/--
theorem `smul_connectedComponent` / 定理 `smul_connectedComponent`

English:
theorem smul_connectedComponent
  given: (g h : G)
  statement: g • connectedComponent h = connectedComponent (g * h)
  proof: (Homeomorph.mulLeft g).isQuotientMap.image_connectedComponent (by simp [isConnected_singleton]) h

@[to_additive]

中文:
定理 smul_connectedComponent
  条件: (g h : G)
  结论: g • connectedComponent h = connectedComponent (g * h)
  证明: (Homeomorph.mulLeft g).isQuotientMap.image_connectedComponent (by simp [isConnected_singleton]) h

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, image_connectedComponent, isConnected_singleton, isQuotientMap, isQuotientMap.image_connectedComponent, mulLeft
-/
theorem smul_connectedComponent (g h : G) : g • connectedComponent h = connectedComponent (g * h) :=
  (Homeomorph.mulLeft g).isQuotientMap.image_connectedComponent (by simp [isConnected_singleton]) h

@[to_additive]
/--
theorem `totallyDisconnectedSpace_iff_connectedComponent_one` / 定理 `totallyDisconnectedSpace_iff_connectedComponent_one`

English:
theorem totallyDisconnectedSpace_iff_connectedComponent_one
  proof: ⟨fun _ => connectedComponent_eq_singleton 1,
    fun h => totallyDisconnectedSpace_iff_connectedComponent_singleton.mpr fun g => by
      rw [← mul_one g]; rw [← smul_connectedComponent]; rw [h]; rw [Set.smul_set_singleton]; rw [smul_eq_mul]⟩

@[to_additive]

中文:
定理 totallyDisconnectedSpace_iff_connectedComponent_one
  证明: ⟨fun _ => connectedComponent_eq_singleton 1,
    fun h => totallyDisconnectedSpace_iff_connectedComponent_singleton.mpr fun g => by
      rw [← mul_one g]; rw [← smul_connectedComponent]; rw [h]; rw [Set.smul_set_singleton]; rw [smul_eq_mul]⟩

@[to_additive]

Depends on / 依赖: Set.smul_set_singleton, connectedComponent_eq_singleton, mul_one, smul_connectedComponent, smul_eq_mul, smul_set_singleton, totallyDisconnectedSpace_iff_connectedComponent_singleton, totallyDisconnectedSpace_iff_connectedComponent_singleton.mpr
-/
theorem totallyDisconnectedSpace_iff_connectedComponent_one :
    TotallyDisconnectedSpace G ↔ connectedComponent (1 : G) = {1} :=
  ⟨fun _ => connectedComponent_eq_singleton 1,
    fun h => totallyDisconnectedSpace_iff_connectedComponent_singleton.mpr fun g => by
      rw [← mul_one g]; rw [← smul_connectedComponent]; rw [h]; rw [Set.smul_set_singleton]; rw [smul_eq_mul]⟩

@[to_additive]
/--
lemma `Filter.tendsto_mul_const_iff` / 引理 `Filter.tendsto_mul_const_iff`

English:
lemma Filter.tendsto_mul_const_iff
  given: (b : G) {c : G} {f : α -> G} {l : Filter α}
  proof: by
  refine ⟨?_, Tendsto.mul_const b⟩
  convert! Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]

中文:
引理 滤子.tendsto_mul_const_iff
  条件: (b : G) {c : G} {f : α -> G} {l : 滤子 α}
  证明: by
  refine ⟨?_, Tendsto.mul_const b⟩
  convert! Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]

Depends on / 依赖: Tendsto, Tendsto.mul_const, convert, mul_const, mul_inv_cancel_right
-/
lemma Filter.tendsto_mul_const_iff (b : G) {c : G} {f : α -> G} {l : Filter α} :
    Tendsto (f · * b) l (𝓝 (c * b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.mul_const b⟩
  convert! Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]
/--
lemma `Filter.tendsto_const_mul_iff` / 引理 `Filter.tendsto_const_mul_iff`

English:
lemma Filter.tendsto_const_mul_iff
  given: (b : G) {c : G} {f : α -> G} {l : Filter α}
  proof: by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert! Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

中文:
引理 滤子.tendsto_const_mul_iff
  条件: (b : G) {c : G} {f : α -> G} {l : 滤子 α}
  证明: by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert! Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

Depends on / 依赖: Tendsto, Tendsto.const_mul, const_mul, convert, inv_mul_cancel_left
-/
lemma Filter.tendsto_const_mul_iff (b : G) {c : G} {f : α -> G} {l : Filter α} :
    Tendsto (b * f ·) l (𝓝 (b * c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert! Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

end ContinuousMulGroup

/-!
### `ContinuousInv` and `ContinuousNeg`
-/

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

@[to_additive]
/--
theorem `ContinuousInv.induced` / 定理 `ContinuousInv.induced`

English:
theorem ContinuousInv.induced
  statement: {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Group α]
  proof: by
  let _tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_inv]
  fun_prop

@[to_additive]

中文:
定理 连续取逆.induced
  结论: {α : 类型} {β : 类型} {F : 类型} [函数状 F α β] [群 α]
  证明: by
  let _tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_inv]
  fun_prop

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, continuous_induced_rng, fun_prop, induced, map_inv
-/
theorem ContinuousInv.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Group α]
    [DivisionMonoid β] [MonoidHomClass F α β] [tβ : TopologicalSpace β] [ContinuousInv β] (f : F) :
    @ContinuousInv α (tβ.induced f) _ := by
  let _tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_inv]
  fun_prop

@[to_additive]
/--
theorem `Specializes.inv` / 定理 `Specializes.inv`

English:
theorem Specializes.inv
  given: {x y : G} (h : x ⤳ y)
  statement: (x⁻¹) ⤳ (y⁻¹)
  proof: h.map continuous_inv

@[to_additive]

中文:
定理 Specializes.inv
  条件: {x y : G} (h : x ⤳ y)
  结论: (x⁻¹) ⤳ (y⁻¹)
  证明: h.map continuous_inv

@[to_additive]
-/
protected theorem Specializes.inv {x y : G} (h : x ⤳ y) : (x⁻¹) ⤳ (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
/--
theorem `Inseparable.inv` / 定理 `Inseparable.inv`

English:
theorem Inseparable.inv
  given: {x y : G} (h : Inseparable x y)
  statement: Inseparable (x⁻¹) (y⁻¹)
  proof: h.map continuous_inv

@[to_additive]

中文:
定理 不可分.inv
  条件: {x y : G} (h : 不可分 x y)
  结论: 不可分 (x⁻¹) (y⁻¹)
  证明: h.map continuous_inv

@[to_additive]
-/
protected theorem Inseparable.inv {x y : G} (h : Inseparable x y) : Inseparable (x⁻¹) (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
/--
theorem `Specializes.zpow` / 定理 `Specializes.zpow`

English:
theorem Specializes.zpow
  statement: {G : Type*} [DivInvMonoid G] [TopologicalSpace G]

中文:
定理 Specializes.zpow
  结论: {G : 类型} [除逆幺半群 G] [拓扑空间 G]
-/
protected theorem Specializes.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : x ⤳ y) : forall m : Int, (x ^ m) ⤳ (y ^ m)
  | .ofNat n => by simpa using h.pow n
  | .negSucc n => by simpa using (h.pow (n + 1)).inv

@[to_additive]
/--
theorem `Inseparable.zpow` / 定理 `Inseparable.zpow`

English:
theorem Inseparable.zpow
  statement: {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
  proof: (h.specializes.zpow m).antisymm (h.specializes'.zpow m)

@[to_additive]

中文:
定理 不可分.zpow
  结论: {G : 类型} [除逆幺半群 G] [拓扑空间 G]
  证明: (h.specializes.zpow m).antisymm (h.specializes'.zpow m)

@[to_additive]
-/
protected theorem Inseparable.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : Inseparable x y) (m : Int) :
    Inseparable (x ^ m) (y ^ m) :=
  (h.specializes.zpow m).antisymm (h.specializes'.zpow m)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousInv (ULift G)
  body: ⟨continuous_uliftUp.comp (continuous_inv.comp continuous_uliftDown)⟩

@[to_additive]

中文:
实例 :
  签名: 连续取逆 (类型层提升 G)
  定义体: ⟨continuous_uliftUp.comp (continuous_inv.comp continuous_uliftDown)⟩

@[to_additive]

Depends on / 依赖: continuous_inv, continuous_inv.comp, continuous_uliftDown, continuous_uliftUp, continuous_uliftUp.comp
-/
instance : ContinuousInv (ULift G) :=
  ⟨continuous_uliftUp.comp (continuous_inv.comp continuous_uliftDown)⟩

@[to_additive]
/--
theorem `continuousOn_inv` / 定理 `continuousOn_inv`

English:
theorem continuousOn_inv
  given: {s : Set G}
  statement: ContinuousOn Inv.inv s
  proof: continuous_inv.continuousOn

@[to_additive]

中文:
定理 continuousOn_inv
  条件: {s : 集合 G}
  结论: ContinuousOn 取逆.inv s
  证明: continuous_inv.continuousOn

@[to_additive]

Depends on / 依赖: continuousOn, continuous_inv, continuous_inv.continuousOn
-/
theorem continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.continuousOn

@[to_additive]
/--
theorem `continuousWithinAt_inv` / 定理 `continuousWithinAt_inv`

English:
theorem continuousWithinAt_inv
  given: {s : Set G} {x : G}
  statement: ContinuousWithinAt Inv.inv s x
  proof: continuous_inv.continuousWithinAt

@[to_additive]

中文:
定理 continuousWithinAt_inv
  条件: {s : 集合 G} {x : G}
  结论: ContinuousWithinAt 取逆.inv s x
  证明: continuous_inv.continuousWithinAt

@[to_additive]

Depends on / 依赖: continuousWithinAt, continuous_inv, continuous_inv.continuousWithinAt
-/
theorem continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.continuousWithinAt

@[to_additive]
/--
theorem `continuousAt_inv` / 定理 `continuousAt_inv`

English:
theorem continuousAt_inv
  given: {x : G}
  statement: ContinuousAt Inv.inv x
  proof: continuous_inv.continuousAt

@[to_additive]

中文:
定理 continuousAt_inv
  条件: {x : G}
  结论: ContinuousAt 取逆.inv x
  证明: continuous_inv.continuousAt

@[to_additive]

Depends on / 依赖: continuousAt, continuous_inv, continuous_inv.continuousAt
-/
theorem continuousAt_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.continuousAt

@[to_additive]
/--
theorem `tendsto_inv` / 定理 `tendsto_inv`

English:
theorem tendsto_inv
  given: (a : G)
  statement: Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹)
  proof: continuousAt_inv

中文:
定理 tendsto_inv
  条件: (a : G)
  结论: 收敛 取逆.inv (𝓝 a) (𝓝 a⁻¹)
  证明: continuousAt_inv

Depends on / 依赖: continuousAt_inv
-/
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuousAt_inv

variable [TopologicalSpace α] {f : α -> G} {s : Set α} {x : α}

@[to_additive]
/--
Instance `OrderDual.instContinuousInv` / 实例 `OrderDual.instContinuousInv`

English:
instance OrderDual.instContinuousInv
  signature: : ContinuousInv Gᵒᵈ
  body: ‹ContinuousInv G›

@[to_additive]

中文:
实例 OrderDual.instContinuousInv
  签名: : 连续取逆 Gᵒᵈ
  定义体: ‹ContinuousInv G›

@[to_additive]

Depends on / 依赖: ContinuousInv
-/
instance OrderDual.instContinuousInv : ContinuousInv Gᵒᵈ := ‹ContinuousInv G›

@[to_additive]
/--
Instance `Prod.continuousInv` / 实例 `Prod.continuousInv`

English:
instance Prod.continuousInv
  signature: [TopologicalSpace H] [Inv H] [ContinuousInv H]
  body: ⟨continuous_inv.fst'.prodMk continuous_inv.snd'⟩

中文:
实例 积类型.continuousInv
  签名: [拓扑空间 H] [取逆 H] [连续取逆 H]
  定义体: ⟨continuous_inv.fst'.prodMk continuous_inv.snd'⟩

Depends on / 依赖: continuous_inv, continuous_inv.fst, continuous_inv.snd, prodMk
-/
instance Prod.continuousInv [TopologicalSpace H] [Inv H] [ContinuousInv H] :
    ContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prodMk continuous_inv.snd'⟩

variable {ι : Type*}

@[to_additive]
/--
Instance `Pi.continuousInv` / 实例 `Pi.continuousInv`

English:
instance Pi.continuousInv
  signature: {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Inv (C i)]
  body: continuous_pi fun i => (continuous_apply i).inv

中文:
实例 依赖函数类型.continuousInv
  签名: {C : ι -> 类型} [对任意 i, 拓扑空间 (C i)] [对任意 i, 取逆 (C i)]
  定义体: continuous_pi fun i => (continuous_apply i).inv

Depends on / 依赖: continuous_apply, continuous_pi
-/
instance Pi.continuousInv {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Inv (C i)]
    [forall i, ContinuousInv (C i)] : ContinuousInv (forall i, C i) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

/-- A version of `Pi.continuousInv` for non-dependent functions. It is needed because sometimes
Lean fails to use `Pi.continuousInv` for non-dependent functions. -/
@[to_additive
  /-- A version of `Pi.continuousNeg` for non-dependent functions. It is needed
  because sometimes Lean fails to use `Pi.continuousNeg` for non-dependent functions. -/]
/--
Instance `Pi.has_continuous_inv'` / 实例 `Pi.has_continuous_inv'`

English:
instance Pi.has_continuous_inv'
  signature: : ContinuousInv (ι -> G)
  body: Pi.continuousInv

@[to_additive]

中文:
实例 依赖函数类型.has_continuous_inv'
  签名: : 连续取逆 (ι -> G)
  定义体: Pi.continuousInv

@[to_additive]

Depends on / 依赖: Pi.continuousInv, continuousInv
-/
instance Pi.has_continuous_inv' : ContinuousInv (ι -> G) :=
  Pi.continuousInv

@[to_additive]
instance (priority := 100) continuousInv_of_discreteTopology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousInv_of_indiscreteTopology [TopologicalSpace H] [Inv H]
    [IndiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
instance (priority := 100) continuousDiv_of_discreteTopology [TopologicalSpace H] [Div H]
    [DiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousDiv_of_indiscreteTopology [TopologicalSpace H] [Div H]
    [IndiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
instance (priority := 100) topologicalGroup_of_discreteTopology
    [TopologicalSpace H] [Group H] [DiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

@[to_additive]
instance (priority := 100) topologicalGroup_of_indiscreteTopology
    [TopologicalSpace H] [Group H] [IndiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

section PointwiseLimits

variable (G₁ G₂ : Type*) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
/--
theorem `isClosed_setOfPred_map_inv` / 定理 `isClosed_setOfPred_map_inv`

English:
theorem isClosed_setOfPred_map_inv
  given: [Inv G₁] [Inv G₂] [ContinuousInv G₂]
  proof: by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_inv := isClosed_setOfPred_map_inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_neg := isClosed_setOfPred_map_neg

中文:
定理 isClosed_setOfPred_map_inv
  条件: [取逆 G₁] [取逆 G₂] [连续取逆 G₂]
  证明: by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_inv := isClosed_setOfPred_map_inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_neg := isClosed_setOfPred_map_neg

Depends on / 依赖: continuous_apply, isClosed_eq, isClosed_iInter, ofPred_forall
-/
theorem isClosed_setOfPred_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] :
    IsClosed { f : G₁ -> G₂ | forall x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_inv := isClosed_setOfPred_map_inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_neg := isClosed_setOfPred_map_neg

end PointwiseLimits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H) where
  body: @continuous_inv H _ _ _

中文:
实例 [拓扑空间
  签名: H] [取逆 H] [连续取逆 H] : 连续取负 (加性 H) where
  定义体: @continuous_inv H _ _ _

Depends on / 依赖: continuous_inv
-/
instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H) where
  continuous_neg := @continuous_inv H _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H) where
  body: @continuous_neg H _ _ _

中文:
实例 [拓扑空间
  签名: H] [取负 H] [连续取负 H] : 连续取逆 (Multiplicative H) where
  定义体: @continuous_neg H _ _ _

Depends on / 依赖: continuous_neg
-/
instance [TopologicalSpace H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H) where
  continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] {s : Set G}

@[to_additive (attr := simp)]
/--
theorem `tendsto_inv_iff` / 定理 `tendsto_inv_iff`

English:
theorem tendsto_inv_iff
  given: {l : Filter α} {m : α -> G} {a : G}
  proof: ⟨fun h => by simpa only [inv_inv] using h.inv, Tendsto.inv⟩

@[to_additive]

中文:
定理 tendsto_inv_iff
  条件: {l : 滤子 α} {m : α -> G} {a : G}
  证明: ⟨fun h => by simpa only [inv_inv] using h.inv, Tendsto.inv⟩

@[to_additive]

Depends on / 依赖: Tendsto, Tendsto.inv, h.inv, inv_inv
-/
theorem tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} :
    Tendsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, Tendsto.inv⟩

@[to_additive]
/--
theorem `IsCompact.inv` / 定理 `IsCompact.inv`

English:
theorem IsCompact.inv
  given: (hs : IsCompact s)
  statement: IsCompact s⁻¹
  proof: by
  rw [← image_inv_eq_inv]
  exact hs.image continuous_inv

中文:
定理 是紧集.inv
  条件: (hs : 是紧集 s)
  结论: 是紧集 s⁻¹
  证明: by
  rw [← image_inv_eq_inv]
  exact hs.image continuous_inv

Depends on / 依赖: continuous_inv, hs.image, image_inv_eq_inv
-/
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv_eq_inv]
  exact hs.image continuous_inv

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive /-- Negation in a topological group as a homeomorphism. -/]
/--
Definition of `Homeomorph.inv` / `Homeomorph.inv` 的定义

English:
definition Homeomorph.inv
  signature: (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
  body: { Equiv.inv G with }

@[to_additive (attr := simp)]

中文:
定义 同胚.inv
  签名: (G : 类型) [拓扑空间 G] [InvolutiveInv G]
  定义体: { Equiv.inv G with }

@[to_additive (attr := simp)]
-/
protected def Homeomorph.inv (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
    [ContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with }

@[to_additive (attr := simp)]
/--
lemma `Homeomorph.symm_inv` / 引理 `Homeomorph.symm_inv`

English:
lemma Homeomorph.symm_inv
  given: {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 同胚.symm_inv
  条件: {G : 类型} [拓扑空间 G] [InvolutiveInv G] [连续取逆 G]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma Homeomorph.symm_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    (Homeomorph.inv G).symm = Homeomorph.inv G := rfl

@[to_additive (attr := simp)]
/--
lemma `Homeomorph.coe_inv` / 引理 `Homeomorph.coe_inv`

English:
lemma Homeomorph.coe_inv
  given: {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G]
  proof: rfl

@[to_additive]

中文:
引理 同胚.coe_inv
  条件: {G : 类型} [拓扑空间 G] [InvolutiveInv G] [连续取逆 G]
  证明: rfl

@[to_additive]
-/
lemma Homeomorph.coe_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    ⇑(Homeomorph.inv G) = Inv.inv := rfl

@[to_additive]
/--
theorem `nhds_inv` / 定理 `nhds_inv`

English:
theorem nhds_inv
  given: (a : G)
  statement: 𝓝 a⁻¹ = (𝓝 a)⁻¹
  proof: ((Homeomorph.inv G).map_nhds_eq a).symm

@[to_additive]

中文:
定理 nhds_inv
  条件: (a : G)
  结论: 𝓝 a⁻¹ = (𝓝 a)⁻¹
  证明: ((Homeomorph.inv G).map_nhds_eq a).symm

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, map_nhds_eq
-/
theorem nhds_inv (a : G) : 𝓝 a⁻¹ = (𝓝 a)⁻¹ :=
  ((Homeomorph.inv G).map_nhds_eq a).symm

@[to_additive]
/--
theorem `isOpenMap_inv` / 定理 `isOpenMap_inv`

English:
theorem isOpenMap_inv
  statement: IsOpenMap (Inv.inv : G -> G)
  proof: (Homeomorph.inv _).isOpenMap

@[to_additive]

中文:
定理 isOpenMap_inv
  结论: 是开映射 (取逆.inv : G -> G)
  证明: (Homeomorph.inv _).isOpenMap

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, isOpenMap
-/
theorem isOpenMap_inv : IsOpenMap (Inv.inv : G -> G) :=
  (Homeomorph.inv _).isOpenMap

@[to_additive]
/--
theorem `isClosedMap_inv` / 定理 `isClosedMap_inv`

English:
theorem isClosedMap_inv
  statement: IsClosedMap (Inv.inv : G -> G)
  proof: (Homeomorph.inv _).isClosedMap

中文:
定理 isClosedMap_inv
  结论: 是闭映射 (取逆.inv : G -> G)
  证明: (Homeomorph.inv _).isClosedMap

Depends on / 依赖: Homeomorph, Homeomorph.inv, isClosedMap
-/
theorem isClosedMap_inv : IsClosedMap (Inv.inv : G -> G) :=
  (Homeomorph.inv _).isClosedMap

variable {G}

@[to_additive]
/--
theorem `IsOpen.inv` / 定理 `IsOpen.inv`

English:
theorem IsOpen.inv
  given: (hs : IsOpen s)
  statement: IsOpen s⁻¹
  proof: hs.preimage continuous_inv

@[to_additive]

中文:
定理 是开集.inv
  条件: (hs : 是开集 s)
  结论: 是开集 s⁻¹
  证明: hs.preimage continuous_inv

@[to_additive]

Depends on / 依赖: continuous_inv, hs.preimage, preimage
-/
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
/--
theorem `IsClosed.inv` / 定理 `IsClosed.inv`

English:
theorem IsClosed.inv
  given: (hs : IsClosed s)
  statement: IsClosed s⁻¹
  proof: hs.preimage continuous_inv

@[to_additive]

中文:
定理 是闭集.inv
  条件: (hs : 是闭集 s)
  结论: 是闭集 s⁻¹
  证明: hs.preimage continuous_inv

@[to_additive]

Depends on / 依赖: continuous_inv, hs.preimage, preimage
-/
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
/--
theorem `inv_closure` / 定理 `inv_closure`

English:
theorem inv_closure
  statement: forall s : Set G, (closure s)⁻¹ = closure s⁻¹
  proof: (Homeomorph.inv G).preimage_closure

中文:
定理 inv_closure
  结论: 对任意 s : 集合 G, (closure s)⁻¹ = closure s⁻¹
  证明: (Homeomorph.inv G).preimage_closure

Depends on / 依赖: Homeomorph, Homeomorph.inv, preimage_closure
-/
theorem inv_closure : forall s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure

variable [TopologicalSpace α] {f : α -> G} {s : Set α} {x : α}

@[to_additive (attr := simp)]
/--
lemma `continuous_inv_iff` / 引理 `continuous_inv_iff`

English:
lemma continuous_inv_iff
  statement: Continuous f⁻¹ ↔ Continuous f
  proof: (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]

中文:
引理 continuous_inv_iff
  结论: 连续 f⁻¹ ↔ 连续 f
  证明: (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.inv, comp_continuous_iff
-/
lemma continuous_inv_iff : Continuous f⁻¹ ↔ Continuous f := (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]
/--
lemma `continuousAt_inv_iff` / 引理 `continuousAt_inv_iff`

English:
lemma continuousAt_inv_iff
  statement: ContinuousAt f⁻¹ x ↔ ContinuousAt f x
  proof: (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]

中文:
引理 continuousAt_inv_iff
  结论: ContinuousAt f⁻¹ x ↔ ContinuousAt f x
  证明: (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.inv, comp_continuousAt_iff
-/
lemma continuousAt_inv_iff : ContinuousAt f⁻¹ x ↔ ContinuousAt f x :=
  (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]
/--
lemma `continuousOn_inv_iff` / 引理 `continuousOn_inv_iff`

English:
lemma continuousOn_inv_iff
  statement: ContinuousOn f⁻¹ s ↔ ContinuousOn f s
  proof: (Homeomorph.inv G).comp_continuousOn_iff _ _

@[to_additive] alias ⟨Continuous.of_inv, _⟩ := continuous_inv_iff
@[to_additive] alias ⟨ContinuousAt.of_inv, _⟩ := continuousAt_inv_iff
@[to_additive] alias ⟨ContinuousOn.of_inv, _⟩ := continuousOn_inv_iff

@[to_additive (attr := simp)]

中文:
引理 continuousOn_inv_iff
  结论: ContinuousOn f⁻¹ s ↔ ContinuousOn f s
  证明: (Homeomorph.inv G).comp_continuousOn_iff _ _

@[to_additive] alias ⟨Continuous.of_inv, _⟩ := continuous_inv_iff
@[to_additive] alias ⟨ContinuousAt.of_inv, _⟩ := continuousAt_inv_iff
@[to_additive] alias ⟨ContinuousOn.of_inv, _⟩ := continuousOn_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.inv, comp_continuousOn_iff
-/
lemma continuousOn_inv_iff : ContinuousOn f⁻¹ s ↔ ContinuousOn f s :=
  (Homeomorph.inv G).comp_continuousOn_iff _ _

@[to_additive] alias ⟨Continuous.of_inv, _⟩ := continuous_inv_iff
@[to_additive] alias ⟨ContinuousAt.of_inv, _⟩ := continuousAt_inv_iff
@[to_additive] alias ⟨ContinuousOn.of_inv, _⟩ := continuousOn_inv_iff

@[to_additive (attr := simp)]
/--
theorem `Filter.inv_nhdsNE` / 定理 `Filter.inv_nhdsNE`

English:
theorem Filter.inv_nhdsNE
  given: {a : G}
  statement: (𝓝[!=] a)⁻¹ = 𝓝[!=] (a⁻¹)
  proof: by
  convert! (Homeomorph.inv G).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

中文:
定理 滤子.inv_nhdsNE
  条件: {a : G}
  结论: (𝓝[!=] a)⁻¹ = 𝓝[!=] (a⁻¹)
  证明: by
  convert! (Homeomorph.inv G).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

Depends on / 依赖: Homeomorph, Homeomorph.inv, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.inv_nhdsNE {a : G} : (𝓝[!=] a)⁻¹ = 𝓝[!=] (a⁻¹) := by
  convert! (Homeomorph.inv G).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort*} [Inv G]

@[to_additive]
/--
theorem `continuousInv_sInf` / 定理 `continuousInv_sInf`

English:
theorem continuousInv_sInf
  statement: {ts : Set (TopologicalSpace G)}
  proof: letI := sInf ts
  { continuous_inv :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }

@[to_additive]

中文:
定理 continuousInv_sInf
  结论: {ts : 集合 (拓扑空间 G)}
  证明: letI := sInf ts
  { continuous_inv :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }

@[to_additive]

Depends on / 依赖: ContinuousInv, ContinuousInv.continuous_inv, continuous_inv, continuous_sInf_dom, continuous_sInf_rng
-/
theorem continuousInv_sInf {ts : Set (TopologicalSpace G)}
    (h : forall t in ts, @ContinuousInv G t _) : @ContinuousInv G (sInf ts) _ :=
  letI := sInf ts
  { continuous_inv :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }

@[to_additive]
/--
theorem `continuousInv_iInf` / 定理 `continuousInv_iInf`

English:
theorem continuousInv_iInf
  statement: {ts' : ι' -> TopologicalSpace G}
  proof: by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

中文:
定理 continuousInv_iInf
  结论: {ts' : ι' -> 拓扑空间 G}
  证明: by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

Depends on / 依赖: Set.forall_mem_range.mpr, continuousInv_sInf, forall_mem_range, sInf_range
-/
theorem continuousInv_iInf {ts' : ι' -> TopologicalSpace G}
    (h' : forall i, @ContinuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/--
theorem `continuousInv_inf` / 定理 `continuousInv_inf`

English:
theorem continuousInv_inf
  statement: {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
  proof: by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption

中文:
定理 continuousInv_inf
  结论: {t₁ t₂ : 拓扑空间 G} (h₁ : @连续取逆 G t₁ _)
  证明: by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption

Depends on / 依赖: continuousInv_iInf, inf_eq_iInf
-/
theorem continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
    (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

@[to_additive]
/--
theorem `Topology.IsInducing.continuousInv` / 定理 `Topology.IsInducing.continuousInv`

English:
theorem Topology.IsInducing.continuousInv
  statement: {G H : Type*} [Inv G] [Inv H] [TopologicalSpace G]
  proof: ⟨hf.continuous_iff.2 by simpa only [Function.comp_def, hf_inv] using hf.continuous.fun_inv⟩

中文:
定理 拓扑.是Inducing.continuousInv
  结论: {G H : 类型} [取逆 G] [取逆 H] [拓扑空间 G]
  证明: ⟨hf.continuous_iff.2 by simpa only [Function.comp_def, hf_inv] using hf.continuous.fun_inv⟩

Depends on / 依赖: Function, Function.comp_def, comp_def, continuous, continuous_iff, fun_inv, hf.continuous.fun_inv, hf.continuous_iff, hf_inv
-/
theorem Topology.IsInducing.continuousInv {G H : Type*} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [ContinuousInv H] {f : G -> H} (hf : IsInducing f)
    (hf_inv : forall x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G :=
⟨hf.continuous_iff.2 by simpa only [Function.comp_def, hf_inv] using hf.continuous.fun_inv⟩

section IsTopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `x y ↦ x * y⁻¹` (resp., subtraction) is continuous.
-/

section Conj

/--
Instance `ConjAct.units_continuousConstSMul` / 实例 `ConjAct.units_continuousConstSMul`

English:
instance ConjAct.units_continuousConstSMul
  signature: {M} [Monoid M] [TopologicalSpace M]
  body: ⟨fun _ => (continuous_const.mul continuous_id).mul continuous_const⟩

中文:
实例 ConjAct.units_continuousConstSMul
  签名: {M} [幺半群 M] [拓扑空间 M]
  定义体: ⟨fun _ => (continuous_const.mul continuous_id).mul continuous_const⟩

Depends on / 依赖: continuous_const, continuous_const.mul, continuous_id
-/
instance ConjAct.units_continuousConstSMul {M} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] : ContinuousConstSMul (ConjAct Mˣ) M :=
  ⟨fun _ => (continuous_const.mul continuous_id).mul continuous_const⟩

open scoped Pointwise in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [Group H] [TopologicalSpace G] [MulDistribMulAction H G]
  body: by
  simp only [← SetLike.coe_sort_coe, ← isDiscrete_iff_discreteTopology] at *
  refine IsDiscrete.image_of_isOpenMap ‹_› ?_ fun x y => by simp
  apply IsOpenMap.of_inverse (f' := fun x => h⁻¹ • x) (continuous_const_smul _) <;>
  · intro x
    simp

中文:
实例 [群
  签名: G] [群 H] [拓扑空间 G] [MulDistribMul作用 H G]
  定义体: by
  simp only [← SetLike.coe_sort_coe, ← isDiscrete_iff_discreteTopology] at *
  refine IsDiscrete.image_of_isOpenMap ‹_› ?_ fun x y => by simp
  apply IsOpenMap.of_inverse (f' := fun x => h⁻¹ • x) (continuous_const_smul _) <;>
  · intro x
    simp
-/
instance [Group G] [Group H] [TopologicalSpace G] [MulDistribMulAction H G]
    [ContinuousConstSMul H G] {𝒢 : Subgroup G} (h : H) [DiscreteTopology 𝒢] :
    DiscreteTopology ↑(h • 𝒢) := by
  simp only [← SetLike.coe_sort_coe, ← isDiscrete_iff_discreteTopology] at *
  refine IsDiscrete.image_of_isOpenMap ‹_› ?_ fun x y => by simp
  apply IsOpenMap.of_inverse (f' := fun x => h⁻¹ • x) (continuous_const_smul _) <;>
  · intro x
    simp

variable [TopologicalSpace G] [Inv G] [Mul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive continuous_addConj_prod
  /-- Conjugation is jointly continuous on `G × G` when both `add` and `neg` are continuous. -/]
/--
theorem `IsTopologicalGroup.continuous_conj_prod` / 定理 `IsTopologicalGroup.continuous_conj_prod`

English:
theorem IsTopologicalGroup.continuous_conj_prod
  given: [ContinuousMul G] [ContinuousInv G]
  proof: continuous_mul.mul (continuous_inv.comp continuous_fst)

中文:
定理 是拓扑群.continuous_conj_prod
  条件: [连续乘法 G] [连续取逆 G]
  证明: continuous_mul.mul (continuous_inv.comp continuous_fst)

Depends on / 依赖: continuous_fst, continuous_inv, continuous_inv.comp, continuous_mul, continuous_mul.mul
-/
theorem IsTopologicalGroup.continuous_conj_prod [ContinuousMul G] [ContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation by a fixed element is continuous when `add` is continuous. -/]
/--
theorem `IsTopologicalGroup.continuous_conj` / 定理 `IsTopologicalGroup.continuous_conj`

English:
theorem IsTopologicalGroup.continuous_conj
  given: [SeparatelyContinuousMul G] (g : G)
  proof: (continuous_mul_const g⁻¹).comp (continuous_const_mul g)

中文:
定理 是拓扑群.continuous_conj
  条件: [SeparatelyContinuousMul G] (g : G)
  证明: (continuous_mul_const g⁻¹).comp (continuous_const_mul g)

Depends on / 依赖: continuous_const_mul, continuous_mul_const
-/
theorem IsTopologicalGroup.continuous_conj [SeparatelyContinuousMul G] (g : G) :
    Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_const g⁻¹).comp (continuous_const_mul g)

instance {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G where
  continuous_const_smul h := IsTopologicalGroup.continuous_conj (ConjAct.ofConjAct h)

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation acting on fixed element of the additive group is continuous when both
    `add` and `neg` are continuous. -/]
/--
theorem `IsTopologicalGroup.continuous_conj'` / 定理 `IsTopologicalGroup.continuous_conj'`

English:
theorem IsTopologicalGroup.continuous_conj'
  given: [ContinuousMul G] [ContinuousInv G] (h : G)
  proof: (continuous_mul_const h).mul continuous_inv

中文:
定理 是拓扑群.continuous_conj'
  条件: [连续乘法 G] [连续取逆 G] (h : G)
  证明: (continuous_mul_const h).mul continuous_inv

Depends on / 依赖: DFunLike, DFunLike.ext, continuous_inv, continuous_mul_const, subtype_mk
-/
theorem IsTopologicalGroup.continuous_conj' [ContinuousMul G] [ContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_const h).mul continuous_inv

end Conj

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace α] {f : α -> G}
  {s : Set α} {x : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalGroup (ULift G)

中文:
实例 :
  签名: 是拓扑群 (类型层提升 G)

Depends on / 依赖: RegularSpace, UniformSpace, UniformSpace.to_regularSpace, to_regularSpace
-/
instance : IsTopologicalGroup (ULift G) where

section ZPow

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_zpow` / 定理 `continuous_zpow`

English:
theorem continuous_zpow
  statement: forall z : Int, Continuous fun a : G => a ^ z

中文:
定理 continuous_zpow
  结论: 对任意 z : 整数, 连续 fun a : G => a ^ z
-/
theorem continuous_zpow : forall z : Int, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | Int.negSucc n => by simpa using (continuous_pow (n + 1)).fun_inv

/--
Instance `AddGroup.continuousConstSMul_int` / 实例 `AddGroup.continuousConstSMul_int`

English:
instance AddGroup.continuousConstSMul_int
  signature: {A} [AddGroup A] [TopologicalSpace A]
  body: ⟨continuous_zsmul⟩

中文:
实例 加法群.continuousConstSMul_int
  签名: {A} [加法群 A] [拓扑空间 A]
  定义体: ⟨continuous_zsmul⟩

Depends on / 依赖: UniformSpace, UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity, completelyNormalSpace_of_isCountablyGenerated_uniformity, continuous_zsmul
-/
instance AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousConstSMul Int A :=
  ⟨continuous_zsmul⟩

/--
Instance `AddGroup.continuousSMul_int` / 实例 `AddGroup.continuousSMul_int`

English:
instance AddGroup.continuousSMul_int
  signature: {A} [AddGroup A] [TopologicalSpace A]
  body: ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]

中文:
实例 加法群.continuousSMul_int
  签名: {A} [加法群 A] [拓扑空间 A]
  定义体: ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]

Depends on / 依赖: continuous_prod_of_discrete_left, continuous_prod_of_discrete_left.mpr, continuous_zsmul
-/
instance AddGroup.continuousSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousSMul Int A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/--
theorem `Continuous.zpow` / 定理 `Continuous.zpow`

English:
theorem Continuous.zpow
  given: {f : α -> G} (h : Continuous f) (z : Int)
  statement: Continuous (f ^ z)
  proof: (continuous_zpow z).comp h

@[to_additive]

中文:
定理 连续.zpow
  条件: {f : α -> G} (h : 连续 f) (z : 整数)
  结论: 连续 (f ^ z)
  证明: (continuous_zpow z).comp h

@[to_additive]

Depends on / 依赖: continuous_zpow
-/
theorem Continuous.zpow {f : α -> G} (h : Continuous f) (z : Int) : Continuous (f ^ z) :=
  (continuous_zpow z).comp h

@[to_additive]
/--
theorem `continuousOn_zpow` / 定理 `continuousOn_zpow`

English:
theorem continuousOn_zpow
  given: {s : Set G} (z : Int)
  statement: ContinuousOn (fun x => x ^ z) s
  proof: (continuous_zpow z).continuousOn

@[to_additive]

中文:
定理 continuousOn_zpow
  条件: {s : 集合 G} (z : 整数)
  结论: ContinuousOn (fun x => x ^ z) s
  证明: (continuous_zpow z).continuousOn

@[to_additive]

Depends on / 依赖: continuousOn, continuous_zpow
-/
theorem continuousOn_zpow {s : Set G} (z : Int) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).continuousOn

@[to_additive]
/--
theorem `continuousAt_zpow` / 定理 `continuousAt_zpow`

English:
theorem continuousAt_zpow
  given: (x : G) (z : Int)
  statement: ContinuousAt (fun x => x ^ z) x
  proof: (continuous_zpow z).continuousAt

@[to_additive]

中文:
定理 continuousAt_zpow
  条件: (x : G) (z : 整数)
  结论: ContinuousAt (fun x => x ^ z) x
  证明: (continuous_zpow z).continuousAt

@[to_additive]

Depends on / 依赖: continuousAt, continuous_zpow
-/
theorem continuousAt_zpow (x : G) (z : Int) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).continuousAt

@[to_additive]
/--
theorem `Filter.Tendsto.zpow` / 定理 `Filter.Tendsto.zpow`

English:
theorem Filter.Tendsto.zpow
  statement: {α} {l : Filter α} {f : α -> G} {x : G} (hf : Tendsto f l (𝓝 x))
  proof: (continuousAt_zpow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 滤子.收敛.zpow
  结论: {α} {l : 滤子 α} {f : α -> G} {x : G} (hf : 收敛 f l (𝓝 x))
  证明: (continuousAt_zpow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: continuousAt_zpow, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α -> G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : Int) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuousAt_zpow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousWithinAt.zpow` / 定理 `ContinuousWithinAt.zpow`

English:
theorem ContinuousWithinAt.zpow
  statement: {f : α -> G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
  proof: Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousWithinAt.zpow
  结论: {f : α -> G} {x : α} {s : 集合 α} (hf : ContinuousWithinAt f s x)
  证明: Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.zpow, Tendsto
-/
theorem ContinuousWithinAt.zpow {f : α -> G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : Int) : ContinuousWithinAt (f ^ z) s x :=
  Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousAt.zpow` / 定理 `ContinuousAt.zpow`

English:
theorem ContinuousAt.zpow
  given: {f : α -> G} {x : α} (hf : ContinuousAt f x) (z : Int)
  proof: Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousAt.zpow
  条件: {f : α -> G} {x : α} (hf : ContinuousAt f x) (z : 整数)
  证明: Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.zpow, Tendsto
-/
theorem ContinuousAt.zpow {f : α -> G} {x : α} (hf : ContinuousAt f x) (z : Int) :
    ContinuousAt (f ^ z) x :=
  Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousOn.zpow` / 定理 `ContinuousOn.zpow`

English:
theorem ContinuousOn.zpow
  given: {f : α -> G} {s : Set α} (hf : ContinuousOn f s) (z : Int)
  proof: fun x hx => (hf x hx).zpow z

中文:
定理 ContinuousOn.zpow
  条件: {f : α -> G} {s : 集合 α} (hf : ContinuousOn f s) (z : 整数)
  证明: fun x hx => (hf x hx).zpow z
-/
theorem ContinuousOn.zpow {f : α -> G} {s : Set α} (hf : ContinuousOn f s) (z : Int) :
    ContinuousOn (f ^ z) s := fun x hx => (hf x hx).zpow z

end ZPow

section OrderedCommGroup

variable [TopologicalSpace H] [CommGroup H] [PartialOrder H] [IsOrderedMonoid H]

section mul

variable [ContinuousMul H]

@[to_additive (attr := simp)]
/--
theorem `Filter.map_mul_left_nhdsGT` / 定理 `Filter.map_mul_left_nhdsGT`

English:
theorem Filter.map_mul_left_nhdsGT
  given: {c a : H}
  statement: map (c * ·) (𝓝[>] a) = 𝓝[>] (c * a)
  proof: by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]

中文:
定理 滤子.map_mul_left_nhdsGT
  条件: {c a : H}
  结论: map (c * ·) (𝓝[>] a) = 𝓝[>] (c * a)
  证明: by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq, mulLeft, mul_comm
-/
theorem Filter.map_mul_left_nhdsGT {c a : H} : map (c * ·) (𝓝[>] a) = 𝓝[>] (c * a) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
/--
theorem `Filter.map_mul_left_nhdsLT` / 定理 `Filter.map_mul_left_nhdsLT`

English:
theorem Filter.map_mul_left_nhdsLT
  given: {c a : H}
  statement: map (c * ·) (𝓝[<] a) = 𝓝[<] (c * a)
  proof: by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]

中文:
定理 滤子.map_mul_left_nhdsLT
  条件: {c a : H}
  结论: map (c * ·) (𝓝[<] a) = 𝓝[<] (c * a)
  证明: by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq, mulLeft, mul_comm
-/
theorem Filter.map_mul_left_nhdsLT {c a : H} : map (c * ·) (𝓝[<] a) = 𝓝[<] (c * a) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
/--
theorem `Filter.map_mul_right_nhdsGT` / 定理 `Filter.map_mul_right_nhdsGT`

English:
theorem Filter.map_mul_right_nhdsGT
  given: {c a : H}
  statement: map (· * c) (𝓝[>] a) = 𝓝[>] (a * c)
  proof: by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

中文:
定理 滤子.map_mul_right_nhdsGT
  条件: {c a : H}
  结论: map (· * c) (𝓝[>] a) = 𝓝[>] (a * c)
  证明: by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq, mulRight
-/
theorem Filter.map_mul_right_nhdsGT {c a : H} : map (· * c) (𝓝[>] a) = 𝓝[>] (a * c) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/--
theorem `Filter.map_mul_right_nhdsLT` / 定理 `Filter.map_mul_right_nhdsLT`

English:
theorem Filter.map_mul_right_nhdsLT
  given: {c a : H}
  statement: map (· * c) (𝓝[<] a) = 𝓝[<] (a * c)
  proof: by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

中文:
定理 滤子.map_mul_right_nhdsLT
  条件: {c a : H}
  结论: map (· * c) (𝓝[<] a) = 𝓝[<] (a * c)
  证明: by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq, mulRight
-/
theorem Filter.map_mul_right_nhdsLT {c a : H} : map (· * c) (𝓝[<] a) = 𝓝[<] (a * c) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end mul

section inv

variable [ContinuousInv H]

@[to_additive (attr := simp)]
/--
theorem `Filter.inv_nhdsGT` / 定理 `Filter.inv_nhdsGT`

English:
theorem Filter.inv_nhdsGT
  given: {a : H}
  statement: (𝓝[>] a)⁻¹ = 𝓝[<] (a⁻¹)
  proof: by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

中文:
定理 滤子.inv_nhdsGT
  条件: {a : H}
  结论: (𝓝[>] a)⁻¹ = 𝓝[<] (a⁻¹)
  证明: by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.inv, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.inv_nhdsGT {a : H} : (𝓝[>] a)⁻¹ = 𝓝[<] (a⁻¹) := by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/--
theorem `Filter.inv_nhdsLT` / 定理 `Filter.inv_nhdsLT`

English:
theorem Filter.inv_nhdsLT
  given: {a : H}
  statement: (𝓝[<] a)⁻¹ = 𝓝[>] (a⁻¹)
  proof: by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]

中文:
定理 滤子.inv_nhdsLT
  条件: {a : H}
  结论: (𝓝[<] a)⁻¹ = 𝓝[>] (a⁻¹)
  证明: by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, convert, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.inv_nhdsLT {a : H} : (𝓝[<] a)⁻¹ = 𝓝[>] (a⁻¹) := by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
/--
theorem `tendsto_inv_nhdsGT` / 定理 `tendsto_inv_nhdsGT`

English:
theorem tendsto_inv_nhdsGT
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹)
  proof: (continuous_inv.tendsto a).inf by simp

@[to_additive]

中文:
定理 tendsto_inv_nhdsGT
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[>] a) (𝓝[<] a⁻¹)
  证明: (continuous_inv.tendsto a).inf by simp

@[to_additive]

Depends on / 依赖: continuous_inv, continuous_inv.tendsto, tendsto
-/
theorem tendsto_inv_nhdsGT {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
(continuous_inv.tendsto a).inf by simp

@[to_additive]
/--
theorem `tendsto_inv_nhdsLT` / 定理 `tendsto_inv_nhdsLT`

English:
theorem tendsto_inv_nhdsLT
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹)
  proof: (continuous_inv.tendsto a).inf by simp

@[to_additive]

中文:
定理 tendsto_inv_nhdsLT
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[<] a) (𝓝[>] a⁻¹)
  证明: (continuous_inv.tendsto a).inf by simp

@[to_additive]

Depends on / 依赖: continuous_inv, continuous_inv.tendsto, tendsto
-/
theorem tendsto_inv_nhdsLT {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
(continuous_inv.tendsto a).inf by simp

@[to_additive]
/--
theorem `tendsto_inv_nhdsGT_inv` / 定理 `tendsto_inv_nhdsGT_inv`

English:
theorem tendsto_inv_nhdsGT_inv
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a)
  proof: by
  simpa only [inv_inv] using tendsto_inv_nhdsGT (a := a⁻¹)

@[to_additive]

中文:
定理 tendsto_inv_nhdsGT_inv
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[>] a⁻¹) (𝓝[<] a)
  证明: by
  simpa only [inv_inv] using tendsto_inv_nhdsGT (a := a⁻¹)

@[to_additive]

Depends on / 依赖: inv_inv, tendsto_inv_nhdsGT
-/
theorem tendsto_inv_nhdsGT_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGT (a := a⁻¹)

@[to_additive]
/--
theorem `tendsto_inv_nhdsLT_inv` / 定理 `tendsto_inv_nhdsLT_inv`

English:
theorem tendsto_inv_nhdsLT_inv
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a)
  proof: by
  simpa only [inv_inv] using tendsto_inv_nhdsLT (a := a⁻¹)

@[to_additive]

中文:
定理 tendsto_inv_nhdsLT_inv
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[<] a⁻¹) (𝓝[>] a)
  证明: by
  simpa only [inv_inv] using tendsto_inv_nhdsLT (a := a⁻¹)

@[to_additive]

Depends on / 依赖: inv_inv, tendsto_inv_nhdsLT
-/
theorem tendsto_inv_nhdsLT_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLT (a := a⁻¹)

@[to_additive]
/--
theorem `tendsto_inv_nhdsGE` / 定理 `tendsto_inv_nhdsGE`

English:
theorem tendsto_inv_nhdsGE
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[>=] a) (𝓝[<=] a⁻¹)
  proof: (continuous_inv.tendsto a).inf by simp

@[to_additive]

中文:
定理 tendsto_inv_nhdsGE
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[>=] a) (𝓝[<=] a⁻¹)
  证明: (continuous_inv.tendsto a).inf by simp

@[to_additive]

Depends on / 依赖: continuous_inv, continuous_inv.tendsto, tendsto
-/
theorem tendsto_inv_nhdsGE {a : H} : Tendsto Inv.inv (𝓝[>=] a) (𝓝[<=] a⁻¹) :=
(continuous_inv.tendsto a).inf by simp

@[to_additive]
/--
theorem `tendsto_inv_nhdsLE` / 定理 `tendsto_inv_nhdsLE`

English:
theorem tendsto_inv_nhdsLE
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[<=] a) (𝓝[>=] a⁻¹)
  proof: (continuous_inv.tendsto a).inf by simp

@[to_additive]

中文:
定理 tendsto_inv_nhdsLE
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[<=] a) (𝓝[>=] a⁻¹)
  证明: (continuous_inv.tendsto a).inf by simp

@[to_additive]

Depends on / 依赖: continuous_inv, continuous_inv.tendsto, tendsto
-/
theorem tendsto_inv_nhdsLE {a : H} : Tendsto Inv.inv (𝓝[<=] a) (𝓝[>=] a⁻¹) :=
(continuous_inv.tendsto a).inf by simp

@[to_additive]
/--
theorem `tendsto_inv_nhdsGE_inv` / 定理 `tendsto_inv_nhdsGE_inv`

English:
theorem tendsto_inv_nhdsGE_inv
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[>=] a⁻¹) (𝓝[<=] a)
  proof: by
  simpa only [inv_inv] using tendsto_inv_nhdsGE (a := a⁻¹)

@[to_additive]

中文:
定理 tendsto_inv_nhdsGE_inv
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[>=] a⁻¹) (𝓝[<=] a)
  证明: by
  simpa only [inv_inv] using tendsto_inv_nhdsGE (a := a⁻¹)

@[to_additive]

Depends on / 依赖: inv_inv, tendsto_inv_nhdsGE
-/
theorem tendsto_inv_nhdsGE_inv {a : H} : Tendsto Inv.inv (𝓝[>=] a⁻¹) (𝓝[<=] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGE (a := a⁻¹)

@[to_additive]
/--
theorem `tendsto_inv_nhdsLE_inv` / 定理 `tendsto_inv_nhdsLE_inv`

English:
theorem tendsto_inv_nhdsLE_inv
  given: {a : H}
  statement: Tendsto Inv.inv (𝓝[<=] a⁻¹) (𝓝[>=] a)
  proof: by
  simpa only [inv_inv] using tendsto_inv_nhdsLE (a := a⁻¹)

alias tendsto_inv_nhdsWithin_Iic_inv := tendsto_inv_nhdsLE_inv

中文:
定理 tendsto_inv_nhdsLE_inv
  条件: {a : H}
  结论: 收敛 取逆.inv (𝓝[<=] a⁻¹) (𝓝[>=] a)
  证明: by
  simpa only [inv_inv] using tendsto_inv_nhdsLE (a := a⁻¹)

alias tendsto_inv_nhdsWithin_Iic_inv := tendsto_inv_nhdsLE_inv

Depends on / 依赖: inv_inv, tendsto_inv_nhdsLE
-/
theorem tendsto_inv_nhdsLE_inv {a : H} : Tendsto Inv.inv (𝓝[<=] a⁻¹) (𝓝[>=] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLE (a := a⁻¹)

alias tendsto_inv_nhdsWithin_Iic_inv := tendsto_inv_nhdsLE_inv

end inv

end OrderedCommGroup

@[to_additive]
/--
Instance `Prod.instIsTopologicalGroup` / 实例 `Prod.instIsTopologicalGroup`

English:
instance Prod.instIsTopologicalGroup
  signature: [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  body: continuous_inv.prodMap continuous_inv

@[to_additive]

中文:
实例 积类型.instIsTopologicalGroup
  签名: [拓扑空间 H] [群 H] [是拓扑群 H]
  定义体: continuous_inv.prodMap continuous_inv

@[to_additive]

Depends on / 依赖: continuous_inv, continuous_inv.prodMap, prodMap
-/
instance Prod.instIsTopologicalGroup [TopologicalSpace H] [Group H] [IsTopologicalGroup H] :
    IsTopologicalGroup (G × H) where
  continuous_inv := continuous_inv.prodMap continuous_inv

@[to_additive]
/--
Instance `OrderDual.instIsTopologicalGroup` / 实例 `OrderDual.instIsTopologicalGroup`

English:
instance OrderDual.instIsTopologicalGroup
  signature: : IsTopologicalGroup Gᵒᵈ where

中文:
实例 OrderDual.instIsTopologicalGroup
  签名: : 是拓扑群 Gᵒᵈ where
-/
instance OrderDual.instIsTopologicalGroup : IsTopologicalGroup Gᵒᵈ where

@[to_additive]
/--
Instance `Pi.topologicalGroup` / 实例 `Pi.topologicalGroup`

English:
instance Pi.topologicalGroup
  signature: {C : β -> Type*} [forall b, TopologicalSpace (C b)] [forall b, Group (C b)]
  body: continuous_pi fun i => (continuous_apply i).inv

中文:
实例 依赖函数类型.topologicalGroup
  签名: {C : β -> 类型} [对任意 b, 拓扑空间 (C b)] [对任意 b, 群 (C b)]
  定义体: continuous_pi fun i => (continuous_apply i).inv

Depends on / 依赖: continuous_apply, continuous_pi, dif_pos, lift_mk
-/
instance Pi.topologicalGroup {C : β -> Type*} [forall b, TopologicalSpace (C b)] [forall b, Group (C b)]
    [forall b, IsTopologicalGroup (C b)] : IsTopologicalGroup (forall b, C b) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

open MulOpposite

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] [ContinuousInv α] : ContinuousInv αᵐᵒᵖ
  body: opHomeomorph.symm.isInducing.continuousInv unop_inv

中文:
实例 [取逆
  签名: α] [连续取逆 α] : 连续取逆 αᵐᵒᵖ
  定义体: opHomeomorph.symm.isInducing.continuousInv unop_inv

Depends on / 依赖: continuousInv, isInducing, opHomeomorph, opHomeomorph.symm.isInducing.continuousInv, unop_inv
-/
instance [Inv α] [ContinuousInv α] : ContinuousInv αᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: α] [IsTopologicalGroup α] : IsTopologicalGroup αᵐᵒᵖ where

中文:
实例 [群
  签名: α] [是拓扑群 α] : 是拓扑群 αᵐᵒᵖ where
-/
instance [Group α] [IsTopologicalGroup α] : IsTopologicalGroup αᵐᵒᵖ where

variable (G)

@[to_additive]
/--
theorem `nhds_one_symm` / 定理 `nhds_one_symm`

English:
theorem nhds_one_symm
  statement: comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
  proof: ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]

中文:
定理 nhds_one_symm
  结论: comap 取逆.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
  证明: ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, comap_nhds_eq, congr_arg, inv_one
-/
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]
/--
theorem `nhds_one_symm'` / 定理 `nhds_one_symm'`

English:
theorem nhds_one_symm'
  statement: map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
  proof: ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]

中文:
定理 nhds_one_symm'
  结论: map 取逆.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
  证明: ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, congr_arg, inv_one, map_nhds_eq
-/
theorem nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]
/--
theorem `inv_mem_nhds_one` / 定理 `inv_mem_nhds_one`

English:
theorem inv_mem_nhds_one
  given: {S : Set G} (hS : S in (𝓝 1 : Filter G))
  statement: S⁻¹ in 𝓝 (1 : G)
  proof: by
  rwa [← nhds_one_symm'] at hS

中文:
定理 inv_mem_nhds_one
  条件: {S : 集合 G} (hS : S in (𝓝 1 : 滤子 G))
  结论: S⁻¹ in 𝓝 (1 : G)
  证明: by
  rwa [← nhds_one_symm'] at hS

Depends on / 依赖: nhds_one_symm
-/
theorem inv_mem_nhds_one {S : Set G} (hS : S in (𝓝 1 : Filter G)) : S⁻¹ in 𝓝 (1 : G) := by
  rwa [← nhds_one_symm'] at hS

set_option backward.defeqAttrib.useBackward true in
/-- The map `(x, y) ↦ (x, x * y)` as a homeomorphism. This is a shear mapping. -/
@[to_additive /-- The map `(x, y) ↦ (x, x + y)` as a homeomorphism. This is a shear mapping. -/]
/--
Definition of `Homeomorph.shearMulRight` / `Homeomorph.shearMulRight` 的定义

English:
definition Homeomorph.shearMulRight
  signature: : G × G ≃ₜ G × G
  body: { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with }

@[to_additive (attr := simp)]

中文:
定义 同胚.shearMulRight
  签名: : G × G ≃ₜ G × G
  定义体: { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with }

@[to_additive (attr := simp)]
-/
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with }

@[to_additive (attr := simp)]
/--
theorem `Homeomorph.shearMulRight_coe` / 定理 `Homeomorph.shearMulRight_coe`

English:
theorem Homeomorph.shearMulRight_coe
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 同胚.shearMulRight_coe
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem Homeomorph.shearMulRight_coe :
    ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `Homeomorph.shearMulRight_symm_coe` / 定理 `Homeomorph.shearMulRight_symm_coe`

English:
theorem Homeomorph.shearMulRight_symm_coe
  proof: rfl

中文:
定理 同胚.shearMulRight_symm_coe
  证明: rfl
-/
theorem Homeomorph.shearMulRight_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl

variable {G}

@[to_additive]
/--
theorem `Topology.IsInducing.topologicalGroup` / 定理 `Topology.IsInducing.topologicalGroup`

English:
theorem Topology.IsInducing.topologicalGroup
  statement: {F : Type*} [Group H] [TopologicalSpace H]
  proof: { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }

@[to_additive]

中文:
定理 拓扑.是Inducing.topologicalGroup
  结论: {F : 类型} [群 H] [拓扑空间 H]
  证明: { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }

@[to_additive]
-/
protected theorem Topology.IsInducing.topologicalGroup {F : Type*} [Group H] [TopologicalSpace H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : IsInducing f) : IsTopologicalGroup H :=
  { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }

@[to_additive]
/--
theorem `topologicalGroup_induced` / 定理 `topologicalGroup_induced`

English:
theorem topologicalGroup_induced
  statement: {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
  proof: letI := induced f ‹_›
  IsInducing.topologicalGroup f ⟨rfl⟩

中文:
定理 topologicalGroup_induced
  结论: {F : 类型} [群 H] [函数状 F H G] [幺半群态射类 F H G]
  证明: letI := induced f ‹_›
  IsInducing.topologicalGroup f ⟨rfl⟩

Depends on / 依赖: IsInducing, IsInducing.topologicalGroup, induced, topologicalGroup
-/
theorem topologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
    (f : F) :
    @IsTopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.topologicalGroup f ⟨rfl⟩

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : IsTopologicalGroup S :=
  IsInducing.subtypeVal.topologicalGroup S.subtype

end Subgroup

/-- The (topological-space) closure of a subgroup of a topological group is
itself a subgroup. -/
@[to_additive
  /-- The (topological-space) closure of an additive subgroup of an additive topological group is
  itself an additive subgroup. -/]
/--
Definition of `Subgroup.topologicalClosure` / `Subgroup.topologicalClosure` 的定义

English:
definition Subgroup.topologicalClosure
  signature: (s : Subgroup G)
  body: { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }

@[to_additive (attr := simp)]

中文:
定义 子群.topologicalClosure
  签名: (s : 子群 G)
  定义体: { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_inv, _root_, _root_.closure, carrier, closure, inv_closure, inv_coe_set, inv_mem, mem_inv, s.toSubmonoid.topologicalClosure, toSubmonoid, topologicalClosure
-/
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }

@[to_additive (attr := simp)]
/--
theorem `Subgroup.topologicalClosure_coe` / 定理 `Subgroup.topologicalClosure_coe`

English:
theorem Subgroup.topologicalClosure_coe
  given: {s : Subgroup G}
  proof: rfl

@[to_additive]

中文:
定理 子群.topologicalClosure_coe
  条件: {s : 子群 G}
  证明: rfl

@[to_additive]
-/
theorem Subgroup.topologicalClosure_coe {s : Subgroup G} :
    (s.topologicalClosure : Set G) = _root_.closure s :=
  rfl

@[to_additive]
/--
theorem `Subgroup.le_topologicalClosure` / 定理 `Subgroup.le_topologicalClosure`

English:
theorem Subgroup.le_topologicalClosure
  given: (s : Subgroup G)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

@[to_additive]

中文:
定理 子群.le_topologicalClosure
  条件: (s : 子群 G)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

@[to_additive]

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem Subgroup.le_topologicalClosure (s : Subgroup G) : s <= s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
/--
theorem `Subgroup.isClosed_topologicalClosure` / 定理 `Subgroup.isClosed_topologicalClosure`

English:
theorem Subgroup.isClosed_topologicalClosure
  given: (s : Subgroup G)
  proof: isClosed_closure

@[to_additive]

中文:
定理 子群.isClosed_topologicalClosure
  条件: (s : 子群 G)
  证明: isClosed_closure

@[to_additive]

Depends on / 依赖: isClosed_closure
-/
theorem Subgroup.isClosed_topologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) := isClosed_closure

@[to_additive]
/--
theorem `Subgroup.topologicalClosure_minimal` / 定理 `Subgroup.topologicalClosure_minimal`

English:
theorem Subgroup.topologicalClosure_minimal
  statement: (s : Subgroup G) {t : Subgroup G} (h : s <= t)
  proof: closure_minimal h ht

@[to_additive (attr := gcongr)]

中文:
定理 子群.topologicalClosure_minimal
  结论: (s : 子群 G) {t : 子群 G} (h : s <= t)
  证明: closure_minimal h ht

@[to_additive (attr := gcongr)]

Depends on / 依赖: closure_minimal
-/
theorem Subgroup.topologicalClosure_minimal (s : Subgroup G) {t : Subgroup G} (h : s <= t)
    (ht : IsClosed (t : Set G)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[to_additive (attr := gcongr)]
/--
theorem `Subgroup.topologicalClosure_mono` / 定理 `Subgroup.topologicalClosure_mono`

English:
theorem Subgroup.topologicalClosure_mono
  given: {s t : Subgroup G} (h : s <= t)
  proof: _root_.closure_mono h

@[to_additive]

中文:
定理 子群.topologicalClosure_mono
  条件: {s t : 子群 G} (h : s <= t)
  证明: _root_.closure_mono h

@[to_additive]

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem Subgroup.topologicalClosure_mono {s t : Subgroup G} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

@[to_additive]
/--
theorem `DenseRange.topologicalClosure_map_subgroup` / 定理 `DenseRange.topologicalClosure_map_subgroup`

English:
theorem DenseRange.topologicalClosure_map_subgroup
  statement: [Group H] [TopologicalSpace H]
  proof: by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image hf hs

中文:
定理 DenseRange.topologicalClosure_map_subgroup
  结论: [群 H] [拓扑空间 H]
  证明: by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image hf hs

Depends on / 依赖: SetLike, SetLike.ext, Subgroup, Subgroup.coe_top, Subgroup.topologicalClosure_coe, _iff, coe_top, dense_iff_closure_eq, dense_image, topologicalClosure_coe
-/
theorem DenseRange.topologicalClosure_map_subgroup [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {f : G ->* H} (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G}
    (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image hf hs

/-- The topological closure of a normal subgroup is normal. -/
@[to_additive /-- The topological closure of a normal additive subgroup is normal. -/]
/--
theorem `Subgroup.is_normal_topologicalClosure` / 定理 `Subgroup.is_normal_topologicalClosure`

English:
theorem Subgroup.is_normal_topologicalClosure
  statement: {G : Type*} [TopologicalSpace G] [Group G]
  proof: by
    apply map_mem_closure (IsTopologicalGroup.continuous_conj g) hn
    exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g

@[to_additive]

中文:
定理 子群.is_normal_topologicalClosure
  结论: {G : 类型} [拓扑空间 G] [群 G]
  证明: by
    apply map_mem_closure (IsTopologicalGroup.continuous_conj g) hn
    exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.continuous_conj, Normal, Subgroup, Subgroup.Normal.conj_mem, conj_mem, continuous_conj, map_mem_closure
-/
theorem Subgroup.is_normal_topologicalClosure {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] :
    (Subgroup.topologicalClosure N).Normal where
  conj_mem n hn g := by
    apply map_mem_closure (IsTopologicalGroup.continuous_conj g) hn
    exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g

@[to_additive]
/--
theorem `mul_mem_connectedComponent_one` / 定理 `mul_mem_connectedComponent_one`

English:
theorem mul_mem_connectedComponent_one
  statement: {G : Type*} [TopologicalSpace G] [MulOneClass G]
  proof: by
  rw [connectedComponent_eq hg]
  have hmul : g in connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

@[to_additive]

中文:
定理 mul_mem_connectedComponent_one
  结论: {G : 类型} [拓扑空间 G] [MulOne类 G]
  证明: by
  rw [connectedComponent_eq hg]
  have hmul : g in connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

@[to_additive]

Depends on / 依赖: Continuous, Continuous.image_connectedComponent_subset, connectedComponent, connectedComponent_eq, continuous_const_mul, image_connectedComponent_subset, mem_connectedComponent, mul_one
-/
theorem mul_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g h : G} (hg : g in connectedComponent (1 : G))
    (hh : h in connectedComponent (1 : G)) : g * h in connectedComponent (1 : G) := by
  rw [connectedComponent_eq hg]
  have hmul : g in connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

@[to_additive]
/--
theorem `inv_mem_connectedComponent_one` / 定理 `inv_mem_connectedComponent_one`

English:
theorem inv_mem_connectedComponent_one
  statement: {G : Type*} [TopologicalSpace G] [DivisionMonoid G]
  proof: by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

中文:
定理 inv_mem_connectedComponent_one
  结论: {G : 类型} [拓扑空间 G] [Division幺半群 G]
  证明: by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

Depends on / 依赖: Continuous, Continuous.image_connectedComponent_subset, Set.mem_image, continuous_inv, image_connectedComponent_subset, inv_one, mem_image
-/
theorem inv_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [DivisionMonoid G]
    [ContinuousInv G] {g : G} (hg : g in connectedComponent (1 : G)) :
    g⁻¹ in connectedComponent (1 : G) := by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive /-- The connected component of 0 is a subgroup of `G`. -/]
/--
Definition of `Subgroup.connectedComponentOfOne` / `Subgroup.connectedComponentOfOne` 的定义

English:
definition Subgroup.connectedComponentOfOne
  signature: (G : Type*) [TopologicalSpace G] [Group G]
  body: connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg

中文:
定义 子群.connectedComponentOfOne
  签名: (G : 类型) [拓扑空间 G] [群 G]
  定义体: connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg

Depends on / 依赖: connectedComponent
-/
def Subgroup.connectedComponentOfOne (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg

/-- If a subgroup of a topological group is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
@[to_additive
  /-- If a subgroup of an additive topological group is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/]
/--
Definition of `Subgroup.commGroupTopologicalClosure` / `Subgroup.commGroupTopologicalClosure` 的定义

English:
abbreviation Subgroup.commGroupTopologicalClosure
  signature: [T2Space G] (s : Subgroup G)
  body: { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }

中文:
缩写 子群.commGroupTopologicalClosure
  签名: [T2空间 G] (s : 子群 G)
  定义体: { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }

Depends on / 依赖: commMonoidTopologicalClosure, s.toSubmonoid.commMonoidTopologicalClosure, s.topologicalClosure.toGroup, toGroup, toSubmonoid, topologicalClosure
-/
abbrev Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : forall x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }

variable (G) in
@[to_additive]
/--
lemma `Subgroup.coe_topologicalClosure_bot` / 引理 `Subgroup.coe_topologicalClosure_bot`

English:
lemma Subgroup.coe_topologicalClosure_bot
  proof: by simp

@[to_additive exists_nhds_half_neg]

中文:
引理 子群.coe_topologicalClosure_bot
  证明: by simp

@[to_additive exists_nhds_half_neg]
-/
lemma Subgroup.coe_topologicalClosure_bot :
    ((⊥ : Subgroup G).topologicalClosure : Set G) = _root_.closure ({1} : Set G) := by simp

@[to_additive exists_nhds_half_neg]
/--
theorem `exists_nhds_split_inv` / 定理 `exists_nhds_split_inv`

English:
theorem exists_nhds_split_inv
  given: {s : Set G} (hs : s in 𝓝 (1 : G))
  proof: by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s in 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this

@[to_additive]

中文:
定理 存在_nhds_split_inv
  条件: {s : 集合 G} (hs : s in 𝓝 (1 : G))
  证明: by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s in 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this

@[to_additive]

Depends on / 依赖: continuousAt_fst, continuousAt_fst.mul, continuousAt_snd, continuousAt_snd.inv, div_eq_mul_inv, mem_preimage, mem_prod_self_iff, nhds_prod_eq, prod_subset_iff
-/
theorem exists_nhds_split_inv {s : Set G} (hs : s in 𝓝 (1 : G)) :
    exists V in 𝓝 (1 : G), forall v in V, forall w in V, v / w in s := by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s in 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this

@[to_additive]
/--
theorem `nhds_translation_mul_inv` / 定理 `nhds_translation_mul_inv`

English:
theorem nhds_translation_mul_inv
  given: (x : G)
  statement: comap (· * x⁻¹) (𝓝 1) = 𝓝 x
  proof: ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp

@[to_additive]

中文:
定理 nhds_translation_mul_inv
  条件: (x : G)
  结论: comap (· * x⁻¹) (𝓝 1) = 𝓝 x
  证明: ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, comap_nhds_eq, mulRight
-/
theorem nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x :=
((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp

@[to_additive]
/--
theorem `nhds_translation_inv_mul` / 定理 `nhds_translation_inv_mul`

English:
theorem nhds_translation_inv_mul
  given: (x : G)
  statement: comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x
  proof: ((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp

@[to_additive (attr := simp)]

中文:
定理 nhds_translation_inv_mul
  条件: (x : G)
  结论: comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x
  证明: ((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, comap_nhds_eq, mulLeft
-/
theorem nhds_translation_inv_mul (x : G) : comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x :=
((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp

@[to_additive (attr := simp)]
/--
theorem `map_mul_left_nhds` / 定理 `map_mul_left_nhds`

English:
theorem map_mul_left_nhds
  given: (x y : G)
  statement: map (x * ·) (𝓝 y) = 𝓝 (x * y)
  proof: (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]

中文:
定理 map_mul_left_nhds
  条件: (x y : G)
  结论: map (x * ·) (𝓝 y) = 𝓝 (x * y)
  证明: (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, map_nhds_eq, mulLeft
-/
theorem map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]
/--
theorem `map_mul_left_nhds_one` / 定理 `map_mul_left_nhds_one`

English:
theorem map_mul_left_nhds_one
  given: (x : G)
  statement: map (x * ·) (𝓝 1) = 𝓝 x
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 map_mul_left_nhds_one
  条件: (x : G)
  结论: map (x * ·) (𝓝 1) = 𝓝 x
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x := by simp

@[to_additive (attr := simp)]
/--
theorem `map_mul_right_nhds` / 定理 `map_mul_right_nhds`

English:
theorem map_mul_right_nhds
  given: (x y : G)
  statement: map (· * x) (𝓝 y) = 𝓝 (y * x)
  proof: (Homeomorph.mulRight x).map_nhds_eq y

@[to_additive]

中文:
定理 map_mul_right_nhds
  条件: (x y : G)
  结论: map (· * x) (𝓝 y) = 𝓝 (y * x)
  证明: (Homeomorph.mulRight x).map_nhds_eq y

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, map_nhds_eq, mulRight
-/
theorem map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x) :=
  (Homeomorph.mulRight x).map_nhds_eq y

@[to_additive]
/--
theorem `map_mul_right_nhds_one` / 定理 `map_mul_right_nhds_one`

English:
theorem map_mul_right_nhds_one
  given: (x : G)
  statement: map (· * x) (𝓝 1) = 𝓝 x
  proof: by simp

@[to_additive]

中文:
定理 map_mul_right_nhds_one
  条件: (x : G)
  结论: map (· * x) (𝓝 1) = 𝓝 x
  证明: by simp

@[to_additive]
-/
theorem map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x := by simp

@[to_additive]
/--
theorem `Filter.HasBasis.nhds_of_one` / 定理 `Filter.HasBasis.nhds_of_one`

English:
theorem Filter.HasBasis.nhds_of_one
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set G}
  proof: by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _

@[to_additive]

中文:
定理 滤子.有基.nhds_of_one
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 G}
  证明: by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hb.comap, nhds_translation_mul_inv, simp_rw
-/
theorem Filter.HasBasis.nhds_of_one {ι : Sort*} {p : ι -> Prop} {s : ι -> Set G}
    (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) :
    HasBasis (𝓝 x) p fun i => { y | y / x in s i } := by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _

@[to_additive]
/--
theorem `mem_closure_iff_nhds_one` / 定理 `mem_closure_iff_nhds_one`

English:
theorem mem_closure_iff_nhds_one
  given: {x : G} {s : Set G}
  proof: by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_ofPred, id]

中文:
定理 mem_closure_iff_nhds_one
  条件: {x : G} {s : 集合 G}
  证明: by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_ofPred, id]

Depends on / 依赖: Filter, Set.mem_ofPred, basis_sets, basis_sets.nhds_of_one, mem_closure_iff_nhds_basis, mem_ofPred, nhds_of_one, simp_rw
-/
theorem mem_closure_iff_nhds_one {x : G} {s : Set G} :
    x in closure s ↔ forall U in (𝓝 1 : Filter G), exists y in s, y / x in U := by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_ofPred, id]

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`)
from a topological group to a topological monoid is continuous
provided that it is continuous at one.

This version assumes that `f x → 1` as `x → 1`,
saving a rewrite of `f 1 = 1` compared to `continuous_of_continuousAt_one` in some cases.
See also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero.

  This version assumes that `f x → 0` as `x → 0`,
  saving a rewrite of `f 0 = 0` compared to `continuous_of_continuousAt_zero` in some cases.
  See also `uniformContinuous_of_continuousAt_zero`. -/]
/--
theorem `continuous_of_tendsto_nhds_one` / 定理 `continuous_of_tendsto_nhds_one`

English:
theorem continuous_of_tendsto_nhds_one
  statement: {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
  proof: continuous_iff_continuousAt.2 fun x => by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, Function.comp_def,
      map_mul, mul_one] using hf.const_mul (f x)

中文:
定理 continuous_of_tendsto_nhds_one
  结论: {M hom : 类型} [MulOne类 M] [拓扑空间 M]
  证明: continuous_iff_continuousAt.2 fun x => by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, Function.comp_def,
      map_mul, mul_one] using hf.const_mul (f x)

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, _iff, comp_def, const_mul, continuous_iff_continuousAt, hf.const_mul, map_mul, map_mul_left_nhds_one, mul_one, tendsto_map
-/
theorem continuous_of_tendsto_nhds_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : Tendsto f (𝓝 1) (𝓝 1)) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x => by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, Function.comp_def,
      map_mul, mul_one] using hf.const_mul (f x)

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero. See also
  `uniformContinuous_of_continuousAt_zero`. -/]
/--
theorem `continuous_of_continuousAt_one` / 定理 `continuous_of_continuousAt_one`

English:
theorem continuous_of_continuousAt_one
  statement: {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
  proof: continuous_of_tendsto_nhds_one f by simpa using hf.tendsto

@[to_additive continuous_of_continuousAt_zero₂]

中文:
定理 continuous_of_continuousAt_one
  结论: {M hom : 类型} [MulOne类 M] [拓扑空间 M]
  证明: continuous_of_tendsto_nhds_one f by simpa using hf.tendsto

@[to_additive continuous_of_continuousAt_zero₂]

Depends on / 依赖: continuous_of_tendsto_nhds_one, hf.tendsto, tendsto
-/
theorem continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : ContinuousAt f 1) :
    Continuous f :=
continuous_of_tendsto_nhds_one f by simpa using hf.tendsto

@[to_additive continuous_of_continuousAt_zero₂]
/--
theorem `continuous_of_continuousAt_one₂` / 定理 `continuous_of_continuousAt_one₂`

English:
theorem continuous_of_continuousAt_one₂
  statement: {H M : Type*} [CommMonoid M] [TopologicalSpace M]
  proof: continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, Function.comp_def, map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]

中文:
定理 continuous_of_continuousAt_one₂
  结论: {H M : 类型} [交换幺半群 M] [拓扑空间 M]
  证明: continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, Function.comp_def, map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, MonoidHom, MonoidHom.mul_apply, MonoidHom.one_apply, _iff, comp_def, continuous_iff_continuousAt, le_of_eq, map_mul, map_mul_left_nhds_one, map_one, mono_right, mul_apply, mul_one, nhds_prod_eq, one_apply, prod_map_map_eq, tendsto_const_nhds
-/
theorem continuous_of_continuousAt_one₂ {H M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G ->* H ->* M)
    (hf : ContinuousAt (fun x : G × H => f x.1 x.2) (1, 1))
    (hl : forall x, ContinuousAt (f x) 1) (hr : forall y, ContinuousAt (f · y) 1) :
    Continuous (fun x : G × H => f x.1 x.2) := continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, Function.comp_def, map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]
/--
lemma `IsTopologicalGroup.isInducing_iff_nhds_one` / 引理 `IsTopologicalGroup.isInducing_iff_nhds_one`

English:
lemma IsTopologicalGroup.isInducing_iff_nhds_one
  proof: by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x => ?_⟩
  rw [← nhds_translation_mul_inv]; rw [← nhds_translation_mul_inv (f x)]; rw [Filter.comap_comap]; rw [hf]; rw [Filter.comap_comap]
  congr 1
  ext; simp

@[to_additive]

中文:
引理 是拓扑群.isInducing_iff_nhds_one
  证明: by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x => ?_⟩
  rw [← nhds_translation_mul_inv]; rw [← nhds_translation_mul_inv (f x)]; rw [Filter.comap_comap]; rw [hf]; rw [Filter.comap_comap]
  congr 1
  ext; simp

@[to_additive]

Depends on / 依赖: Filter, Filter.comap_comap, Topology, Topology.isInducing_iff_nhds, comap_comap, isInducing_iff_nhds, map_one, nhds_translation_mul_inv
-/
lemma IsTopologicalGroup.isInducing_iff_nhds_one
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {F : Type*}
    [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    Topology.IsInducing f ↔ 𝓝 (1 : G) = (𝓝 (1 : H)).comap f := by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x => ?_⟩
  rw [← nhds_translation_mul_inv]; rw [← nhds_translation_mul_inv (f x)]; rw [Filter.comap_comap]; rw [hf]; rw [Filter.comap_comap]
  congr 1
  ext; simp

@[to_additive]
/--
lemma `IsTopologicalGroup.isOpenMap_iff_nhds_one` / 引理 `IsTopologicalGroup.isOpenMap_iff_nhds_one`

English:
lemma IsTopologicalGroup.isOpenMap_iff_nhds_one
  proof: by
  refine ⟨fun H => map_one f ▸ H.nhds_le 1, fun h => IsOpenMap.of_nhds_le fun x => ?_⟩
  have : Filter.map (f x * ·) (𝓝 1) = 𝓝 (f x) := by
    simpa [-Homeomorph.map_nhds_eq, Units.smul_def] using!
      (Homeomorph.smul ((toUnits x).map (MonoidHomClass.toMonoidHom f))).map_nhds_eq (1 : H)
  rw [← map_mul_left_nhds_one x]; rw [Filter.map_map]; rw [Function.comp_def]; rw [← this]
  refine (Filter.map_mono h).trans ?_
  simp [Function.comp_def]

中文:
引理 是拓扑群.isOpenMap_iff_nhds_one
  证明: by
  refine ⟨fun H => map_one f ▸ H.nhds_le 1, fun h => IsOpenMap.of_nhds_le fun x => ?_⟩
  have : Filter.map (f x * ·) (𝓝 1) = 𝓝 (f x) := by
    simpa [-Homeomorph.map_nhds_eq, Units.smul_def] using!
      (Homeomorph.smul ((toUnits x).map (MonoidHomClass.toMonoidHom f))).map_nhds_eq (1 : H)
  rw [← map_mul_left_nhds_one x]; rw [Filter.map_map]; rw [Function.comp_def]; rw [← this]
  refine (Filter.map_mono h).trans ?_
  simp [Function.comp_def]

Depends on / 依赖: Filter, Filter.map, Filter.map_map, Filter.map_mono, Function, Function.comp_def, H.nhds_le, Homeomorph, Homeomorph.map_nhds_eq, Homeomorph.smul, IsOpenMap, IsOpenMap.of_nhds_le, MonoidHomClass, MonoidHomClass.toMonoidHom, Units.smul_def, comp_def, map_map, map_mono, map_mul_left_nhds_one, map_nhds_eq
-/
lemma IsTopologicalGroup.isOpenMap_iff_nhds_one
    {H : Type*} [Monoid H] [TopologicalSpace H] [ContinuousConstSMul H H]
    {F : Type*} [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    IsOpenMap f ↔ 𝓝 1 <= .map f (𝓝 1) := by
  refine ⟨fun H => map_one f ▸ H.nhds_le 1, fun h => IsOpenMap.of_nhds_le fun x => ?_⟩
  have : Filter.map (f x * ·) (𝓝 1) = 𝓝 (f x) := by
    simpa [-Homeomorph.map_nhds_eq, Units.smul_def] using!
      (Homeomorph.smul ((toUnits x).map (MonoidHomClass.toMonoidHom f))).map_nhds_eq (1 : H)
  rw [← map_mul_left_nhds_one x]; rw [Filter.map_map]; rw [Function.comp_def]; rw [← this]
  refine (Filter.map_mono h).trans ?_
  simp [Function.comp_def]

-- TODO: unify with `QuotientGroup.isOpenQuotientMap_mk`
/-- Let `A` and `B` be topological groups, and let `φ : A → B` be a continuous surjective group
homomorphism. Assume furthermore that `φ` is a quotient map (i.e., `V ⊆ B`
is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an open map. -/
@[to_additive /-- Let `A` and `B` be topological additive groups, and let `φ : A → B` be a
continuous surjective additive group homomorphism. Assume furthermore that `φ` is a quotient map
(i.e., `V ⊆ B` is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an
open map. -/]
/--
lemma `MonoidHom.isOpenQuotientMap_of_isQuotientMap` / 引理 `MonoidHom.isOpenQuotientMap_of_isQuotientMap`

English:
lemma MonoidHom.isOpenQuotientMap_of_isQuotientMap
  statement: {A : Type*} [Group A]
  proof: hφ.surjective
    continuous := hφ.continuous
    isOpenMap := by
      -- We need to check that if `U ⊆ A` is open then `φ⁻¹ (φ U)` is open.
      intro U hU
      rw [← hφ.isOpen_preimage]
      -- It suffices to show that `φ⁻¹ (φ U) = ⋃ (U * k⁻¹)` as `k` runs through the kernel of `φ`,
      -- as `U * k⁻¹` is open because `x ↦ x * k` is continuous.
      -- Remark: here is where we use that we have groups not monoids (you cannot avoid
      -- using both `k` and `k⁻¹` at this point).
      suffices ⇑φ ⁻¹' ⇑φ '' U = ⋃ k in ker (φ : A ->* B), (fun x => x * k) ⁻¹' U by
        exact this ▸ isOpen_biUnion (fun k _ => Continuous.isOpen_preimage (by fun_prop) _ hU)
      ext x
      -- But this is an elementary calculation.
      constructor
      · rintro ⟨y, hyU, hyx⟩
        apply Set.mem_iUnion_of_mem (x⁻¹ * y)
        simp_all
      · rintro ⟨_, ⟨k, rfl⟩, _, ⟨(hk : φ k = 1), rfl⟩, hx⟩
        use x * k, hx
        rw [map_mul]; rw [hk]; rw [mul_one]

@[to_additive]

中文:
引理 幺半群态射.isOpenQuotientMap_of_isQuotientMap
  结论: {A : 类型} [群 A]
  证明: hφ.surjective
    continuous := hφ.continuous
    isOpenMap := by
      -- We need to check that if `U ⊆ A` is open then `φ⁻¹ (φ U)` is open.
      intro U hU
      rw [← hφ.isOpen_preimage]
      -- It suffices to show that `φ⁻¹ (φ U) = ⋃ (U * k⁻¹)` as `k` runs through the kernel of `φ`,
      -- as `U * k⁻¹` is open because `x ↦ x * k` is continuous.
      -- Remark: here is where we use that we have groups not monoids (you cannot avoid
      -- using both `k` and `k⁻¹` at this point).
      suffices ⇑φ ⁻¹' ⇑φ '' U = ⋃ k in ker (φ : A ->* B), (fun x => x * k) ⁻¹' U by
        exact this ▸ isOpen_biUnion (fun k _ => Continuous.isOpen_preimage (by fun_prop) _ hU)
      ext x
      -- But this is an elementary calculation.
      constructor
      · rintro ⟨y, hyU, hyx⟩
        apply Set.mem_iUnion_of_mem (x⁻¹ * y)
        simp_all
      · rintro ⟨_, ⟨k, rfl⟩, _, ⟨(hk : φ k = 1), rfl⟩, hx⟩
        use x * k, hx
        rw [map_mul]; rw [hk]; rw [mul_one]

@[to_additive]

Depends on / 依赖: surjective
-/
lemma MonoidHom.isOpenQuotientMap_of_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F}
    (hφ : IsQuotientMap φ) : IsOpenQuotientMap φ where
    surjective := hφ.surjective
    continuous := hφ.continuous
    isOpenMap := by
      -- We need to check that if `U ⊆ A` is open then `φ⁻¹ (φ U)` is open.
      intro U hU
      rw [← hφ.isOpen_preimage]
      -- It suffices to show that `φ⁻¹ (φ U) = ⋃ (U * k⁻¹)` as `k` runs through the kernel of `φ`,
      -- as `U * k⁻¹` is open because `x ↦ x * k` is continuous.
      -- Remark: here is where we use that we have groups not monoids (you cannot avoid
      -- using both `k` and `k⁻¹` at this point).
      suffices ⇑φ ⁻¹' ⇑φ '' U = ⋃ k in ker (φ : A ->* B), (fun x => x * k) ⁻¹' U by
        exact this ▸ isOpen_biUnion (fun k _ => Continuous.isOpen_preimage (by fun_prop) _ hU)
      ext x
      -- But this is an elementary calculation.
      constructor
      · rintro ⟨y, hyU, hyx⟩
        apply Set.mem_iUnion_of_mem (x⁻¹ * y)
        simp_all
      · rintro ⟨_, ⟨k, rfl⟩, _, ⟨(hk : φ k = 1), rfl⟩, hx⟩
        use x * k, hx
        rw [map_mul]; rw [hk]; rw [mul_one]

@[to_additive]
/--
lemma `MonoidHom.isOpenQuotientMap_iff_isQuotientMap` / 引理 `MonoidHom.isOpenQuotientMap_iff_isQuotientMap`

English:
lemma MonoidHom.isOpenQuotientMap_iff_isQuotientMap
  statement: {A : Type*} [Group A]
  proof: ⟨fun hf => hf.isQuotientMap, MonoidHom.isOpenQuotientMap_of_isQuotientMap⟩

@[to_additive]

中文:
引理 幺半群态射.isOpenQuotientMap_iff_isQuotientMap
  结论: {A : 类型} [群 A]
  证明: ⟨fun hf => hf.isQuotientMap, MonoidHom.isOpenQuotientMap_of_isQuotientMap⟩

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.isOpenQuotientMap_of_isQuotientMap, hf.isQuotientMap, isOpenQuotientMap_of_isQuotientMap, isQuotientMap
-/
lemma MonoidHom.isOpenQuotientMap_iff_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F} :
    IsOpenQuotientMap φ ↔ IsQuotientMap φ :=
  ⟨fun hf => hf.isQuotientMap, MonoidHom.isOpenQuotientMap_of_isQuotientMap⟩

@[to_additive]
/--
theorem `IsTopologicalGroup.ext` / 定理 `IsTopologicalGroup.ext`

English:
theorem IsTopologicalGroup.ext
  statement: {G : Type*} [Group G] {t t' : TopologicalSpace G}
  proof: TopologicalSpace.ext_nhds fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x]; rw [← @nhds_translation_mul_inv G t' _ _ x]; rw [← h]

@[to_additive]

中文:
定理 是拓扑群.ext
  结论: {G : 类型} [群 G] {t t' : 拓扑空间 G}
  证明: TopologicalSpace.ext_nhds fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x]; rw [← @nhds_translation_mul_inv G t' _ _ x]; rw [← h]

@[to_additive]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext_nhds, ext_nhds, nhds_translation_mul_inv
-/
theorem IsTopologicalGroup.ext {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  TopologicalSpace.ext_nhds fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x]; rw [← @nhds_translation_mul_inv G t' _ _ x]; rw [← h]

@[to_additive]
/--
theorem `IsTopologicalGroup.ext_iff` / 定理 `IsTopologicalGroup.ext_iff`

English:
theorem IsTopologicalGroup.ext_iff
  statement: {G : Type*} [Group G] {t t' : TopologicalSpace G}
  proof: ⟨fun h => h ▸ rfl, tg.ext tg'⟩

@[to_additive]

中文:
定理 是拓扑群.ext_iff
  结论: {G : 类型} [群 G] {t t' : 拓扑空间 G}
  证明: ⟨fun h => h ▸ rfl, tg.ext tg'⟩

@[to_additive]

Depends on / 依赖: tg.ext
-/
theorem IsTopologicalGroup.ext_iff {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩

@[to_additive]
/--
theorem `ContinuousInv.of_nhds_one` / 定理 `ContinuousInv.of_nhds_one`

English:
theorem ContinuousInv.of_nhds_one
  statement: {G : Type*} [Group G] [TopologicalSpace G]
  proof: by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, Function.comp_def, mul_assoc,
    mul_inv_rev, inv_mul_cancel_left] using this

@[to_additive]

中文:
定理 连续取逆.of_nhds_one
  结论: {G : 类型} [群 G] [拓扑空间 G]
  证明: by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, Function.comp_def, mul_assoc,
    mul_inv_rev, inv_mul_cancel_left] using this

@[to_additive]

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, Tendsto, _iff, comp_def, continuous_iff_continuousAt, inv_mul_cancel_left, mul_assoc, mul_inv_rev, tendsto_map, tendsto_map.comp
-/
theorem ContinuousInv.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : forall x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : forall x₀ : G, Tendsto (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G := by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, Function.comp_def, mul_assoc,
    mul_inv_rev, inv_mul_cancel_left] using this

@[to_additive]
/--
theorem `IsTopologicalGroup.of_nhds_one'` / 定理 `IsTopologicalGroup.of_nhds_one'`

English:
theorem IsTopologicalGroup.of_nhds_one'
  statement: {G : Type u} [Group G] [TopologicalSpace G]
  proof: { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl]; rw [←
              map_map]; rw [← hleft]; rw [hright]; rw [map_map]
            simp) }

@[to_additive]

中文:
定理 是拓扑群.of_nhds_one'
  结论: {G : 类型u} [群 G] [拓扑空间 G]
  证明: { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl]; rw [←
              map_map]; rw [← hleft]; rw [hright]; rw [map_map]
            simp) }

@[to_additive]

Depends on / 依赖: ContinuousInv, ContinuousInv.of_nhds_one, ContinuousMul, ContinuousMul.of_nhds_one, hright, le_of_eq, map_map, of_nhds_one, toContinuousInv, toContinuousMul
-/
theorem IsTopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : forall x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : forall x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : IsTopologicalGroup G :=
  { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl]; rw [←
              map_map]; rw [← hleft]; rw [hright]; rw [map_map]
            simp) }

@[to_additive]
/--
theorem `IsTopologicalGroup.of_nhds_one` / 定理 `IsTopologicalGroup.of_nhds_one`

English:
theorem IsTopologicalGroup.of_nhds_one
  statement: {G : Type u} [Group G] [TopologicalSpace G]
  proof: by
  refine IsTopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : forall x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [Function.comp_def] using hleft _

@[to_additive]

中文:
定理 是拓扑群.of_nhds_one
  结论: {G : 类型u} [群 G] [拓扑空间 G]
  证明: by
  refine IsTopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : forall x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [Function.comp_def] using hleft _

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, IsTopologicalGroup, IsTopologicalGroup.of_nhds_one, comp_def, map_eq_of_inverse, mul_assoc, of_nhds_one, replace
-/
theorem IsTopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : forall x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1))
    (hconj : forall x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)) : IsTopologicalGroup G := by
  refine IsTopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : forall x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [Function.comp_def] using hleft _

@[to_additive]
/--
theorem `IsTopologicalGroup.of_comm_of_nhds_one` / 定理 `IsTopologicalGroup.of_comm_of_nhds_one`

English:
theorem IsTopologicalGroup.of_comm_of_nhds_one
  statement: {G : Type u} [CommGroup G] [TopologicalSpace G]
  proof: IsTopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using! tendsto_id)

中文:
定理 是拓扑群.of_comm_of_nhds_one
  结论: {G : 类型u} [交换群 G] [拓扑空间 G]
  证明: IsTopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using! tendsto_id)

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.of_nhds_one, of_nhds_one, tendsto_id
-/
theorem IsTopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : forall x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1)) : IsTopologicalGroup G :=
  IsTopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using! tendsto_id)

variable (G) in
/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → Set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`QuotientGroup.completeSpace_right`. -/
@[to_additive
  /-- Any first countable topological additive group has an antitone neighborhood basis
  `u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`.
  The existence of such a neighborhood basis is a key tool
  for `QuotientAddGroup.completeSpace_right`. -/]
/--
theorem `IsTopologicalGroup.exists_antitone_basis_nhds_one` / 定理 `IsTopologicalGroup.exists_antitone_basis_nhds_one`

English:
theorem IsTopologicalGroup.exists_antitone_basis_nhds_one
  given: [FirstCountableTopology G]
  proof: by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, Prod.exists,
    forall_true_left] at this
  have event_mul : forall n : Nat, forallᶠ m in atTop, u m * u m subseteq u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩

中文:
定理 是拓扑群.存在_antitone_basis_nhds_one
  条件: [第一可数拓扑 G]
  证明: by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, Prod.exists,
    forall_true_left] at this
  have event_mul : forall n : Nat, forallᶠ m in atTop, u m * u m subseteq u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩

Depends on / 依赖: Prod.exists, Prod.forall, True.intro, and_imp, and_self_iff, atTop_basis, atTop_basis.eventually_iff.mpr, continuous_mul, continuous_mul.tendsto, event_mul, eventually_iff, exists_antitone_basis, forall_true_left, hu.prod_nhds, mem_prod, mul_one, prod_nhds, subseteq, tendsto, tendsto_iff
-/
theorem IsTopologicalGroup.exists_antitone_basis_nhds_one [FirstCountableTopology G] :
    exists u : Nat -> Set G, (𝓝 1).HasAntitoneBasis u ∧ forall n, u (n + 1) * u (n + 1) subseteq u n := by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, Prod.exists,
    forall_true_left] at this
  have event_mul : forall n : Nat, forallᶠ m in atTop, u m * u m subseteq u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩

end IsTopologicalGroup

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub_const]
/--
theorem `Filter.Tendsto.div_const'` / 定理 `Filter.Tendsto.div_const'`

English:
theorem Filter.Tendsto.div_const'
  statement: {c : G} {f : α -> G} {l : Filter α} (h : Tendsto f l (𝓝 c))
  proof: h.div' tendsto_const_nhds

中文:
定理 滤子.收敛.div_const'
  结论: {c : G} {f : α -> G} {l : 滤子 α} (h : 收敛 f l (𝓝 c))
  证明: h.div' tendsto_const_nhds

Depends on / 依赖: h.div, tendsto_const_nhds
-/
theorem Filter.Tendsto.div_const' {c : G} {f : α -> G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (f · / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds

/--
lemma `Filter.tendsto_div_const_iff` / 引理 `Filter.tendsto_div_const_iff`

English:
lemma Filter.tendsto_div_const_iff
  statement: {G : Type*}
  proof: by
  refine ⟨fun h => ?_, fun h => Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel₀ hb, div_one]

@[to_additive tendsto_sub_const_iff]

中文:
引理 滤子.tendsto_div_const_iff
  结论: {G : 类型}
  证明: by
  refine ⟨fun h => ?_, fun h => Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel₀ hb, div_one]

@[to_additive tendsto_sub_const_iff]

Depends on / 依赖: Filter, Filter.Tendsto.div_const, Tendsto, convert, div_const, div_mul_eq_div_div_swap, div_one, h.div_const
-/
lemma Filter.tendsto_div_const_iff {G : Type*}
    [GroupWithZero G] [TopologicalSpace G] [ContinuousDiv G]
    {b : G} (hb : b != 0) {c : G} {f : α -> G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h => ?_, fun h => Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel₀ hb, div_one]

@[to_additive tendsto_sub_const_iff]
/--
lemma `Filter.tendsto_div_const_iff'` / 引理 `Filter.tendsto_div_const_iff'`

English:
lemma Filter.tendsto_div_const_iff'
  statement: {G : Type*}
  proof: by
  refine ⟨fun h => ?_, fun h => Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel, div_one]

@[to_additive const_sub]

中文:
引理 滤子.tendsto_div_const_iff'
  结论: {G : 类型}
  证明: by
  refine ⟨fun h => ?_, fun h => Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel, div_one]

@[to_additive const_sub]

Depends on / 依赖: Filter, Filter.Tendsto.div_const, Tendsto, convert, div_const, div_mul_eq_div_div_swap, div_one, h.div_const, inv_mul_cancel
-/
lemma Filter.tendsto_div_const_iff' {G : Type*}
    [TopologicalSpace G] [Group G] [ContinuousDiv G]
    (b : G) {c : G} {f : α -> G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h => ?_, fun h => Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel, div_one]

@[to_additive const_sub]
/--
theorem `Filter.Tendsto.const_div'` / 定理 `Filter.Tendsto.const_div'`

English:
theorem Filter.Tendsto.const_div'
  statement: (b : G) {c : G} {f : α -> G} {l : Filter α}
  proof: tendsto_const_nhds.div' h

@[to_additive (attr := continuity) continuous_sub_left]

中文:
定理 滤子.收敛.const_div'
  结论: (b : G) {c : G} {f : α -> G} {l : 滤子 α}
  证明: tendsto_const_nhds.div' h

@[to_additive (attr := continuity) continuous_sub_left]

Depends on / 依赖: tendsto_const_nhds, tendsto_const_nhds.div
-/
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α -> G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (b / f ·) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h

@[to_additive (attr := continuity) continuous_sub_left]
/--
lemma `continuous_div_left'` / 引理 `continuous_div_left'`

English:
lemma continuous_div_left'
  given: (a : G)
  statement: Continuous (a / ·)
  proof: by fun_prop

@[to_additive (attr := continuity) continuous_sub_right]

中文:
引理 continuous_div_left'
  条件: (a : G)
  结论: 连续 (a / ·)
  证明: by fun_prop

@[to_additive (attr := continuity) continuous_sub_right]

Depends on / 依赖: fun_prop
-/
lemma continuous_div_left' (a : G) : Continuous (a / ·) := by fun_prop

@[to_additive (attr := continuity) continuous_sub_right]
/--
lemma `continuous_div_right'` / 引理 `continuous_div_right'`

English:
lemma continuous_div_right'
  given: (a : G)
  statement: Continuous (· / a)
  proof: by fun_prop

中文:
引理 continuous_div_right'
  条件: (a : G)
  结论: 连续 (· / a)
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
lemma continuous_div_right' (a : G) : Continuous (· / a) := by fun_prop

end ContinuousDiv

section DivInvTopologicalGroup

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive tendsto_const_sub_iff]
/--
lemma `Filter.tendsto_const_div_iff'` / 引理 `Filter.tendsto_const_div_iff'`

English:
lemma Filter.tendsto_const_div_iff'
  given: (b : G) {c : G} {f : α -> G} {l : Filter α}
  proof: by
  refine ⟨fun h => ?_, Filter.Tendsto.const_div' b⟩
  convert! h.inv.mul_const b with k <;> rw [inv_div, div_mul_cancel]

@[deprecated (since := "2026-02-03")]
alias Filter.tendsto_const_div_iff := Filter.tendsto_const_div_iff'

中文:
引理 滤子.tendsto_const_div_iff'
  条件: (b : G) {c : G} {f : α -> G} {l : 滤子 α}
  证明: by
  refine ⟨fun h => ?_, Filter.Tendsto.const_div' b⟩
  convert! h.inv.mul_const b with k <;> rw [inv_div, div_mul_cancel]

@[deprecated (since := "2026-02-03")]
alias Filter.tendsto_const_div_iff := Filter.tendsto_const_div_iff'

Depends on / 依赖: Filter, Filter.Tendsto.const_div, Tendsto, const_div, convert, div_mul_cancel, h.inv.mul_const, inv_div, mul_const
-/
lemma Filter.tendsto_const_div_iff' (b : G) {c : G} {f : α -> G} {l : Filter α} :
    Tendsto (fun k : α => b / f k) l (𝓝 (b / c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h => ?_, Filter.Tendsto.const_div' b⟩
  convert! h.inv.mul_const b with k <;> rw [inv_div, div_mul_cancel]

@[deprecated (since := "2026-02-03")]
alias Filter.tendsto_const_div_iff := Filter.tendsto_const_div_iff'

/-- A version of `Homeomorph.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addLeft a (-b)` that is defeq to `a - b`. -/]
/--
Definition of `Homeomorph.divLeft` / `Homeomorph.divLeft` 的定义

English:
definition Homeomorph.divLeft
  signature: (x : G)
  body: { Equiv.divLeft x with }

@[to_additive (attr := simp)]

中文:
定义 同胚.divLeft
  签名: (x : G)
  定义体: { Equiv.divLeft x with }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.divLeft, divLeft
-/
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with }

@[to_additive (attr := simp)]
/--
theorem `Homeomorph.coe_divLeft` / 定理 `Homeomorph.coe_divLeft`

English:
theorem Homeomorph.coe_divLeft
  given: (a : G)
  statement: ⇑(Homeomorph.divLeft a) = (a / ·)
  proof: rfl

@[to_additive]

中文:
定理 同胚.coe_divLeft
  条件: (a : G)
  结论: ⇑(同胚.divLeft a) = (a / ·)
  证明: rfl

@[to_additive]
-/
theorem Homeomorph.coe_divLeft (a : G) : ⇑(Homeomorph.divLeft a) = (a / ·) :=
  rfl

@[to_additive]
/--
theorem `isOpenMap_div_left` / 定理 `isOpenMap_div_left`

English:
theorem isOpenMap_div_left
  given: (a : G)
  statement: IsOpenMap (a / ·)
  proof: (Homeomorph.divLeft _).isOpenMap

@[to_additive]

中文:
定理 isOpenMap_div_left
  条件: (a : G)
  结论: 是开映射 (a / ·)
  证明: (Homeomorph.divLeft _).isOpenMap

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.divLeft, divLeft, isOpenMap
-/
theorem isOpenMap_div_left (a : G) : IsOpenMap (a / ·) :=
  (Homeomorph.divLeft _).isOpenMap

@[to_additive]
/--
theorem `isClosedMap_div_left` / 定理 `isClosedMap_div_left`

English:
theorem isClosedMap_div_left
  given: (a : G)
  statement: IsClosedMap (a / ·)
  proof: (Homeomorph.divLeft _).isClosedMap

中文:
定理 isClosedMap_div_left
  条件: (a : G)
  结论: 是闭映射 (a / ·)
  证明: (Homeomorph.divLeft _).isClosedMap

Depends on / 依赖: Homeomorph, Homeomorph.divLeft, divLeft, isClosedMap
-/
theorem isClosedMap_div_left (a : G) : IsClosedMap (a / ·) :=
  (Homeomorph.divLeft _).isClosedMap

/-- A version of `Homeomorph.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addRight (-a) b` that is defeq to `b - a`. -/]
/--
Definition of `Homeomorph.divRight` / `Homeomorph.divRight` 的定义

English:
definition Homeomorph.divRight
  signature: (x : G)
  body: { Equiv.divRight x with }

@[to_additive (attr := simp)]

中文:
定义 同胚.divRight
  签名: (x : G)
  定义体: { Equiv.divRight x with }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.divRight, divRight
-/
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with }

@[to_additive (attr := simp)]
/--
theorem `Homeomorph.coe_divRight` / 定理 `Homeomorph.coe_divRight`

English:
theorem Homeomorph.coe_divRight
  given: (a : G)
  statement: ⇑(Homeomorph.divRight a) = (· / a)
  proof: rfl

@[to_additive]

中文:
定理 同胚.coe_divRight
  条件: (a : G)
  结论: ⇑(同胚.divRight a) = (· / a)
  证明: rfl

@[to_additive]
-/
theorem Homeomorph.coe_divRight (a : G) : ⇑(Homeomorph.divRight a) = (· / a) :=
  rfl

@[to_additive]
/--
lemma `isOpenMap_div_right` / 引理 `isOpenMap_div_right`

English:
lemma isOpenMap_div_right
  given: (a : G)
  statement: IsOpenMap (· / a)
  proof: (Homeomorph.divRight a).isOpenMap

@[to_additive]

中文:
引理 isOpenMap_div_right
  条件: (a : G)
  结论: 是开映射 (· / a)
  证明: (Homeomorph.divRight a).isOpenMap

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.divRight, divRight, isOpenMap
-/
lemma isOpenMap_div_right (a : G) : IsOpenMap (· / a) := (Homeomorph.divRight a).isOpenMap

@[to_additive]
/--
lemma `isClosedMap_div_right` / 引理 `isClosedMap_div_right`

English:
lemma isClosedMap_div_right
  given: (a : G)
  statement: IsClosedMap (· / a)
  proof: (Homeomorph.divRight a).isClosedMap

@[to_additive]

中文:
引理 isClosedMap_div_right
  条件: (a : G)
  结论: 是闭映射 (· / a)
  证明: (Homeomorph.divRight a).isClosedMap

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.divRight, divRight, isClosedMap
-/
lemma isClosedMap_div_right (a : G) : IsClosedMap (· / a) := (Homeomorph.divRight a).isClosedMap

@[to_additive]
/--
theorem `tendsto_div_nhds_one_iff` / 定理 `tendsto_div_nhds_one_iff`

English:
theorem tendsto_div_nhds_one_iff
  given: {α : Type*} {l : Filter α} {x : G} {u : α -> G}
  proof: haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩

中文:
定理 tendsto_div_nhds_one_iff
  条件: {α : 类型} {l : 滤子 α} {x : G} {u : α -> G}
  证明: haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩

Depends on / 依赖: Tendsto, h.div, h.mul, tendsto_const_nhds
-/
theorem tendsto_div_nhds_one_iff {α : Type*} {l : Filter α} {x : G} {u : α -> G} :
    Tendsto (u · / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩

/-- If `f → a` and `g → b` along a nontrivial filter on the domain, valued in a
Hausdorff topological group, then `f / g → 1` if and only if `a = b`. -/
@[to_additive]
/--
theorem `tendsto_div_nhds_one_iff_eq` / 定理 `tendsto_div_nhds_one_iff_eq`

English:
theorem tendsto_div_nhds_one_iff_eq
  statement: {α : Type*} {l : Filter α} [l.NeBot] [T2Space G]
  proof: ⟨fun hfg => tendsto_nhds_unique hf by simpa using hfg.mul hg,
   fun h => by subst h; simpa using hf.div' hg⟩

@[to_additive]
alias ⟨eq_of_tendsto_div_nhds_one, _⟩ := tendsto_div_nhds_one_iff_eq

@[to_additive]

中文:
定理 tendsto_div_nhds_one_iff_eq
  结论: {α : 类型} {l : 滤子 α} [l.NeBot] [T2空间 G]
  证明: ⟨fun hfg => tendsto_nhds_unique hf by simpa using hfg.mul hg,
   fun h => by subst h; simpa using hf.div' hg⟩

@[to_additive]
alias ⟨eq_of_tendsto_div_nhds_one, _⟩ := tendsto_div_nhds_one_iff_eq

@[to_additive]

Depends on / 依赖: hf.div, hfg.mul, tendsto_nhds_unique
-/
theorem tendsto_div_nhds_one_iff_eq {α : Type*} {l : Filter α} [l.NeBot] [T2Space G]
    {f g : α -> G} {a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => f x / g x) l (𝓝 1) ↔ a = b :=
⟨fun hfg => tendsto_nhds_unique hf by simpa using hfg.mul hg,
   fun h => by subst h; simpa using hf.div' hg⟩

@[to_additive]
alias ⟨eq_of_tendsto_div_nhds_one, _⟩ := tendsto_div_nhds_one_iff_eq

@[to_additive]
/--
theorem `nhds_translation_div` / 定理 `nhds_translation_div`

English:
theorem nhds_translation_div
  given: (x : G)
  statement: comap (· / x) (𝓝 1) = 𝓝 x
  proof: by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

中文:
定理 nhds_translation_div
  条件: (x : G)
  结论: comap (· / x) (𝓝 1) = 𝓝 x
  证明: by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

Depends on / 依赖: div_eq_mul_inv, nhds_translation_mul_inv
-/
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

variable [TopologicalSpace H] [CommGroup H] [IsTopologicalGroup H]
  [PartialOrder H] [IsOrderedMonoid H]

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divRight_nhdsGT` / 定理 `Filter.map_divRight_nhdsGT`

English:
theorem Filter.map_divRight_nhdsGT
  given: {c a : H}
  statement: map (· / c) (𝓝[>] a) = 𝓝[>] (a / c)
  proof: by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divRight_nhdsGT
  条件: {c a : H}
  结论: map (· / c) (𝓝[>] a) = 𝓝[>] (a / c)
  证明: by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divRight, convert, divRight, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.map_divRight_nhdsGT {c a : H} : map (· / c) (𝓝[>] a) = 𝓝[>] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divRight_nhdsLT` / 定理 `Filter.map_divRight_nhdsLT`

English:
theorem Filter.map_divRight_nhdsLT
  given: {c a : H}
  statement: map (· / c) (𝓝[<] a) = 𝓝[<] (a / c)
  proof: by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divRight_nhdsLT
  条件: {c a : H}
  结论: map (· / c) (𝓝[<] a) = 𝓝[<] (a / c)
  证明: by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divRight, convert, divRight, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.map_divRight_nhdsLT {c a : H} : map (· / c) (𝓝[<] a) = 𝓝[<] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divRight_nhdsNE` / 定理 `Filter.map_divRight_nhdsNE`

English:
theorem Filter.map_divRight_nhdsNE
  given: {c a : G}
  proof: by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divRight_nhdsNE
  条件: {c a : G}
  证明: by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divRight, convert, divRight, div_eq_mul_inv, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.map_divRight_nhdsNE {c a : G} :
    map (· / c) (𝓝[!=] a) = 𝓝[!=] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divRight_nhds` / 定理 `Filter.map_divRight_nhds`

English:
theorem Filter.map_divRight_nhds
  given: {c a : G}
  proof: by
  convert! (Homeomorph.divRight c).map_nhds_eq .. using 2

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divRight_nhds
  条件: {c a : G}
  证明: by
  convert! (Homeomorph.divRight c).map_nhds_eq .. using 2

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divRight, convert, divRight, map_nhds_eq
-/
theorem Filter.map_divRight_nhds {c a : G} :
    map (· / c) (𝓝 a) = 𝓝 (a / c) := by
  convert! (Homeomorph.divRight c).map_nhds_eq .. using 2

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divLeft_nhdsGT` / 定理 `Filter.map_divLeft_nhdsGT`

English:
theorem Filter.map_divLeft_nhdsGT
  given: {c a : H}
  statement: map (c / ·) (𝓝[>] a) = 𝓝[<] (c / a)
  proof: by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divLeft_nhdsGT
  条件: {c a : H}
  结论: map (c / ·) (𝓝[>] a) = 𝓝[<] (c / a)
  证明: by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divLeft, convert, divLeft, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.map_divLeft_nhdsGT {c a : H} : map (c / ·) (𝓝[>] a) = 𝓝[<] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divLeft_nhdsLT` / 定理 `Filter.map_divLeft_nhdsLT`

English:
theorem Filter.map_divLeft_nhdsLT
  given: {c a : H}
  statement: map (c / ·) (𝓝[<] a) = 𝓝[>] (c / a)
  proof: by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divLeft_nhdsLT
  条件: {c a : H}
  结论: map (c / ·) (𝓝[<] a) = 𝓝[>] (c / a)
  证明: by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divLeft, convert, divLeft, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.map_divLeft_nhdsLT {c a : H} : map (c / ·) (𝓝[<] a) = 𝓝[>] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divLeft_nhdsNE` / 定理 `Filter.map_divLeft_nhdsNE`

English:
theorem Filter.map_divLeft_nhdsNE
  given: {c a : G}
  proof: by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [image_div_left]

@[to_additive (attr := simp)]

中文:
定理 滤子.map_divLeft_nhdsNE
  条件: {c a : G}
  证明: by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [image_div_left]

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.divLeft, convert, divLeft, image_div_left, isEmbedding, isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem Filter.map_divLeft_nhdsNE {c a : G} :
    map (c / ·) (𝓝[!=] a) = 𝓝[!=] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [image_div_left]

@[to_additive (attr := simp)]
/--
theorem `Filter.map_divLeft_nhds` / 定理 `Filter.map_divLeft_nhds`

English:
theorem Filter.map_divLeft_nhds
  given: {c a : G}
  proof: by
  convert! (Homeomorph.divLeft c).map_nhds_eq .. using 2

中文:
定理 滤子.map_divLeft_nhds
  条件: {c a : G}
  证明: by
  convert! (Homeomorph.divLeft c).map_nhds_eq .. using 2

Depends on / 依赖: Homeomorph, Homeomorph.divLeft, convert, divLeft, map_nhds_eq
-/
theorem Filter.map_divLeft_nhds {c a : G} :
    map (c / ·) (𝓝 a) = 𝓝 (c / a) := by
  convert! (Homeomorph.divLeft c).map_nhds_eq .. using 2

end DivInvTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [ContinuousMul G]

@[to_additive]
/--
theorem `IsTopologicalGroup.t1Space` / 定理 `IsTopologicalGroup.t1Space`

English:
theorem IsTopologicalGroup.t1Space
  given: (h : @IsClosed G _ {1})
  statement: T1Space G
  proof: ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩

中文:
定理 是拓扑群.t1Space
  条件: (h : @是闭集 G _ {1})
  结论: T1空间 G
  证明: ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩

Depends on / 依赖: isClosedMap_mul_right
-/
theorem IsTopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

variable (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the left, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.) -/
@[to_additive
  /-- A subgroup `S` of an additive topological group `G` acts on `G` properly
  discontinuously on the left, if it is discrete in the sense that `S ∩ K` is finite for all compact
  `K`. (See also `DiscreteTopology`.) -/]
/--
theorem `Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite` / 定理 `Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite`

English:
theorem Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
  statement: (S : Subgroup G)
  proof: { finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl]; rw [compl_compl] at H
      convert! H
      ext x
      simp only [image_smul, mem_ofPred_eq, coe_subtype, mem_preimage, mem_image, Prod.exists]
      exact Set.smul_inter_nonempty_iff' }

中文:
定理 子群.properlyDiscontinuousSMul_of_tendsto_cofinite
  结论: (S : 子群 G)
  证明: { finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl]; rw [compl_compl] at H
      convert! H
      ext x
      simp only [image_smul, mem_ofPred_eq, coe_subtype, mem_preimage, mem_image, Prod.exists]
      exact Set.smul_inter_nonempty_iff' }

Depends on / 依赖: Finite, Prod.exists, Set.Finite, Set.smul_inter_nonempty_iff, coe_subtype, compl_compl, compl_mem_cocompact, continuous_div, convert, finite_disjoint_inter_image, hL.prod, image_smul, mem_image, mem_ofPred_eq, mem_preimage, preimage_compl, smul_inter_nonempty_iff
-/
theorem Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl]; rw [compl_compl] at H
      convert! H
      ext x
      simp only [image_smul, mem_ofPred_eq, coe_subtype, mem_preimage, mem_image, Prod.exists]
      exact Set.smul_inter_nonempty_iff' }

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the right, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.)

If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousSMul_of_t2Space`
to show that the quotient group `G ⧸ S` is Hausdorff. -/
@[to_additive
  /-- A subgroup `S` of an additive topological group `G` acts on `G` properly discontinuously
  on the right, if it is discrete in the sense that `S ∩ K` is finite for all compact `K`.
  (See also `DiscreteTopology`.)

  If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousVAdd_of_t2Space`
  to show that the quotient group `G ⧸ S` is Hausdorff. -/]
/--
theorem `Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite` / 定理 `Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite`

English:
theorem Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
  statement: (S : Subgroup G)
  proof: { finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prodMap continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      simp only [preimage_compl, compl_compl, coe_subtype, comp_apply] at H
      apply Finite.of_preimage _ (equivOp S).surjective
      convert! H using 1
      ext x
      simp only [image_smul, mem_ofPred_eq, mem_preimage, mem_image, Prod.exists]
      exact Set.op_smul_inter_nonempty_iff }

中文:
定理 子群.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
  结论: (S : 子群 G)
  证明: { finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prodMap continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      simp only [preimage_compl, compl_compl, coe_subtype, comp_apply] at H
      apply Finite.of_preimage _ (equivOp S).surjective
      convert! H using 1
      ext x
      simp only [image_smul, mem_ofPred_eq, mem_preimage, mem_image, Prod.exists]
      exact Set.op_smul_inter_nonempty_iff }

Depends on / 依赖: Continuous, Finite, Finite.of_preimage, Prod.exists, Set.Finite, Set.op_smul_inter_nonempty_iff, coe_subtype, comp_apply, compl_compl, compl_mem_cocompact, continuous_id, continuous_inv, continuous_inv.prodMap, continuous_mul, continuous_mul.comp, convert, equivOp, finite_disjoint_inter_image, hK.prod, image_smul
-/
theorem Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S.op G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prodMap continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      simp only [preimage_compl, compl_compl, coe_subtype, comp_apply] at H
      apply Finite.of_preimage _ (equivOp S).surjective
      convert! H using 1
      ext x
      simp only [image_smul, mem_ofPred_eq, mem_preimage, mem_image, Prod.exists]
      exact Set.op_smul_inter_nonempty_iff }

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
  /-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `K + V ⊆ U`. -/]
/--
theorem `compact_open_separated_mul_right` / 定理 `compact_open_separated_mul_right`

English:
theorem compact_open_separated_mul_right
  statement: {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
  proof: by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V inter W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U in 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq]; rw [mem_map]; rw [mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff]; rw [image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

中文:
定理 compact_open_separated_mul_right
  结论: {K U : 集合 G} (hK : 是紧集 K) (hU : 是开集 U)
  证明: by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V inter W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U in 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq]; rw [mem_map]; rw [mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff]; rw [image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

Depends on / 依赖: V.inter_subset_left, V.inter_subset_right, V_in, W_in, hK.induction_on, hU.mem_nhds, induction_on, inter_mem, inter_subset_left, inter_subset_right, mem_map, mem_nhds, mem_pro, mul_subset_mul_left, mul_subset_mul_right, nhds_prod_eq, tendsto_mul, union_mul, union_subset
-/
theorem compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K subseteq U) : exists V in 𝓝 (1 : G), K * V subseteq U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V inter W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U in 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq]; rw [mem_map]; rw [mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff]; rw [image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

open MulOpposite

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
  /-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `V + K ⊆ U`. -/]
/--
theorem `compact_open_separated_mul_left` / 定理 `compact_open_separated_mul_left`

English:
theorem compact_open_separated_mul_left
  statement: {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
  proof: by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (opHomeomorph.isOpenMap U hU)
      (image_mono hKU) with
    ⟨V, hV : V in 𝓝 (op (1 : G)), hV' : op '' K * V subseteq op '' U⟩
  refine ⟨op ⁻¹' V, continuous_op.continuousAt hV, ?_⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'

中文:
定理 compact_open_separated_mul_left
  结论: {K U : 集合 G} (hK : 是紧集 K) (hU : 是开集 U)
  证明: by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (opHomeomorph.isOpenMap U hU)
      (image_mono hKU) with
    ⟨V, hV : V in 𝓝 (op (1 : G)), hV' : op '' K * V subseteq op '' U⟩
  refine ⟨op ⁻¹' V, continuous_op.continuousAt hV, ?_⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'

Depends on / 依赖: compact_open_separated_mul_right, continuousAt, continuous_op, continuous_op.continuousAt, hK.image, image_mono, image_op_mul, image_preimage_eq, image_subset_iff, isOpenMap, opHomeomorph, opHomeomorph.isOpenMap, op_injective, op_surjective, preimage_image_eq, subseteq
-/
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K subseteq U) : exists V in 𝓝 (1 : G), V * K subseteq U := by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (opHomeomorph.isOpenMap U hU)
      (image_mono hKU) with
    ⟨V, hV : V in 𝓝 (op (1 : G)), hV' : op '' K * V subseteq op '' U⟩
  refine ⟨op ⁻¹' V, continuous_op.continuousAt hV, ?_⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive
  /-- A compact set is covered by finitely many left additive translates of a set
    with non-empty interior. -/]
/--
theorem `compact_covered_by_mul_left_translates` / 定理 `compact_covered_by_mul_left_translates`

English:
theorem compact_covered_by_mul_left_translates
  statement: {K V : Set G} (hK : IsCompact K)
  proof: by
  obtain ⟨t, ht⟩ : exists t : Finset G, K subseteq ⋃ x in t, interior ((x * ·) ⁻¹' V) := by
    refine
      hK.elim_finite_subcover (fun x => interior <| (x * ·) ⁻¹' V) (fun x => isOpen_interior) ?_
    obtain ⟨g₀, hg₀⟩ := hV
    refine fun g _ => mem_iUnion.2 ⟨g₀ * g⁻¹, ?_⟩
    refine preimage_interior_subset_interior_preimage (by fun_prop) ?_
    rwa [mem_preimage, inv_mul_cancel_right]
exact ⟨t, Subset.trans ht iUnion₂_mono fun g _ => interior_subset⟩

中文:
定理 compact_covered_by_mul_left_translates
  结论: {K V : 集合 G} (hK : 是紧集 K)
  证明: by
  obtain ⟨t, ht⟩ : exists t : Finset G, K subseteq ⋃ x in t, interior ((x * ·) ⁻¹' V) := by
    refine
      hK.elim_finite_subcover (fun x => interior <| (x * ·) ⁻¹' V) (fun x => isOpen_interior) ?_
    obtain ⟨g₀, hg₀⟩ := hV
    refine fun g _ => mem_iUnion.2 ⟨g₀ * g⁻¹, ?_⟩
    refine preimage_interior_subset_interior_preimage (by fun_prop) ?_
    rwa [mem_preimage, inv_mul_cancel_right]
exact ⟨t, Subset.trans ht iUnion₂_mono fun g _ => interior_subset⟩

Depends on / 依赖: Finset, Subset, Subset.trans, elim_finite_subcover, fun_prop, hK.elim_finite_subcover, interior, interior_subset, inv_mul_cancel_right, isOpen_interior, mem_iUnion, mem_preimage, preimage_interior_subset_interior_preimage, subseteq
-/
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K)
    (hV : (interior V).Nonempty) : exists t : Finset G, K subseteq ⋃ g in t, (g * ·) ⁻¹' V := by
  obtain ⟨t, ht⟩ : exists t : Finset G, K subseteq ⋃ x in t, interior ((x * ·) ⁻¹' V) := by
    refine
      hK.elim_finite_subcover (fun x => interior <| (x * ·) ⁻¹' V) (fun x => isOpen_interior) ?_
    obtain ⟨g₀, hg₀⟩ := hV
    refine fun g _ => mem_iUnion.2 ⟨g₀ * g⁻¹, ?_⟩
    refine preimage_interior_subset_interior_preimage (by fun_prop) ?_
    rwa [mem_preimage, inv_mul_cancel_right]
exact ⟨t, Subset.trans ht iUnion₂_mono fun g _ => interior_subset⟩

/-- Every weakly locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace
  /-- Every weakly locally compact separable topological additive group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/]
instance (priority := 100) SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace [SeparableSpace G]
    [WeaklyLocallyCompactSpace G] : SigmaCompactSpace G := by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨⟨fun n => (fun x => x * denseSeq G n) ⁻¹' L, ?_, ?_⟩⟩
  · intro n
    exact (Homeomorph.mulRight _).isCompact_preimage.mpr hLc
  · refine iUnion_eq_univ_iff.2 fun x => ?_
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (denseSeq G) inter (fun y => x * y) ⁻¹' L).Nonempty := by
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact (denseRange_denseSeq G).inter_nhds_nonempty
          ((Homeomorph.mulLeft x).continuous.continuousAt <| hL1)
    exact ⟨n, hn⟩

/-- Given two compact sets in a noncompact topological group, there is a translate of the second
one that is disjoint from the first one. -/
@[to_additive
  /-- Given two compact sets in a noncompact additive topological group, there is a
  translate of the second one that is disjoint from the first one. -/]
/--
theorem `exists_disjoint_smul_of_isCompact` / 定理 `exists_disjoint_smul_of_isCompact`

English:
theorem exists_disjoint_smul_of_isCompact
  statement: [NoncompactSpace G] {K L : Set G} (hK : IsCompact K)
  proof: by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : exists g, g ∉ K * L⁻¹ := by
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine ⟨g, ?_⟩
  refine disjoint_left.2 fun a ha h'a => hg ?_
  rcases h'a with ⟨b, bL, rfl⟩
  refine ⟨g * b, ha, b⁻¹, by simpa only [Set.mem_inv, inv_inv] using bL, ?_⟩
  simp only [mul_inv_cancel_right]

中文:
定理 存在_disjoint_smul_of_isCompact
  结论: [Noncompact空间 G] {K L : 集合 G} (hK : 是紧集 K)
  证明: by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : exists g, g ∉ K * L⁻¹ := by
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine ⟨g, ?_⟩
  refine disjoint_left.2 fun a ha h'a => hg ?_
  rcases h'a with ⟨b, bL, rfl⟩
  refine ⟨g * b, ha, b⁻¹, by simpa only [Set.mem_inv, inv_inv] using bL, ?_⟩
  simp only [mul_inv_cancel_right]

Depends on / 依赖: Set.mem_inv, contrapose, disjoint_left, eq_univ_iff_forall, hK.mul, hL.inv, inv_inv, mem_inv, mul_inv_cancel_right, ne_univ
-/
theorem exists_disjoint_smul_of_isCompact [NoncompactSpace G] {K L : Set G} (hK : IsCompact K)
    (hL : IsCompact L) : exists g : G, Disjoint K (g • L) := by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : exists g, g ∉ K * L⁻¹ := by
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine ⟨g, ?_⟩
  refine disjoint_left.2 fun a ha h'a => hg ?_
  rcases h'a with ⟨b, bL, rfl⟩
  refine ⟨g * b, ha, b⁻¹, by simpa only [Set.mem_inv, inv_inv] using bL, ?_⟩
  simp only [mul_inv_cancel_right]

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
/--
theorem `nhds_mul` / 定理 `nhds_mul`

English:
theorem nhds_mul
  given: (x y : G)
  statement: 𝓝 (x * y) = 𝓝 x * 𝓝 y
  proof: calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x]; rw [← map_mul_right_nhds_one y]; rw [← map₂_mul]; rw [map₂_map_left]; rw [map₂_map_right]

中文:
定理 nhds_mul
  条件: (x y : G)
  结论: 𝓝 (x * y) = 𝓝 x * 𝓝 y
  证明: calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x]; rw [← map_mul_right_nhds_one y]; rw [← map₂_mul]; rw [map₂_map_left]; rw [map₂_map_right]

Depends on / 依赖: map_mul_left_nhds_one, map_mul_right_nhds_one, mul_assoc
-/
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x]; rw [← map_mul_right_nhds_one y]; rw [← map₂_mul]; rw [map₂_map_left]; rw [map₂_map_right]

/-- On a topological group, `𝓝 : G → Filter G` can be promoted to a `MulHom`. -/
@[to_additive (attr := simps)
  /-- On an additive topological group, `𝓝 : G → Filter G` can be promoted to an `AddHom`. -/]
/--
Definition of `nhdsMulHom` / `nhdsMulHom` 的定义

English:
definition nhdsMulHom
  signature: : G ->ₙ* Filter G where
  body: 𝓝
  map_mul' _ _ := nhds_mul _ _

中文:
定义 nhdsMulHom
  签名: : G ->ₙ* 滤子 G where
  定义体: 𝓝
  map_mul' _ _ := nhds_mul _ _
-/
def nhdsMulHom : G ->ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _

end

end FilterMul

instance {G} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    IsTopologicalAddGroup (Additive G) where
  continuous_neg := @continuous_inv G _ _ _

instance {G} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] :
    IsTopologicalGroup (Multiplicative G) where
  continuous_inv := @continuous_neg G _ _ _

/-- If `G` is a group with topological `⁻¹`, then it is homeomorphic to its units. -/
@[to_additive /-- If `G` is an additive group with topological negation, then it is homeomorphic to
its additive units. -/]
/--
Definition of `toUnits_homeomorph` / `toUnits_homeomorph` 的定义

English:
definition toUnits_homeomorph
  signature: [Group G] [TopologicalSpace G] [ContinuousInv G]
  body: toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩

中文:
定义 toUnits_homeomorph
  签名: [群 G] [拓扑空间 G] [连续取逆 G]
  定义体: toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩

Depends on / 依赖: toEquiv, toUnits, toUnits.toEquiv
-/
def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩

/--
theorem `Units.isEmbedding_val` / 定理 `Units.isEmbedding_val`

English:
theorem Units.isEmbedding_val
  given: [Group G] [TopologicalSpace G] [ContinuousInv G]
  proof: toUnits_homeomorph.symm.isEmbedding

中文:
定理 单位群.isEmbedding_val
  条件: [群 G] [拓扑空间 G] [连续取逆 G]
  证明: toUnits_homeomorph.symm.isEmbedding
-/
@[to_additive] theorem Units.isEmbedding_val [Group G] [TopologicalSpace G] [ContinuousInv G] :
    IsEmbedding (val : Gˣ -> G) :=
  toUnits_homeomorph.symm.isEmbedding

/--
lemma `Continuous.of_coeHom_comp` / 引理 `Continuous.of_coeHom_comp`

English:
lemma Continuous.of_coeHom_comp
  statement: [Group G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
  proof: by
  apply continuous_induced_rng.mpr ?_
  refine continuous_prodMk.mpr ⟨hf, ?_⟩
  simp_rw [← map_inv]
  exact MulOpposite.continuous_op.comp (hf.comp continuous_inv)

中文:
引理 连续.of_coeHom_comp
  结论: [群 G] [幺半群 H] [拓扑空间 G] [拓扑空间 H]
  证明: by
  apply continuous_induced_rng.mpr ?_
  refine continuous_prodMk.mpr ⟨hf, ?_⟩
  simp_rw [← map_inv]
  exact MulOpposite.continuous_op.comp (hf.comp continuous_inv)

Depends on / 依赖: MulOpposite, MulOpposite.continuous_op.comp, continuous_induced_rng, continuous_induced_rng.mpr, continuous_inv, continuous_op, continuous_prodMk, continuous_prodMk.mpr, hf.comp, map_inv, simp_rw
-/
lemma Continuous.of_coeHom_comp [Group G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousInv G] {f : G ->* Hˣ} (hf : Continuous ((Units.coeHom H).comp f)) : Continuous f := by
  apply continuous_induced_rng.mpr ?_
  refine continuous_prodMk.mpr ⟨hf, ?_⟩
  simp_rw [← map_inv]
  exact MulOpposite.continuous_op.comp (hf.comp continuous_inv)

namespace Units

open MulOpposite (continuous_op continuous_unop)

@[to_additive]
/--
theorem `range_embedProduct` / 定理 `range_embedProduct`

English:
theorem range_embedProduct
  given: [Monoid α]
  proof: .mpr Set.range_eq_iff _ _
    ⟨fun a => ⟨a.mul_inv, a.inv_mul⟩, fun p hp => ⟨⟨p.1, unop p.2, hp.1, hp.2⟩, rfl⟩⟩

中文:
定理 range_embedProduct
  条件: [幺半群 α]
  证明: .mpr Set.range_eq_iff _ _
    ⟨fun a => ⟨a.mul_inv, a.inv_mul⟩, fun p hp => ⟨⟨p.1, unop p.2, hp.1, hp.2⟩, rfl⟩⟩

Depends on / 依赖: Set.range_eq_iff, a.inv_mul, a.mul_inv, inv_mul, mul_inv, range_eq_iff
-/
theorem range_embedProduct [Monoid α] :
    Set.range (embedProduct α) = {p : α × αᵐᵒᵖ | p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1} :=
.mpr Set.range_eq_iff _ _
    ⟨fun a => ⟨a.mul_inv, a.inv_mul⟩, fun p hp => ⟨⟨p.1, unop p.2, hp.1, hp.2⟩, rfl⟩⟩

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousMul
  signature: α] : IsTopologicalGroup αˣ where
  body: Units.continuous_iff.2 ⟨continuous_coe_inv, continuous_val⟩

@[to_additive]

中文:
实例 [连续乘法
  签名: α] : 是拓扑群 αˣ where
  定义体: Units.continuous_iff.2 ⟨continuous_coe_inv, continuous_val⟩

@[to_additive]

Depends on / 依赖: Units.continuous_iff, continuous_coe_inv, continuous_iff, continuous_val
-/
instance [ContinuousMul α] : IsTopologicalGroup αˣ where
continuous_inv := Units.continuous_iff.2 ⟨continuous_coe_inv, continuous_val⟩

@[to_additive]
/--
theorem `isClosedEmbedding_embedProduct` / 定理 `isClosedEmbedding_embedProduct`

English:
theorem isClosedEmbedding_embedProduct
  given: [T1Space α] [ContinuousMul α]
  proof: isEmbedding_embedProduct
  isClosed_range := by
    rw [range_embedProduct]
    refine .inter (isClosed_singleton.preimage ?_) (isClosed_singleton.preimage ?_) <;>
    fun_prop

中文:
定理 isClosedEmbedding_embedProduct
  条件: [T1空间 α] [连续乘法 α]
  证明: isEmbedding_embedProduct
  isClosed_range := by
    rw [range_embedProduct]
    refine .inter (isClosed_singleton.preimage ?_) (isClosed_singleton.preimage ?_) <;>
    fun_prop

Depends on / 依赖: isEmbedding_embedProduct
-/
theorem isClosedEmbedding_embedProduct [T1Space α] [ContinuousMul α] :
    IsClosedEmbedding (embedProduct α) where
  toIsEmbedding := isEmbedding_embedProduct
  isClosed_range := by
    rw [range_embedProduct]
    refine .inter (isClosed_singleton.preimage ?_) (isClosed_singleton.preimage ?_) <;>
    fun_prop

/--
lemma `_root_.Topology.IsClosedEmbedding.units_map` / 引理 `_root_.Topology.IsClosedEmbedding.units_map`

English:
lemma _root_.Topology.IsClosedEmbedding.units_map
  statement: [ContinuousMul α] [T1Space α] {f : α ->* β}
  proof: by
  refine .of_comp isEmbedding_embedProduct ?_
  exact (hf.prodMap (opHomeomorph.isClosedEmbedding.comp
 hf.comp opHomeomorph.symm.isClosedEmbedding)).comp isClosedEmbedding_embedProduct

@[to_additive]

中文:
引理 _root_.拓扑.是闭嵌入.units_map
  结论: [连续乘法 α] [T1空间 α] {f : α ->* β}
  证明: by
  refine .of_comp isEmbedding_embedProduct ?_
  exact (hf.prodMap (opHomeomorph.isClosedEmbedding.comp
 hf.comp opHomeomorph.symm.isClosedEmbedding)).comp isClosedEmbedding_embedProduct

@[to_additive]

Depends on / 依赖: hf.comp, hf.prodMap, isClosedEmbedding, isClosedEmbedding_embedProduct, isEmbedding_embedProduct, of_comp, opHomeomorph, opHomeomorph.isClosedEmbedding.comp, opHomeomorph.symm.isClosedEmbedding, prodMap
-/
lemma _root_.Topology.IsClosedEmbedding.units_map [ContinuousMul α] [T1Space α] {f : α ->* β}
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map f) := by
  refine .of_comp isEmbedding_embedProduct ?_
  exact (hf.prodMap (opHomeomorph.isClosedEmbedding.comp
 hf.comp opHomeomorph.symm.isClosedEmbedding)).comp isClosedEmbedding_embedProduct

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: α] [ContinuousMul α] [CompactSpace α] : CompactSpace αˣ
  body: isClosedEmbedding_embedProduct.compactSpace

@[to_additive]

中文:
实例 [T1空间
  签名: α] [连续乘法 α] [紧空间 α] : 紧空间 αˣ
  定义体: isClosedEmbedding_embedProduct.compactSpace

@[to_additive]

Depends on / 依赖: compactSpace, isClosedEmbedding_embedProduct, isClosedEmbedding_embedProduct.compactSpace
-/
instance [T1Space α] [ContinuousMul α] [CompactSpace α] : CompactSpace αˣ :=
  isClosedEmbedding_embedProduct.compactSpace

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: α] [ContinuousMul α] [WeaklyLocallyCompactSpace α] :
  body: isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace

@[to_additive]

中文:
实例 [T1空间
  签名: α] [连续乘法 α] [WeaklyLocallyCompact空间 α] :
  定义体: isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace

@[to_additive]

Depends on / 依赖: isClosedEmbedding_embedProduct, isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace, weaklyLocallyCompactSpace
-/
instance [T1Space α] [ContinuousMul α] [WeaklyLocallyCompactSpace α] :
    WeaklyLocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: α] [ContinuousMul α] [LocallyCompactSpace α] : LocallyCompactSpace αˣ
  body: isClosedEmbedding_embedProduct.locallyCompactSpace

中文:
实例 [T1空间
  签名: α] [连续乘法 α] [局部紧空间 α] : 局部紧空间 αˣ
  定义体: isClosedEmbedding_embedProduct.locallyCompactSpace

Depends on / 依赖: isClosedEmbedding_embedProduct, isClosedEmbedding_embedProduct.locallyCompactSpace, locallyCompactSpace
-/
instance [T1Space α] [ContinuousMul α] [LocallyCompactSpace α] : LocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.locallyCompactSpace

/--
lemma `_root_.Submonoid.units_isCompact` / 引理 `_root_.Submonoid.units_isCompact`

English:
lemma _root_.Submonoid.units_isCompact
  statement: [T1Space α] [ContinuousMul α] {S : Submonoid α}
  proof: by
  have : IsCompact (S ×ˢ S.op) := hS.prod (opHomeomorph.isCompact_preimage.mp hS)
  exact isClosedEmbedding_embedProduct.isCompact_preimage this

中文:
引理 _root_.子幺半群.units_isCompact
  结论: [T1空间 α] [连续乘法 α] {S : 子幺半群 α}
  证明: by
  have : IsCompact (S ×ˢ S.op) := hS.prod (opHomeomorph.isCompact_preimage.mp hS)
  exact isClosedEmbedding_embedProduct.isCompact_preimage this

Depends on / 依赖: IsCompact, S.op, hS.prod, isClosedEmbedding_embedProduct, isClosedEmbedding_embedProduct.isCompact_preimage, isCompact_preimage, opHomeomorph, opHomeomorph.isCompact_preimage.mp
-/
lemma _root_.Submonoid.units_isCompact [T1Space α] [ContinuousMul α] {S : Submonoid α}
    (hS : IsCompact (S : Set α)) : IsCompact (S.units : Set αˣ) := by
  have : IsCompact (S ×ˢ S.op) := hS.prod (opHomeomorph.isCompact_preimage.mp hS)
  exact isClosedEmbedding_embedProduct.isCompact_preimage this

/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive prodAddUnits
  /-- The topological group isomorphism between the additive units of a product of two
  additive monoids, and the product of the additive units of each additive monoid. -/]
/--
Definition of `_root_.Homeomorph.prodUnits` / `_root_.Homeomorph.prodUnits` 的定义

English:
definition _root_.Homeomorph.prodUnits
  signature: : (α × β)ˣ ≃ₜ αˣ × βˣ where
  body: (continuous_fst.units_map (MonoidHom.fst α β)).prodMk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prodMk continuous_val.snd',
        continuous_coe_inv.fst'.prodMk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv

中文:
定义 _root_.同胚.prodUnits
  签名: : (α × β)ˣ ≃ₜ αˣ × βˣ where
  定义体: (continuous_fst.units_map (MonoidHom.fst α β)).prodMk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prodMk continuous_val.snd',
        continuous_coe_inv.fst'.prodMk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv

Depends on / 依赖: MonoidHom, MonoidHom.fst, MonoidHom.snd, MulEquiv, MulEquiv.prodUnits.toEquiv, Units.continuous_iff, continuous_coe_inv, continuous_coe_inv.fst, continuous_coe_inv.snd, continuous_fst, continuous_fst.units_map, continuous_iff, continuous_invFun, continuous_snd, continuous_snd.units_map, continuous_val, continuous_val.fst, continuous_val.snd, prodMk, prodUnits
-/
def _root_.Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prodMk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prodMk continuous_val.snd',
        continuous_coe_inv.fst'.prodMk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv

end Units

section LatticeOps

variable {ι : Sort*} [Group G]

@[to_additive]
/--
theorem `topologicalGroup_sInf` / 定理 `topologicalGroup_sInf`

English:
theorem topologicalGroup_sInf
  statement: {ts : Set (TopologicalSpace G)}
  proof: letI := sInf ts
  { toContinuousInv :=
@continuousInv_sInf _ _ _ fun t ht => @IsTopologicalGroup.toContinuousInv G t _ h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
@IsTopologicalGroup.toContinuousMul G t _ h t ht }

@[to_additive]

中文:
定理 topologicalGroup_sInf
  结论: {ts : 集合 (拓扑空间 G)}
  证明: letI := sInf ts
  { toContinuousInv :=
@continuousInv_sInf _ _ _ fun t ht => @IsTopologicalGroup.toContinuousInv G t _ h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
@IsTopologicalGroup.toContinuousMul G t _ h t ht }

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.toContinuousInv, IsTopologicalGroup.toContinuousMul, continuousInv_sInf, continuousMul_sInf, toContinuousInv, toContinuousMul
-/
theorem topologicalGroup_sInf {ts : Set (TopologicalSpace G)}
    (h : forall t in ts, @IsTopologicalGroup G t _) : @IsTopologicalGroup G (sInf ts) _ :=
  letI := sInf ts
  { toContinuousInv :=
@continuousInv_sInf _ _ _ fun t ht => @IsTopologicalGroup.toContinuousInv G t _ h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
@IsTopologicalGroup.toContinuousMul G t _ h t ht }

@[to_additive]
/--
theorem `topologicalGroup_iInf` / 定理 `topologicalGroup_iInf`

English:
theorem topologicalGroup_iInf
  statement: {ts' : ι -> TopologicalSpace G}
  proof: by
  rw [← sInf_range]
  exact topologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

中文:
定理 topologicalGroup_iInf
  结论: {ts' : ι -> 拓扑空间 G}
  证明: by
  rw [← sInf_range]
  exact topologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

Depends on / 依赖: Set.forall_mem_range.mpr, forall_mem_range, sInf_range, topologicalGroup_sInf
-/
theorem topologicalGroup_iInf {ts' : ι -> TopologicalSpace G}
    (h' : forall i, @IsTopologicalGroup G (ts' i) _) : @IsTopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact topologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/--
theorem `topologicalGroup_inf` / 定理 `topologicalGroup_inf`

English:
theorem topologicalGroup_inf
  statement: {t₁ t₂ : TopologicalSpace G} (h₁ : @IsTopologicalGroup G t₁ _)
  proof: by
  rw [inf_eq_iInf]
  refine topologicalGroup_iInf fun b => ?_
  cases b <;> assumption

中文:
定理 topologicalGroup_inf
  结论: {t₁ t₂ : 拓扑空间 G} (h₁ : @是拓扑群 G t₁ _)
  证明: by
  rw [inf_eq_iInf]
  refine topologicalGroup_iInf fun b => ?_
  cases b <;> assumption

Depends on / 依赖: inf_eq_iInf, topologicalGroup_iInf
-/
theorem topologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @IsTopologicalGroup G t₁ _)
    (h₂ : @IsTopologicalGroup G t₂ _) : @IsTopologicalGroup G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine topologicalGroup_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps
