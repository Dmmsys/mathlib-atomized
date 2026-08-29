/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.Sign.Defs
public import Mathlib.Topology.Order.Basic

/-!
# Topology on `SignType`

This file gives `SignType` the discrete topology, and proves continuity results for `SignType.sign`
in an `OrderTopology`.
-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace SignType
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 SignType
  定义体: ⊥
-/
instance : TopologicalSpace SignType :=
  ⊥

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology SignType
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 SignType
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology SignType :=
  ⟨rfl⟩

variable {α : Type*} [Zero α] [TopologicalSpace α]

section PartialOrder

variable [PartialOrder α] [DecidableLT α] [OrderTopology α]

/--
theorem `continuousAt_sign_of_pos` / 定理 `continuousAt_sign_of_pos`

English:
theorem continuousAt_sign_of_pos
  given: {a : α} (h : 0 < a)
  statement: ContinuousAt SignType.sign a
  proof: by
  refine (continuousAt_const : ContinuousAt (fun _ => (1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq]; rw [eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩

中文:
定理 continuousAt_sign_of_pos
  条件: {a : α} (h : 0 < a)
  结论: ContinuousAt SignType.sign a
  证明: by
  refine (continuousAt_const : ContinuousAt (fun _ => (1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq]; rw [eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩

Depends on / 依赖: ContinuousAt, EventuallyEq, Filter, Filter.EventuallyEq, SignType, continuousAt_const, eventually_nhds_iff, isOpen_lt, sign_pos
-/
theorem continuousAt_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt SignType.sign a := by
  refine (continuousAt_const : ContinuousAt (fun _ => (1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq]; rw [eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩

/--
theorem `continuousAt_sign_of_neg` / 定理 `continuousAt_sign_of_neg`

English:
theorem continuousAt_sign_of_neg
  given: {a : α} (h : a < 0)
  statement: ContinuousAt SignType.sign a
  proof: by
  refine (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq]; rw [eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩

中文:
定理 continuousAt_sign_of_neg
  条件: {a : α} (h : a < 0)
  结论: ContinuousAt SignType.sign a
  证明: by
  refine (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq]; rw [eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩

Depends on / 依赖: ContinuousAt, EventuallyEq, Filter, Filter.EventuallyEq, SignType, continuousAt_const, eventually_nhds_iff, isOpen_gt, sign_neg
-/
theorem continuousAt_sign_of_neg {a : α} (h : a < 0) : ContinuousAt SignType.sign a := by
  refine (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq]; rw [eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderTopology α]

/--
theorem `continuousAt_sign_of_ne_zero` / 定理 `continuousAt_sign_of_ne_zero`

English:
theorem continuousAt_sign_of_ne_zero
  given: {a : α} (h : a != 0)
  statement: ContinuousAt SignType.sign a
  proof: by
  rcases h.lt_or_gt with (h_neg | h_pos)
  · exact continuousAt_sign_of_neg h_neg
  · exact continuousAt_sign_of_pos h_pos

中文:
定理 continuousAt_sign_of_ne_zero
  条件: {a : α} (h : a != 0)
  结论: ContinuousAt SignType.sign a
  证明: by
  rcases h.lt_or_gt with (h_neg | h_pos)
  · exact continuousAt_sign_of_neg h_neg
  · exact continuousAt_sign_of_pos h_pos

Depends on / 依赖: continuousAt_sign_of_neg, continuousAt_sign_of_pos, h.lt_or_gt, h_neg, h_pos, lt_or_gt
-/
theorem continuousAt_sign_of_ne_zero {a : α} (h : a != 0) : ContinuousAt SignType.sign a := by
  rcases h.lt_or_gt with (h_neg | h_pos)
  · exact continuousAt_sign_of_neg h_neg
  · exact continuousAt_sign_of_pos h_pos

end LinearOrder
