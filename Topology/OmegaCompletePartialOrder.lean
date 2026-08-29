/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Order.ScottTopology

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

* https://ncatlab.org/nlab/show/Scott+topology

-/

@[expose] public section

open Set OmegaCompletePartialOrder Topology

universe u

open Topology.IsScott in
/--
lemma `Topology.IsScott.ωScottContinuous_iff_continuous` / 引理 `Topology.IsScott.ωScottContinuous_iff_continuous`

English:
lemma Topology.IsScott.ωScottContinuous_iff_continuous
  statement: {α : Type*}
  proof: by
  rw [ωScottContinuous]; rw [scottContinuousOn_iff_continuous (fun a b hab => by
    use Chain.pair a b hab; exact OmegaCompletePartialOrder.Chain.range_pair a b hab)]

中文:
引理 Topology.IsScott.ωScottContinuous_iff_continuous
  结论: {α : 类型}
  证明: by
  rw [ωScottContinuous]; rw [scottContinuousOn_iff_continuous (fun a b hab => by
    use Chain.pair a b hab; exact OmegaCompletePartialOrder.Chain.range_pair a b hab)]
-/
@[simp] lemma Topology.IsScott.ωScottContinuous_iff_continuous {α : Type*}
    [OmegaCompletePartialOrder α] [TopologicalSpace α]
    [Topology.IsScott α (Set.range fun c : Chain α => Set.range c)] {f : α -> Prop} :
    ωScottContinuous f ↔ Continuous f := by
  rw [ωScottContinuous]; rw [scottContinuousOn_iff_continuous (fun a b hab => by
    use Chain.pair a b hab; exact OmegaCompletePartialOrder.Chain.range_pair a b hab)]

namespace Scott

/--
Definition of `IsωSup` / `IsωSup` 的定义

English:
definition IsωSup
  signature: {α : Type u} [Preorder α] (c : Chain α) (x : α)
  body: (forall i, c i <= x) ∧ forall y, (forall i, c i <= y) -> x <= y

中文:
定义 IsωSup
  签名: {α : 类型u} [Preorder α] (c : Chain α) (x : α)
  定义体: (forall i, c i <= x) ∧ forall y, (forall i, c i <= y) -> x <= y
-/
def IsωSup {α : Type u} [Preorder α] (c : Chain α) (x : α) : Prop :=
  (forall i, c i <= x) ∧ forall y, (forall i, c i <= y) -> x <= y

/--
theorem `isωSup_iff_isLUB` / 定理 `isωSup_iff_isLUB`

English:
theorem isωSup_iff_isLUB
  given: {α : Type u} [Preorder α] {c : Chain α} {x : α}
  proof: by
  simp [IsωSup, IsLUB, IsLeast, upperBounds, lowerBounds]

中文:
定理 isωSup_iff_isLUB
  条件: {α : 类型u} [Preorder α] {c : Chain α} {x : α}
  证明: by
  simp [IsωSup, IsLUB, IsLeast, upperBounds, lowerBounds]

Depends on / 依赖: IsLeast, lowerBounds, upperBounds
-/
theorem isωSup_iff_isLUB {α : Type u} [Preorder α] {c : Chain α} {x : α} :
    IsωSup c x ↔ IsLUB (range c) x := by
  simp [IsωSup, IsLUB, IsLeast, upperBounds, lowerBounds]

variable (α : Type u) [OmegaCompletePartialOrder α]

/--
Definition of `IsOpen` / `IsOpen` 的定义

English:
definition IsOpen
  signature: (s : Set α)
  body: ωScottContinuous fun x => x in s

中文:
定义 IsOpen
  签名: (s : Set α)
  定义体: ωScottContinuous fun x => x in s
-/
def IsOpen (s : Set α) : Prop :=
  ωScottContinuous fun x => x in s

/--
theorem `isOpen_univ` / 定理 `isOpen_univ`

English:
theorem isOpen_univ
  statement: IsOpen α univ
  proof: @CompleteLattice.ωScottContinuous.top α Prop _ _

中文:
定理 isOpen_univ
  结论: IsOpen α univ
  证明: @CompleteLattice.ωScottContinuous.top α Prop _ _

Depends on / 依赖: CompleteLattice, ScottContinuous.top
-/
theorem isOpen_univ : IsOpen α univ := @CompleteLattice.ωScottContinuous.top α Prop _ _

/--
theorem `IsOpen.inter` / 定理 `IsOpen.inter`

English:
theorem IsOpen.inter
  given: (s t : Set α)
  statement: IsOpen α s -> IsOpen α t -> IsOpen α (s inter t)
  proof: CompleteLattice.ωScottContinuous.inf

中文:
定理 IsOpen.inter
  条件: (s t : Set α)
  结论: IsOpen α s -> IsOpen α t -> IsOpen α (s inter t)
  证明: CompleteLattice.ωScottContinuous.inf

Depends on / 依赖: CompleteLattice, ScottContinuous.inf
-/
theorem IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> IsOpen α (s inter t) :=
  CompleteLattice.ωScottContinuous.inf

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isOpen_sUnion` / 定理 `isOpen_sUnion`

English:
theorem isOpen_sUnion
  given: (s : Set (Set α)) (hs : forall t in s, IsOpen α t)
  statement: IsOpen α (⋃₀ s)
  proof: by
  simp only [IsOpen] at hs ⊢
  convert! CompleteLattice.ωScottContinuous.sSup hs
  aesop

中文:
定理 isOpen_sUnion
  条件: (s : Set (Set α)) (hs : 对任意 t in s, IsOpen α t)
  结论: IsOpen α (⋃₀ s)
  证明: by
  simp only [IsOpen] at hs ⊢
  convert! CompleteLattice.ωScottContinuous.sSup hs
  aesop

Depends on / 依赖: CompleteLattice, IsOpen, ScottContinuous.sSup, convert
-/
theorem isOpen_sUnion (s : Set (Set α)) (hs : forall t in s, IsOpen α t) : IsOpen α (⋃₀ s) := by
  simp only [IsOpen] at hs ⊢
  convert! CompleteLattice.ωScottContinuous.sSup hs
  aesop

/--
theorem `IsOpen.isUpperSet` / 定理 `IsOpen.isUpperSet`

English:
theorem IsOpen.isUpperSet
  given: {s : Set α} (hs : IsOpen α s)
  statement: IsUpperSet s
  proof: hs.monotone

中文:
定理 IsOpen.isUpperSet
  条件: {s : Set α} (hs : IsOpen α s)
  结论: IsUpperSet s
  证明: hs.monotone

Depends on / 依赖: hs.monotone, monotone
-/
theorem IsOpen.isUpperSet {s : Set α} (hs : IsOpen α s) : IsUpperSet s := hs.monotone

end Scott

open Scott hiding IsOpen IsOpen.isUpperSet

/--
theorem `isωSup_ωSup` / 定理 `isωSup_ωSup`

English:
theorem isωSup_ωSup
  given: {α} [OmegaCompletePartialOrder α] (c : Chain α)
  statement: IsωSup c (ωSup c)
  proof: by
  constructor
  · apply le_ωSup
  · apply ωSup_le

中文:
定理 isωSup_ωSup
  条件: {α} [OmegaCompletePartialOrder α] (c : Chain α)
  结论: IsωSup c (ωSup c)
  证明: by
  constructor
  · apply le_ωSup
  · apply ωSup_le
-/
theorem isωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
  · apply ωSup_le
