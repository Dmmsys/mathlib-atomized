/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Short exact sequences of topological groups

In this file, we define a short exact sequence of topological groups to be a closed embedding `φ`
followed by an open quotient map `ψ` satisfying `φ.range = ψ.ker`.

## Main definitions

* `TopologicalGroup.IsSES φ ψ`: A predicate stating that `φ` is a closed embedding, `ψ` is an open
  quotient map, and `φ.range = ψ.ker`.

-/

public section

open scoped Pointwise

/--
Definition of `TopologicalGroup.IsSES` / `TopologicalGroup.IsSES` 的定义

English:
structure TopologicalGroup.IsSES
  parameters: {A B C : Type*} [Group A] [Group B] [Group C]
  axioms and operations (3):
    - isClosedEmbedding : Topology.IsClosedEmbedding φ
    - isOpenQuotientMap : IsOpenQuotientMap ψ
    - mulExact : Function.MulExact φ ψ

中文:
结构 TopologicalGroup.IsSES
  参数: {A B C : 类型} [Group A] [Group B] [Group C]
  公理与运算 (3 个):
    - isClosedEmbedding : Topology.IsClosedEmbedding φ
    - isOpenQuotientMap : IsOpenQuotientMap ψ
    - mulExact : Function.MulExact φ ψ
-/
structure TopologicalGroup.IsSES {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A ->* B) (ψ : B ->* C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  mulExact : Function.MulExact φ ψ

/--
Definition of `TopologicalAddGroup.IsSES` / `TopologicalAddGroup.IsSES` 的定义

English:
structure TopologicalAddGroup.IsSES
  parameters: {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
  axioms and operations (3):
    - isClosedEmbedding : Topology.IsClosedEmbedding φ
    - isOpenQuotientMap : IsOpenQuotientMap ψ
    - exact : Function.Exact φ ψ

中文:
结构 TopologicalAddGroup.IsSES
  参数: {A B C : 类型} [AddGroup A] [AddGroup B] [AddGroup C]
  公理与运算 (3 个):
    - isClosedEmbedding : Topology.IsClosedEmbedding φ
    - isOpenQuotientMap : IsOpenQuotientMap ψ
    - exact : Function.Exact φ ψ
-/
structure TopologicalAddGroup.IsSES {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A ->+ B) (ψ : B ->+ C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  exact : Function.Exact φ ψ

attribute [to_additive TopologicalAddGroup.IsSES] TopologicalGroup.IsSES

namespace TopologicalGroup.IsSES

/-- Construct a short exact sequence of topological groups from a closed normal subgroup. -/
@[to_additive /-- Construct a short exact sequence of topological groups from a
closed normal subgroup. -/]
/--
theorem `ofClosedSubgroup` / 定理 `ofClosedSubgroup`

English:
theorem ofClosedSubgroup
  statement: {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  proof: ⟨⟨Topology.IsInducing.subtypeVal, H.subtype_injective⟩, by simpa⟩
  isOpenQuotientMap := MulAction.isOpenQuotientMap_quotientMk
  mulExact := by simp [Function.MulExact]

中文:
定理 ofClosedSubgroup
  结论: {G : 类型} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  证明: ⟨⟨Topology.IsInducing.subtypeVal, H.subtype_injective⟩, by simpa⟩
  isOpenQuotientMap := MulAction.isOpenQuotientMap_quotientMk
  mulExact := by simp [Function.MulExact]

Depends on / 依赖: H.subtype_injective, IsInducing, Topology, Topology.IsInducing.subtypeVal, subtypeVal, subtype_injective
-/
theorem ofClosedSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.Normal] (hH : IsClosed (H : Set G)) :
    TopologicalGroup.IsSES H.subtype (QuotientGroup.mk' H) where
  isClosedEmbedding := ⟨⟨Topology.IsInducing.subtypeVal, H.subtype_injective⟩, by simpa⟩
  isOpenQuotientMap := MulAction.isOpenQuotientMap_quotientMk
  mulExact := by simp [Function.MulExact]

end TopologicalGroup.IsSES
