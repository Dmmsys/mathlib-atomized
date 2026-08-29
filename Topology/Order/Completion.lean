/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Completion

import Mathlib.Algebra.Order.Field.Basic

/-!
# Dense and continuous completion of a linear order

Let `α` be a linear order.

* `DedekindCut.continuous_principal`: the map `DedekindCut.principal : α → DedekindCut α`
  that embeds `α` in its Dedekind completion is continuous for the order topologies.
* `Order.Fill α`: this is a type with a dense linear order endowed
  with a continuous order-embedding `Order.Fill.some` of `α`.
  It is defined as a subtype of `α × ℚ` and its order is induced by the lexicographic order.
* `Order.Fill.some`: the order embedding `α ↪o Order.Fill α` given by `a ↦ (a, 0)`.
* `Order.Fill.continuous_some`: the map `⇑Order.Fill.some` is continuous for the order topologies.
* `Order.exists_dense_continuous_completion`: any linear order embeds continuously
  (for the order topologies) into a dense and complete linear order.
  The linearly ordered type provided by the proof is given by the Dedekind completion of
  `Order.Fill α`, although the user does not need to know that.
-/

@[expose] public section

open Set

variable {α : Type*} [LinearOrder α]

/--
theorem `DedekindCut.continuous_principal` / 定理 `DedekindCut.continuous_principal`

English:
theorem DedekindCut.continuous_principal
  statement: [TopologicalSpace α] [OrderTopology α]
  proof: by
  rw [OrderTopology.continuous_iff]
  refine fun c => ⟨?_, ?_⟩
  · have : IsOpen (⋃ a in c.right, Ioi a) := isOpen_biUnion fun _ _ => isOpen_Ioi
    convert this
    ext
    simp [lt_principal_iff]
  · have : IsOpen (⋃ a in c.left, Iio a) := isOpen_biUnion fun _ _ => isOpen_Iio
    convert this
 

中文:
定理 DedekindCut.continuous_principal
  结论: [拓扑空间 α] [Order拓扑 α]
  证明: by
  rw [OrderTopology.continuous_iff]
  refine fun c => ⟨?_, ?_⟩
  · have : IsOpen (⋃ a in c.right, Ioi a) := isOpen_biUnion fun _ _ => isOpen_Ioi
    convert this
    ext
    simp [lt_principal_iff]
  · have : IsOpen (⋃ a in c.left, Iio a) := isOpen_biUnion fun _ _ => isOpen_Iio
    convert this
 

Depends on / 依赖: IsOpen, OrderTopology, OrderTopology.continuous_iff, c.left, c.right, continuous_iff, convert, isOpen_Iio, isOpen_Ioi, isOpen_biUnion, lt_principal_iff, principal_lt_iff
-/
theorem DedekindCut.continuous_principal [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace (DedekindCut α)] [OrderTopology (DedekindCut α)] :
    Continuous (fun a : α => principal a) := by
  rw [OrderTopology.continuous_iff]
  refine fun c => ⟨?_, ?_⟩
  · have : IsOpen (⋃ a in c.right, Ioi a) := isOpen_biUnion fun _ _ => isOpen_Ioi
    convert this
    ext
    simp [lt_principal_iff]
  · have : IsOpen (⋃ a in c.left, Iio a) := isOpen_biUnion fun _ _ => isOpen_Iio
    convert this
    ext
    simp [principal_lt_iff]

namespace Order

/--
Definition of `Fill` / `Fill` 的定义

English:
abbreviation Fill
  signature: (α : Type*) [LinearOrder α]
  body: {x : α ×ₗ Rat //
    (IsSuccPrelimit (ofLex x).1 -> 0 <= (ofLex x).2) ∧
    (IsPredPrelimit (ofLex x).1 -> (ofLex x).2 <= 0) }

中文:
缩写 Fill
  签名: (α : 类型) [线性序 α]
  定义体: {x : α ×ₗ Rat //
    (IsSuccPrelimit (ofLex x).1 -> 0 <= (ofLex x).2) ∧
    (IsPredPrelimit (ofLex x).1 -> (ofLex x).2 <= 0) }

Depends on / 依赖: IsPredPrelimit, IsSuccPrelimit
-/
abbrev Fill (α : Type*) [LinearOrder α] : Type _ :=
  {x : α ×ₗ Rat //
    (IsSuccPrelimit (ofLex x).1 -> 0 <= (ofLex x).2) ∧
    (IsPredPrelimit (ofLex x).1 -> (ofLex x).2 <= 0) }

namespace Fill

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (Fill α)
  body: Preorder.topology _

中文:
实例 :
  签名: 拓扑空间 (Fill α)
  定义体: Preorder.topology _

Depends on / 依赖: Preorder, Preorder.topology, topology
-/
instance : TopologicalSpace (Fill α) := Preorder.topology _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology (Fill α)
  body: ⟨rfl⟩

中文:
实例 :
  签名: Order拓扑 (Fill α)
  定义体: ⟨rfl⟩
-/
instance : OrderTopology (Fill α) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `some` / `some` 的定义

English:
definition some
  signature: : α ↪o Fill α where
  body: ⟨toLex (x, 0), by simp⟩
  inj' _ := by simp
  map_rel_iff' := by simp [Prod.Lex.toLex_le_toLex']

中文:
定义 some
  签名: : α ↪o Fill α where
  定义体: ⟨toLex (x, 0), by simp⟩
  inj' _ := by simp
  map_rel_iff' := by simp [Prod.Lex.toLex_le_toLex']
-/
def some : α ↪o Fill α where
  toFun x := ⟨toLex (x, 0), by simp⟩
  inj' _ := by simp
  map_rel_iff' := by simp [Prod.Lex.toLex_le_toLex']

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DenselyOrdered (Fill α)
  body: by
    simp only [ofLex_toLex, Subtype.forall, Prod.Lex.lt_iff, Subtype.mk_lt_mk,
      Lex.forall, Prod.forall]
    rintro x q ⟨hx₁, hx₂⟩ y r ⟨hy₁, hy₂⟩ (h | ⟨rfl, h⟩)
    · by_cases hx : IsPredPrelimit x
      · obtain ⟨z, hz, hz'⟩ := hx.lt_iff_exists_lt.1 h
        use some z
        simp [some, 

中文:
实例 :
  签名: 稠密序 (Fill α)
  定义体: by
    simp only [ofLex_toLex, Subtype.forall, Prod.Lex.lt_iff, Subtype.mk_lt_mk,
      Lex.forall, Prod.forall]
    rintro x q ⟨hx₁, hx₂⟩ y r ⟨hy₁, hy₂⟩ (h | ⟨rfl, h⟩)
    · by_cases hx : IsPredPrelimit x
      · obtain ⟨z, hz, hz'⟩ := hx.lt_iff_exists_lt.1 h
        use some z
        simp [some, 

Depends on / 依赖: IsPredPrelimit, Lex.forall, Prod.Lex.lt_iff, Prod.forall, Subtype, Subtype.forall, Subtype.mk_lt_mk, exists_between, exists_gt, hx.lt_iff_exists_lt, lt_iff, lt_iff_exists_lt, max_lt_iff, mk_lt_mk, ofLex_toLex
-/
instance : DenselyOrdered (Fill α) where
  dense := by
    simp only [ofLex_toLex, Subtype.forall, Prod.Lex.lt_iff, Subtype.mk_lt_mk,
      Lex.forall, Prod.forall]
    rintro x q ⟨hx₁, hx₂⟩ y r ⟨hy₁, hy₂⟩ (h | ⟨rfl, h⟩)
    · by_cases hx : IsPredPrelimit x
      · obtain ⟨z, hz, hz'⟩ := hx.lt_iff_exists_lt.1 h
        use some z
        simp [some, Prod.Lex.lt_iff, hz', hz]
      obtain ⟨s, hs⟩ := exists_gt (max 0 q)
      rw [max_lt_iff] at hs
      refine ⟨⟨toLex (x, s), ?_⟩, ?_⟩
      · simp [hx, hs.1.le]
      · simp [Prod.Lex.lt_iff, hs.2, h]
    · obtain ⟨s, hs, hs'⟩ := exists_between h
      refine ⟨⟨toLex (x, s), ?_⟩, ?_⟩
      · grind [ofLex_toLex]
      · simp [Prod.Lex.lt_iff, hs, hs']

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `continuous_some` / 定理 `continuous_some`

English:
theorem continuous_some
  given: [TopologicalSpace α] [OrderTopology α]
  statement: Continuous (X := α) some
  proof: by
  simp only [OrderTopology.continuous_iff, ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall]
  refine fun x q ⟨hx₁, hx₂⟩ => ⟨?_, ?_⟩
  · obtain hq | hq := le_or_gt 0 q
    · convert isOpen_Ioi (a := x)
      ext
      simp [some, Prod.Lex.lt_iff, hq.not_gt]
· obtain ⟨y, hy⟩ := not_isSuccPreli

中文:
定理 continuous_some
  条件: [拓扑空间 α] [Order拓扑 α]
  结论: 连续 (X := α) some
  证明: by
  simp only [OrderTopology.continuous_iff, ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall]
  refine fun x q ⟨hx₁, hx₂⟩ => ⟨?_, ?_⟩
  · obtain hq | hq := le_or_gt 0 q
    · convert isOpen_Ioi (a := x)
      ext
      simp [some, Prod.Lex.lt_iff, hq.not_gt]
· obtain ⟨y, hy⟩ := not_isSuccPreli

Depends on / 依赖: Lex.forall, OrderTopology, OrderTopology.continuous_iff, Prod.Lex.lt_iff, Prod.forall, Subtype, Subtype.forall, continuous_iff, convert, hq.not_ge, hq.not_gt, hy.le_iff_lt_right, isOpen_Iio, isOpen_Ioi, le_iff_lt_or_eq, le_iff_lt_right, le_or_gt, lt_iff, not_ge, not_gt
-/
theorem continuous_some [TopologicalSpace α] [OrderTopology α] : Continuous (X := α) some := by
  simp only [OrderTopology.continuous_iff, ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall]
  refine fun x q ⟨hx₁, hx₂⟩ => ⟨?_, ?_⟩
  · obtain hq | hq := le_or_gt 0 q
    · convert isOpen_Ioi (a := x)
      ext
      simp [some, Prod.Lex.lt_iff, hq.not_gt]
· obtain ⟨y, hy⟩ := not_isSuccPrelimit_iff.1 mt hx₁ hq.not_ge
      convert isOpen_Ioi (a := y)
      ext
      simpa [some, Prod.Lex.lt_iff, hq, le_iff_lt_or_eq] using hy.le_iff_lt_right
  · obtain hq | hq := le_or_gt q 0
    · convert isOpen_Iio (a := x)
      ext
      simp [some, Prod.Lex.lt_iff, hq.not_gt]
· obtain ⟨y, hy⟩ := not_isPredPrelimit_iff.1 mt hx₂ hq.not_ge
      convert isOpen_Iio (a := y)
      ext
      simpa [some, Prod.Lex.lt_iff, hq, le_iff_lt_or_eq] using hy.le_iff_lt_left

end Fill

universe u

/--
theorem `exists_dense_continuous_completion` / 定理 `exists_dense_continuous_completion`

English:
theorem exists_dense_continuous_completion
  proof: let : TopologicalSpace (DedekindCut (Fill α)) := Preorder.topology _
  have : OrderTopology (DedekindCut (Fill α)) := ⟨rfl⟩
  ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
    Fill.some.trans DedekindCut.principalEmbedding,
    DedekindCut.continuous_principal.comp Fill.continuous_

中文:
定理 存在_dense_continuous_completion
  证明: let : TopologicalSpace (DedekindCut (Fill α)) := Preorder.topology _
  have : OrderTopology (DedekindCut (Fill α)) := ⟨rfl⟩
  ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
    Fill.some.trans DedekindCut.principalEmbedding,
    DedekindCut.continuous_principal.comp Fill.continuous_

Depends on / 依赖: DedekindCut, DedekindCut.continuous_principal.comp, DedekindCut.principalEmbedding, Fill.continuous_some, Fill.some.trans, OrderTopology, Preorder, Preorder.topology, TopologicalSpace, continuous_principal, continuous_some, principalEmbedding, topology
-/
theorem exists_dense_continuous_completion
    (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    exists (β : Type u) (_ : CompleteLinearOrder β) (_ : DenselyOrdered β) (_ : TopologicalSpace β)
      (_ : OrderTopology β) (ι : α ↪o β), Continuous ι :=
  let : TopologicalSpace (DedekindCut (Fill α)) := Preorder.topology _
  have : OrderTopology (DedekindCut (Fill α)) := ⟨rfl⟩
  ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
    Fill.some.trans DedekindCut.principalEmbedding,
    DedekindCut.continuous_principal.comp Fill.continuous_some⟩

end Order
