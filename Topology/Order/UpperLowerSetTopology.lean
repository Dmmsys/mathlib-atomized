/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Logic.Lemmas
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.LowerUpperTopology

/-!
# Upper and lower sets topologies

This file introduces the upper set topology on a preorder as the topology where the open sets are
the upper sets and the lower set topology on a preorder as the topology where the open sets are
the lower sets.

In general the upper set topology does not coincide with the upper topology and the lower set
topology does not coincide with the lower topology.

## Main statements

- `Topology.IsUpperSet.toAlexandrovDiscrete`: The upper set topology is Alexandrov-discrete.
- `Topology.IsUpperSet.isClosed_iff_isLower` - a set is closed if and only if it is a Lower set
- `Topology.IsUpperSet.closure_eq_lowerClosure` - topological closure coincides with lower closure
- `Topology.IsUpperSet.monotone_iff_continuous` - the continuous functions are the monotone
  functions
- `IsUpperSet.monotone_to_upperTopology_continuous`: A monotone map from a preorder with the upper
  set topology to a preorder with the upper topology is continuous.

We provide the upper set topology in three ways (and similarly for the lower set topology):
* `Topology.upperSet`: The upper set topology as a `TopologicalSpace α`
* `Topology.IsUpperSet`: Prop-valued mixin typeclass stating that an existing topology is the upper
  set topology.
* `Topology.WithUpperSet`: Type synonym equipping a preorder with its upper set topology.

## Motivation

An Alexandrov topology is a topology where the intersection of any collection of open sets is open.
The upper set topology is an Alexandrov topology and, given any Alexandrov topological space, we can
equip it with a preorder (namely the specialization preorder) whose upper set topology coincides
with the original topology. See `Topology.Specialization`.

## Tags

upper set topology, lower set topology, preorder, Alexandrov
-/

@[expose] public section

open Set TopologicalSpace Filter

variable {α β γ : Type*}

namespace Topology

/-- Topology whose open sets are upper sets.

Note: In general the upper set topology does not coincide with the upper topology. -/
@[instance_reducible]
/--
Definition of `upperSet` / `upperSet` 的定义

English:
definition upperSet
  signature: (α : Type*) [Preorder α]
  body: IsUpperSet
  isOpen_univ := isUpperSet_univ
  isOpen_inter _ _ := IsUpperSet.inter
  isOpen_sUnion _ := isUpperSet_sUnion

中文:
定义 upperSet
  签名: (α : 类型) [预序 α]
  定义体: IsUpperSet
  isOpen_univ := isUpperSet_univ
  isOpen_inter _ _ := IsUpperSet.inter
  isOpen_sUnion _ := isUpperSet_sUnion

Depends on / 依赖: IsUpperSet
-/
def upperSet (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsUpperSet
  isOpen_univ := isUpperSet_univ
  isOpen_inter _ _ := IsUpperSet.inter
  isOpen_sUnion _ := isUpperSet_sUnion

/-- Topology whose open sets are lower sets.

Note: In general the lower set topology does not coincide with the lower topology. -/
@[instance_reducible]
/--
Definition of `lowerSet` / `lowerSet` 的定义

English:
definition lowerSet
  signature: (α : Type*) [Preorder α]
  body: IsLowerSet
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ := IsLowerSet.inter
  isOpen_sUnion _ := isLowerSet_sUnion

中文:
定义 lowerSet
  签名: (α : 类型) [预序 α]
  定义体: IsLowerSet
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ := IsLowerSet.inter
  isOpen_sUnion _ := isLowerSet_sUnion

Depends on / 依赖: IsLowerSet
-/
def lowerSet (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsLowerSet
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ := IsLowerSet.inter
  isOpen_sUnion _ := isLowerSet_sUnion

/--
Definition of `WithUpperSet` / `WithUpperSet` 的定义

English:
definition WithUpperSet
  signature: (α : Type*)
  body: α

中文:
定义 WithUpperSet
  签名: (α : 类型)
  定义体: α
-/
def WithUpperSet (α : Type*) := α

namespace WithUpperSet

/--
Definition of `toUpperSet` / `toUpperSet` 的定义

English:
definition toUpperSet
  signature: : α ≃ WithUpperSet α
  body: Equiv.refl _

中文:
定义 toUpperSet
  签名: : α ≃ WithUpperSet α
  定义体: Equiv.refl _
-/
@[match_pattern] def toUpperSet : α ≃ WithUpperSet α := Equiv.refl _

/--
Definition of `ofUpperSet` / `ofUpperSet` 的定义

English:
definition ofUpperSet
  signature: : WithUpperSet α ≃ α
  body: Equiv.refl _

中文:
定义 ofUpperSet
  签名: : WithUpperSet α ≃ α
  定义体: Equiv.refl _
-/
@[match_pattern] def ofUpperSet : WithUpperSet α ≃ α := Equiv.refl _

/--
lemma `toUpperSet_symm` / 引理 `toUpperSet_symm`

English:
lemma toUpperSet_symm
  statement: (@toUpperSet α).symm = ofUpperSet
  proof: rfl

中文:
引理 toUpperSet_symm
  结论: (@toUpperSet α).symm = ofUpperSet
  证明: rfl
-/
@[simp] lemma toUpperSet_symm : (@toUpperSet α).symm = ofUpperSet := rfl
/--
lemma `ofUpperSet_symm` / 引理 `ofUpperSet_symm`

English:
lemma ofUpperSet_symm
  statement: (@ofUpperSet α).symm = toUpperSet
  proof: rfl

中文:
引理 ofUpperSet_symm
  结论: (@ofUpperSet α).symm = toUpperSet
  证明: rfl
-/
@[simp] lemma ofUpperSet_symm : (@ofUpperSet α).symm = toUpperSet := rfl
/--
lemma `toUpperSet_ofUpperSet` / 引理 `toUpperSet_ofUpperSet`

English:
lemma toUpperSet_ofUpperSet
  given: (a : WithUpperSet α)
  statement: toUpperSet (ofUpperSet a) = a
  proof: rfl

中文:
引理 toUpperSet_ofUpperSet
  条件: (a : WithUpperSet α)
  结论: toUpperSet (ofUpperSet a) = a
  证明: rfl
-/
@[simp] lemma toUpperSet_ofUpperSet (a : WithUpperSet α) : toUpperSet (ofUpperSet a) = a := rfl
/--
lemma `ofUpperSet_toUpperSet` / 引理 `ofUpperSet_toUpperSet`

English:
lemma ofUpperSet_toUpperSet
  given: (a : α)
  statement: ofUpperSet (toUpperSet a) = a
  proof: rfl

中文:
引理 ofUpperSet_toUpperSet
  条件: (a : α)
  结论: ofUpperSet (toUpperSet a) = a
  证明: rfl
-/
@[simp] lemma ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a := rfl
/--
lemma `toUpperSet_inj` / 引理 `toUpperSet_inj`

English:
lemma toUpperSet_inj
  given: {a b : α}
  statement: toUpperSet a = toUpperSet b ↔ a = b
  proof: Iff.rfl

中文:
引理 toUpperSet_inj
  条件: {a b : α}
  结论: toUpperSet a = toUpperSet b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b := Iff.rfl
/--
lemma `ofUpperSet_inj` / 引理 `ofUpperSet_inj`

English:
lemma ofUpperSet_inj
  given: {a b : WithUpperSet α}
  statement: ofUpperSet a = ofUpperSet b ↔ a = b
  proof: Iff.rfl

中文:
引理 ofUpperSet_inj
  条件: {a b : WithUpperSet α}
  结论: ofUpperSet a = ofUpperSet b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofUpperSet_inj {a b : WithUpperSet α} : ofUpperSet a = ofUpperSet b ↔ a = b := Iff.rfl

/-- A recursor for `WithUpperSet`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : WithUpperSet α -> Sort*} (toUpperSet : forall a, motive (toUpperSet a))
  body: fun a => toUpperSet (ofUpperSet a)

中文:
定义 rec
  签名: {motive : WithUpperSet α -> 类型层*} (toUpperSet : 对任意 a, motive (toUpperSet a))
  定义体: fun a => toUpperSet (ofUpperSet a)
-/
protected def rec {motive : WithUpperSet α -> Sort*} (toUpperSet : forall a, motive (toUpperSet a)) :
    forall a, motive a :=
  fun a => toUpperSet (ofUpperSet a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (WithUpperSet α)
  body: ‹Nonempty α›

中文:
实例 [非空
  签名: α] : 非空 (WithUpperSet α)
  定义体: ‹Nonempty α›

Depends on / 依赖: Nonempty
-/
instance [Nonempty α] : Nonempty (WithUpperSet α) := ‹Nonempty α›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (WithUpperSet α)
  body: ‹Inhabited α›

中文:
实例 [可居
  签名: α] : 可居 (WithUpperSet α)
  定义体: ‹Inhabited α›

Depends on / 依赖: Inhabited
-/
instance [Inhabited α] : Inhabited (WithUpperSet α) := ‹Inhabited α›

variable [Preorder α] [Preorder β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (WithUpperSet α)
  body: ‹Preorder α›

中文:
实例 :
  签名: 预序 (WithUpperSet α)
  定义体: ‹Preorder α›

Depends on / 依赖: Preorder
-/
instance : Preorder (WithUpperSet α) := ‹Preorder α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (WithUpperSet α)
  body: fast_instance% upperSet α

中文:
实例 :
  签名: 拓扑空间 (WithUpperSet α)
  定义体: fast_instance% upperSet α

Depends on / 依赖: fast_instance, upperSet
-/
instance : TopologicalSpace (WithUpperSet α) :=
  fast_instance% upperSet α

/--
lemma `ofUpperSet_le_iff` / 引理 `ofUpperSet_le_iff`

English:
lemma ofUpperSet_le_iff
  given: {a b : WithUpperSet α}
  statement: ofUpperSet a <= ofUpperSet b ↔ a <= b
  proof: Iff.rfl

中文:
引理 ofUpperSet_le_iff
  条件: {a b : WithUpperSet α}
  结论: ofUpperSet a <= ofUpperSet b ↔ a <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofUpperSet_le_iff {a b : WithUpperSet α} : ofUpperSet a <= ofUpperSet b ↔ a <= b := Iff.rfl
/--
lemma `toUpperSet_le_iff` / 引理 `toUpperSet_le_iff`

English:
lemma toUpperSet_le_iff
  given: {a b : α}
  statement: toUpperSet a <= toUpperSet b ↔ a <= b
  proof: Iff.rfl

中文:
引理 toUpperSet_le_iff
  条件: {a b : α}
  结论: toUpperSet a <= toUpperSet b ↔ a <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toUpperSet_le_iff {a b : α} : toUpperSet a <= toUpperSet b ↔ a <= b := Iff.rfl

/--
Definition of `ofUpperSetOrderIso` / `ofUpperSetOrderIso` 的定义

English:
definition ofUpperSetOrderIso
  signature: : WithUpperSet α ≃o α where
  body: ofUpperSet
  map_rel_iff' := ofUpperSet_le_iff

中文:
定义 ofUpperSetOrderIso
  签名: : WithUpperSet α ≃o α where
  定义体: ofUpperSet
  map_rel_iff' := ofUpperSet_le_iff

Depends on / 依赖: ofUpperSet
-/
def ofUpperSetOrderIso : WithUpperSet α ≃o α where
  toEquiv := ofUpperSet
  map_rel_iff' := ofUpperSet_le_iff

/--
Definition of `toUpperSetOrderIso` / `toUpperSetOrderIso` 的定义

English:
definition toUpperSetOrderIso
  signature: : α ≃o WithUpperSet α where
  body: toUpperSet
  map_rel_iff' := toUpperSet_le_iff

中文:
定义 toUpperSetOrderIso
  签名: : α ≃o WithUpperSet α where
  定义体: toUpperSet
  map_rel_iff' := toUpperSet_le_iff

Depends on / 依赖: toUpperSet
-/
def toUpperSetOrderIso : α ≃o WithUpperSet α where
  toEquiv := toUpperSet
  map_rel_iff' := toUpperSet_le_iff

end WithUpperSet

/--
Definition of `WithLowerSet` / `WithLowerSet` 的定义

English:
definition WithLowerSet
  signature: (α : Type*)
  body: α

中文:
定义 WithLowerSet
  签名: (α : 类型)
  定义体: α
-/
def WithLowerSet (α : Type*) := α

namespace WithLowerSet

/--
Definition of `toLowerSet` / `toLowerSet` 的定义

English:
definition toLowerSet
  signature: : α ≃ WithLowerSet α
  body: Equiv.refl _

中文:
定义 toLowerSet
  签名: : α ≃ WithLowerSet α
  定义体: Equiv.refl _
-/
@[match_pattern] def toLowerSet : α ≃ WithLowerSet α := Equiv.refl _

/--
Definition of `ofLowerSet` / `ofLowerSet` 的定义

English:
definition ofLowerSet
  signature: : WithLowerSet α ≃ α
  body: Equiv.refl _

中文:
定义 ofLowerSet
  签名: : WithLowerSet α ≃ α
  定义体: Equiv.refl _
-/
@[match_pattern] def ofLowerSet : WithLowerSet α ≃ α := Equiv.refl _

/--
lemma `toLowerSet_symm` / 引理 `toLowerSet_symm`

English:
lemma toLowerSet_symm
  statement: (@toLowerSet α).symm = ofLowerSet
  proof: rfl

中文:
引理 toLowerSet_symm
  结论: (@toLowerSet α).symm = ofLowerSet
  证明: rfl
-/
@[simp] lemma toLowerSet_symm : (@toLowerSet α).symm = ofLowerSet := rfl
/--
lemma `ofLowerSet_symm` / 引理 `ofLowerSet_symm`

English:
lemma ofLowerSet_symm
  statement: (@ofLowerSet α).symm = toLowerSet
  proof: rfl

中文:
引理 ofLowerSet_symm
  结论: (@ofLowerSet α).symm = toLowerSet
  证明: rfl
-/
@[simp] lemma ofLowerSet_symm : (@ofLowerSet α).symm = toLowerSet := rfl
/--
lemma `toLowerSet_ofLowerSet` / 引理 `toLowerSet_ofLowerSet`

English:
lemma toLowerSet_ofLowerSet
  given: (a : WithLowerSet α)
  statement: toLowerSet (ofLowerSet a) = a
  proof: rfl

中文:
引理 toLowerSet_ofLowerSet
  条件: (a : WithLowerSet α)
  结论: toLowerSet (ofLowerSet a) = a
  证明: rfl
-/
@[simp] lemma toLowerSet_ofLowerSet (a : WithLowerSet α) : toLowerSet (ofLowerSet a) = a := rfl
/--
lemma `ofLowerSet_toLowerSet` / 引理 `ofLowerSet_toLowerSet`

English:
lemma ofLowerSet_toLowerSet
  given: (a : α)
  statement: ofLowerSet (toLowerSet a) = a
  proof: rfl

中文:
引理 ofLowerSet_toLowerSet
  条件: (a : α)
  结论: ofLowerSet (toLowerSet a) = a
  证明: rfl
-/
@[simp] lemma ofLowerSet_toLowerSet (a : α) : ofLowerSet (toLowerSet a) = a := rfl
/--
lemma `toLowerSet_inj` / 引理 `toLowerSet_inj`

English:
lemma toLowerSet_inj
  given: {a b : α}
  statement: toLowerSet a = toLowerSet b ↔ a = b
  proof: Iff.rfl

中文:
引理 toLowerSet_inj
  条件: {a b : α}
  结论: toLowerSet a = toLowerSet b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b := Iff.rfl
/--
lemma `ofLowerSet_inj` / 引理 `ofLowerSet_inj`

English:
lemma ofLowerSet_inj
  given: {a b : WithLowerSet α}
  statement: ofLowerSet a = ofLowerSet b ↔ a = b
  proof: Iff.rfl

中文:
引理 ofLowerSet_inj
  条件: {a b : WithLowerSet α}
  结论: ofLowerSet a = ofLowerSet b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofLowerSet_inj {a b : WithLowerSet α} : ofLowerSet a = ofLowerSet b ↔ a = b := Iff.rfl

/-- A recursor for `WithLowerSet`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : WithLowerSet α -> Sort*} (toLowerSet : forall a, motive (toLowerSet a))
  body: fun a => toLowerSet (ofLowerSet a)

中文:
定义 rec
  签名: {motive : WithLowerSet α -> 类型层*} (toLowerSet : 对任意 a, motive (toLowerSet a))
  定义体: fun a => toLowerSet (ofLowerSet a)
-/
protected def rec {motive : WithLowerSet α -> Sort*} (toLowerSet : forall a, motive (toLowerSet a)) :
    forall a, motive a :=
  fun a => toLowerSet (ofLowerSet a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (WithLowerSet α)
  body: ‹Nonempty α›

中文:
实例 [非空
  签名: α] : 非空 (WithLowerSet α)
  定义体: ‹Nonempty α›

Depends on / 依赖: Nonempty
-/
instance [Nonempty α] : Nonempty (WithLowerSet α) := ‹Nonempty α›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (WithLowerSet α)
  body: ‹Inhabited α›

中文:
实例 [可居
  签名: α] : 可居 (WithLowerSet α)
  定义体: ‹Inhabited α›

Depends on / 依赖: Inhabited
-/
instance [Inhabited α] : Inhabited (WithLowerSet α) := ‹Inhabited α›

variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (WithLowerSet α)
  body: ‹Preorder α›

中文:
实例 :
  签名: 预序 (WithLowerSet α)
  定义体: ‹Preorder α›

Depends on / 依赖: Preorder
-/
instance : Preorder (WithLowerSet α) := ‹Preorder α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (WithLowerSet α)
  body: fast_instance% lowerSet α

中文:
实例 :
  签名: 拓扑空间 (WithLowerSet α)
  定义体: fast_instance% lowerSet α

Depends on / 依赖: fast_instance, lowerSet
-/
instance : TopologicalSpace (WithLowerSet α) :=
  fast_instance% lowerSet α

/--
lemma `ofLowerSet_le_iff` / 引理 `ofLowerSet_le_iff`

English:
lemma ofLowerSet_le_iff
  given: {a b : WithLowerSet α}
  statement: ofLowerSet a <= ofLowerSet b ↔ a <= b
  proof: Iff.rfl

中文:
引理 ofLowerSet_le_iff
  条件: {a b : WithLowerSet α}
  结论: ofLowerSet a <= ofLowerSet b ↔ a <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofLowerSet_le_iff {a b : WithLowerSet α} : ofLowerSet a <= ofLowerSet b ↔ a <= b := Iff.rfl
/--
lemma `toLowerSet_le_iff` / 引理 `toLowerSet_le_iff`

English:
lemma toLowerSet_le_iff
  given: {a b : α}
  statement: toLowerSet a <= toLowerSet b ↔ a <= b
  proof: Iff.rfl

中文:
引理 toLowerSet_le_iff
  条件: {a b : α}
  结论: toLowerSet a <= toLowerSet b ↔ a <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toLowerSet_le_iff {a b : α} : toLowerSet a <= toLowerSet b ↔ a <= b := Iff.rfl

/--
Definition of `ofLowerSetOrderIso` / `ofLowerSetOrderIso` 的定义

English:
definition ofLowerSetOrderIso
  signature: : WithLowerSet α ≃o α where
  body: ofLowerSet
  map_rel_iff' := ofLowerSet_le_iff

中文:
定义 ofLowerSetOrderIso
  签名: : WithLowerSet α ≃o α where
  定义体: ofLowerSet
  map_rel_iff' := ofLowerSet_le_iff

Depends on / 依赖: ofLowerSet
-/
def ofLowerSetOrderIso : WithLowerSet α ≃o α where
  toEquiv := ofLowerSet
  map_rel_iff' := ofLowerSet_le_iff

/--
Definition of `toLowerSetOrderIso` / `toLowerSetOrderIso` 的定义

English:
definition toLowerSetOrderIso
  signature: : α ≃o WithLowerSet α where
  body: toLowerSet
  map_rel_iff' := toLowerSet_le_iff

中文:
定义 toLowerSetOrderIso
  签名: : α ≃o WithLowerSet α where
  定义体: toLowerSet
  map_rel_iff' := toLowerSet_le_iff

Depends on / 依赖: toLowerSet
-/
def toLowerSetOrderIso : α ≃o WithLowerSet α where
  toEquiv := toLowerSet
  map_rel_iff' := toLowerSet_le_iff

end WithLowerSet

/--
Definition of `WithUpperSet.toDualHomeomorph` / `WithUpperSet.toDualHomeomorph` 的定义

English:
definition WithUpperSet.toDualHomeomorph
  signature: [Preorder α]
  body: OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

中文:
定义 WithUpperSet.toDualHomeomorph
  签名: [预序 α]
  定义体: OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

Depends on / 依赖: OrderDual, OrderDual.toDual, toDual
-/
def WithUpperSet.toDualHomeomorph [Preorder α] : WithUpperSet α ≃ₜ WithLowerSet αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

/--
Definition of `IsUpperSet` / `IsUpperSet` 的定义

English:
class IsUpperSet
  parameters: (α : Type*) [t : TopologicalSpace α] [Preorder α]
  axioms and operations (1):
    - topology_eq_upperSetTopology : t = upperSet α

中文:
类 是上集
  参数: (α : 类型) [t : 拓扑空间 α] [预序 α]
  公理与运算 (1 个):
    - topology_eq_upperSetTopology : t = upperSet α
-/
protected class IsUpperSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSet α

attribute [nolint docBlame] IsUpperSet.topology_eq_upperSetTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Topology.IsUpperSet (WithUpperSet α)
  body: ⟨rfl⟩

中文:
实例 [预序
  签名: α] : 拓扑.是上集 (WithUpperSet α)
  定义体: ⟨rfl⟩
-/
instance [Preorder α] : Topology.IsUpperSet (WithUpperSet α) := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : @Topology.IsUpperSet α (upperSet α) _
  body: by
  let := upperSet α
  exact ⟨rfl⟩

中文:
实例 [预序
  签名: α] : @拓扑.是上集 α (upperSet α) _
  定义体: by
  let := upperSet α
  exact ⟨rfl⟩

Depends on / 依赖: upperSet
-/
instance [Preorder α] : @Topology.IsUpperSet α (upperSet α) _ := by
  let := upperSet α
  exact ⟨rfl⟩

/--
Definition of `IsLowerSet` / `IsLowerSet` 的定义

English:
class IsLowerSet
  parameters: (α : Type*) [t : TopologicalSpace α] [Preorder α]
  axioms and operations (1):
    - topology_eq_lowerSetTopology : t = lowerSet α

中文:
类 是下集
  参数: (α : 类型) [t : 拓扑空间 α] [预序 α]
  公理与运算 (1 个):
    - topology_eq_lowerSetTopology : t = lowerSet α
-/
protected class IsLowerSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerSetTopology : t = lowerSet α

attribute [nolint docBlame] IsLowerSet.topology_eq_lowerSetTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Topology.IsLowerSet (WithLowerSet α)
  body: ⟨rfl⟩

中文:
实例 [预序
  签名: α] : 拓扑.是下集 (WithLowerSet α)
  定义体: ⟨rfl⟩
-/
instance [Preorder α] : Topology.IsLowerSet (WithLowerSet α) := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : @Topology.IsLowerSet α (lowerSet α) _
  body: by
  let := lowerSet α
  exact ⟨rfl⟩

中文:
实例 [预序
  签名: α] : @拓扑.是下集 α (lowerSet α) _
  定义体: by
  let := lowerSet α
  exact ⟨rfl⟩

Depends on / 依赖: lowerSet
-/
instance [Preorder α] : @Topology.IsLowerSet α (lowerSet α) _ := by
  let := lowerSet α
  exact ⟨rfl⟩

namespace IsUpperSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] {s : Set α}

/--
lemma `topology_eq` / 引理 `topology_eq`

English:
lemma topology_eq
  statement: ‹_› = upperSet α
  proof: topology_eq_upperSetTopology

中文:
引理 topology_eq
  结论: ‹_› = upperSet α
  证明: topology_eq_upperSetTopology

Depends on / 依赖: topology_eq_upperSetTopology
-/
lemma topology_eq : ‹_› = upperSet α := topology_eq_upperSetTopology

variable {α}

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_root_.OrderDual.instIsLowerSet` / 实例 `_root_.OrderDual.instIsLowerSet`

English:
instance _root_.OrderDual.instIsLowerSet
  signature: : Topology.IsLowerSet αᵒᵈ where
  body: by ext; rw [IsUpperSet.topology_eq α]

中文:
实例 _root_.OrderDual.instIsLowerSet
  签名: : 拓扑.是下集 αᵒᵈ where
  定义体: by ext; rw [IsUpperSet.topology_eq α]

Depends on / 依赖: IsUpperSet, IsUpperSet.topology_eq, topology_eq
-/
instance _root_.OrderDual.instIsLowerSet : Topology.IsLowerSet αᵒᵈ where
  topology_eq_lowerSetTopology := by ext; rw [IsUpperSet.topology_eq α]

/--
Definition of `WithUpperSetHomeomorph` / `WithUpperSetHomeomorph` 的定义

English:
definition WithUpperSetHomeomorph
  signature: : WithUpperSet α ≃ₜ α
  body: WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

中文:
定义 WithUpperSetHomeomorph
  签名: : WithUpperSet α ≃ₜ α
  定义体: WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

Depends on / 依赖: WithUpperSet, WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing, induced_id, induced_id.symm, ofUpperSet, toHomeomorphOfIsInducing, topology_eq
-/
def WithUpperSetHomeomorph : WithUpperSet α ≃ₜ α :=
  WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

/--
lemma `isOpen_iff_isUpperSet` / 引理 `isOpen_iff_isUpperSet`

English:
lemma isOpen_iff_isUpperSet
  statement: IsOpen s ↔ IsUpperSet s
  proof: by
  rw [topology_eq α]
  rfl

中文:
引理 isOpen_iff_isUpperSet
  结论: 是开集 s ↔ 是上集 s
  证明: by
  rw [topology_eq α]
  rfl

Depends on / 依赖: topology_eq
-/
lemma isOpen_iff_isUpperSet : IsOpen s ↔ IsUpperSet s := by
  rw [topology_eq α]
  rfl

/--
Instance `toAlexandrovDiscrete` / 实例 `toAlexandrovDiscrete`

English:
instance toAlexandrovDiscrete
  signature: : AlexandrovDiscrete α where
  body: by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)

中文:
实例 toAlexandrovDiscrete
  签名: : AlexandrovDiscrete α where
  定义体: by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)

Depends on / 依赖: isOpen_iff_isUpperSet, isUpperSet_sInter
-/
instance toAlexandrovDiscrete : AlexandrovDiscrete α where
  isOpen_sInter S := by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)

-- c.f. isClosed_iff_lower_and_subset_implies_LUB_mem
/--
lemma `isClosed_iff_isLower` / 引理 `isClosed_iff_isLower`

English:
lemma isClosed_iff_isLower
  statement: IsClosed s ↔ IsLowerSet s
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isUpperSet]; rw [isLowerSet_compl.symm]; rw [compl_compl]

中文:
引理 isClosed_iff_isLower
  结论: 是闭集 s ↔ 是下集 s
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isUpperSet]; rw [isLowerSet_compl.symm]; rw [compl_compl]

Depends on / 依赖: compl_compl, isLowerSet_compl, isLowerSet_compl.symm, isOpen_compl_iff, isOpen_iff_isUpperSet
-/
lemma isClosed_iff_isLower : IsClosed s ↔ IsLowerSet s := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isUpperSet]; rw [isLowerSet_compl.symm]; rw [compl_compl]

/--
lemma `closure_eq_lowerClosure` / 引理 `closure_eq_lowerClosure`

English:
lemma closure_eq_lowerClosure
  given: {s : Set α}
  statement: closure s = lowerClosure s
  proof: by
  rw [subset_antisymm_iff]
  refine ⟨?_, lowerClosure_min subset_closure (isClosed_iff_isLower.1 isClosed_closure)⟩
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)

中文:
引理 closure_eq_lowerClosure
  条件: {s : 集合 α}
  结论: closure s = lowerClosure s
  证明: by
  rw [subset_antisymm_iff]
  refine ⟨?_, lowerClosure_min subset_closure (isClosed_iff_isLower.1 isClosed_closure)⟩
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)

Depends on / 依赖: LowerSet, LowerSet.lower, closure_minimal, isClosed_closure, isClosed_iff_isLower, lowerClosure, lowerClosure_min, subset_antisymm_iff, subset_closure, subset_lowerClosure
-/
lemma closure_eq_lowerClosure {s : Set α} : closure s = lowerClosure s := by
  rw [subset_antisymm_iff]
  refine ⟨?_, lowerClosure_min subset_closure (isClosed_iff_isLower.1 isClosed_closure)⟩
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)

/--
lemma `closure_singleton` / 引理 `closure_singleton`

English:
lemma closure_singleton
  given: {a : α}
  statement: closure {a} = Iic a
  proof: by
  rw [closure_eq_lowerClosure]; rw [lowerClosure_singleton]
  rfl

中文:
引理 closure_singleton
  条件: {a : α}
  结论: closure {a} = 左无界右闭区间 a
  证明: by
  rw [closure_eq_lowerClosure]; rw [lowerClosure_singleton]
  rfl
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [closure_eq_lowerClosure]; rw [lowerClosure_singleton]
  rfl

/--
lemma `specializes_iff_le` / 引理 `specializes_iff_le`

English:
lemma specializes_iff_le
  given: {a b : α}
  statement: a ⤳ b ↔ b <= a
  proof: by
  simp only [specializes_iff_closure_subset, closure_singleton, Iic_subset_Iic]

中文:
引理 specializes_iff_le
  条件: {a b : α}
  结论: a ⤳ b ↔ b <= a
  证明: by
  simp only [specializes_iff_closure_subset, closure_singleton, Iic_subset_Iic]

Depends on / 依赖: Iic_subset_Iic, closure_singleton, specializes_iff_closure_subset
-/
lemma specializes_iff_le {a b : α} : a ⤳ b ↔ b <= a := by
  simp only [specializes_iff_closure_subset, closure_singleton, Iic_subset_Iic]

/--
lemma `nhdsKer_eq_upperClosure` / 引理 `nhdsKer_eq_upperClosure`

English:
lemma nhdsKer_eq_upperClosure
  given: (s : Set α)
  statement: nhdsKer s = ↑(upperClosure s)
  proof: by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

中文:
引理 nhdsKer_eq_upperClosure
  条件: (s : 集合 α)
  结论: nhdsKer s = ↑(upperClosure s)
  证明: by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

Depends on / 依赖: mem_nhdsKer_iff_specializes, specializes_iff_le
-/
lemma nhdsKer_eq_upperClosure (s : Set α) : nhdsKer s = ↑(upperClosure s) := by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

/--
lemma `nhdsKer_singleton` / 引理 `nhdsKer_singleton`

English:
lemma nhdsKer_singleton
  given: (a : α)
  statement: nhdsKer {a} = Ici a
  proof: by
  rw [nhdsKer_eq_upperClosure]; rw [upperClosure_singleton]; rw [UpperSet.coe_Ici]

中文:
引理 nhdsKer_singleton
  条件: (a : α)
  结论: nhdsKer {a} = 左闭右无界区间 a
  证明: by
  rw [nhdsKer_eq_upperClosure]; rw [upperClosure_singleton]; rw [UpperSet.coe_Ici]
-/
@[simp] lemma nhdsKer_singleton (a : α) : nhdsKer {a} = Ici a := by
  rw [nhdsKer_eq_upperClosure]; rw [upperClosure_singleton]; rw [UpperSet.coe_Ici]

/--
lemma `nhds_eq_principal_Ici` / 引理 `nhds_eq_principal_Ici`

English:
lemma nhds_eq_principal_Ici
  given: (a : α)
  statement: 𝓝 a = 𝓟 (Ici a)
  proof: by
  rw [← principal_nhdsKer_singleton]; rw [nhdsKer_singleton]

中文:
引理 nhds_eq_principal_Ici
  条件: (a : α)
  结论: 𝓝 a = 𝓟 (左闭右无界区间 a)
  证明: by
  rw [← principal_nhdsKer_singleton]; rw [nhdsKer_singleton]

Depends on / 依赖: nhdsKer_singleton, principal_nhdsKer_singleton
-/
lemma nhds_eq_principal_Ici (a : α) : 𝓝 a = 𝓟 (Ici a) := by
  rw [← principal_nhdsKer_singleton]; rw [nhdsKer_singleton]

/--
lemma `nhdsSet_eq_principal_upperClosure` / 引理 `nhdsSet_eq_principal_upperClosure`

English:
lemma nhdsSet_eq_principal_upperClosure
  given: (s : Set α)
  statement: 𝓝ˢ s = 𝓟 ↑(upperClosure s)
  proof: by
  rw [← principal_nhdsKer]; rw [nhdsKer_eq_upperClosure]

中文:
引理 nhdsSet_eq_principal_upperClosure
  条件: (s : 集合 α)
  结论: 𝓝ˢ s = 𝓟 ↑(upperClosure s)
  证明: by
  rw [← principal_nhdsKer]; rw [nhdsKer_eq_upperClosure]

Depends on / 依赖: nhdsKer_eq_upperClosure, principal_nhdsKer
-/
lemma nhdsSet_eq_principal_upperClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(upperClosure s) := by
  rw [← principal_nhdsKer]; rw [nhdsKer_eq_upperClosure]

end Preorder

/--
lemma `_root_.Topology.isUpperSet_iff_nhds` / 引理 `_root_.Topology.isUpperSet_iff_nhds`

English:
lemma _root_.Topology.isUpperSet_iff_nhds
  given: {α : Type*} [TopologicalSpace α] [Preorder α]
  proof: nhds_eq_principal_Ici a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Ici]⟩

中文:
引理 _root_.拓扑.isUpperSet_iff_nhds
  条件: {α : 类型} [拓扑空间 α] [预序 α]
  证明: nhds_eq_principal_Ici a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Ici]⟩
-/
protected lemma _root_.Topology.isUpperSet_iff_nhds {α : Type*} [TopologicalSpace α] [Preorder α] :
    Topology.IsUpperSet α ↔ (forall a : α, 𝓝 a = 𝓟 (Ici a)) where
  mp _ a := nhds_eq_principal_Ici a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Ici]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Topology.IsUpperSet Prop
  body: by
  simp [Topology.isUpperSet_iff_nhds, Prop.forall]

中文:
实例 :
  签名: 拓扑.是上集 命题
  定义体: by
  simp [Topology.isUpperSet_iff_nhds, Prop.forall]

Depends on / 依赖: Prop.forall, Topology, Topology.isUpperSet_iff_nhds, isUpperSet_iff_nhds
-/
instance : Topology.IsUpperSet Prop := by
  simp [Topology.isUpperSet_iff_nhds, Prop.forall]

section maps

variable [Preorder α] [Preorder β]

open Topology

/--
lemma `monotone_iff_continuous` / 引理 `monotone_iff_continuous`

English:
lemma monotone_iff_continuous
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs => IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic]; rw [← closure_singleton] at hab ⊢
    apply Continuous.closure_preimage_subset hf {f b}
    apply mem_of_mem_of_subset hab
    ap

中文:
引理 monotone_iff_continuous
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs => IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic]; rw [← closure_singleton] at hab ⊢
    apply Continuous.closure_preimage_subset hf {f b}
    apply mem_of_mem_of_subset hab
    ap
-/
protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [Topology.IsUpperSet β] {f : α -> β} : Monotone f ↔ Continuous f := by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs => IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic]; rw [← closure_singleton] at hab ⊢
    apply Continuous.closure_preimage_subset hf {f b}
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff]; rw [mem_preimage]; rw [mem_singleton_iff]

/--
lemma `monotone_to_upperTopology_continuous` / 引理 `monotone_to_upperTopology_continuous`

English:
lemma monotone_to_upperTopology_continuous
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  simp_rw [continuous_def, isOpen_iff_isUpperSet]
  intro s hs
  exact (IsUpper.isUpperSet_of_isOpen hs).preimage hf

中文:
引理 monotone_to_upperTopology_continuous
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  simp_rw [continuous_def, isOpen_iff_isUpperSet]
  intro s hs
  exact (IsUpper.isUpperSet_of_isOpen hs).preimage hf

Depends on / 依赖: IsUpper, IsUpper.isUpperSet_of_isOpen, continuous_def, isOpen_iff_isUpperSet, isUpperSet_of_isOpen, preimage, simp_rw
-/
lemma monotone_to_upperTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [IsUpper β] {f : α -> β} (hf : Monotone f) : Continuous f := by
  simp_rw [continuous_def, isOpen_iff_isUpperSet]
  intro s hs
  exact (IsUpper.isUpperSet_of_isOpen hs).preimage hf

/--
lemma `upperSet_le_upper` / 引理 `upperSet_le_upper`

English:
lemma upperSet_le_upper
  statement: {t₁ t₂ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ _]
  proof: fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact IsUpper.isUpperSet_of_isOpen hs

中文:
引理 upperSet_le_upper
  结论: {t₁ t₂ : 拓扑空间 α} [@拓扑.是上集 α t₁ _]
  证明: fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact IsUpper.isUpperSet_of_isOpen hs

Depends on / 依赖: IsUpper, IsUpper.isUpperSet_of_isOpen, isOpen_iff_isUpperSet, isUpperSet_of_isOpen
-/
lemma upperSet_le_upper {t₁ t₂ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ _]
    [@Topology.IsUpper α t₂ _] : t₁ <= t₂ := fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact IsUpper.isUpperSet_of_isOpen hs

end maps

end IsUpperSet

namespace IsLowerSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] {s : Set α}

/--
lemma `topology_eq` / 引理 `topology_eq`

English:
lemma topology_eq
  statement: ‹_› = lowerSet α
  proof: topology_eq_lowerSetTopology

中文:
引理 topology_eq
  结论: ‹_› = lowerSet α
  证明: topology_eq_lowerSetTopology

Depends on / 依赖: topology_eq_lowerSetTopology
-/
lemma topology_eq : ‹_› = lowerSet α := topology_eq_lowerSetTopology

variable {α}

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_root_.OrderDual.instIsUpperSet` / 实例 `_root_.OrderDual.instIsUpperSet`

English:
instance _root_.OrderDual.instIsUpperSet
  signature: : Topology.IsUpperSet αᵒᵈ where
  body: by ext; rw [IsLowerSet.topology_eq α]

中文:
实例 _root_.OrderDual.instIsUpperSet
  签名: : 拓扑.是上集 αᵒᵈ where
  定义体: by ext; rw [IsLowerSet.topology_eq α]

Depends on / 依赖: IsLowerSet, IsLowerSet.topology_eq, topology_eq
-/
instance _root_.OrderDual.instIsUpperSet : Topology.IsUpperSet αᵒᵈ where
  topology_eq_upperSetTopology := by ext; rw [IsLowerSet.topology_eq α]

/--
Definition of `WithLowerSetHomeomorph` / `WithLowerSetHomeomorph` 的定义

English:
definition WithLowerSetHomeomorph
  signature: : WithLowerSet α ≃ₜ α
  body: WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

中文:
定义 WithLowerSetHomeomorph
  签名: : WithLowerSet α ≃ₜ α
  定义体: WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

Depends on / 依赖: WithLowerSet, WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing, induced_id, induced_id.symm, ofLowerSet, toHomeomorphOfIsInducing, topology_eq
-/
def WithLowerSetHomeomorph : WithLowerSet α ≃ₜ α :=
  WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

/--
lemma `isOpen_iff_isLowerSet` / 引理 `isOpen_iff_isLowerSet`

English:
lemma isOpen_iff_isLowerSet
  statement: IsOpen s ↔ IsLowerSet s
  proof: by rw [topology_eq α]; rfl

中文:
引理 isOpen_iff_isLowerSet
  结论: 是开集 s ↔ 是下集 s
  证明: by rw [topology_eq α]; rfl

Depends on / 依赖: topology_eq
-/
lemma isOpen_iff_isLowerSet : IsOpen s ↔ IsLowerSet s := by rw [topology_eq α]; rfl

/--
Instance `toAlexandrovDiscrete` / 实例 `toAlexandrovDiscrete`

English:
instance toAlexandrovDiscrete
  signature: : AlexandrovDiscrete α
  body: IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)

中文:
实例 toAlexandrovDiscrete
  签名: : AlexandrovDiscrete α
  定义体: IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)

Depends on / 依赖: IsUpperSet, IsUpperSet.toAlexandrovDiscrete, toAlexandrovDiscrete
-/
instance toAlexandrovDiscrete : AlexandrovDiscrete α := IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)

/--
lemma `isClosed_iff_isUpper` / 引理 `isClosed_iff_isUpper`

English:
lemma isClosed_iff_isUpper
  statement: IsClosed s ↔ IsUpperSet s
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isLowerSet]; rw [isUpperSet_compl.symm]; rw [compl_compl]

中文:
引理 isClosed_iff_isUpper
  结论: 是闭集 s ↔ 是上集 s
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isLowerSet]; rw [isUpperSet_compl.symm]; rw [compl_compl]

Depends on / 依赖: compl_compl, isOpen_compl_iff, isOpen_iff_isLowerSet, isUpperSet_compl, isUpperSet_compl.symm
-/
lemma isClosed_iff_isUpper : IsClosed s ↔ IsUpperSet s := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isLowerSet]; rw [isUpperSet_compl.symm]; rw [compl_compl]

/--
lemma `closure_eq_upperClosure` / 引理 `closure_eq_upperClosure`

English:
lemma closure_eq_upperClosure
  given: {s : Set α}
  statement: closure s = upperClosure s
  proof: IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)

中文:
引理 closure_eq_upperClosure
  条件: {s : 集合 α}
  结论: closure s = upperClosure s
  证明: IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)

Depends on / 依赖: IsUpperSet, IsUpperSet.closure_eq_lowerClosure, closure_eq_lowerClosure
-/
lemma closure_eq_upperClosure {s : Set α} : closure s = upperClosure s :=
  IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)

/--
lemma `closure_singleton` / 引理 `closure_singleton`

English:
lemma closure_singleton
  given: {a : α}
  statement: closure {a} = Ici a
  proof: by
  rw [closure_eq_upperClosure]; rw [upperClosure_singleton]
  rfl

中文:
引理 closure_singleton
  条件: {a : α}
  结论: closure {a} = 左闭右无界区间 a
  证明: by
  rw [closure_eq_upperClosure]; rw [upperClosure_singleton]
  rfl
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Ici a := by
  rw [closure_eq_upperClosure]; rw [upperClosure_singleton]
  rfl

/--
lemma `specializes_iff_le` / 引理 `specializes_iff_le`

English:
lemma specializes_iff_le
  given: {a b : α}
  statement: a ⤳ b ↔ a <= b
  proof: by
  simp only [specializes_iff_closure_subset, closure_singleton, Ici_subset_Ici]

中文:
引理 specializes_iff_le
  条件: {a b : α}
  结论: a ⤳ b ↔ a <= b
  证明: by
  simp only [specializes_iff_closure_subset, closure_singleton, Ici_subset_Ici]

Depends on / 依赖: Ici_subset_Ici, closure_singleton, specializes_iff_closure_subset
-/
lemma specializes_iff_le {a b : α} : a ⤳ b ↔ a <= b := by
  simp only [specializes_iff_closure_subset, closure_singleton, Ici_subset_Ici]

/--
lemma `nhdsKer_eq_lowerClosure` / 引理 `nhdsKer_eq_lowerClosure`

English:
lemma nhdsKer_eq_lowerClosure
  given: (s : Set α)
  statement: nhdsKer s = ↑(lowerClosure s)
  proof: by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

中文:
引理 nhdsKer_eq_lowerClosure
  条件: (s : 集合 α)
  结论: nhdsKer s = ↑(lowerClosure s)
  证明: by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

Depends on / 依赖: mem_nhdsKer_iff_specializes, specializes_iff_le
-/
lemma nhdsKer_eq_lowerClosure (s : Set α) : nhdsKer s = ↑(lowerClosure s) := by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

/--
lemma `nhdsKer_singleton` / 引理 `nhdsKer_singleton`

English:
lemma nhdsKer_singleton
  given: (a : α)
  statement: nhdsKer {a} = Iic a
  proof: by
  rw [nhdsKer_eq_lowerClosure]; rw [lowerClosure_singleton]; rw [LowerSet.coe_Iic]

中文:
引理 nhdsKer_singleton
  条件: (a : α)
  结论: nhdsKer {a} = 左无界右闭区间 a
  证明: by
  rw [nhdsKer_eq_lowerClosure]; rw [lowerClosure_singleton]; rw [LowerSet.coe_Iic]
-/
@[simp] lemma nhdsKer_singleton (a : α) : nhdsKer {a} = Iic a := by
  rw [nhdsKer_eq_lowerClosure]; rw [lowerClosure_singleton]; rw [LowerSet.coe_Iic]

/--
lemma `nhds_eq_principal_Iic` / 引理 `nhds_eq_principal_Iic`

English:
lemma nhds_eq_principal_Iic
  given: (a : α)
  statement: 𝓝 a = 𝓟 (Iic a)
  proof: by
  rw [← principal_nhdsKer_singleton]; rw [nhdsKer_singleton]

中文:
引理 nhds_eq_principal_Iic
  条件: (a : α)
  结论: 𝓝 a = 𝓟 (左无界右闭区间 a)
  证明: by
  rw [← principal_nhdsKer_singleton]; rw [nhdsKer_singleton]

Depends on / 依赖: nhdsKer_singleton, principal_nhdsKer_singleton
-/
lemma nhds_eq_principal_Iic (a : α) : 𝓝 a = 𝓟 (Iic a) := by
  rw [← principal_nhdsKer_singleton]; rw [nhdsKer_singleton]

/--
lemma `nhdsSet_eq_principal_lowerClosure` / 引理 `nhdsSet_eq_principal_lowerClosure`

English:
lemma nhdsSet_eq_principal_lowerClosure
  given: (s : Set α)
  statement: 𝓝ˢ s = 𝓟 ↑(lowerClosure s)
  proof: by
  rw [← principal_nhdsKer]; rw [nhdsKer_eq_lowerClosure]

中文:
引理 nhdsSet_eq_principal_lowerClosure
  条件: (s : 集合 α)
  结论: 𝓝ˢ s = 𝓟 ↑(lowerClosure s)
  证明: by
  rw [← principal_nhdsKer]; rw [nhdsKer_eq_lowerClosure]

Depends on / 依赖: nhdsKer_eq_lowerClosure, principal_nhdsKer
-/
lemma nhdsSet_eq_principal_lowerClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(lowerClosure s) := by
  rw [← principal_nhdsKer]; rw [nhdsKer_eq_lowerClosure]

end Preorder

/--
lemma `_root_.Topology.isLowerSet_iff_nhds` / 引理 `_root_.Topology.isLowerSet_iff_nhds`

English:
lemma _root_.Topology.isLowerSet_iff_nhds
  given: {α : Type*} [TopologicalSpace α] [Preorder α]
  proof: nhds_eq_principal_Iic a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Iic]⟩

中文:
引理 _root_.拓扑.isLowerSet_iff_nhds
  条件: {α : 类型} [拓扑空间 α] [预序 α]
  证明: nhds_eq_principal_Iic a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Iic]⟩
-/
protected lemma _root_.Topology.isLowerSet_iff_nhds {α : Type*} [TopologicalSpace α] [Preorder α] :
    Topology.IsLowerSet α ↔ (forall a : α, 𝓝 a = 𝓟 (Iic a)) where
  mp _ a := nhds_eq_principal_Iic a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Iic]⟩

section maps

variable [Preorder α] [Preorder β]

open Topology
open OrderDual

/--
lemma `monotone_iff_continuous` / 引理 `monotone_iff_continuous`

English:
lemma monotone_iff_continuous
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  rw [← monotone_dual_iff]
  exact IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f := (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ))

中文:
引理 monotone_iff_continuous
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  rw [← monotone_dual_iff]
  exact IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f := (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ))
-/
protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [Topology.IsLowerSet β] {f : α -> β} : Monotone f ↔ Continuous f := by
  rw [← monotone_dual_iff]
  exact IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f := (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ))

/--
lemma `monotone_to_lowerTopology_continuous` / 引理 `monotone_to_lowerTopology_continuous`

English:
lemma monotone_to_lowerTopology_continuous
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ) hf.dual

中文:
引理 monotone_to_lowerTopology_continuous
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ) hf.dual

Depends on / 依赖: IsUpperSet, IsUpperSet.monotone_to_upperTopology_continuous, hf.dual, monotone_to_upperTopology_continuous
-/
lemma monotone_to_lowerTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [IsLower β] {f : α -> β} (hf : Monotone f) : Continuous f :=
  IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ) hf.dual

/--
lemma `lowerSet_le_lower` / 引理 `lowerSet_le_lower`

English:
lemma lowerSet_le_lower
  statement: {t₁ t₂ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ _]
  proof: fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact IsLower.isLowerSet_of_isOpen hs

中文:
引理 lowerSet_le_lower
  结论: {t₁ t₂ : 拓扑空间 α} [@拓扑.是下集 α t₁ _]
  证明: fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact IsLower.isLowerSet_of_isOpen hs

Depends on / 依赖: IsLower, IsLower.isLowerSet_of_isOpen, isLowerSet_of_isOpen, isOpen_iff_isLowerSet
-/
lemma lowerSet_le_lower {t₁ t₂ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ _]
    [@IsLower α t₂ _] : t₁ <= t₂ := fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact IsLower.isLowerSet_of_isOpen hs

end maps

end IsLowerSet

/--
lemma `isUpperSet_orderDual` / 引理 `isUpperSet_orderDual`

English:
lemma isUpperSet_orderDual
  given: [Preorder α] [TopologicalSpace α]
  proof: by
  constructor
  · apply OrderDual.instIsLowerSet
  · apply OrderDual.instIsUpperSet

中文:
引理 isUpperSet_orderDual
  条件: [预序 α] [拓扑空间 α]
  证明: by
  constructor
  · apply OrderDual.instIsLowerSet
  · apply OrderDual.instIsUpperSet

Depends on / 依赖: OrderDual, OrderDual.instIsLowerSet, OrderDual.instIsUpperSet, instIsLowerSet, instIsUpperSet
-/
lemma isUpperSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsUpperSet αᵒᵈ ↔ Topology.IsLowerSet α := by
  constructor
  · apply OrderDual.instIsLowerSet
  · apply OrderDual.instIsUpperSet

/--
lemma `isLowerSet_orderDual` / 引理 `isLowerSet_orderDual`

English:
lemma isLowerSet_orderDual
  given: [Preorder α] [TopologicalSpace α]
  proof: isUpperSet_orderDual.symm

中文:
引理 isLowerSet_orderDual
  条件: [预序 α] [拓扑空间 α]
  证明: isUpperSet_orderDual.symm

Depends on / 依赖: isUpperSet_orderDual, isUpperSet_orderDual.symm
-/
lemma isLowerSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsLowerSet αᵒᵈ ↔ Topology.IsUpperSet α := isUpperSet_orderDual.symm

namespace WithUpperSet
variable [Preorder α] [Preorder β] [Preorder γ]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ->o β)
  body: toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 fun _s hs => IsUpperSet.preimage hs f.monotone

中文:
定义 map
  签名: (f : α ->o β)
  定义体: toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 fun _s hs => IsUpperSet.preimage hs f.monotone

Depends on / 依赖: ofUpperSet, toUpperSet
-/
def map (f : α ->o β) : C(WithUpperSet α, WithUpperSet β) where
  toFun := toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 fun _s hs => IsUpperSet.preimage hs f.monotone

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (OrderHom.id : α ->o α) = ContinuousMap.id _
  proof: rfl

中文:
引理 map_id
  结论: map (序态射.id : α ->o α) = 连续映射.id _
  证明: rfl
-/
@[simp] lemma map_id : map (OrderHom.id : α ->o α) = ContinuousMap.id _ := rfl
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (g : β ->o γ) (f : α ->o β)
  statement: map (g.comp f) = (map g).comp (map f)
  proof: rfl

中文:
引理 map_comp
  条件: (g : β ->o γ) (f : α ->o β)
  结论: map (g.comp f) = (map g).comp (map f)
  证明: rfl
-/
@[simp] lemma map_comp (g : β ->o γ) (f : α ->o β) : map (g.comp f) = (map g).comp (map f) := rfl

/--
lemma `toUpperSet_specializes_toUpperSet` / 引理 `toUpperSet_specializes_toUpperSet`

English:
lemma toUpperSet_specializes_toUpperSet
  given: {a b : α}
  proof: by
  simp_rw [specializes_iff_closure_subset, IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]

中文:
引理 toUpperSet_specializes_toUpperSet
  条件: {a b : α}
  证明: by
  simp_rw [specializes_iff_closure_subset, IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]
-/
@[simp] lemma toUpperSet_specializes_toUpperSet {a b : α} :
    toUpperSet a ⤳ toUpperSet b ↔ b <= a := by
  simp_rw [specializes_iff_closure_subset, IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]

/--
lemma `ofUpperSet_le_ofUpperSet` / 引理 `ofUpperSet_le_ofUpperSet`

English:
lemma ofUpperSet_le_ofUpperSet
  given: {a b : WithUpperSet α}
  proof: toUpperSet_specializes_toUpperSet.symm

中文:
引理 ofUpperSet_le_ofUpperSet
  条件: {a b : WithUpperSet α}
  证明: toUpperSet_specializes_toUpperSet.symm
-/
@[simp] lemma ofUpperSet_le_ofUpperSet {a b : WithUpperSet α} :
    ofUpperSet a <= ofUpperSet b ↔ b ⤳ a := toUpperSet_specializes_toUpperSet.symm

/--
lemma `isUpperSet_toUpperSet_preimage` / 引理 `isUpperSet_toUpperSet_preimage`

English:
lemma isUpperSet_toUpperSet_preimage
  given: {s : Set (WithUpperSet α)}
  proof: Iff.rfl

中文:
引理 isUpperSet_toUpperSet_preimage
  条件: {s : 集合 (WithUpperSet α)}
  证明: Iff.rfl
-/
@[simp] lemma isUpperSet_toUpperSet_preimage {s : Set (WithUpperSet α)} :
    IsUpperSet (toUpperSet ⁻¹' s) ↔ IsOpen s := Iff.rfl

/--
lemma `isOpen_ofUpperSet_preimage` / 引理 `isOpen_ofUpperSet_preimage`

English:
lemma isOpen_ofUpperSet_preimage
  given: {s : Set α}
  proof: isUpperSet_toUpperSet_preimage.symm

中文:
引理 isOpen_ofUpperSet_preimage
  条件: {s : 集合 α}
  证明: isUpperSet_toUpperSet_preimage.symm
-/
@[simp] lemma isOpen_ofUpperSet_preimage {s : Set α} :
    IsOpen (ofUpperSet ⁻¹' s) ↔ IsUpperSet s := isUpperSet_toUpperSet_preimage.symm

end WithUpperSet

namespace WithLowerSet
variable [Preorder α] [Preorder β] [Preorder γ]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ->o β)
  body: toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 fun _s hs => IsLowerSet.preimage hs f.monotone

中文:
定义 map
  签名: (f : α ->o β)
  定义体: toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 fun _s hs => IsLowerSet.preimage hs f.monotone

Depends on / 依赖: ofLowerSet, toLowerSet
-/
def map (f : α ->o β) : C(WithLowerSet α, WithLowerSet β) where
  toFun := toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 fun _s hs => IsLowerSet.preimage hs f.monotone

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (OrderHom.id : α ->o α) = ContinuousMap.id _
  proof: rfl

中文:
引理 map_id
  结论: map (序态射.id : α ->o α) = 连续映射.id _
  证明: rfl
-/
@[simp] lemma map_id : map (OrderHom.id : α ->o α) = ContinuousMap.id _ := rfl
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (g : β ->o γ) (f : α ->o β)
  statement: map (g.comp f) = (map g).comp (map f)
  proof: rfl

中文:
引理 map_comp
  条件: (g : β ->o γ) (f : α ->o β)
  结论: map (g.comp f) = (map g).comp (map f)
  证明: rfl
-/
@[simp] lemma map_comp (g : β ->o γ) (f : α ->o β) : map (g.comp f) = (map g).comp (map f) := rfl

/--
lemma `toLowerSet_specializes_toLowerSet` / 引理 `toLowerSet_specializes_toLowerSet`

English:
lemma toLowerSet_specializes_toLowerSet
  given: {a b : α}
  proof: by
  simp_rw [specializes_iff_closure_subset, IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]

中文:
引理 toLowerSet_specializes_toLowerSet
  条件: {a b : α}
  证明: by
  simp_rw [specializes_iff_closure_subset, IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]
-/
@[simp] lemma toLowerSet_specializes_toLowerSet {a b : α} :
    toLowerSet a ⤳ toLowerSet b ↔ a <= b := by
  simp_rw [specializes_iff_closure_subset, IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]

/--
lemma `ofLowerSet_le_ofLowerSet` / 引理 `ofLowerSet_le_ofLowerSet`

English:
lemma ofLowerSet_le_ofLowerSet
  given: {a b : WithLowerSet α}
  proof: toLowerSet_specializes_toLowerSet.symm

中文:
引理 ofLowerSet_le_ofLowerSet
  条件: {a b : WithLowerSet α}
  证明: toLowerSet_specializes_toLowerSet.symm
-/
@[simp] lemma ofLowerSet_le_ofLowerSet {a b : WithLowerSet α} :
    ofLowerSet a <= ofLowerSet b ↔ a ⤳ b := toLowerSet_specializes_toLowerSet.symm

/--
lemma `isLowerSet_toLowerSet_preimage` / 引理 `isLowerSet_toLowerSet_preimage`

English:
lemma isLowerSet_toLowerSet_preimage
  given: {s : Set (WithLowerSet α)}
  proof: Iff.rfl

中文:
引理 isLowerSet_toLowerSet_preimage
  条件: {s : 集合 (WithLowerSet α)}
  证明: Iff.rfl
-/
@[simp] lemma isLowerSet_toLowerSet_preimage {s : Set (WithLowerSet α)} :
    IsLowerSet (toLowerSet ⁻¹' s) ↔ IsOpen s := Iff.rfl

/--
lemma `isOpen_ofLowerSet_preimage` / 引理 `isOpen_ofLowerSet_preimage`

English:
lemma isOpen_ofLowerSet_preimage
  given: {s : Set α}
  proof: isLowerSet_toLowerSet_preimage.symm

中文:
引理 isOpen_ofLowerSet_preimage
  条件: {s : 集合 α}
  证明: isLowerSet_toLowerSet_preimage.symm
-/
@[simp] lemma isOpen_ofLowerSet_preimage {s : Set α} :
    IsOpen (ofLowerSet ⁻¹' s) ↔ IsLowerSet s := isLowerSet_toLowerSet_preimage.symm

end WithLowerSet
end Topology
