/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.Order.LowerUpperTopology
public import Mathlib.Topology.Order.ScottTopology

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `Topology.lawson` - the Lawson topology is defined as the meet of the lower topology and the
  Scott topology.
- `Topology.IsLawson.lawsonBasis` - The complements of the upper closures of finite sets
  intersected with Scott open sets.

## Main statements

- `Topology.IsLawson.isTopologicalBasis` - `Topology.IsLawson.lawsonBasis` is a basis for
  `Topology.IsLawson`
- `Topology.lawsonOpen_iff_scottOpen_of_isUpperSet'` - An upper set is Lawson open if and only if it
  is Scott open
- `Topology.lawsonClosed_iff_dirSupClosed_of_isLowerSet` - A lower set is Lawson closed if and only
  if it is closed under sups of directed sets
- `Topology.IsLawson.t0Space` - The Lawson topology is T₀

## Implementation notes

A type synonym `Topology.WithLawson` is introduced and for a preorder `α`, `Topology.WithLawson α`
is made an instance of `TopologicalSpace` by `Topology.lawson`.

We define a mixin class `Topology.IsLawson` for the class of types which are both a preorder and a
topology and where the topology is `Topology.lawson`.
It is shown that `Topology.WithLawson α` is an instance of `Topology.IsLawson`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags

Lawson topology, preorder
-/

@[expose] public section

open Set TopologicalSpace

variable {α : Type*}

namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

/--
The Lawson topology is defined as the meet of `Topology.lower` and the `Topology.scott`.
-/
@[instance_reducible]
/--
Definition of `lawson` / `lawson` 的定义

English:
definition lawson
  signature: (α : Type*) [Preorder α]
  body: lower α ⊓ scott α univ

中文:
定义 lawson
  签名: (α : 类型) [预序 α]
  定义体: lower α ⊓ scott α univ
-/
def lawson (α : Type*) [Preorder α] : TopologicalSpace α := lower α ⊓ scott α univ

variable (α) [Preorder α] [TopologicalSpace α]

/--
Definition of `IsLawson` / `IsLawson` 的定义

English:
class IsLawson
  parameters: : Prop where
  axioms and operations (1):
    - topology_eq_lawson : ‹TopologicalSpace α› = lawson α

中文:
类 是Lawson
  参数: : 命题 where
  公理与运算 (1 个):
    - topology_eq_lawson : ‹拓扑空间 α› = lawson α
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson α

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsLawson α]

/--
Definition of `lawsonBasis` / `lawsonBasis` 的定义

English:
definition lawsonBasis
  body: { s : Set α | exists t : Set α, t.Finite ∧ exists u : Set α, IsOpen[scott α univ] u ∧
      u \ upperClosure t = s }

中文:
定义 lawsonBasis
  定义体: { s : Set α | exists t : Set α, t.Finite ∧ exists u : Set α, IsOpen[scott α univ] u ∧
      u \ upperClosure t = s }

Depends on / 依赖: Finite, IsOpen, t.Finite
-/
def lawsonBasis := { s : Set α | exists t : Set α, t.Finite ∧ exists u : Set α, IsOpen[scott α univ] u ∧
      u \ upperClosure t = s }

/--
theorem `isTopologicalBasis` / 定理 `isTopologicalBasis`

English:
theorem isTopologicalBasis
  statement: TopologicalSpace.IsTopologicalBasis (lawsonBasis α)
  proof: by
  have lawsonBasis_image2 : lawsonBasis α =
      (image2 (fun x x_1 => ⇑WithLower.toLower ⁻¹' x inter ⇑WithScott.toScott ⁻¹' x_1)
        (IsLower.lowerBasis (WithLower α)) {U | IsOpen[scott α univ] U}) := by
    rw [lawsonBasis]; rw [image2]; rw [IsLower.lowerBasis]
    simp_rw [sdiff_eq_compl_inter]
    aesop
  rw [lawsonBasis_image2]
  convert!
    IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
      (isTopologicalBasis_opens (α := WithScott α)) WithLower.toLower WithScott.toScott
  rw [@topology_eq_lawson α _ _ _]; rw [lawson]
  apply (congrArg₂ min _) _
  · let _ := lower α
    exact (@IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩).isInducing.eq_induced
  · let _ := scott α univ
    exact (@IsScott.withScottHomeomorph α _ (scott α univ) ⟨rfl⟩).isInducing.eq_induced

中文:
定理 isTopologicalBasis
  结论: 拓扑空间.是TopologicalBasis (lawsonBasis α)
  证明: by
  have lawsonBasis_image2 : lawsonBasis α =
      (image2 (fun x x_1 => ⇑WithLower.toLower ⁻¹' x inter ⇑WithScott.toScott ⁻¹' x_1)
        (IsLower.lowerBasis (WithLower α)) {U | IsOpen[scott α univ] U}) := by
    rw [lawsonBasis]; rw [image2]; rw [IsLower.lowerBasis]
    simp_rw [sdiff_eq_compl_inter]
    aesop
  rw [lawsonBasis_image2]
  convert!
    IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
      (isTopologicalBasis_opens (α := WithScott α)) WithLower.toLower WithScott.toScott
  rw [@topology_eq_lawson α _ _ _]; rw [lawson]
  apply (congrArg₂ min _) _
  · let _ := lower α
    exact (@IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩).isInducing.eq_induced
  · let _ := scott α univ
    exact (@IsScott.withScottHomeomorph α _ (scott α univ) ⟨rfl⟩).isInducing.eq_induced
-/
protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawsonBasis α) := by
  have lawsonBasis_image2 : lawsonBasis α =
      (image2 (fun x x_1 => ⇑WithLower.toLower ⁻¹' x inter ⇑WithScott.toScott ⁻¹' x_1)
        (IsLower.lowerBasis (WithLower α)) {U | IsOpen[scott α univ] U}) := by
    rw [lawsonBasis]; rw [image2]; rw [IsLower.lowerBasis]
    simp_rw [sdiff_eq_compl_inter]
    aesop
  rw [lawsonBasis_image2]
  convert!
    IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
      (isTopologicalBasis_opens (α := WithScott α)) WithLower.toLower WithScott.toScott
  rw [@topology_eq_lawson α _ _ _]; rw [lawson]
  apply (congrArg₂ min _) _
  · let _ := lower α
    exact (@IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩).isInducing.eq_induced
  · let _ := scott α univ
    exact (@IsScott.withScottHomeomorph α _ (scott α univ) ⟨rfl⟩).isInducing.eq_induced

end Preorder
end IsLawson

/--
Definition of `WithLawson` / `WithLawson` 的定义

English:
definition WithLawson
  signature: (α : Type*)
  body: α

中文:
定义 WithLawson
  签名: (α : 类型)
  定义体: α
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/--
Definition of `toLawson` / `toLawson` 的定义

English:
definition toLawson
  signature: : α ≃ WithLawson α
  body: Equiv.refl _

中文:
定义 toLawson
  签名: : α ≃ WithLawson α
  定义体: Equiv.refl _
-/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/--
Definition of `ofLawson` / `ofLawson` 的定义

English:
definition ofLawson
  signature: : WithLawson α ≃ α
  body: Equiv.refl _

中文:
定义 ofLawson
  签名: : WithLawson α ≃ α
  定义体: Equiv.refl _
-/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

/--
lemma `to_Lawson_symm_eq` / 引理 `to_Lawson_symm_eq`

English:
lemma to_Lawson_symm_eq
  statement: (@toLawson α).symm = ofLawson
  proof: rfl

中文:
引理 to_Lawson_symm_eq
  结论: (@toLawson α).symm = ofLawson
  证明: rfl
-/
@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
/--
lemma `of_Lawson_symm_eq` / 引理 `of_Lawson_symm_eq`

English:
lemma of_Lawson_symm_eq
  statement: (@ofLawson α).symm = toLawson
  proof: rfl

中文:
引理 of_Lawson_symm_eq
  结论: (@ofLawson α).symm = toLawson
  证明: rfl
-/
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
/--
lemma `toLawson_ofLawson` / 引理 `toLawson_ofLawson`

English:
lemma toLawson_ofLawson
  given: (a : WithLawson α)
  statement: toLawson (ofLawson a) = a
  proof: rfl

中文:
引理 toLawson_ofLawson
  条件: (a : WithLawson α)
  结论: toLawson (ofLawson a) = a
  证明: rfl
-/
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
/--
lemma `ofLawson_toLawson` / 引理 `ofLawson_toLawson`

English:
lemma ofLawson_toLawson
  given: (a : α)
  statement: ofLawson (toLawson a) = a
  proof: rfl

中文:
引理 ofLawson_toLawson
  条件: (a : α)
  结论: ofLawson (toLawson a) = a
  证明: rfl
-/
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl

/--
lemma `toLawson_inj` / 引理 `toLawson_inj`

English:
lemma toLawson_inj
  given: {a b : α}
  statement: toLawson a = toLawson b ↔ a = b
  proof: Iff.rfl

中文:
引理 toLawson_inj
  条件: {a b : α}
  结论: toLawson a = toLawson b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl

/--
lemma `ofLawson_inj` / 引理 `ofLawson_inj`

English:
lemma ofLawson_inj
  given: {a b : WithLawson α}
  statement: ofLawson a = ofLawson b ↔ a = b
  proof: Iff.rfl

中文:
引理 ofLawson_inj
  条件: {a b : WithLawson α}
  结论: ofLawson a = ofLawson b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b := Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {β : WithLawson α -> Sort*}
  body: fun a => h (ofLawson a)

中文:
定义 rec
  签名: {β : WithLawson α -> 类型层*}
  定义体: fun a => h (ofLawson a)
-/
protected def rec {β : WithLawson α -> Sort*}
    (h : forall a, β (toLawson a)) : forall a, β a := fun a => h (ofLawson a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (WithLawson α)
  body: ‹Nonempty α›

中文:
实例 [非空
  签名: α] : 非空 (WithLawson α)
  定义体: ‹Nonempty α›

Depends on / 依赖: Nonempty
-/
instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (WithLawson α)
  body: ‹Inhabited α›

中文:
实例 [可居
  签名: α] : 可居 (WithLawson α)
  定义体: ‹Inhabited α›

Depends on / 依赖: Inhabited
-/
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder (WithLawson α)
  body: ‹Preorder α›

中文:
实例 instPreorder
  签名: : 预序 (WithLawson α)
  定义体: ‹Preorder α›

Depends on / 依赖: Preorder
-/
instance instPreorder : Preorder (WithLawson α) := ‹Preorder α›

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (WithLawson α)
  body: -- fast_instance% lawson α fails
  letI : TopologicalSpace α := lawson α
inferInstanceAs TopologicalSpace α

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (WithLawson α)
  定义体: -- fast_instance% lawson α fails
  letI : TopologicalSpace α := lawson α
inferInstanceAs TopologicalSpace α
-/
instance instTopologicalSpace : TopologicalSpace (WithLawson α) :=
  -- fast_instance% lawson α fails
  letI : TopologicalSpace α := lawson α
inferInstanceAs TopologicalSpace α

/--
Instance `instIsLawson` / 实例 `instIsLawson`

English:
instance instIsLawson
  signature: : IsLawson (WithLawson α)
  body: ⟨rfl⟩

中文:
实例 instIsLawson
  签名: : 是Lawson (WithLawson α)
  定义体: ⟨rfl⟩
-/
instance instIsLawson : IsLawson (WithLawson α) := ⟨rfl⟩

/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: [TopologicalSpace α] [IsLawson α]
  body: ofLawson.toHomeomorphOfIsInducing ⟨IsLawson.topology_eq_lawson (α := α) ▸ induced_id.symm⟩

中文:
定义 homeomorph
  签名: [拓扑空间 α] [是Lawson α]
  定义体: ofLawson.toHomeomorphOfIsInducing ⟨IsLawson.topology_eq_lawson (α := α) ▸ induced_id.symm⟩

Depends on / 依赖: IsLawson, IsLawson.topology_eq_lawson, induced_id, induced_id.symm, ofLawson, ofLawson.toHomeomorphOfIsInducing, toHomeomorphOfIsInducing, topology_eq_lawson
-/
def homeomorph [TopologicalSpace α] [IsLawson α] : WithLawson α ≃ₜ α :=
  ofLawson.toHomeomorphOfIsInducing ⟨IsLawson.topology_eq_lawson (α := α) ▸ induced_id.symm⟩

/--
theorem `isOpen_preimage_ofLawson` / 定理 `isOpen_preimage_ofLawson`

English:
theorem isOpen_preimage_ofLawson
  given: {S : Set α}
  proof: Iff.rfl

中文:
定理 isOpen_preimage_ofLawson
  条件: {S : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_preimage_ofLawson {S : Set α} :
    IsOpen (ofLawson ⁻¹' S) ↔ (lawson α).IsOpen S := Iff.rfl

/--
theorem `isClosed_preimage_ofLawson` / 定理 `isClosed_preimage_ofLawson`

English:
theorem isClosed_preimage_ofLawson
  given: {S : Set α}
  proof: Iff.rfl

中文:
定理 isClosed_preimage_ofLawson
  条件: {S : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isClosed_preimage_ofLawson {S : Set α} :
    IsClosed (ofLawson ⁻¹' S) ↔ IsClosed[lawson α] S := Iff.rfl

/--
theorem `isOpen_def` / 定理 `isOpen_def`

English:
theorem isOpen_def
  given: {T : Set (WithLawson α)}
  proof: Iff.rfl

中文:
定理 isOpen_def
  条件: {T : 集合 (WithLawson α)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_def {T : Set (WithLawson α)} :
    IsOpen T ↔ (lawson α).IsOpen (toLawson ⁻¹' T) := Iff.rfl

end WithLawson
end Lawson

section Preorder

variable [Preorder α]

/--
lemma `lawson_le_scott` / 引理 `lawson_le_scott`

English:
lemma lawson_le_scott
  statement: lawson α <= scott α univ
  proof: inf_le_right

中文:
引理 lawson_le_scott
  结论: lawson α <= scott α univ
  证明: inf_le_right

Depends on / 依赖: inf_le_right
-/
lemma lawson_le_scott : lawson α <= scott α univ := inf_le_right

/--
lemma `lawson_le_lower` / 引理 `lawson_le_lower`

English:
lemma lawson_le_lower
  statement: lawson α <= lower α
  proof: inf_le_left

中文:
引理 lawson_le_lower
  结论: lawson α <= lower α
  证明: inf_le_left

Depends on / 依赖: inf_le_left
-/
lemma lawson_le_lower : lawson α <= lower α := inf_le_left

/--
lemma `scottHausdorff_le_lawson` / 引理 `scottHausdorff_le_lawson`

English:
lemma scottHausdorff_le_lawson
  statement: scottHausdorff α univ <= lawson α
  proof: le_inf scottHausdorff_le_lower scottHausdorff_le_scott

中文:
引理 scottHausdorff_le_lawson
  结论: scottHausdorff α univ <= lawson α
  证明: le_inf scottHausdorff_le_lower scottHausdorff_le_scott

Depends on / 依赖: le_inf, scottHausdorff_le_lower, scottHausdorff_le_scott
-/
lemma scottHausdorff_le_lawson : scottHausdorff α univ <= lawson α :=
  le_inf scottHausdorff_le_lower scottHausdorff_le_scott

/--
lemma `lawsonClosed_of_scottClosed` / 引理 `lawsonClosed_of_scottClosed`

English:
lemma lawsonClosed_of_scottClosed
  given: (s : Set α) (h : IsClosed (WithScott.ofScott ⁻¹' s))
  proof: h.mono lawson_le_scott

中文:
引理 lawsonClosed_of_scottClosed
  条件: (s : 集合 α) (h : 是闭集 (WithScott.ofScott ⁻¹' s))
  证明: h.mono lawson_le_scott

Depends on / 依赖: h.mono, lawson_le_scott
-/
lemma lawsonClosed_of_scottClosed (s : Set α) (h : IsClosed (WithScott.ofScott ⁻¹' s)) :
    IsClosed (WithLawson.ofLawson ⁻¹' s) := h.mono lawson_le_scott

/--
lemma `lawsonClosed_of_lowerClosed` / 引理 `lawsonClosed_of_lowerClosed`

English:
lemma lawsonClosed_of_lowerClosed
  given: (s : Set α) (h : IsClosed (WithLower.ofLower ⁻¹' s))
  proof: h.mono lawson_le_lower

中文:
引理 lawsonClosed_of_lowerClosed
  条件: (s : 集合 α) (h : 是闭集 (WithLower.ofLower ⁻¹' s))
  证明: h.mono lawson_le_lower

Depends on / 依赖: h.mono, lawson_le_lower
-/
lemma lawsonClosed_of_lowerClosed (s : Set α) (h : IsClosed (WithLower.ofLower ⁻¹' s)) :
    IsClosed (WithLawson.ofLawson ⁻¹' s) := h.mono lawson_le_lower

/--
lemma `lawsonOpen_iff_scottOpen_of_isUpperSet` / 引理 `lawsonOpen_iff_scottOpen_of_isUpperSet`

English:
lemma lawsonOpen_iff_scottOpen_of_isUpperSet
  given: {s : Set α} (h : IsUpperSet s)
  proof: ⟨fun hs => IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D := univ).mpr
    ⟨h, (scottHausdorff_le_lawson s) hs⟩, lawson_le_scott _⟩

中文:
引理 lawsonOpen_iff_scottOpen_of_isUpperSet
  条件: {s : 集合 α} (h : 是上集 s)
  证明: ⟨fun hs => IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D := univ).mpr
    ⟨h, (scottHausdorff_le_lawson s) hs⟩, lawson_le_scott _⟩

Depends on / 依赖: IsScott, IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open, isOpen_iff_isUpperSet_and_scottHausdorff_open, lawson_le_scott, scottHausdorff_le_lawson
-/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet {s : Set α} (h : IsUpperSet s) :
    IsOpen (WithLawson.ofLawson ⁻¹' s) ↔ IsOpen (WithScott.ofScott ⁻¹' s) :=
  ⟨fun hs => IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D := univ).mpr
    ⟨h, (scottHausdorff_le_lawson s) hs⟩, lawson_le_scott _⟩

variable (L : TopologicalSpace α) (S : TopologicalSpace α)
variable [@IsLawson α _ L] [@IsScott α univ _ S]

/--
lemma `isLawson_le_isScott` / 引理 `isLawson_le_isScott`

English:
lemma isLawson_le_isScott
  statement: L <= S
  proof: by
  rw [@IsScott.topology_eq α univ _ S _]; rw [@IsLawson.topology_eq_lawson α _ L _]
  exact inf_le_right

中文:
引理 isLawson_le_isScott
  结论: L <= S
  证明: by
  rw [@IsScott.topology_eq α univ _ S _]; rw [@IsLawson.topology_eq_lawson α _ L _]
  exact inf_le_right

Depends on / 依赖: IsLawson, IsLawson.topology_eq_lawson, IsScott, IsScott.topology_eq, inf_le_right, topology_eq, topology_eq_lawson
-/
lemma isLawson_le_isScott : L <= S := by
  rw [@IsScott.topology_eq α univ _ S _]; rw [@IsLawson.topology_eq_lawson α _ L _]
  exact inf_le_right

/--
lemma `scottHausdorff_le_isLawson` / 引理 `scottHausdorff_le_isLawson`

English:
lemma scottHausdorff_le_isLawson
  statement: scottHausdorff α univ <= L
  proof: by
  rw [@IsLawson.topology_eq_lawson α _ L _]
  exact scottHausdorff_le_lawson

中文:
引理 scottHausdorff_le_isLawson
  结论: scottHausdorff α univ <= L
  证明: by
  rw [@IsLawson.topology_eq_lawson α _ L _]
  exact scottHausdorff_le_lawson

Depends on / 依赖: IsLawson, IsLawson.topology_eq_lawson, scottHausdorff_le_lawson, topology_eq_lawson
-/
lemma scottHausdorff_le_isLawson : scottHausdorff α univ <= L := by
  rw [@IsLawson.topology_eq_lawson α _ L _]
  exact scottHausdorff_le_lawson

/--
lemma `lawsonOpen_iff_scottOpen_of_isUpperSet'` / 引理 `lawsonOpen_iff_scottOpen_of_isUpperSet'`

English:
lemma lawsonOpen_iff_scottOpen_of_isUpperSet'
  given: (s : Set α) (h : IsUpperSet s)
  proof: by
  rw [@IsLawson.topology_eq_lawson α _ L _]; rw [@IsScott.topology_eq α univ _ S _]
  exact lawsonOpen_iff_scottOpen_of_isUpperSet h

中文:
引理 lawsonOpen_iff_scottOpen_of_isUpperSet'
  条件: (s : 集合 α) (h : 是上集 s)
  证明: by
  rw [@IsLawson.topology_eq_lawson α _ L _]; rw [@IsScott.topology_eq α univ _ S _]
  exact lawsonOpen_iff_scottOpen_of_isUpperSet h

Depends on / 依赖: IsLawson, IsLawson.topology_eq_lawson, IsScott, IsScott.topology_eq, lawsonOpen_iff_scottOpen_of_isUpperSet, topology_eq, topology_eq_lawson
-/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet' (s : Set α) (h : IsUpperSet s) :
    IsOpen[L] s ↔ IsOpen[S] s := by
  rw [@IsLawson.topology_eq_lawson α _ L _]; rw [@IsScott.topology_eq α univ _ S _]
  exact lawsonOpen_iff_scottOpen_of_isUpperSet h

/--
lemma `lawsonClosed_iff_scottClosed_of_isLowerSet` / 引理 `lawsonClosed_iff_scottClosed_of_isLowerSet`

English:
lemma lawsonClosed_iff_scottClosed_of_isLowerSet
  given: (s : Set α) (h : IsLowerSet s)
  proof: by
  rw [← @isOpen_compl_iff]; rw [← isOpen_compl_iff]; rw [(lawsonOpen_iff_scottOpen_of_isUpperSet' L S _ (isUpperSet_compl.mpr h))]

include S in

中文:
引理 lawsonClosed_iff_scottClosed_of_isLowerSet
  条件: (s : 集合 α) (h : 是下集 s)
  证明: by
  rw [← @isOpen_compl_iff]; rw [← isOpen_compl_iff]; rw [(lawsonOpen_iff_scottOpen_of_isUpperSet' L S _ (isUpperSet_compl.mpr h))]

include S in

Depends on / 依赖: isOpen_compl_iff, isUpperSet_compl, isUpperSet_compl.mpr, lawsonOpen_iff_scottOpen_of_isUpperSet
-/
lemma lawsonClosed_iff_scottClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ IsClosed[S] s := by
  rw [← @isOpen_compl_iff]; rw [← isOpen_compl_iff]; rw [(lawsonOpen_iff_scottOpen_of_isUpperSet' L S _ (isUpperSet_compl.mpr h))]

include S in
/--
lemma `lawsonClosed_iff_dirSupClosed_of_isLowerSet` / 引理 `lawsonClosed_iff_dirSupClosed_of_isLowerSet`

English:
lemma lawsonClosed_iff_dirSupClosed_of_isLowerSet
  given: (s : Set α) (h : IsLowerSet s)
  proof: by
  rw [lawsonClosed_iff_scottClosed_of_isLowerSet L S _ h]; rw [@IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  simp_all

中文:
引理 lawsonClosed_iff_dirSupClosed_of_isLowerSet
  条件: (s : 集合 α) (h : 是下集 s)
  证明: by
  rw [lawsonClosed_iff_scottClosed_of_isLowerSet L S _ h]; rw [@IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  simp_all

Depends on / 依赖: IsScott, IsScott.isClosed_iff_isLowerSet_and_dirSupClosed, isClosed_iff_isLowerSet_and_dirSupClosed, lawsonClosed_iff_scottClosed_of_isLowerSet
-/
lemma lawsonClosed_iff_dirSupClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ DirSupClosed s := by
  rw [lawsonClosed_iff_scottClosed_of_isLowerSet L S _ h]; rw [@IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  simp_all

end Preorder

namespace IsLawson
variable [PartialOrder α] [TopologicalSpace α] [IsLawson α]

set_option backward.isDefEq.respectTransparency false in
/-- The Lawson topology on a partial order is T₁. -/
-- see Note [lower instance priority]
instance (priority := 90) toT1Space : T1Space α where
  t1 a := by
    simp +instances only [IsLawson.topology_eq_lawson]
    rw [← (Set.OrdConnected.upperClosure_inter_lowerClosure ordConnected_singleton)]; rw [← WithLawson.isClosed_preimage_ofLawson]
    apply IsClosed.inter
      (lawsonClosed_of_lowerClosed _ (IsLower.isClosed_upperClosure (finite_singleton a)))
    rw [lowerClosure_singleton]; rw [LowerSet.coe_Iic]; rw [← WithLawson.isClosed_preimage_ofLawson]
    exact lawsonClosed_of_scottClosed _ isClosed_Iic

end IsLawson

end Topology
