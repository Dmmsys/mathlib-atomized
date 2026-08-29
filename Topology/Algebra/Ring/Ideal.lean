/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Ideals and quotients of topological rings

In this file we define `Ideal.closure` to be the topological closure of an ideal in a topological
ring. We also define a `TopologicalSpace` structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/

@[expose] public section

open Topology

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]

/--
Definition of `Ideal.closure` / `Ideal.closure` 的定义

English:
definition Ideal.closure
  signature: (I : Ideal R)
  body: {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }

@[simp]

中文:
定义 理想.closure
  签名: (I : 理想 R)
  定义体: {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }

@[simp]
-/
protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }

@[simp]
/--
theorem `Ideal.coe_closure` / 定理 `Ideal.coe_closure`

English:
theorem Ideal.coe_closure
  given: (I : Ideal R)
  statement: (I.closure : Set R) = closure I
  proof: rfl

中文:
定理 理想.coe_closure
  条件: (I : 理想 R)
  结论: (I.closure : 集合 R) = closure I
  证明: rfl
-/
theorem Ideal.coe_closure (I : Ideal R) : (I.closure : Set R) = closure I :=
  rfl

/--
theorem `Ideal.closure_eq_of_isClosed` / 定理 `Ideal.closure_eq_of_isClosed`

English:
theorem Ideal.closure_eq_of_isClosed
  given: (I : Ideal R) (hI : IsClosed (I : Set R))
  statement: I.closure = I
  proof: SetLike.ext' hI.closure_eq

中文:
定理 理想.closure_eq_of_isClosed
  条件: (I : 理想 R) (hI : 是闭集 (I : 集合 R))
  结论: I.closure = I
  证明: SetLike.ext' hI.closure_eq

Depends on / 依赖: SetLike, SetLike.ext, closure_eq, hI.closure_eq
-/
theorem Ideal.closure_eq_of_isClosed (I : Ideal R) (hI : IsClosed (I : Set R)) : I.closure = I :=
  SetLike.ext' hI.closure_eq

variable (R)

/--
Definition of `Ideal.connectedComponentOfZero` / `Ideal.connectedComponentOfZero` 的定义

English:
definition Ideal.connectedComponentOfZero
  signature: : Ideal R where
  body: AddSubgroup.connectedComponentOfZero R
  smul_mem' c x h := IsConnected.subset_connectedComponent
    (isConnected_connectedComponent.image _ (continuous_const_mul c).continuousOn)
    ⟨0, mem_connectedComponent, mul_zero c⟩ ⟨x, h, rfl⟩

@[simp]

中文:
定义 理想.connectedComponentOfZero
  签名: : 理想 R where
  定义体: AddSubgroup.connectedComponentOfZero R
  smul_mem' c x h := IsConnected.subset_connectedComponent
    (isConnected_connectedComponent.image _ (continuous_const_mul c).continuousOn)
    ⟨0, mem_connectedComponent, mul_zero c⟩ ⟨x, h, rfl⟩

@[simp]

Depends on / 依赖: AddSubgroup, AddSubgroup.connectedComponentOfZero, connectedComponentOfZero
-/
def Ideal.connectedComponentOfZero : Ideal R where
  __ := AddSubgroup.connectedComponentOfZero R
  smul_mem' c x h := IsConnected.subset_connectedComponent
    (isConnected_connectedComponent.image _ (continuous_const_mul c).continuousOn)
    ⟨0, mem_connectedComponent, mul_zero c⟩ ⟨x, h, rfl⟩

@[simp]
/--
theorem `Ideal.coe_connectedComponentOfZero` / 定理 `Ideal.coe_connectedComponentOfZero`

English:
theorem Ideal.coe_connectedComponentOfZero
  proof: rfl

中文:
定理 理想.coe_connectedComponentOfZero
  证明: rfl
-/
theorem Ideal.coe_connectedComponentOfZero :
    (Ideal.connectedComponentOfZero R : Set R) = connectedComponent 0 :=
  rfl

end Ring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] (N : Ideal R)

open Ideal.Quotient

/--
Instance `topologicalRingQuotientTopology` / 实例 `topologicalRingQuotientTopology`

English:
instance topologicalRingQuotientTopology
  signature: : TopologicalSpace (R ⧸ N)
  body: instTopologicalSpaceQuotient

中文:
实例 topologicalRingQuotientTopology
  签名: : 拓扑空间 (R ⧸ N)
  定义体: instTopologicalSpaceQuotient

Depends on / 依赖: instTopologicalSpaceQuotient
-/
instance topologicalRingQuotientTopology : TopologicalSpace (R ⧸ N) :=
  instTopologicalSpaceQuotient

-- note for the reader: in the following, `mk` is `Ideal.Quotient.mk`, the canonical map `R → R/I`.
variable [IsTopologicalRing R]

/--
theorem `QuotientRing.isOpenMap_coe` / 定理 `QuotientRing.isOpenMap_coe`

English:
theorem QuotientRing.isOpenMap_coe
  statement: IsOpenMap (mk N)
  proof: QuotientAddGroup.isOpenMap_coe

中文:
定理 QuotientRing.isOpenMap_coe
  结论: 是开映射 (mk N)
  证明: QuotientAddGroup.isOpenMap_coe

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.isOpenMap_coe, isOpenMap_coe
-/
theorem QuotientRing.isOpenMap_coe : IsOpenMap (mk N) :=
  QuotientAddGroup.isOpenMap_coe

/--
theorem `QuotientRing.isOpenQuotientMap_mk` / 定理 `QuotientRing.isOpenQuotientMap_mk`

English:
theorem QuotientRing.isOpenQuotientMap_mk
  statement: IsOpenQuotientMap (mk N)
  proof: QuotientAddGroup.isOpenQuotientMap_mk

中文:
定理 QuotientRing.isOpenQuotientMap_mk
  结论: 是OpenQuotient映射 (mk N)
  证明: QuotientAddGroup.isOpenQuotientMap_mk

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.isOpenQuotientMap_mk, isOpenQuotientMap_mk
-/
theorem QuotientRing.isOpenQuotientMap_mk : IsOpenQuotientMap (mk N) :=
  QuotientAddGroup.isOpenQuotientMap_mk

/--
theorem `QuotientRing.isQuotientMap_coe_coe` / 定理 `QuotientRing.isQuotientMap_coe_coe`

English:
theorem QuotientRing.isQuotientMap_coe_coe
  statement: IsQuotientMap fun p : R × R => (mk N p.1, mk N p.2)
  proof: ((isOpenQuotientMap_mk N).prodMap (isOpenQuotientMap_mk N)).isQuotientMap

中文:
定理 QuotientRing.isQuotientMap_coe_coe
  结论: 是商映射 fun p : R × R => (mk N p.1, mk N p.2)
  证明: ((isOpenQuotientMap_mk N).prodMap (isOpenQuotientMap_mk N)).isQuotientMap

Depends on / 依赖: isOpenQuotientMap_mk, isQuotientMap, prodMap
-/
theorem QuotientRing.isQuotientMap_coe_coe : IsQuotientMap fun p : R × R => (mk N p.1, mk N p.2) :=
  ((isOpenQuotientMap_mk N).prodMap (isOpenQuotientMap_mk N)).isQuotientMap

/--
Instance `topologicalRing_quotient` / 实例 `topologicalRing_quotient`

English:
instance topologicalRing_quotient
  signature: : IsTopologicalRing (R ⧸ N) where
  body: QuotientAddGroup.instIsTopologicalAddGroup _
continuous_mul := (QuotientRing.isQuotientMap_coe_coe N).continuous_iff.2
    continuous_quot_mk.comp continuous_mul

中文:
实例 topologicalRing_quotient
  签名: : 是拓扑环 (R ⧸ N) where
  定义体: QuotientAddGroup.instIsTopologicalAddGroup _
continuous_mul := (QuotientRing.isQuotientMap_coe_coe N).continuous_iff.2
    continuous_quot_mk.comp continuous_mul

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.instIsTopologicalAddGroup, instIsTopologicalAddGroup
-/
instance topologicalRing_quotient : IsTopologicalRing (R ⧸ N) where
  __ := QuotientAddGroup.instIsTopologicalAddGroup _
continuous_mul := (QuotientRing.isQuotientMap_coe_coe N).continuous_iff.2
    continuous_quot_mk.comp continuous_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: R] : CompactSpace (R ⧸ N)
  body: Quotient.compactSpace

中文:
实例 [紧空间
  签名: R] : 紧空间 (R ⧸ N)
  定义体: Quotient.compactSpace

Depends on / 依赖: Quotient, Quotient.compactSpace, compactSpace
-/
instance [CompactSpace R] : CompactSpace (R ⧸ N) :=
  Quotient.compactSpace

end CommRing
