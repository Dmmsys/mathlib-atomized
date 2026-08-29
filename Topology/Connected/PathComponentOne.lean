/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.LocallyPathConnected

/-! # The path component of the identity in a locally path connected topological group

This file defines the path component of the identity is an `OpenNormalSubgroup` when the ambient
topological group is locally path connected. We place this in a separate file to avoid importing
additional algebra into the topology hierarchy.
-/

@[expose] public section

section PathComponentOne

variable (G : Type*) [TopologicalSpace G]

/-- The path component of the identity in a locally path connected topological group,
as an open normal subgroup. It is, in fact, clopen. -/
@[to_additive (attr := simps!)
/-- The path component of the identity in a locally path connected additive topological group,
as an open normal additive subgroup. It is, in fact, clopen. -/]
/--
Definition of `OpenNormalSubgroup.pathComponentOne` / `OpenNormalSubgroup.pathComponentOne` 的定义

English:
definition OpenNormalSubgroup.pathComponentOne
  signature: [Group G]
  body: .pathComponentOne G
  isOpen' := .pathComponent 1
  isNormal' := .pathComponentOne G

中文:
定义 OpenNormalSubgroup.pathComponentOne
  签名: [Group G]
  定义体: .pathComponentOne G
  isOpen' := .pathComponent 1
  isNormal' := .pathComponentOne G

Depends on / 依赖: pathComponentOne
-/
def OpenNormalSubgroup.pathComponentOne [Group G]
    [IsTopologicalGroup G] [LocallyPathConnectedSpace G] :
    OpenNormalSubgroup G where
  toSubgroup := .pathComponentOne G
  isOpen' := .pathComponent 1
  isNormal' := .pathComponentOne G

namespace OpenNormalSubgroup

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [IsTopologicalGroup G] [LocallyPathConnectedSpace G] :
  body: .pathComponent 1

中文:
实例 [Group
  签名: G] [IsTopologicalGroup G] [LocallyPathConnectedSpace G] :
  定义体: .pathComponent 1

Depends on / 依赖: pathComponent
-/
instance [Group G] [IsTopologicalGroup G] [LocallyPathConnectedSpace G] :
    IsClosed (OpenNormalSubgroup.pathComponentOne G : Set G) :=
  .pathComponent 1

end OpenNormalSubgroup

end PathComponentOne
