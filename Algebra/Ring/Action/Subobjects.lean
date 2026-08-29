/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.DistribMulAction
public import Mathlib.Algebra.Ring.Action.Basic

/-!
# Instances of `MulSemiringAction` for subobjects

These are defined in this file as `Semiring`s are not available yet where `Submonoid` and `Subgroup`
are defined.

Instances for `Subsemiring` and `Subring` are provided next to the other scalar actions instances
for those subobjects.

-/

public section

assert_not_exists RelIso

variable {M G R : Type*}
variable [Monoid M] [Group G] [Semiring R]

instance (priority := low) [MulSemiringAction M R] {S : Type*} [SetLike S M] (s : S)
    [SubmonoidClass S M] : MulSemiringAction s R :=
  { (inferInstance : DistribMulAction s R), (inferInstance : MulDistribMulAction s R) with }

/--
Instance `Submonoid.mulSemiringAction` / 实例 `Submonoid.mulSemiringAction`

English:
instance Submonoid.mulSemiringAction
  signature: [MulSemiringAction M R] (H : Submonoid M)
  body: inferInstance

中文:
实例 子幺半群.mulSemiringAction
  签名: [MulSemiring作用 M R] (H : 子幺半群 M)
  定义体: inferInstance
-/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  inferInstance

/--
Instance `Subgroup.mulSemiringAction` / 实例 `Subgroup.mulSemiringAction`

English:
instance Subgroup.mulSemiringAction
  signature: [MulSemiringAction G R] (H : Subgroup G)
  body: inferInstance

中文:
实例 子群.mulSemiringAction
  签名: [MulSemiring作用 G R] (H : 子群 G)
  定义体: inferInstance
-/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  inferInstance
