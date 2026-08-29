/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Distributive actions by submonoids
-/

public section

assert_not_exists RelIso Ring

namespace Submonoid

variable {M α : Type*} [Monoid M]

variable {S : Type*} [SetLike S M] (s : S) [SubmonoidClass S M]

instance (priority := low) [AddMonoid α] [DistribMulAction M α] : DistribMulAction s α where
  smul_zero r := smul_zero (r : M)
  smul_add r := smul_add (r : M)

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [AddMonoid α] [DistribMulAction M α] (S : Submonoid M)
  body: inferInstance

中文:
实例 distribMulAction
  签名: [加法幺半群 α] [分配乘法作用 M α] (S : 子幺半群 M)
  定义体: inferInstance
-/
instance distribMulAction [AddMonoid α] [DistribMulAction M α] (S : Submonoid M) :
    DistribMulAction S α :=
  inferInstance

instance (priority := low) [Monoid α] [MulDistribMulAction M α] : MulDistribMulAction s α where
  smul_mul r := smul_mul' (r : M)
  smul_one r := smul_one (r : M)

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: [Monoid α] [MulDistribMulAction M α] (S : Submonoid M)
  body: inferInstance

中文:
实例 mulDistribMulAction
  签名: [幺半群 α] [MulDistribMul作用 M α] (S : 子幺半群 M)
  定义体: inferInstance
-/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] (S : Submonoid M) :
    MulDistribMulAction S α :=
  inferInstance

end Submonoid
