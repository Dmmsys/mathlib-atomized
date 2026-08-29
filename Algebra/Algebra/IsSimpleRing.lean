/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Facts about algebras when the coefficient ring is a simple ring
-/

public section

variable (R A : Type*) [CommRing R] [Semiring A] [Algebra R A] [IsSimpleRing R] [Nontrivial A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul R A
  body: .2 RingHom.injective _ faithfulSMul_iff_algebraMap_injective R A

中文:
实例 :
  签名: FaithfulSMul R A
  定义体: .2 RingHom.injective _ faithfulSMul_iff_algebraMap_injective R A

Depends on / 依赖: RingHom, RingHom.injective, faithfulSMul_iff_algebraMap_injective, injective
-/
instance : FaithfulSMul R A :=
.2 RingHom.injective _ faithfulSMul_iff_algebraMap_injective R A
