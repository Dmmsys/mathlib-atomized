/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Algebraic operations on `SeparationQuotient`

In this file we define algebraic operations (multiplication, addition etc)
on the separation quotient of a topological space with corresponding operation,
provided that the original operation is continuous.

We also prove continuity of these operations
and show that they satisfy the same kind of laws (`Monoid` etc) as the original ones.

Finally, we construct a section of the quotient map
which is a continuous linear map `SeparationQuotient E →L[K] E`.
-/

@[expose] public section

assert_not_exists LinearIndependent

open scoped Topology

namespace SeparationQuotient

section SMul

variable {M X : Type*} [TopologicalSpace X] [SMul M X] [ContinuousConstSMul M X]

@[to_additive]
/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul M (SeparationQuotient X) where
  body: Quotient.map' (c • ·) fun _ _ h => h.const_smul c

@[to_additive (attr := simp)]

中文:
实例 instSMul
  签名: : 标量乘法 M (SeparationQuotient X) where
  定义体: Quotient.map' (c • ·) fun _ _ h => h.const_smul c

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.map, const_smul, h.const_smul
-/
instance instSMul : SMul M (SeparationQuotient X) where
  smul c := Quotient.map' (c • ·) fun _ _ h => h.const_smul c

@[to_additive (attr := simp)]
/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: (c : M) (x : X)
  statement: mk (c • x) = c • mk x
  proof: rfl

@[to_additive]

中文:
定理 mk_smul
  条件: (c : M) (x : X)
  结论: mk (c • x) = c • mk x
  证明: rfl

@[to_additive]
-/
theorem mk_smul (c : M) (x : X) : mk (c • x) = c • mk x := rfl

@[to_additive]
/--
Instance `instContinuousConstSMul` / 实例 `instContinuousConstSMul`

English:
instance instContinuousConstSMul
  signature: : ContinuousConstSMul M (SeparationQuotient X) where
  body: isQuotientMap_mk.continuous_iff.2
continuous_mk.comp continuous_const_smul c

@[to_additive]

中文:
实例 instContinuousConstSMul
  签名: : 连续常数标量乘法 M (SeparationQuotient X) where
  定义体: isQuotientMap_mk.continuous_iff.2
continuous_mk.comp continuous_const_smul c

@[to_additive]

Depends on / 依赖: continuous_iff, isQuotientMap_mk, isQuotientMap_mk.continuous_iff
-/
instance instContinuousConstSMul : ContinuousConstSMul M (SeparationQuotient X) where
continuous_const_smul c := isQuotientMap_mk.continuous_iff.2
continuous_mk.comp continuous_const_smul c

@[to_additive]
/--
Instance `instIsPretransitiveSMul` / 实例 `instIsPretransitiveSMul`

English:
instance instIsPretransitiveSMul
  signature: [MulAction.IsPretransitive M X]
  body: surjective_mk.forall₂.2 fun x y =>
    (MulAction.exists_smul_eq M x y).imp fun _ => congr_arg mk

@[to_additive]

中文:
实例 instIsPretransitiveSMul
  签名: [乘法作用.是Pretransitive M X]
  定义体: surjective_mk.forall₂.2 fun x y =>
    (MulAction.exists_smul_eq M x y).imp fun _ => congr_arg mk

@[to_additive]

Depends on / 依赖: surjective_mk, surjective_mk.forall
-/
instance instIsPretransitiveSMul [MulAction.IsPretransitive M X] :
    MulAction.IsPretransitive M (SeparationQuotient X) where
  exists_smul_eq := surjective_mk.forall₂.2 fun x y =>
    (MulAction.exists_smul_eq M x y).imp fun _ => congr_arg mk

@[to_additive]
/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
  body: surjective_mk.forall.2 (congr_arg mk <| op_smul_eq_smul a ·)

中文:
实例 instIsCentralScalar
  签名: [标量乘法 Mᵐᵒᵖ X] [中心标量 M X]
  定义体: surjective_mk.forall.2 (congr_arg mk <| op_smul_eq_smul a ·)

Depends on / 依赖: congr_arg, op_smul_eq_smul, surjective_mk, surjective_mk.forall
-/
instance instIsCentralScalar [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] :
    IsCentralScalar M (SeparationQuotient X) where
  op_smul_eq_smul a := surjective_mk.forall.2 (congr_arg mk <| op_smul_eq_smul a ·)

variable {N : Type*} [SMul N X]

@[to_additive]
/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [ContinuousConstSMul N X] [SMulCommClass M N X]
  body: surjective_mk.smulCommClass mk_smul mk_smul

@[to_additive]

中文:
实例 instSMulCommClass
  签名: [连续常数标量乘法 N X] [标量交换类 M N X]
  定义体: surjective_mk.smulCommClass mk_smul mk_smul

@[to_additive]

Depends on / 依赖: mk_smul, smulCommClass, surjective_mk, surjective_mk.smulCommClass
-/
instance instSMulCommClass [ContinuousConstSMul N X] [SMulCommClass M N X] :
    SMulCommClass M N (SeparationQuotient X) :=
  surjective_mk.smulCommClass mk_smul mk_smul

@[to_additive]
/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul M N] [ContinuousConstSMul N X] [IsScalarTower M N X]
  body: surjective_mk.forall.2 fun x => congr_arg mk smul_assoc a b x

中文:
实例 instIsScalarTower
  签名: [标量乘法 M N] [连续常数标量乘法 N X] [标量塔 M N X]
  定义体: surjective_mk.forall.2 fun x => congr_arg mk smul_assoc a b x

Depends on / 依赖: congr_arg, smul_assoc, surjective_mk, surjective_mk.forall
-/
instance instIsScalarTower [SMul M N] [ContinuousConstSMul N X] [IsScalarTower M N X] :
    IsScalarTower M N (SeparationQuotient X) where
smul_assoc a b := surjective_mk.forall.2 fun x => congr_arg mk smul_assoc a b x

end SMul

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: {M X : Type*} [SMul M X] [TopologicalSpace M] [TopologicalSpace X]
  body: by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).isQuotientMap.continuous_iff]
    exact continuous_mk.comp continuous_smul

中文:
实例 instContinuousSMul
  签名: {M X : 类型} [标量乘法 M X] [拓扑空间 M] [拓扑空间 X]
  定义体: by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).isQuotientMap.continuous_iff]
    exact continuous_mk.comp continuous_smul

Depends on / 依赖: IsOpenQuotientMap, IsOpenQuotientMap.id.prodMap, continuous_iff, continuous_mk, continuous_mk.comp, continuous_smul, isOpenQuotientMap_mk, isQuotientMap, isQuotientMap.continuous_iff, prodMap
-/
instance instContinuousSMul {M X : Type*} [SMul M X] [TopologicalSpace M] [TopologicalSpace X]
    [ContinuousSMul M X] : ContinuousSMul M (SeparationQuotient X) where
  continuous_smul := by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).isQuotientMap.continuous_iff]
    exact continuous_mk.comp continuous_smul

/--
Instance `instSMulZeroClass` / 实例 `instSMulZeroClass`

English:
instance instSMulZeroClass
  signature: {M X : Type*} [Zero X] [SMulZeroClass M X] [TopologicalSpace X]
  body: ZeroHom.smulZeroClass ⟨mk, mk_zero⟩ mk_smul

@[to_additive]

中文:
实例 instSMulZeroClass
  签名: {M X : 类型} [零 X] [SMulZero类 M X] [拓扑空间 X]
  定义体: ZeroHom.smulZeroClass ⟨mk, mk_zero⟩ mk_smul

@[to_additive]

Depends on / 依赖: ZeroHom, ZeroHom.smulZeroClass, mk_smul, mk_zero, smulZeroClass
-/
instance instSMulZeroClass {M X : Type*} [Zero X] [SMulZeroClass M X] [TopologicalSpace X]
    [ContinuousConstSMul M X] : SMulZeroClass M (SeparationQuotient X) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero⟩ mk_smul

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: {M X : Type*} [Monoid M] [MulAction M X] [TopologicalSpace X]
  body: surjective_mk.mulAction mk mk_smul

中文:
实例 instMulAction
  签名: {M X : 类型} [幺半群 M] [乘法作用 M X] [拓扑空间 X]
  定义体: surjective_mk.mulAction mk mk_smul

Depends on / 依赖: mk_smul, mulAction, surjective_mk, surjective_mk.mulAction
-/
instance instMulAction {M X : Type*} [Monoid M] [MulAction M X] [TopologicalSpace X]
    [ContinuousConstSMul M X] : MulAction M (SeparationQuotient X) :=
  surjective_mk.mulAction mk mk_smul

section Monoid

variable {M : Type*} [TopologicalSpace M]

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul M] [ContinuousMul M]
  body: Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => Inseparable.mul h₁ h₂

@[to_additive (attr := simp)]

中文:
实例 instMul
  签名: [乘法 M] [连续乘法 M]
  定义体: Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => Inseparable.mul h₁ h₂

@[to_additive (attr := simp)]

Depends on / 依赖: Inseparable, Inseparable.mul, Quotient, Quotient.map
-/
instance instMul [Mul M] [ContinuousMul M] : Mul (SeparationQuotient M) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => Inseparable.mul h₁ h₂

@[to_additive (attr := simp)]
/--
theorem `mk_mul` / 定理 `mk_mul`

English:
theorem mk_mul
  given: [Mul M] [ContinuousMul M] (a b : M)
  statement: mk (a * b) = mk a * mk b
  proof: rfl

@[to_additive]

中文:
定理 mk_mul
  条件: [乘法 M] [连续乘法 M] (a b : M)
  结论: mk (a * b) = mk a * mk b
  证明: rfl

@[to_additive]
-/
theorem mk_mul [Mul M] [ContinuousMul M] (a b : M) : mk (a * b) = mk a * mk b := rfl

@[to_additive]
/--
Instance `instContinuousMul` / 实例 `instContinuousMul`

English:
instance instContinuousMul
  signature: [Mul M] [ContinuousMul M]
  body: isQuotientMap_prodMap_mk.continuous_iff.2 continuous_mk.comp continuous_mul

@[to_additive]

中文:
实例 instContinuousMul
  签名: [乘法 M] [连续乘法 M]
  定义体: isQuotientMap_prodMap_mk.continuous_iff.2 continuous_mk.comp continuous_mul

@[to_additive]

Depends on / 依赖: continuous_iff, continuous_mk, continuous_mk.comp, continuous_mul, isQuotientMap_prodMap_mk, isQuotientMap_prodMap_mk.continuous_iff
-/
instance instContinuousMul [Mul M] [ContinuousMul M] : ContinuousMul (SeparationQuotient M) where
continuous_mul := isQuotientMap_prodMap_mk.continuous_iff.2 continuous_mk.comp continuous_mul

@[to_additive]
/--
Instance `instCommMagma` / 实例 `instCommMagma`

English:
instance instCommMagma
  signature: [CommMagma M] [ContinuousMul M]
  body: fast_instance% surjective_mk.commMagma mk mk_mul

@[to_additive]

中文:
实例 instCommMagma
  签名: [交换原群 M] [连续乘法 M]
  定义体: fast_instance% surjective_mk.commMagma mk mk_mul

@[to_additive]

Depends on / 依赖: commMagma, fast_instance, mk_mul, surjective_mk, surjective_mk.commMagma
-/
instance instCommMagma [CommMagma M] [ContinuousMul M] : CommMagma (SeparationQuotient M) :=
  fast_instance% surjective_mk.commMagma mk mk_mul

@[to_additive]
/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: [Semigroup M] [ContinuousMul M]
  body: fast_instance% surjective_mk.semigroup mk mk_mul

@[to_additive]

中文:
实例 instSemigroup
  签名: [半群 M] [连续乘法 M]
  定义体: fast_instance% surjective_mk.semigroup mk mk_mul

@[to_additive]

Depends on / 依赖: fast_instance, mk_mul, semigroup, surjective_mk, surjective_mk.semigroup
-/
instance instSemigroup [Semigroup M] [ContinuousMul M] : Semigroup (SeparationQuotient M) :=
  fast_instance% surjective_mk.semigroup mk mk_mul

@[to_additive]
/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: [CommSemigroup M] [ContinuousMul M]
  body: fast_instance% surjective_mk.commSemigroup mk mk_mul

@[to_additive]

中文:
实例 instCommSemigroup
  签名: [交换半群 M] [连续乘法 M]
  定义体: fast_instance% surjective_mk.commSemigroup mk mk_mul

@[to_additive]

Depends on / 依赖: commSemigroup, fast_instance, mk_mul, surjective_mk, surjective_mk.commSemigroup
-/
instance instCommSemigroup [CommSemigroup M] [ContinuousMul M] :
    CommSemigroup (SeparationQuotient M) :=
  fast_instance% surjective_mk.commSemigroup mk mk_mul

@[to_additive]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [MulOneClass M] [ContinuousMul M]
  body: fast_instance% surjective_mk.mulOneClass mk mk_one mk_mul

中文:
实例 instMulOneClass
  签名: [MulOne类 M] [连续乘法 M]
  定义体: fast_instance% surjective_mk.mulOneClass mk mk_one mk_mul

Depends on / 依赖: fast_instance, mk_mul, mk_one, mulOneClass, surjective_mk, surjective_mk.mulOneClass
-/
instance instMulOneClass [MulOneClass M] [ContinuousMul M] :
    MulOneClass (SeparationQuotient M) :=
  fast_instance% surjective_mk.mulOneClass mk mk_one mk_mul

/-- `SeparationQuotient.mk` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `SeparationQuotient.mk` as an `AddMonoidHom`. -/]
/--
Definition of `mkMonoidHom` / `mkMonoidHom` 的定义

English:
definition mkMonoidHom
  signature: [MulOneClass M] [ContinuousMul M]
  body: mk
  map_mul' := mk_mul
  map_one' := mk_one

中文:
定义 mkMonoidHom
  签名: [MulOne类 M] [连续乘法 M]
  定义体: mk
  map_mul' := mk_mul
  map_one' := mk_one
-/
def mkMonoidHom [MulOneClass M] [ContinuousMul M] : M ->* SeparationQuotient M where
  toFun := mk
  map_mul' := mk_mul
  map_one' := mk_one

instance (priority := 900) instNSMul [AddMonoid M] [ContinuousAdd M] :
    SMul Nat (SeparationQuotient M) :=
  inferInstance

@[to_additive existing]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: [Monoid M] [ContinuousMul M]
  body: Quotient.map' (s₁ := inseparableSetoid M) (· ^ n) (fun _ _ h => Inseparable.pow h n) x

@[to_additive, simp] -- `mk_nsmul` is not a `simp` lemma because we have `mk_smul`

中文:
实例 instPow
  签名: [幺半群 M] [连续乘法 M]
  定义体: Quotient.map' (s₁ := inseparableSetoid M) (· ^ n) (fun _ _ h => Inseparable.pow h n) x

@[to_additive, simp] -- `mk_nsmul` is not a `simp` lemma because we have `mk_smul`

Depends on / 依赖: Inseparable, Inseparable.pow, Quotient, Quotient.map, inseparableSetoid
-/
instance instPow [Monoid M] [ContinuousMul M] : Pow (SeparationQuotient M) Nat where
  pow x n := Quotient.map' (s₁ := inseparableSetoid M) (· ^ n) (fun _ _ h => Inseparable.pow h n) x

@[to_additive, simp] -- `mk_nsmul` is not a `simp` lemma because we have `mk_smul`
/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: [Monoid M] [ContinuousMul M] (x : M) (n : Nat)
  statement: mk (x ^ n) = (mk x) ^ n
  proof: rfl

@[to_additive]

中文:
定理 mk_pow
  条件: [幺半群 M] [连续乘法 M] (x : M) (n : 自然数)
  结论: mk (x ^ n) = (mk x) ^ n
  证明: rfl

@[to_additive]
-/
theorem mk_pow [Monoid M] [ContinuousMul M] (x : M) (n : Nat) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid M] [ContinuousMul M]
  body: fast_instance% surjective_mk.monoid mk mk_one mk_mul mk_pow

@[to_additive]

中文:
实例 instMonoid
  签名: [幺半群 M] [连续乘法 M]
  定义体: fast_instance% surjective_mk.monoid mk mk_one mk_mul mk_pow

@[to_additive]

Depends on / 依赖: fast_instance, mk_mul, mk_one, mk_pow, monoid, surjective_mk, surjective_mk.monoid
-/
instance instMonoid [Monoid M] [ContinuousMul M] : Monoid (SeparationQuotient M) :=
  fast_instance% surjective_mk.monoid mk mk_one mk_mul mk_pow

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid M] [ContinuousMul M]
  body: fast_instance% surjective_mk.commMonoid mk mk_one mk_mul mk_pow

中文:
实例 instCommMonoid
  签名: [交换幺半群 M] [连续乘法 M]
  定义体: fast_instance% surjective_mk.commMonoid mk mk_one mk_mul mk_pow

Depends on / 依赖: commMonoid, fast_instance, mk_mul, mk_one, mk_pow, surjective_mk, surjective_mk.commMonoid
-/
instance instCommMonoid [CommMonoid M] [ContinuousMul M] : CommMonoid (SeparationQuotient M) :=
  fast_instance% surjective_mk.commMonoid mk mk_one mk_mul mk_pow

end Monoid

section Group

variable {G : Type*} [TopologicalSpace G]

@[to_additive]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: [Inv G] [ContinuousInv G]
  body: Quotient.map' (·⁻¹) fun _ _ => Inseparable.inv

@[to_additive (attr := simp)]

中文:
实例 instInv
  签名: [取逆 G] [连续取逆 G]
  定义体: Quotient.map' (·⁻¹) fun _ _ => Inseparable.inv

@[to_additive (attr := simp)]

Depends on / 依赖: Inseparable, Inseparable.inv, Quotient, Quotient.map
-/
instance instInv [Inv G] [ContinuousInv G] : Inv (SeparationQuotient G) where
  inv := Quotient.map' (·⁻¹) fun _ _ => Inseparable.inv

@[to_additive (attr := simp)]
/--
theorem `mk_inv` / 定理 `mk_inv`

English:
theorem mk_inv
  given: [Inv G] [ContinuousInv G] (x : G)
  statement: mk x⁻¹ = (mk x)⁻¹
  proof: rfl

@[to_additive]

中文:
定理 mk_inv
  条件: [取逆 G] [连续取逆 G] (x : G)
  结论: mk x⁻¹ = (mk x)⁻¹
  证明: rfl

@[to_additive]
-/
theorem mk_inv [Inv G] [ContinuousInv G] (x : G) : mk x⁻¹ = (mk x)⁻¹ := rfl

@[to_additive]
/--
Instance `instContinuousInv` / 实例 `instContinuousInv`

English:
instance instContinuousInv
  signature: [Inv G] [ContinuousInv G]
  body: isQuotientMap_mk.continuous_iff.2 continuous_mk.comp continuous_inv

@[to_additive]

中文:
实例 instContinuousInv
  签名: [取逆 G] [连续取逆 G]
  定义体: isQuotientMap_mk.continuous_iff.2 continuous_mk.comp continuous_inv

@[to_additive]

Depends on / 依赖: continuous_iff, continuous_inv, continuous_mk, continuous_mk.comp, isQuotientMap_mk, isQuotientMap_mk.continuous_iff
-/
instance instContinuousInv [Inv G] [ContinuousInv G] : ContinuousInv (SeparationQuotient G) where
continuous_inv := isQuotientMap_mk.continuous_iff.2 continuous_mk.comp continuous_inv

@[to_additive]
/--
Instance `instInvolutiveInv` / 实例 `instInvolutiveInv`

English:
instance instInvolutiveInv
  signature: [InvolutiveInv G] [ContinuousInv G]
  body: surjective_mk.involutiveInv mk mk_inv

@[to_additive]

中文:
实例 instInvolutiveInv
  签名: [InvolutiveInv G] [连续取逆 G]
  定义体: surjective_mk.involutiveInv mk mk_inv

@[to_additive]

Depends on / 依赖: involutiveInv, mk_inv, surjective_mk, surjective_mk.involutiveInv
-/
instance instInvolutiveInv [InvolutiveInv G] [ContinuousInv G] :
    InvolutiveInv (SeparationQuotient G) :=
  surjective_mk.involutiveInv mk mk_inv

@[to_additive]
/--
Instance `instInvOneClass` / 实例 `instInvOneClass`

English:
instance instInvOneClass
  signature: [InvOneClass G] [ContinuousInv G]
  body: congr_arg mk inv_one

@[to_additive]

中文:
实例 instInvOneClass
  签名: [InvOne类 G] [连续取逆 G]
  定义体: congr_arg mk inv_one

@[to_additive]

Depends on / 依赖: congr_arg, inv_one
-/
instance instInvOneClass [InvOneClass G] [ContinuousInv G] :
    InvOneClass (SeparationQuotient G) where
  inv_one := congr_arg mk inv_one

@[to_additive]
/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: [Div G] [ContinuousDiv G]
  body: Quotient.map₂ (· / ·) fun _ _ h₁ _ _ h₂ => (Inseparable.prod h₁ h₂).map continuous_div'

@[to_additive (attr := simp)]

中文:
实例 instDiv
  签名: [除法 G] [余ntinuousDiv G]
  定义体: Quotient.map₂ (· / ·) fun _ _ h₁ _ _ h₂ => (Inseparable.prod h₁ h₂).map continuous_div'

@[to_additive (attr := simp)]

Depends on / 依赖: Inseparable, Inseparable.prod, Quotient, Quotient.map, continuous_div
-/
instance instDiv [Div G] [ContinuousDiv G] : Div (SeparationQuotient G) where
  div := Quotient.map₂ (· / ·) fun _ _ h₁ _ _ h₂ => (Inseparable.prod h₁ h₂).map continuous_div'

@[to_additive (attr := simp)]
/--
theorem `mk_div` / 定理 `mk_div`

English:
theorem mk_div
  given: [Div G] [ContinuousDiv G] (x y : G)
  statement: mk (x / y) = mk x / mk y
  proof: rfl

@[to_additive]

中文:
定理 mk_div
  条件: [除法 G] [余ntinuousDiv G] (x y : G)
  结论: mk (x / y) = mk x / mk y
  证明: rfl

@[to_additive]
-/
theorem mk_div [Div G] [ContinuousDiv G] (x y : G) : mk (x / y) = mk x / mk y := rfl

@[to_additive]
/--
Instance `instContinuousDiv` / 实例 `instContinuousDiv`

English:
instance instContinuousDiv
  signature: [Div G] [ContinuousDiv G]
  body: isQuotientMap_prodMap_mk.continuous_iff.2 continuous_mk.comp continuous_div'

中文:
实例 instContinuousDiv
  签名: [除法 G] [余ntinuousDiv G]
  定义体: isQuotientMap_prodMap_mk.continuous_iff.2 continuous_mk.comp continuous_div'

Depends on / 依赖: continuous_div, continuous_iff, continuous_mk, continuous_mk.comp, isQuotientMap_prodMap_mk, isQuotientMap_prodMap_mk.continuous_iff
-/
instance instContinuousDiv [Div G] [ContinuousDiv G] : ContinuousDiv (SeparationQuotient G) where
continuous_div' := isQuotientMap_prodMap_mk.continuous_iff.2 continuous_mk.comp continuous_div'

/--
Instance `instZSMul` / 实例 `instZSMul`

English:
instance instZSMul
  signature: [AddGroup G] [IsTopologicalAddGroup G]
  body: inferInstance

@[to_additive existing]

中文:
实例 instZSMul
  签名: [加法群 G] [是拓扑加群 G]
  定义体: inferInstance

@[to_additive existing]
-/
instance instZSMul [AddGroup G] [IsTopologicalAddGroup G] : SMul Int (SeparationQuotient G) :=
  inferInstance

@[to_additive existing]
/--
Instance `instZPow` / 实例 `instZPow`

English:
instance instZPow
  signature: [Group G] [IsTopologicalGroup G]
  body: Quotient.map' (s₁ := inseparableSetoid G) (· ^ n) (fun _ _ h => Inseparable.zpow h n) x

@[to_additive, simp] -- `mk_zsmul` is not a `simp` lemma because we have `mk_smul`

中文:
实例 instZPow
  签名: [群 G] [是拓扑群 G]
  定义体: Quotient.map' (s₁ := inseparableSetoid G) (· ^ n) (fun _ _ h => Inseparable.zpow h n) x

@[to_additive, simp] -- `mk_zsmul` is not a `simp` lemma because we have `mk_smul`

Depends on / 依赖: Inseparable, Inseparable.zpow, Quotient, Quotient.map, inseparableSetoid
-/
instance instZPow [Group G] [IsTopologicalGroup G] : Pow (SeparationQuotient G) Int where
  pow x n := Quotient.map' (s₁ := inseparableSetoid G) (· ^ n) (fun _ _ h => Inseparable.zpow h n) x

@[to_additive, simp] -- `mk_zsmul` is not a `simp` lemma because we have `mk_smul`
/--
theorem `mk_zpow` / 定理 `mk_zpow`

English:
theorem mk_zpow
  given: [Group G] [IsTopologicalGroup G] (x : G) (n : Int)
  statement: mk (x ^ n) = (mk x) ^ n
  proof: rfl

@[to_additive]

中文:
定理 mk_zpow
  条件: [群 G] [是拓扑群 G] (x : G) (n : 整数)
  结论: mk (x ^ n) = (mk x) ^ n
  证明: rfl

@[to_additive]
-/
theorem mk_zpow [Group G] [IsTopologicalGroup G] (x : G) (n : Int) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group G] [IsTopologicalGroup G]
  body: fast_instance% surjective_mk.group mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]

中文:
实例 instGroup
  签名: [群 G] [是拓扑群 G]
  定义体: fast_instance% surjective_mk.group mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]

Depends on / 依赖: fast_instance, mk_div, mk_inv, mk_mul, mk_one, mk_pow, mk_zpow, surjective_mk, surjective_mk.group
-/
instance instGroup [Group G] [IsTopologicalGroup G] : Group (SeparationQuotient G) :=
  fast_instance% surjective_mk.group mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup G] [IsTopologicalGroup G]
  body: fast_instance% surjective_mk.commGroup mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]

中文:
实例 instCommGroup
  签名: [交换群 G] [是拓扑群 G]
  定义体: fast_instance% surjective_mk.commGroup mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]

Depends on / 依赖: commGroup, fast_instance, mk_div, mk_inv, mk_mul, mk_one, mk_pow, mk_zpow, surjective_mk, surjective_mk.commGroup
-/
instance instCommGroup [CommGroup G] [IsTopologicalGroup G] : CommGroup (SeparationQuotient G) :=
  fast_instance% surjective_mk.commGroup mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
/--
Instance `instIsTopologicalGroup` / 实例 `instIsTopologicalGroup`

English:
instance instIsTopologicalGroup
  signature: [Group G] [IsTopologicalGroup G]

中文:
实例 instIsTopologicalGroup
  签名: [群 G] [是拓扑群 G]
-/
instance instIsTopologicalGroup [Group G] [IsTopologicalGroup G] :
    IsTopologicalGroup (SeparationQuotient G) where

end Group

section IsUniformGroup

@[to_additive]
/--
Instance `instIsUniformGroup` / 实例 `instIsUniformGroup`

English:
instance instIsUniformGroup
  signature: {G : Type*} [Group G] [UniformSpace G] [IsUniformGroup G]
  body: by
    rw [uniformContinuous_dom₂]
    exact uniformContinuous_mk.comp uniformContinuous_div

中文:
实例 instIsUniformGroup
  签名: {G : 类型} [群 G] [一致空间 G] [是一致群 G]
  定义体: by
    rw [uniformContinuous_dom₂]
    exact uniformContinuous_mk.comp uniformContinuous_div

Depends on / 依赖: uniformContinuous_div, uniformContinuous_mk, uniformContinuous_mk.comp
-/
instance instIsUniformGroup {G : Type*} [Group G] [UniformSpace G] [IsUniformGroup G] :
    IsUniformGroup (SeparationQuotient G) where
  uniformContinuous_div := by
    rw [uniformContinuous_dom₂]
    exact uniformContinuous_mk.comp uniformContinuous_div

end IsUniformGroup

section MonoidWithZero

variable {M₀ : Type*} [TopologicalSpace M₀]

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: [MulZeroClass M₀] [ContinuousMul M₀]
  body: fast_instance% surjective_mk.mulZeroClass mk mk_zero mk_mul

中文:
实例 instMulZeroClass
  签名: [乘零类 M₀] [连续乘法 M₀]
  定义体: fast_instance% surjective_mk.mulZeroClass mk mk_zero mk_mul

Depends on / 依赖: fast_instance, mk_mul, mk_zero, mulZeroClass, surjective_mk, surjective_mk.mulZeroClass
-/
instance instMulZeroClass [MulZeroClass M₀] [ContinuousMul M₀] :
    MulZeroClass (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.mulZeroClass mk mk_zero mk_mul

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero M₀] [ContinuousMul M₀]
  body: fast_instance% surjective_mk.semigroupWithZero mk mk_zero mk_mul

中文:
实例 instSemigroupWithZero
  签名: [带零半群 M₀] [连续乘法 M₀]
  定义体: fast_instance% surjective_mk.semigroupWithZero mk mk_zero mk_mul

Depends on / 依赖: fast_instance, mk_mul, mk_zero, semigroupWithZero, surjective_mk, surjective_mk.semigroupWithZero
-/
instance instSemigroupWithZero [SemigroupWithZero M₀] [ContinuousMul M₀] :
    SemigroupWithZero (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.semigroupWithZero mk mk_zero mk_mul

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass M₀] [ContinuousMul M₀]
  body: fast_instance% surjective_mk.mulZeroOneClass mk mk_zero mk_one mk_mul

中文:
实例 instMulZeroOneClass
  签名: [乘零幺类 M₀] [连续乘法 M₀]
  定义体: fast_instance% surjective_mk.mulZeroOneClass mk mk_zero mk_one mk_mul

Depends on / 依赖: fast_instance, mk_mul, mk_one, mk_zero, mulZeroOneClass, surjective_mk, surjective_mk.mulZeroOneClass
-/
instance instMulZeroOneClass [MulZeroOneClass M₀] [ContinuousMul M₀] :
    MulZeroOneClass (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.mulZeroOneClass mk mk_zero mk_one mk_mul

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: [MonoidWithZero M₀] [ContinuousMul M₀]
  body: fast_instance% surjective_mk.monoidWithZero mk mk_zero mk_one mk_mul mk_pow

中文:
实例 instMonoidWithZero
  签名: [带零幺半群 M₀] [连续乘法 M₀]
  定义体: fast_instance% surjective_mk.monoidWithZero mk mk_zero mk_one mk_mul mk_pow

Depends on / 依赖: fast_instance, mk_mul, mk_one, mk_pow, mk_zero, monoidWithZero, surjective_mk, surjective_mk.monoidWithZero
-/
instance instMonoidWithZero [MonoidWithZero M₀] [ContinuousMul M₀] :
    MonoidWithZero (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.monoidWithZero mk mk_zero mk_one mk_mul mk_pow

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: [CommMonoidWithZero M₀] [ContinuousMul M₀]
  body: fast_instance% surjective_mk.commMonoidWithZero mk mk_zero mk_one mk_mul mk_pow

中文:
实例 instCommMonoidWithZero
  签名: [带零交换幺半群 M₀] [连续乘法 M₀]
  定义体: fast_instance% surjective_mk.commMonoidWithZero mk mk_zero mk_one mk_mul mk_pow

Depends on / 依赖: commMonoidWithZero, fast_instance, mk_mul, mk_one, mk_pow, mk_zero, surjective_mk, surjective_mk.commMonoidWithZero
-/
instance instCommMonoidWithZero [CommMonoidWithZero M₀] [ContinuousMul M₀] :
    CommMonoidWithZero (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.commMonoidWithZero mk mk_zero mk_one mk_mul mk_pow

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R]

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: [Distrib R] [ContinuousMul R] [ContinuousAdd R]
  body: fast_instance% surjective_mk.distrib mk mk_add mk_mul

中文:
实例 instDistrib
  签名: [Distrib R] [连续乘法 R] [连续加法 R]
  定义体: fast_instance% surjective_mk.distrib mk mk_add mk_mul

Depends on / 依赖: distrib, fast_instance, mk_add, mk_mul, surjective_mk, surjective_mk.distrib
-/
instance instDistrib [Distrib R] [ContinuousMul R] [ContinuousAdd R] :
    Distrib (SeparationQuotient R) :=
  fast_instance% surjective_mk.distrib mk mk_add mk_mul

/--
Instance `instLeftDistribClass` / 实例 `instLeftDistribClass`

English:
instance instLeftDistribClass
  signature: [Mul R] [Add R] [LeftDistribClass R]
  body: surjective_mk.leftDistribClass mk mk_add mk_mul

中文:
实例 instLeftDistribClass
  签名: [乘法 R] [加法 R] [LeftDistrib类 R]
  定义体: surjective_mk.leftDistribClass mk mk_add mk_mul

Depends on / 依赖: leftDistribClass, mk_add, mk_mul, surjective_mk, surjective_mk.leftDistribClass
-/
instance instLeftDistribClass [Mul R] [Add R] [LeftDistribClass R]
    [ContinuousMul R] [ContinuousAdd R] :
    LeftDistribClass (SeparationQuotient R) :=
  surjective_mk.leftDistribClass mk mk_add mk_mul

/--
Instance `instRightDistribClass` / 实例 `instRightDistribClass`

English:
instance instRightDistribClass
  signature: [Mul R] [Add R] [RightDistribClass R]
  body: surjective_mk.rightDistribClass mk mk_add mk_mul

中文:
实例 instRightDistribClass
  签名: [乘法 R] [加法 R] [RightDistrib类 R]
  定义体: surjective_mk.rightDistribClass mk mk_add mk_mul

Depends on / 依赖: mk_add, mk_mul, rightDistribClass, surjective_mk, surjective_mk.rightDistribClass
-/
instance instRightDistribClass [Mul R] [Add R] [RightDistribClass R]
    [ContinuousMul R] [ContinuousAdd R] :
    RightDistribClass (SeparationQuotient R) :=
  surjective_mk.rightDistribClass mk mk_add mk_mul

/--
Instance `instNonUnitalnonAssocSemiring` / 实例 `instNonUnitalnonAssocSemiring`

English:
instance instNonUnitalnonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R]
  body: fast_instance% surjective_mk.nonUnitalNonAssocSemiring mk mk_zero mk_add mk_mul mk_smul

中文:
实例 instNonUnitalnonAssocSemiring
  签名: [非幺非结合半环 R]
  定义体: fast_instance% surjective_mk.nonUnitalNonAssocSemiring mk mk_zero mk_add mk_mul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_smul, mk_zero, nonUnitalNonAssocSemiring, surjective_mk, surjective_mk.nonUnitalNonAssocSemiring
-/
instance instNonUnitalnonAssocSemiring [NonUnitalNonAssocSemiring R]
    [IsTopologicalSemiring R] : NonUnitalNonAssocSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocSemiring mk mk_zero mk_add mk_mul mk_smul

/--
Instance `instIsTopologicalSemiring` / 实例 `instIsTopologicalSemiring`

English:
instance instIsTopologicalSemiring
  signature: [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R]

中文:
实例 instIsTopologicalSemiring
  签名: [非幺非结合半环 R] [是TopologicalSemiring R]
-/
instance instIsTopologicalSemiring [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (SeparationQuotient R) where

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring R] [IsTopologicalSemiring R]
  body: fast_instance% surjective_mk.nonUnitalSemiring mk mk_zero mk_add mk_mul mk_smul

中文:
实例 instNonUnitalSemiring
  签名: [非幺半环 R] [是TopologicalSemiring R]
  定义体: fast_instance% surjective_mk.nonUnitalSemiring mk mk_zero mk_add mk_mul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_smul, mk_zero, nonUnitalSemiring, surjective_mk, surjective_mk.nonUnitalSemiring
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] [IsTopologicalSemiring R] :
    NonUnitalSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalSemiring mk mk_zero mk_add mk_mul mk_smul

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: [NatCast R]
  body: mk n

@[simp, norm_cast]

中文:
实例 inst自然数Cast
  签名: [自然数嵌入 R]
  定义体: mk n

@[simp, norm_cast]
-/
instance instNatCast [NatCast R] : NatCast (SeparationQuotient R) where
  natCast n := mk n

@[simp, norm_cast]
/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: [NatCast R] (n : Nat)
  statement: mk (n : R) = n
  proof: rfl

@[simp]

中文:
定理 mk_natCast
  条件: [自然数嵌入 R] (n : 自然数)
  结论: mk (n : R) = n
  证明: rfl

@[simp]
-/
theorem mk_natCast [NatCast R] (n : Nat) : mk (n : R) = n := rfl

@[simp]
/--
theorem `mk_ofNat` / 定理 `mk_ofNat`

English:
theorem mk_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 mk_of自然数
  条件: [自然数嵌入 R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
theorem mk_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    mk (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: [IntCast R]
  body: mk n

@[simp, norm_cast]

中文:
实例 inst整数Cast
  签名: [整数嵌入 R]
  定义体: mk n

@[simp, norm_cast]
-/
instance instIntCast [IntCast R] : IntCast (SeparationQuotient R) where
  intCast n := mk n

@[simp, norm_cast]
/--
theorem `mk_intCast` / 定理 `mk_intCast`

English:
theorem mk_intCast
  given: [IntCast R] (n : Int)
  statement: mk (n : R) = n
  proof: rfl

中文:
定理 mk_intCast
  条件: [整数嵌入 R] (n : 整数)
  结论: mk (n : R) = n
  证明: rfl
-/
theorem mk_intCast [IntCast R] (n : Int) : mk (n : R) = n := rfl

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [NonAssocSemiring R] [IsTopologicalSemiring R]
  body: fast_instance% surjective_mk.nonAssocSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_natCast

中文:
实例 instNonAssocSemiring
  签名: [非结合半环 R] [是TopologicalSemiring R]
  定义体: fast_instance% surjective_mk.nonAssocSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_natCast

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_natCast, mk_one, mk_smul, mk_zero, nonAssocSemiring, surjective_mk, surjective_mk.nonAssocSemiring
-/
instance instNonAssocSemiring [NonAssocSemiring R] [IsTopologicalSemiring R] :
    NonAssocSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonAssocSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_natCast

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.nonUnitalNonAssocRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

中文:
实例 instNonUnitalNonAssocRing
  签名: [非幺非结合环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.nonUnitalNonAssocRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_neg, mk_smul, mk_sub, mk_zero, nonUnitalNonAssocRing, surjective_mk, surjective_mk.nonUnitalNonAssocRing
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    NonUnitalNonAssocRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

/--
Instance `instIsTopologicalRing` / 实例 `instIsTopologicalRing`

English:
instance instIsTopologicalRing
  signature: [NonUnitalNonAssocRing R] [IsTopologicalRing R]

中文:
实例 instIsTopologicalRing
  签名: [非幺非结合环 R] [是拓扑环 R]
-/
instance instIsTopologicalRing [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsTopologicalRing (SeparationQuotient R) where

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [NonUnitalRing R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.nonUnitalRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

中文:
实例 instNonUnitalRing
  签名: [非幺环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.nonUnitalRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_neg, mk_smul, mk_sub, mk_zero, nonUnitalRing, surjective_mk, surjective_mk.nonUnitalRing
-/
instance instNonUnitalRing [NonUnitalRing R] [IsTopologicalRing R] :
    NonUnitalRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [NonAssocRing R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.nonAssocRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_natCast mk_intCast

中文:
实例 instNonAssocRing
  签名: [非结合环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.nonAssocRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_natCast mk_intCast

Depends on / 依赖: fast_instance, mk_add, mk_intCast, mk_mul, mk_natCast, mk_neg, mk_one, mk_smul, mk_sub, mk_zero, nonAssocRing, surjective_mk, surjective_mk.nonAssocRing
-/
instance instNonAssocRing [NonAssocRing R] [IsTopologicalRing R] :
    NonAssocRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonAssocRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_natCast mk_intCast

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring R] [IsTopologicalSemiring R]
  body: fast_instance% surjective_mk.semiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

中文:
实例 instSemiring
  签名: [半环 R] [是TopologicalSemiring R]
  定义体: fast_instance% surjective_mk.semiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_natCast, mk_one, mk_pow, mk_smul, mk_zero, semiring, surjective_mk, surjective_mk.semiring
-/
instance instSemiring [Semiring R] [IsTopologicalSemiring R] :
    Semiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.semiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Ring R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.ring mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul
    mk_smul mk_pow mk_natCast mk_intCast

中文:
实例 instRing
  签名: [环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.ring mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul
    mk_smul mk_pow mk_natCast mk_intCast

Depends on / 依赖: fast_instance, mk_add, mk_intCast, mk_mul, mk_natCast, mk_neg, mk_one, mk_pow, mk_smul, mk_sub, mk_zero, surjective_mk, surjective_mk.ring
-/
instance instRing [Ring R] [IsTopologicalRing R] :
    Ring (SeparationQuotient R) :=
  fast_instance% surjective_mk.ring mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul
    mk_smul mk_pow mk_natCast mk_intCast

/--
Instance `instNonUnitalNonAssocCommSemiring` / 实例 `instNonUnitalNonAssocCommSemiring`

English:
instance instNonUnitalNonAssocCommSemiring
  signature: [NonUnitalNonAssocCommSemiring R]
  body: fast_instance% surjective_mk.nonUnitalNonAssocCommSemiring mk mk_zero mk_add mk_mul mk_smul

中文:
实例 instNonUnitalNonAssocCommSemiring
  签名: [非幺非结合交换半环 R]
  定义体: fast_instance% surjective_mk.nonUnitalNonAssocCommSemiring mk mk_zero mk_add mk_mul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_smul, mk_zero, nonUnitalNonAssocCommSemiring, surjective_mk, surjective_mk.nonUnitalNonAssocCommSemiring
-/
instance instNonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    [IsTopologicalSemiring R] :
    NonUnitalNonAssocCommSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocCommSemiring mk mk_zero mk_add mk_mul mk_smul

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R] [IsTopologicalSemiring R]
  body: fast_instance% surjective_mk.nonUnitalCommSemiring mk mk_zero mk_add mk_mul mk_smul

中文:
实例 instNonUnitalCommSemiring
  签名: [非幺交换半环 R] [是TopologicalSemiring R]
  定义体: fast_instance% surjective_mk.nonUnitalCommSemiring mk mk_zero mk_add mk_mul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_smul, mk_zero, nonUnitalCommSemiring, surjective_mk, surjective_mk.nonUnitalCommSemiring
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [IsTopologicalSemiring R] :
    NonUnitalCommSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalCommSemiring mk mk_zero mk_add mk_mul mk_smul

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring R] [IsTopologicalSemiring R]
  body: fast_instance% surjective_mk.commSemiring mk mk_zero mk_one mk_add mk_mul mk_smul
    mk_pow mk_natCast

中文:
实例 instCommSemiring
  签名: [交换半环 R] [是TopologicalSemiring R]
  定义体: fast_instance% surjective_mk.commSemiring mk mk_zero mk_one mk_add mk_mul mk_smul
    mk_pow mk_natCast

Depends on / 依赖: commSemiring, fast_instance, mk_add, mk_mul, mk_natCast, mk_one, mk_pow, mk_smul, mk_zero, surjective_mk, surjective_mk.commSemiring
-/
instance instCommSemiring [CommSemiring R] [IsTopologicalSemiring R] :
    CommSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.commSemiring mk mk_zero mk_one mk_add mk_mul mk_smul
    mk_pow mk_natCast

/--
Instance `instHasDistribNeg` / 实例 `instHasDistribNeg`

English:
instance instHasDistribNeg
  signature: [Mul R] [HasDistribNeg R] [ContinuousMul R] [ContinuousNeg R]
  body: fast_instance% surjective_mk.hasDistribNeg mk mk_neg mk_mul

中文:
实例 instHasDistribNeg
  签名: [乘法 R] [有DistribNeg R] [连续乘法 R] [连续取负 R]
  定义体: fast_instance% surjective_mk.hasDistribNeg mk mk_neg mk_mul

Depends on / 依赖: fast_instance, hasDistribNeg, mk_mul, mk_neg, surjective_mk, surjective_mk.hasDistribNeg
-/
instance instHasDistribNeg [Mul R] [HasDistribNeg R] [ContinuousMul R] [ContinuousNeg R] :
    HasDistribNeg (SeparationQuotient R) :=
  fast_instance% surjective_mk.hasDistribNeg mk mk_neg mk_mul

/--
Instance `instNonUnitalNonAssocCommRing` / 实例 `instNonUnitalNonAssocCommRing`

English:
instance instNonUnitalNonAssocCommRing
  signature: [NonUnitalNonAssocCommRing R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.nonUnitalNonAssocCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

中文:
实例 instNonUnitalNonAssocCommRing
  签名: [非幺非结合交换环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.nonUnitalNonAssocCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_neg, mk_smul, mk_sub, mk_zero, nonUnitalNonAssocCommRing, surjective_mk, surjective_mk.nonUnitalNonAssocCommRing
-/
instance instNonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] [IsTopologicalRing R] :
    NonUnitalNonAssocCommRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: [NonUnitalCommRing R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.nonUnitalCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

中文:
实例 instNonUnitalCommRing
  签名: [非幺交换环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.nonUnitalCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

Depends on / 依赖: fast_instance, mk_add, mk_mul, mk_neg, mk_smul, mk_sub, mk_zero, nonUnitalCommRing, surjective_mk, surjective_mk.nonUnitalCommRing
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] [IsTopologicalRing R] :
    NonUnitalCommRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [CommRing R] [IsTopologicalRing R]
  body: fast_instance% surjective_mk.commRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_pow mk_natCast mk_intCast

中文:
实例 instCommRing
  签名: [交换环 R] [是拓扑环 R]
  定义体: fast_instance% surjective_mk.commRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_pow mk_natCast mk_intCast

Depends on / 依赖: commRing, fast_instance, mk_add, mk_intCast, mk_mul, mk_natCast, mk_neg, mk_one, mk_pow, mk_smul, mk_sub, mk_zero, surjective_mk, surjective_mk.commRing
-/
instance instCommRing [CommRing R] [IsTopologicalRing R] :
    CommRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.commRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_pow mk_natCast mk_intCast

/-- `SeparationQuotient.mk` as a `RingHom`. -/
@[simps]
/--
Definition of `mkRingHom` / `mkRingHom` 的定义

English:
definition mkRingHom
  signature: [NonAssocSemiring R] [IsTopologicalSemiring R]
  body: mk
  map_one' := mk_one; map_zero' := mk_zero; map_add' := mk_add; map_mul' := mk_mul

中文:
定义 mkRingHom
  签名: [非结合半环 R] [是TopologicalSemiring R]
  定义体: mk
  map_one' := mk_one; map_zero' := mk_zero; map_add' := mk_add; map_mul' := mk_mul
-/
def mkRingHom [NonAssocSemiring R] [IsTopologicalSemiring R] : R ->+* SeparationQuotient R where
  toFun := mk
  map_one' := mk_one; map_zero' := mk_zero; map_add' := mk_add; map_mul' := mk_mul

end Ring

section DistribSMul

variable {M A : Type*} [TopologicalSpace A]

/--
Instance `instDistribSMul` / 实例 `instDistribSMul`

English:
instance instDistribSMul
  signature: [AddZeroClass A] [DistribSMul M A]
  body: fast_instance% surjective_mk.distribSMul mkAddMonoidHom mk_smul

中文:
实例 instDistribSMul
  签名: [加法零类 A] [分配标量乘法 M A]
  定义体: fast_instance% surjective_mk.distribSMul mkAddMonoidHom mk_smul

Depends on / 依赖: distribSMul, fast_instance, mkAddMonoidHom, mk_smul, surjective_mk, surjective_mk.distribSMul
-/
instance instDistribSMul [AddZeroClass A] [DistribSMul M A]
    [ContinuousAdd A] [ContinuousConstSMul M A] :
    DistribSMul M (SeparationQuotient A) :=
  fast_instance% surjective_mk.distribSMul mkAddMonoidHom mk_smul

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid M] [AddMonoid A] [DistribMulAction M A]
  body: fast_instance% surjective_mk.distribMulAction mkAddMonoidHom mk_smul

中文:
实例 instDistribMulAction
  签名: [幺半群 M] [加法幺半群 A] [分配乘法作用 M A]
  定义体: fast_instance% surjective_mk.distribMulAction mkAddMonoidHom mk_smul

Depends on / 依赖: distribMulAction, fast_instance, mkAddMonoidHom, mk_smul, surjective_mk, surjective_mk.distribMulAction
-/
instance instDistribMulAction [Monoid M] [AddMonoid A] [DistribMulAction M A]
    [ContinuousAdd A] [ContinuousConstSMul M A] :
    DistribMulAction M (SeparationQuotient A) :=
  fast_instance% surjective_mk.distribMulAction mkAddMonoidHom mk_smul

/--
Instance `instMulDistribMulAction` / 实例 `instMulDistribMulAction`

English:
instance instMulDistribMulAction
  signature: [Monoid M] [Monoid A] [MulDistribMulAction M A]
  body: fast_instance% surjective_mk.mulDistribMulAction mkMonoidHom mk_smul

中文:
实例 instMulDistribMulAction
  签名: [幺半群 M] [幺半群 A] [MulDistribMul作用 M A]
  定义体: fast_instance% surjective_mk.mulDistribMulAction mkMonoidHom mk_smul

Depends on / 依赖: fast_instance, mkMonoidHom, mk_smul, mulDistribMulAction, surjective_mk, surjective_mk.mulDistribMulAction
-/
instance instMulDistribMulAction [Monoid M] [Monoid A] [MulDistribMulAction M A]
    [ContinuousMul A] [ContinuousConstSMul M A] :
    MulDistribMulAction M (SeparationQuotient A) :=
  fast_instance% surjective_mk.mulDistribMulAction mkMonoidHom mk_smul

end DistribSMul

section Module

variable {R S M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    [Semiring S] [AddCommMonoid N] [Module S N]
    [TopologicalSpace N]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module R (SeparationQuotient M)
  body: fast_instance% surjective_mk.module R mkAddMonoidHom mk_smul

中文:
实例 instModule
  签名: : 模 R (SeparationQuotient M)
  定义体: fast_instance% surjective_mk.module R mkAddMonoidHom mk_smul

Depends on / 依赖: fast_instance, mkAddMonoidHom, mk_smul, module, surjective_mk, surjective_mk.module
-/
instance instModule : Module R (SeparationQuotient M) :=
  fast_instance% surjective_mk.module R mkAddMonoidHom mk_smul

variable (R M)

/-- `SeparationQuotient.mk` as a continuous linear map. -/
@[simps]
/--
Definition of `mkCLM` / `mkCLM` 的定义

English:
definition mkCLM
  signature: : M ->L[R] SeparationQuotient M where
  body: mk
  map_add' := mk_add
  map_smul' := mk_smul

中文:
定义 mkCLM
  签名: : M ->L[R] SeparationQuotient M where
  定义体: mk
  map_add' := mk_add
  map_smul' := mk_smul
-/
def mkCLM : M ->L[R] SeparationQuotient M where
  toFun := mk
  map_add' := mk_add
  map_smul' := mk_smul

variable {R M}

/-- The lift (as a continuous linear map) of `f` with `f x = f y` for `Inseparable x y`. -/
@[simps]
/--
Definition of `liftCLM` / `liftCLM` 的定义

English:
definition liftCLM
  signature: {σ : R ->+* S} (f : M ->SL[σ] N) (hf : forall x y, Inseparable x y -> f x = f y)
  body: SeparationQuotient.lift f hf
map_add' := Quotient.ind₂ map_add f
map_smul' {r} := Quotient.ind map_smulₛₗ f r
  cont := by fun_prop

@[simp]

中文:
定义 liftCLM
  签名: {σ : R ->+* S} (f : M ->SL[σ] N) (hf : 对任意 x y, 不可分 x y -> f x = f y)
  定义体: SeparationQuotient.lift f hf
map_add' := Quotient.ind₂ map_add f
map_smul' {r} := Quotient.ind map_smulₛₗ f r
  cont := by fun_prop

@[simp]

Depends on / 依赖: SeparationQuotient, SeparationQuotient.lift
-/
noncomputable def liftCLM {σ : R ->+* S} (f : M ->SL[σ] N) (hf : forall x y, Inseparable x y -> f x = f y) :
    SeparationQuotient M ->SL[σ] N where
  toFun := SeparationQuotient.lift f hf
map_add' := Quotient.ind₂ map_add f
map_smul' {r} := Quotient.ind map_smulₛₗ f r
  cont := by fun_prop

@[simp]
/--
theorem `liftCLM_mk` / 定理 `liftCLM_mk`

English:
theorem liftCLM_mk
  statement: {σ : R ->+* S} (f : M ->SL[σ] N) (hf : forall x y, Inseparable x y -> f x = f y)
  proof: rfl

中文:
定理 liftCLM_mk
  结论: {σ : R ->+* S} (f : M ->SL[σ] N) (hf : 对任意 x y, 不可分 x y -> f x = f y)
  证明: rfl
-/
theorem liftCLM_mk {σ : R ->+* S} (f : M ->SL[σ] N) (hf : forall x y, Inseparable x y -> f x = f y)
    (x : M) : liftCLM f hf (mk x) = f x := rfl

end Module

section Algebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [ContinuousConstSMul R A]

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra R (SeparationQuotient A) where
  body: mkRingHom.comp (algebraMap R A)
commutes' r := Quotient.ind fun a => congrArg _ Algebra.commutes r a
smul_def' r := Quotient.ind fun a => congrArg _ Algebra.smul_def r a

@[simp]

中文:
实例 instAlgebra
  签名: : 代数 R (SeparationQuotient A) where
  定义体: mkRingHom.comp (algebraMap R A)
commutes' r := Quotient.ind fun a => congrArg _ Algebra.commutes r a
smul_def' r := Quotient.ind fun a => congrArg _ Algebra.smul_def r a

@[simp]

Depends on / 依赖: algebraMap, mkRingHom, mkRingHom.comp
-/
instance instAlgebra : Algebra R (SeparationQuotient A) where
  algebraMap := mkRingHom.comp (algebraMap R A)
commutes' r := Quotient.ind fun a => congrArg _ Algebra.commutes r a
smul_def' r := Quotient.ind fun a => congrArg _ Algebra.smul_def r a

@[simp]
/--
theorem `mk_algebraMap` / 定理 `mk_algebraMap`

English:
theorem mk_algebraMap
  given: (r : R)
  statement: mk (algebraMap R A r) = algebraMap R (SeparationQuotient A) r
  proof: rfl

中文:
定理 mk_algebraMap
  条件: (r : R)
  结论: mk (algebraMap R A r) = algebraMap R (SeparationQuotient A) r
  证明: rfl
-/
theorem mk_algebraMap (r : R) : mk (algebraMap R A r) = algebraMap R (SeparationQuotient A) r :=
  rfl

end Algebra

end SeparationQuotient
