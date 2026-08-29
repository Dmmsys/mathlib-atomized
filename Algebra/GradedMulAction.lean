/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.Algebra.GradedMonoid

/-!
# Additively-graded multiplicative action structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(•) : A i → M j → M (i +ᵥ j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `GradedMonoid.GSMul A M`
* `GradedMonoid.GMulAction A M`

With the `SigmaGraded` scope open, these respectively imbue:

* `SMul (GradedMonoid A) (GradedMonoid M)`
* `MulAction (GradedMonoid A) (GradedMonoid M)`

For now, these typeclasses are primarily used in the construction of `DirectSum.GModule.Module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedSMul A M` (which provides the obvious `GradedMonoid.GSMul A` instance)

which provides the API lemma

* `SetLike.graded_smul_mem_graded`

Note that there is no need for `SetLike.graded_mul_action` or similar, as all the information it
would contain is already supplied by `GradedSMul` when the objects within `A` and `M` have
a `MulAction` instance.

## Tags

graded action
-/

public section


variable {ιA ιB ιM : Type*}

namespace GradedMonoid

/-! ### Typeclasses -/


section Defs

variable (A : ιA -> Type*) (M : ιM -> Type*)

/--
Definition of `GSMul` / `GSMul` 的定义

English:
class GSMul
  parameters: [VAdd ιA ιM]
  axioms and operations (1):
    - smul({i j}) : A i -> M j -> M (i +ᵥ j)

中文:
类 GSMul
  参数: [VAdd ιA ιM]
  公理与运算 (1 个):
    - smul({i j}) : A i -> M j -> M (i +ᵥ j)
-/
class GSMul [VAdd ιA ιM] where
  /-- The homogeneous multiplication map `smul` -/
  smul {i j} : A i -> M j -> M (i +ᵥ j)

/--
Instance `GMul.toGSMul` / 实例 `GMul.toGSMul`

English:
instance GMul.toGSMul
  signature: [Add ιA] [GMul A]
  body: GMul.mul

中文:
实例 GMul.toGSMul
  签名: [Add ιA] [GMul A]
  定义体: GMul.mul

Depends on / 依赖: GMul.mul
-/
instance GMul.toGSMul [Add ιA] [GMul A] : GSMul A A where smul := GMul.mul

/--
Instance `GSMul.toSMul` / 实例 `GSMul.toSMul`

English:
instance GSMul.toSMul
  signature: [VAdd ιA ιM] [GSMul A M]
  body: ⟨fun x y => ⟨_, GSMul.smul x.snd y.snd⟩⟩

中文:
实例 GSMul.toSMul
  签名: [VAdd ιA ιM] [GSMul A M]
  定义体: ⟨fun x y => ⟨_, GSMul.smul x.snd y.snd⟩⟩

Depends on / 依赖: GSMul.smul, x.snd, y.snd
-/
instance GSMul.toSMul [VAdd ιA ιM] [GSMul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun x y => ⟨_, GSMul.smul x.snd y.snd⟩⟩

/--
theorem `mk_smul_mk` / 定理 `mk_smul_mk`

English:
theorem mk_smul_mk
  given: [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j)
  proof: rfl

中文:
定理 mk_smul_mk
  条件: [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j)
  证明: rfl
-/
theorem mk_smul_mk [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i +ᵥ j) (GSMul.smul a b) :=
  rfl

/--
Definition of `GMulAction` / `GMulAction` 的定义

English:
class GMulAction
  parameters: [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A]
  extends: GSMul A M
  axioms and operations (2):
    - one_smul((b : GradedMonoid M)) : (1 : GradedMonoid A) • b = b
    - mul_smul((a a' : GradedMonoid A) (b : GradedMonoid M)) : (a * a') • b = a • a' • b

中文:
类 GMulAction
  参数: [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A]
  继承: GSMul A M
  公理与运算 (2 个):
    - one_smul((b : GradedMonoid M)) : (1 : GradedMonoid A) • b = b
    - mul_smul((a a' : GradedMonoid A) (b : GradedMonoid M)) : (a * a') • b = a • a' • b
-/
class GMulAction [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A] extends GSMul A M where
  /-- One is the neutral element for `•` -/
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b

/--
Instance `GMonoid.toGMulAction` / 实例 `GMonoid.toGMulAction`

English:
instance GMonoid.toGMulAction
  signature: [AddMonoid ιA] [GMonoid A]
  body: { GMul.toGSMul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }

中文:
实例 GMonoid.toGMulAction
  签名: [AddMonoid ιA] [GMonoid A]
  定义体: { GMul.toGSMul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }

Depends on / 依赖: GMonoid, GMonoid.mul_assoc, GMonoid.one_mul, GMul.toGSMul, mul_assoc, mul_smul, one_mul, one_smul, toGSMul
-/
instance GMonoid.toGMulAction [AddMonoid ιA] [GMonoid A] : GMulAction A A :=
  { GMul.toGSMul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }

/--
Instance `GMulAction.toMulAction` / 实例 `GMulAction.toMulAction`

English:
instance GMulAction.toMulAction
  signature: [AddMonoid ιA] [GMonoid A] [VAdd ιA ιM] [GMulAction A M]
  body: GMulAction.one_smul
  mul_smul := GMulAction.mul_smul

中文:
实例 GMulAction.toMulAction
  签名: [AddMonoid ιA] [GMonoid A] [VAdd ιA ιM] [GMulAction A M]
  定义体: GMulAction.one_smul
  mul_smul := GMulAction.mul_smul

Depends on / 依赖: GMulAction, GMulAction.one_smul, one_smul
-/
instance GMulAction.toMulAction [AddMonoid ιA] [GMonoid A] [VAdd ιA ιM] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M) where
  one_smul := GMulAction.one_smul
  mul_smul := GMulAction.mul_smul

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type*}

/--
Definition of `SetLike.GradedSMul` / `SetLike.GradedSMul` 的定义

English:
class SetLike.GradedSMul
  parameters: {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  axioms and operations (1):
    - smul_mem : forall ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai in A i -> bj in B j -> ai • bj in B (i +ᵥ j)

中文:
类 SetLike.GradedSMul
  参数: {S R N M : 类型} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  公理与运算 (1 个):
    - smul_mem : 对任意 ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai in A i -> bj in B j -> ai • bj in B (i +ᵥ j)
-/
class SetLike.GradedSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  (A : ιA -> S) (B : ιB -> N) : Prop where
  /-- Multiplication is homogeneous -/
  smul_mem : forall ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai in A i -> bj in B j -> ai • bj in B (i +ᵥ j)

/--
Instance `SetLike.toGSMul` / 实例 `SetLike.toGSMul`

English:
instance SetLike.toGSMul
  signature: {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  body: ⟨a.1 • b.1, SetLike.GradedSMul.smul_mem a.2 b.2⟩

@[simp]

中文:
实例 SetLike.toGSMul
  签名: {S R N M : 类型} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  定义体: ⟨a.1 • b.1, SetLike.GradedSMul.smul_mem a.2 b.2⟩

@[simp]

Depends on / 依赖: GradedSMul, SetLike, SetLike.GradedSMul.smul_mem, smul_mem
-/
instance SetLike.toGSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA -> S) (B : ιB -> N) [SetLike.GradedSMul A B] :
    GradedMonoid.GSMul (fun i => A i) fun i => B i where
  smul a b := ⟨a.1 • b.1, SetLike.GradedSMul.smul_mem a.2 b.2⟩

@[simp]
/--
theorem `SetLike.coe_GSMul` / 定理 `SetLike.coe_GSMul`

English:
theorem SetLike.coe_GSMul
  statement: {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  proof: rfl

中文:
定理 SetLike.coe_GSMul
  结论: {S R N M : 类型} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  证明: rfl
-/
theorem SetLike.coe_GSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA -> S) (B : ιB -> N) [SetLike.GradedSMul A B] {i : ιA} {j : ιB} (x : A i) (y : B j) :
    (@GradedMonoid.GSMul.smul ιA ιB (fun i => A i) (fun i => B i) _ _ i j x y : M) = x.1 • y.1 :=
  rfl

/--
Instance `SetLike.GradedMul.toGradedSMul` / 实例 `SetLike.GradedMul.toGradedSMul`

English:
instance SetLike.GradedMul.toGradedSMul
  signature: [AddMonoid ιA] [Monoid R] {S : Type*} [SetLike S R]
  body: SetLike.GradedMonoid.toGradedMul.mul_mem hi hj

中文:
实例 SetLike.GradedMul.toGradedSMul
  签名: [AddMonoid ιA] [Monoid R] {S : 类型} [SetLike S R]
  定义体: SetLike.GradedMonoid.toGradedMul.mul_mem hi hj

Depends on / 依赖: GradedMonoid, SetLike, SetLike.GradedMonoid.toGradedMul.mul_mem, mul_mem, toGradedMul
-/
instance SetLike.GradedMul.toGradedSMul [AddMonoid ιA] [Monoid R] {S : Type*} [SetLike S R]
    (A : ιA -> S) [SetLike.GradedMonoid A] : SetLike.GradedSMul A A where
  smul_mem _ _ _ _ hi hj := SetLike.GradedMonoid.toGradedMul.mul_mem hi hj

end Subobjects

section HomogeneousElements

variable {S R N M : Type*} [SetLike S R] [SetLike N M]

/--
theorem `SetLike.IsHomogeneousElem.graded_smul` / 定理 `SetLike.IsHomogeneousElem.graded_smul`

English:
theorem SetLike.IsHomogeneousElem.graded_smul
  statement: [VAdd ιA ιB] [SMul R M] {A : ιA -> S} {B : ιB -> N}

中文:
定理 SetLike.IsHomogeneousElem.graded_smul
  结论: [VAdd ιA ιB] [SMul R M] {A : ιA -> S} {B : ιB -> N}
-/
theorem SetLike.IsHomogeneousElem.graded_smul [VAdd ιA ιB] [SMul R M] {A : ιA -> S} {B : ιB -> N}
    [SetLike.GradedSMul A B] {a : R} {b : M} :
    SetLike.IsHomogeneousElem A a -> SetLike.IsHomogeneousElem B b ->
    SetLike.IsHomogeneousElem B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i +ᵥ j, SetLike.GradedSMul.smul_mem hi hj⟩

end HomogeneousElements
