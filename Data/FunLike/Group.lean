/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-! # Group instances for `FunLike` types
In this file we define various instances related to groups for `FunLike` types.

For example given a `FunLike F α β` with `IsMulApply F α β` and `Semigroup β`, then `F` is naturally
a semigroup. Note that currently, these are not registered as instances, but only `abbrev`s to
avoid long typeclass searches.

Moreover, we define the homomorphism `FunLike.coeMulHom : F →* α → β` that acts by coercion. This
definition is mainly needed to define a module instance on `F`.

-/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section CoercionHom

section MulHom

variable [Mul F] [Mul β] [IsMulApply F α β]

variable (F α β) in
/-- Coercion as a multiplicative homomorphism. -/
@[to_additive
/-- Coercion as an additive homomorphism. -/]
/--
Definition of `coeMulHom` / `coeMulHom` 的定义

English:
definition coeMulHom
  signature: : F ->ₙ* α -> β where
  body: f
  map_mul' := coe_mul

@[to_additive (attr := simp)]

中文:
定义 coeMulHom
  签名: : F ->ₙ* α -> β where
  定义体: f
  map_mul' := coe_mul

@[to_additive (attr := simp)]
-/
def coeMulHom : F ->ₙ* α -> β where
  toFun f := f
  map_mul' := coe_mul

@[to_additive (attr := simp)]
/--
theorem `coeMulHom_apply` / 定理 `coeMulHom_apply`

English:
theorem coeMulHom_apply
  given: (f : F)
  statement: coeMulHom F α β f = f
  proof: rfl

@[to_additive (attr := norm_cast)]

中文:
定理 coeMulHom_apply
  条件: (f : F)
  结论: coeMulHom F α β f = f
  证明: rfl

@[to_additive (attr := norm_cast)]
-/
theorem coeMulHom_apply (f : F) : coeMulHom F α β f = f := rfl

@[to_additive (attr := norm_cast)]
/--
theorem `coe_coeMulHom` / 定理 `coe_coeMulHom`

English:
theorem coe_coeMulHom
  statement: (coeMulHom F α β : F -> α -> β) = DFunLike.coe
  proof: rfl

@[to_additive]

中文:
定理 coe_coeMulHom
  结论: (coeMulHom F α β : F -> α -> β) = DFunLike.coe
  证明: rfl

@[to_additive]
-/
theorem coe_coeMulHom : (coeMulHom F α β : F -> α -> β) = DFunLike.coe := rfl

@[to_additive]
/--
theorem `coeMulHom_injective` / 定理 `coeMulHom_injective`

English:
theorem coeMulHom_injective
  statement: Function.Injective (coeMulHom F α β)
  proof: by
  rw [coe_coeMulHom]
  exact DFunLike.coe_injective

中文:
定理 coeMulHom_injective
  结论: Function.Injective (coeMulHom F α β)
  证明: by
  rw [coe_coeMulHom]
  exact DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_coeMulHom, coe_injective
-/
theorem coeMulHom_injective : Function.Injective (coeMulHom F α β) := by
  rw [coe_coeMulHom]
  exact DFunLike.coe_injective

end MulHom

section MonoidHom

variable [MulOne F] [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β]

variable (F α β) in
/-- Coercion as a monoid homomorphism. -/
@[to_additive
/-- Coercion as an additive monoid homomorphism. -/]
/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: : F ->* α -> β where
  body: f
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]

中文:
定义 coeMonoidHom
  签名: : F ->* α -> β where
  定义体: f
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
-/
def coeMonoidHom : F ->* α -> β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
/--
theorem `coeMonoidHom_apply` / 定理 `coeMonoidHom_apply`

English:
theorem coeMonoidHom_apply
  given: (f : F)
  statement: coeMonoidHom F α β f = f
  proof: rfl

@[to_additive (attr := norm_cast)]

中文:
定理 coeMonoidHom_apply
  条件: (f : F)
  结论: coeMonoidHom F α β f = f
  证明: rfl

@[to_additive (attr := norm_cast)]
-/
theorem coeMonoidHom_apply (f : F) : coeMonoidHom F α β f = f := rfl

@[to_additive (attr := norm_cast)]
/--
theorem `coe_coeMonoidHom` / 定理 `coe_coeMonoidHom`

English:
theorem coe_coeMonoidHom
  statement: (coeMonoidHom F α β : F -> α -> β) = DFunLike.coe
  proof: rfl

@[to_additive (attr := norm_cast)]

中文:
定理 coe_coeMonoidHom
  结论: (coeMonoidHom F α β : F -> α -> β) = DFunLike.coe
  证明: rfl

@[to_additive (attr := norm_cast)]
-/
theorem coe_coeMonoidHom : (coeMonoidHom F α β : F -> α -> β) = DFunLike.coe := rfl

@[to_additive (attr := norm_cast)]
/--
theorem `coe_coeMonoidHom'` / 定理 `coe_coeMonoidHom'`

English:
theorem coe_coeMonoidHom'
  statement: (coeMonoidHom F α β : F ->ₙ* α -> β) = coeMulHom F α β
  proof: rfl

@[to_additive]

中文:
定理 coe_coeMonoidHom'
  结论: (coeMonoidHom F α β : F ->ₙ* α -> β) = coeMulHom F α β
  证明: rfl

@[to_additive]
-/
theorem coe_coeMonoidHom' : (coeMonoidHom F α β : F ->ₙ* α -> β) = coeMulHom F α β := rfl

@[to_additive]
/--
theorem `coeMonoidHom_injective` / 定理 `coeMonoidHom_injective`

English:
theorem coeMonoidHom_injective
  statement: Function.Injective (coeMonoidHom F α β)
  proof: by
  rw [coe_coeMonoidHom]
  exact DFunLike.coe_injective

中文:
定理 coeMonoidHom_injective
  结论: Function.Injective (coeMonoidHom F α β)
  证明: by
  rw [coe_coeMonoidHom]
  exact DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_coeMonoidHom, coe_injective
-/
theorem coeMonoidHom_injective : Function.Injective (coeMonoidHom F α β) := by
  rw [coe_coeMonoidHom]
  exact DFunLike.coe_injective

end MonoidHom

end CoercionHom

section GroupInstances

variable [Mul F]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a semigroup if `β` is a semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is an additive semigroup
if `β` is an additive semigroup. -/]
/--
Definition of `semigroup` / `semigroup` 的定义

English:
abbreviation semigroup
  signature: [Semigroup β] [IsMulApply F α β]
  body: DFunLike.coe_injective.semigroup (fun (f : F) => (f : α -> β)) coe_mul

中文:
缩写 semigroup
  签名: [Semigroup β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.semigroup (fun (f : F) => (f : α -> β)) coe_mul
-/
protected abbrev semigroup [Semigroup β] [IsMulApply F α β] : Semigroup F :=
  DFunLike.coe_injective.semigroup (fun (f : F) => (f : α -> β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a commutative semigroup if `β` is a
commutative semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a commatative additive
semigroup if `β` is a commatative additive semigroup. -/]
/--
Definition of `commSemigroup` / `commSemigroup` 的定义

English:
abbreviation commSemigroup
  signature: [CommSemigroup β] [IsMulApply F α β]
  body: DFunLike.coe_injective.commSemigroup (fun (f : F) => (f : α -> β)) coe_mul

中文:
缩写 commSemigroup
  签名: [CommSemigroup β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.commSemigroup (fun (f : F) => (f : α -> β)) coe_mul
-/
protected abbrev commSemigroup [CommSemigroup β] [IsMulApply F α β] :
    CommSemigroup F :=
  DFunLike.coe_injective.commSemigroup (fun (f : F) => (f : α -> β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has left cancellative multiplication if
`β` has left cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has left cancellative
addition if `β` has left cancellative addition. -/]
/--
theorem `isLeftCancelMul` / 定理 `isLeftCancelMul`

English:
theorem isLeftCancelMul
  given: [Mul β] [IsLeftCancelMul β] [IsMulApply F α β]
  proof: DFunLike.coe_injective.isLeftCancelMul (fun (f : F) => (f : α -> β)) coe_mul

中文:
定理 isLeftCancelMul
  条件: [Mul β] [IsLeftCancelMul β] [IsMulApply F α β]
  证明: DFunLike.coe_injective.isLeftCancelMul (fun (f : F) => (f : α -> β)) coe_mul
-/
protected theorem isLeftCancelMul [Mul β] [IsLeftCancelMul β] [IsMulApply F α β] :
    IsLeftCancelMul F :=
  DFunLike.coe_injective.isLeftCancelMul (fun (f : F) => (f : α -> β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right cancellative multiplication if
`β` has right cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right cancellative
addition if `β` has right cancellative addition. -/]
/--
theorem `isRightCancelMul` / 定理 `isRightCancelMul`

English:
theorem isRightCancelMul
  given: [Mul β] [IsRightCancelMul β] [IsMulApply F α β]
  proof: DFunLike.coe_injective.isRightCancelMul (fun (f : F) => (f : α -> β)) coe_mul

中文:
定理 isRightCancelMul
  条件: [Mul β] [IsRightCancelMul β] [IsMulApply F α β]
  证明: DFunLike.coe_injective.isRightCancelMul (fun (f : F) => (f : α -> β)) coe_mul
-/
protected theorem isRightCancelMul [Mul β] [IsRightCancelMul β] [IsMulApply F α β] :
    IsRightCancelMul F :=
  DFunLike.coe_injective.isRightCancelMul (fun (f : F) => (f : α -> β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right multiplication if
`β` has right multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right
addition if `β` has cancellative addition. -/]
/--
theorem `isCancelMul` / 定理 `isCancelMul`

English:
theorem isCancelMul
  given: [Mul β] [IsCancelMul β] [IsMulApply F α β]
  proof: DFunLike.coe_injective.isCancelMul (fun (f : F) => (f : α -> β)) coe_mul

中文:
定理 isCancelMul
  条件: [Mul β] [IsCancelMul β] [IsMulApply F α β]
  证明: DFunLike.coe_injective.isCancelMul (fun (f : F) => (f : α -> β)) coe_mul
-/
protected theorem isCancelMul [Mul β] [IsCancelMul β] [IsMulApply F α β] :
    IsCancelMul F :=
  DFunLike.coe_injective.isCancelMul (fun (f : F) => (f : α -> β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a left cancel semigroup if `β` is a
left cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a left cancel additive
semigroup if `β` is a left cancel additive semigroup. -/]
/--
Definition of `leftCancelSemigroup` / `leftCancelSemigroup` 的定义

English:
abbreviation leftCancelSemigroup
  signature: [LeftCancelSemigroup β] [IsMulApply F α β]
  body: DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) => (f : α -> β)) coe_mul

中文:
缩写 leftCancelSemigroup
  签名: [LeftCancelSemigroup β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) => (f : α -> β)) coe_mul
-/
protected abbrev leftCancelSemigroup [LeftCancelSemigroup β] [IsMulApply F α β] :
    LeftCancelSemigroup F :=
  DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) => (f : α -> β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a right cancel semigroup if `β` is a
right cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a right cancel additive
semigroup if `β` is a right cancel additive semigroup. -/]
/--
Definition of `rightCancelSemigroup` / `rightCancelSemigroup` 的定义

English:
abbreviation rightCancelSemigroup
  signature: [RightCancelSemigroup β] [IsMulApply F α β]
  body: DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) => (f : α -> β)) coe_mul

中文:
缩写 rightCancelSemigroup
  签名: [RightCancelSemigroup β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) => (f : α -> β)) coe_mul
-/
protected abbrev rightCancelSemigroup [RightCancelSemigroup β] [IsMulApply F α β] :
    RightCancelSemigroup F :=
  DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) => (f : α -> β)) coe_mul

variable [One F]

/-- A `FunLike` type with `1` and `*` is `MulOneClass` if `β` is a `MulOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and `+` is `AddZeroClass` if `β` is a
`AddZeroClass`. -/]
/--
Definition of `mulOneClass` / `mulOneClass` 的定义

English:
abbreviation mulOneClass
  signature: [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.mulOneClass (fun (f : F) => (f : α -> β)) coe_one coe_mul

中文:
缩写 mulOneClass
  签名: [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.mulOneClass (fun (f : F) => (f : α -> β)) coe_one coe_mul
-/
protected abbrev mulOneClass [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β] :
    MulOneClass F :=
  DFunLike.coe_injective.mulOneClass (fun (f : F) => (f : α -> β)) coe_one coe_mul

variable [Pow F Nat]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a monoid if `β` is a monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is an additive monoid if `β` is an additive monoid. -/]
/--
Definition of `monoid` / `monoid` 的定义

English:
abbreviation monoid
  signature: [Monoid β] [IsOneApply F α β] [IsMulApply F α β] [IsPowApply Nat F α β]
  body: DFunLike.coe_injective.monoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

中文:
缩写 monoid
  签名: [Monoid β] [IsOneApply F α β] [IsMulApply F α β] [IsPowApply 自然数 F α β]
  定义体: DFunLike.coe_injective.monoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow
-/
protected abbrev monoid [Monoid β] [IsOneApply F α β] [IsMulApply F α β] [IsPowApply Nat F α β] :
    Monoid F :=
  DFunLike.coe_injective.monoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a left cancel monoid if `β` is a left cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a left cancel additive monoid if `β` is a left cancel additive monoid. -/]
/--
Definition of `leftCancelMonoid` / `leftCancelMonoid` 的定义

English:
abbreviation leftCancelMonoid
  signature: [LeftCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.leftCancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

中文:
缩写 leftCancelMonoid
  签名: [LeftCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.leftCancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow
-/
protected abbrev leftCancelMonoid [LeftCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply Nat F α β] : LeftCancelMonoid F :=
  DFunLike.coe_injective.leftCancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a right cancel monoid if `β` is a right cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a right cancel additive monoid if `β` is a right cancel
additive monoid. -/]
/--
Definition of `rightCancelMonoid` / `rightCancelMonoid` 的定义

English:
abbreviation rightCancelMonoid
  signature: [RightCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.rightCancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

中文:
缩写 rightCancelMonoid
  签名: [RightCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.rightCancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow
-/
protected abbrev rightCancelMonoid [RightCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply Nat F α β] : RightCancelMonoid F :=
  DFunLike.coe_injective.rightCancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel monoid if `β` is a cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel additive monoid if `β` is a cancel additive monoid. -/]
/--
Definition of `cancelMonoid` / `cancelMonoid` 的定义

English:
abbreviation cancelMonoid
  signature: [CancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.cancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

中文:
缩写 cancelMonoid
  签名: [CancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.cancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow
-/
protected abbrev cancelMonoid [CancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply Nat F α β] : CancelMonoid F :=
  DFunLike.coe_injective.cancelMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a commutative monoid if `β` is a commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a commutative additive monoid if `β` is a commutative additive monoid. -/]
/--
Definition of `commMonoid` / `commMonoid` 的定义

English:
abbreviation commMonoid
  signature: [CommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.commMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

中文:
缩写 commMonoid
  签名: [CommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.commMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow
-/
protected abbrev commMonoid [CommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply Nat F α β] : CommMonoid F :=
  DFunLike.coe_injective.commMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel commutative monoid if `β` is a cancel commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel commutative additive monoid if `β` is a cancel commutative
additive monoid. -/]
/--
Definition of `cancelCommMonoid` / `cancelCommMonoid` 的定义

English:
abbreviation cancelCommMonoid
  signature: [CancelCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.cancelCommMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

中文:
缩写 cancelCommMonoid
  签名: [CancelCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.cancelCommMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow
-/
protected abbrev cancelCommMonoid [CancelCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply Nat F α β] : CancelCommMonoid F :=
  DFunLike.coe_injective.cancelCommMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_pow

variable [Inv F]

/-- A `FunLike` type with inverse that satisfies `(f⁻¹) x = (f x)⁻¹` is an involutive inversion
if `β` is an involutive inversion. -/
@[to_additive /-- A `FunLike` type with negation that satisfies `(- f) x = - (f x)` is an involutive
negation if `β` is an involutive negation. -/]
/--
Definition of `involutiveInv` / `involutiveInv` 的定义

English:
abbreviation involutiveInv
  signature: [InvolutiveInv β] [IsInvApply F α β]
  body: DFunLike.coe_injective.involutiveInv (fun (f : F) => (f : α -> β)) coe_inv

中文:
缩写 involutiveInv
  签名: [InvolutiveInv β] [IsInvApply F α β]
  定义体: DFunLike.coe_injective.involutiveInv (fun (f : F) => (f : α -> β)) coe_inv
-/
protected abbrev involutiveInv [InvolutiveInv β] [IsInvApply F α β] : InvolutiveInv F :=
  DFunLike.coe_injective.involutiveInv (fun (f : F) => (f : α -> β)) coe_inv

/-- A `FunLike` type with `1` and inverse is an `InvOneClass` if `β` is an `InvOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and negation is a `NegZeroClass` if `β` is a
`NegZeroClass`. -/]
/--
Definition of `invOneClass` / `invOneClass` 的定义

English:
abbreviation invOneClass
  signature: [InvOneClass β] [IsOneApply F α β] [IsInvApply F α β]
  body: DFunLike.coe_injective.invOneClass (fun (f : F) => (f : α -> β)) coe_one coe_inv

中文:
缩写 invOneClass
  签名: [InvOneClass β] [IsOneApply F α β] [IsInvApply F α β]
  定义体: DFunLike.coe_injective.invOneClass (fun (f : F) => (f : α -> β)) coe_one coe_inv
-/
protected abbrev invOneClass [InvOneClass β] [IsOneApply F α β] [IsInvApply F α β] :
    InvOneClass F :=
  DFunLike.coe_injective.invOneClass (fun (f : F) => (f : α -> β)) coe_one coe_inv

variable [Div F] [Pow F Int]

/-- A `FunLike` type is a `DivInvMonoid` if `β` is a `DivInvMonoid`. -/
@[to_additive subNegMonoid /-- A `FunLike` type is a `SubNegMonoid` if `β` is a `SubNegMonoid`. -/]
/--
Definition of `divInvMonoid` / `divInvMonoid` 的定义

English:
abbreviation divInvMonoid
  signature: [DivInvMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.divInvMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

中文:
缩写 divInvMonoid
  签名: [DivInvMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.divInvMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow
-/
protected abbrev divInvMonoid [DivInvMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply Nat F α β] [IsPowApply Int F α β] :
    DivInvMonoid F :=
  DFunLike.coe_injective.divInvMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

/-- A `FunLike` type is a `DivInvOneMonoid` if `β` is a `DivInvOneMonoid`. -/
@[to_additive
/-- A `FunLike` type is a `SubNegOneMonoid` if `β` is a `SubNegOneMonoid`. -/]
/--
Definition of `divInvOneMonoid` / `divInvOneMonoid` 的定义

English:
abbreviation divInvOneMonoid
  signature: [DivInvOneMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.divInvOneMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

中文:
缩写 divInvOneMonoid
  签名: [DivInvOneMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.divInvOneMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow
-/
protected abbrev divInvOneMonoid [DivInvOneMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply Nat F α β] [IsPowApply Int F α β] :
    DivInvOneMonoid F :=
  DFunLike.coe_injective.divInvOneMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division monoid if `β` is a division monoid. -/
@[to_additive /-- A `FunLike` type is a subtraction monoid if `β` is a subtraction monoid. -/]
/--
Definition of `divisionMonoid` / `divisionMonoid` 的定义

English:
abbreviation divisionMonoid
  signature: [DivisionMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.divisionMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

中文:
缩写 divisionMonoid
  签名: [DivisionMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.divisionMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow
-/
protected abbrev divisionMonoid [DivisionMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply Nat F α β] [IsPowApply Int F α β] :
    DivisionMonoid F :=
  DFunLike.coe_injective.divisionMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division commutative monoid if `β` is a division commutative monoid. -/
@[to_additive subtractionCommMonoid /-- A `FunLike` type is a subtraction commutative monoid if `β`
is a subtraction commutative monoid. -/]
/--
Definition of `divisionCommMonoid` / `divisionCommMonoid` 的定义

English:
abbreviation divisionCommMonoid
  signature: [DivisionCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  body: DFunLike.coe_injective.divisionCommMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

中文:
缩写 divisionCommMonoid
  签名: [DivisionCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
  定义体: DFunLike.coe_injective.divisionCommMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow
-/
protected abbrev divisionCommMonoid [DivisionCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply Nat F α β] [IsPowApply Int F α β] :
    DivisionCommMonoid F :=
  DFunLike.coe_injective.divisionCommMonoid (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

/-- A `FunLike` type is a group if `β` is a group. -/
@[to_additive /-- A `FunLike` type is an additive group if `β` is an additive group. -/]
/--
Definition of `group` / `group` 的定义

English:
abbreviation group
  signature: [Group β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
  body: DFunLike.coe_injective.group (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div coe_pow
    coe_pow

中文:
缩写 group
  签名: [Group β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
  定义体: DFunLike.coe_injective.group (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div coe_pow
    coe_pow
-/
protected abbrev group [Group β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
    [IsDivApply F α β] [IsPowApply Nat F α β] [IsPowApply Int F α β] :
    Group F :=
  DFunLike.coe_injective.group (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div coe_pow
    coe_pow

/-- A `FunLike` type is a commutative group if `β` is a commutative group. -/
@[to_additive /-- A `FunLike` type is an additive commutative group if `β` is an additive
commutative group. -/]
/--
Definition of `commGroup` / `commGroup` 的定义

English:
abbreviation commGroup
  signature: [CommGroup β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
  body: DFunLike.coe_injective.commGroup (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

中文:
缩写 commGroup
  签名: [CommGroup β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
  定义体: DFunLike.coe_injective.commGroup (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow
-/
protected abbrev commGroup [CommGroup β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
    [IsDivApply F α β] [IsPowApply Nat F α β] [IsPowApply Int F α β] :
    CommGroup F :=
  DFunLike.coe_injective.commGroup (fun (f : F) => (f : α -> β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

end GroupInstances

end FunLike
