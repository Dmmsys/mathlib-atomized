/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists MulAction Ring

universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `semigroupWithZero` / `semigroupWithZero` 的定义

English:
abbreviation semigroupWithZero
  signature: [SemigroupWithZero β]
  body: by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 semigroupWithZero
  签名: [带零半群 β]
  定义体: by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `mulZeroClass` / `mulZeroClass` 的定义

English:
abbreviation mulZeroClass
  signature: [MulZeroClass β]
  body: by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 mulZeroClass
  签名: [乘零类 β]
  定义体: by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `mulZeroOneClass` / `mulZeroOneClass` 的定义

English:
abbreviation mulZeroOneClass
  signature: [MulZeroOneClass β]
  body: by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 mulZeroOneClass
  签名: [乘零幺类 β]
  定义体: by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _

Depends on / 依赖: add_smul, cat_disch, mul_smul, smul_add, smul_zero, zero_smul
-/
protected abbrev mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `monoidWithZero` / `monoidWithZero` 的定义

English:
abbreviation monoidWithZero
  signature: [MonoidWithZero β]
  body: by
  let _ := e.mulZeroOneClass
  let _ := e.pow Nat
  apply e.injective.monoidWithZero _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 monoidWithZero
  签名: [带零幺半群 β]
  定义体: by
  let _ := e.mulZeroOneClass
  let _ := e.pow Nat
  apply e.injective.monoidWithZero _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev monoidWithZero [MonoidWithZero β] : MonoidWithZero α := by
  let _ := e.mulZeroOneClass
  let _ := e.pow Nat
  apply e.injective.monoidWithZero _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `commMonoidWithZero` / `commMonoidWithZero` 的定义

English:
abbreviation commMonoidWithZero
  signature: [CommMonoidWithZero β]
  body: by
  let _ := e.monoidWithZero
  apply e.injective.commMonoidWithZero _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 commMonoidWithZero
  签名: [带零交换幺半群 β]
  定义体: by
  let _ := e.monoidWithZero
  apply e.injective.commMonoidWithZero _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev commMonoidWithZero [CommMonoidWithZero β] : CommMonoidWithZero α := by
  let _ := e.monoidWithZero
  apply e.injective.commMonoidWithZero _ <;> intros <;> exact e.apply_symm_apply _

end Equiv
