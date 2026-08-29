/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists Module

namespace Equiv
variable {α β : Type*} (e : α ≃ β)

-- See note [instance transfer via equivalence]
/--
Definition of `nnratCast` / `nnratCast` 的定义

English:
abbreviation nnratCast
  signature: [NNRatCast β]
  body: e.invFun q

中文:
缩写 nnratCast
  签名: [NNRatCast β]
  定义体: e.invFun q
-/
protected abbrev nnratCast [NNRatCast β] : NNRatCast α where nnratCast q := e.invFun q

/--
Definition of `ratCast` / `ratCast` 的定义

English:
abbreviation ratCast
  signature: [RatCast β]
  body: e.invFun n

中文:
缩写 ratCast
  签名: [RatCast β]
  定义体: e.invFun n
-/
protected abbrev ratCast [RatCast β] : RatCast α where ratCast n := e.invFun n

/--
Definition of `divisionRing` / `divisionRing` 的定义

English:
abbreviation divisionRing
  signature: [DivisionRing β]
  body: by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow Nat
  let zpow := e.pow Int
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul Rat>=0
  let qsmul := e.smul Rat
  apply e.injective.divisionRin

中文:
缩写 divisionRing
  签名: [DivisionRing β]
  定义体: by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow Nat
  let zpow := e.pow Int
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul Rat>=0
  let qsmul := e.smul Rat
  apply e.injective.divisionRin
-/
protected abbrev divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow Nat
  let zpow := e.pow Int
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul Rat>=0
  let qsmul := e.smul Rat
  apply e.injective.divisionRing _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `field` / `field` 的定义

English:
abbreviation field
  signature: [Field β]
  body: by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow Nat
  let zpow := e.pow Int
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul Rat>=0
  let qsmul := e.smul Rat
  apply e.in

中文:
缩写 field
  签名: [Field β]
  定义体: by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow Nat
  let zpow := e.pow Int
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul Rat>=0
  let qsmul := e.smul Rat
  apply e.in
-/
protected abbrev field [Field β] : Field α := by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow Nat
  let zpow := e.pow Int
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul Rat>=0
  let qsmul := e.smul Rat
  apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _

end Equiv
