/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Squares and even elements

This file defines the subgroup of squares / even elements in an abelian group.
-/

@[expose] public section

assert_not_exists RelIso MonoidWithZero

namespace Subsemigroup
variable {S : Type*} [CommSemigroup S]

variable (S) in
/--
In a commutative semigroup `S`, `Subsemigroup.square S` is the subsemigroup of squares in `S`.
-/
@[to_additive
/-- In a commutative additive semigroup `S`, `AddSubsemigroup.even S`
is the subsemigroup of even elements in `S`. -/]
/--
Definition of `square` / `square` 的定义

English:
definition square
  signature: : Subsemigroup S where
  body: {s : S | IsSquare s}
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]

中文:
定义 square
  签名: : Subsemigroup S where
  定义体: {s : S | IsSquare s}
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]

Depends on / 依赖: IsSquare
-/
def square : Subsemigroup S where
  carrier := {s : S | IsSquare s}
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]
/--
theorem `mem_square` / 定理 `mem_square`

English:
theorem mem_square
  given: {a : S}
  statement: a in square S ↔ IsSquare a
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_square
  条件: {a : S}
  结论: a in square S ↔ IsSquare a
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_square {a : S} : a in square S ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_square` / 定理 `coe_square`

English:
theorem coe_square
  statement: square S = {s : S | IsSquare s}
  proof: rfl

中文:
定理 coe_square
  结论: square S = {s : S | IsSquare s}
  证明: rfl
-/
theorem coe_square : square S = {s : S | IsSquare s} := rfl

end Subsemigroup

namespace Submonoid
variable {M : Type*} [CommMonoid M]

variable (M) in
/--
In a commutative monoid `M`, `Submonoid.square M` is the submonoid of squares in `M`.
-/
@[to_additive
/-- In a commutative additive monoid `M`, `AddSubmonoid.even M`
is the submonoid of even elements in `M`. -/]
/--
Definition of `square` / `square` 的定义

English:
definition square
  signature: : Submonoid M where
  body: Subsemigroup.square M
  one_mem' := IsSquare.one

@[to_additive (attr := simp)]

中文:
定义 square
  签名: : Submonoid M where
  定义体: Subsemigroup.square M
  one_mem' := IsSquare.one

@[to_additive (attr := simp)]

Depends on / 依赖: Subsemigroup, Subsemigroup.square, square
-/
def square : Submonoid M where
  __ := Subsemigroup.square M
  one_mem' := IsSquare.one

@[to_additive (attr := simp)]
/--
theorem `square_toSubsemigroup` / 定理 `square_toSubsemigroup`

English:
theorem square_toSubsemigroup
  statement: (square M).toSubsemigroup = .square M
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 square_toSubsemigroup
  结论: (square M).toSubsemigroup = .square M
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem square_toSubsemigroup : (square M).toSubsemigroup = .square M := rfl

@[to_additive (attr := simp)]
/--
theorem `mem_square` / 定理 `mem_square`

English:
theorem mem_square
  given: {a : M}
  statement: a in square M ↔ IsSquare a
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_square
  条件: {a : M}
  结论: a in square M ↔ IsSquare a
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_square {a : M} : a in square M ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_square` / 定理 `coe_square`

English:
theorem coe_square
  statement: square M = {s : M | IsSquare s}
  proof: rfl

中文:
定理 coe_square
  结论: square M = {s : M | IsSquare s}
  证明: rfl
-/
theorem coe_square : square M = {s : M | IsSquare s} := rfl

end Submonoid

namespace Subgroup
variable {G : Type*} [CommGroup G]

variable (G) in
/--
In an abelian group `G`, `Subgroup.square G` is the subgroup of squares in `G`.
-/
@[to_additive
/-- In an abelian additive group `G`, `AddSubgroup.even G` is
the subgroup of even elements in `G`. -/]
/--
Definition of `square` / `square` 的定义

English:
definition square
  signature: : Subgroup G where
  body: Submonoid.square G
  inv_mem' := IsSquare.inv

@[to_additive (attr := simp)]

中文:
定义 square
  签名: : Subgroup G where
  定义体: Submonoid.square G
  inv_mem' := IsSquare.inv

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.square, square
-/
def square : Subgroup G where
  __ := Submonoid.square G
  inv_mem' := IsSquare.inv

@[to_additive (attr := simp)]
/--
theorem `square_toSubmonoid` / 定理 `square_toSubmonoid`

English:
theorem square_toSubmonoid
  statement: (square G).toSubmonoid = .square G
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 square_toSubmonoid
  结论: (square G).toSubmonoid = .square G
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem square_toSubmonoid : (square G).toSubmonoid = .square G := rfl

@[to_additive (attr := simp)]
/--
theorem `mem_square` / 定理 `mem_square`

English:
theorem mem_square
  given: {a : G}
  statement: a in square G ↔ IsSquare a
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_square
  条件: {a : G}
  结论: a in square G ↔ IsSquare a
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_le, AddSubmonoid.subset_closure, AddSubmonoid.toSubmonoid, Additive, Iff.rfl, Submonoid, Submonoid.closure_le, Submonoid.subset_closure, closure_le, le_antisymm, le_symm_apply, subset_closure, toSubmonoid
-/
theorem mem_square {a : G} : a in square G ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_square` / 定理 `coe_square`

English:
theorem coe_square
  statement: square G = {s : G | IsSquare s}
  proof: rfl

中文:
定理 coe_square
  结论: square G = {s : G | IsSquare s}
  证明: rfl
-/
theorem coe_square : square G = {s : G | IsSquare s} := rfl

end Subgroup
