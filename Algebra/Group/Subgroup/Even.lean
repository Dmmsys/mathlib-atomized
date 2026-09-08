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
/-
**Subsemigroup.square** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：square : Subsemigroup S where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsSquare.mul`：IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a -> I
sSquare b -> IsSquare (a * b)
-/
def square : Subsemigroup S where
  carrier := {s : S | IsSquare s}
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_square** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_square {a : S} : a in square S ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_square {a : S} : a ∈ square S ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Subsemigroup.coe_square** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_square : square S = {s : S | IsSquare s}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Submonoid.square** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：square : Submonoid M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def square : Submonoid M where
  __ := Subsemigroup.square M
  one_mem' := IsSquare.one

@[to_additive (attr := simp)]
/-
**Submonoid.square_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：square_toSubsemigroup : (square M).toSubsemigroup = .square M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem square_toSubsemigroup : (square M).toSubsemigroup = .square M := rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mem_square** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_square {a : M} : a in square M ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_square {a : M} : a ∈ square M ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_square** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_square : square M = {s : M | IsSquare s}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Subgroup.square** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：square : Subgroup G where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def square : Subgroup G where
  __ := Submonoid.square G
  inv_mem' := IsSquare.inv

@[to_additive (attr := simp)]
/-
**Subgroup.square_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：square_toSubmonoid : (square G).toSubmonoid = .square G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem square_toSubmonoid : (square G).toSubmonoid = .square G := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mem_square** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_square {a : G} : a in square G ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_square {a : G} : a ∈ square G ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.coe_square** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_square : square G = {s : G | IsSquare s}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_square : square G = {s : G | IsSquare s} := rfl

end Subgroup

