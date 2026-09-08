/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Notation.Defs

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements, along with their `to_additive`
analogues add-left-regular, add-right-regular and add-regular elements.

For monoids where _every_ element is regular, see `IsCancelMul` and nearby typeclasses.
-/

@[expose] public section

variable {R : Type*} [Mul R]

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective. -/
@[to_additive (attr := instance_reducible)
  /-- An add-left-regular element is an element `c` such that addition
    on the left by `c` is injective. -/]
/-
**IsLeftRegular** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLeftRegular (c : R)
参数：c : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLeftRegular (c : R) :=
  (c * ·).Injective

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive (attr := instance_reducible)
  /-- An add-right-regular element is an element `c` such that addition
    on the right by `c` is injective. -/]
/-
**IsRightRegular** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsRightRegular (c : R)
参数：c : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsRightRegular (c : R) :=
  (· * c).Injective

/-- An add-regular element is an element `c` such that addition by `c` both on the left and
on the right is injective. -/
/-
**IsAddRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_2} → [Add R] → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An add-regular element is an element `c` such that addition by `c` both on the l
eft and
on the right is injective.
-/
structure IsAddRegular {R : Type*} [Add R] (c : R) : Prop where
  /-- An add-regular element `c` is left-regular -/
  left : IsAddLeftRegular c
  /-- An add-regular element `c` is right-regular -/
  right : IsAddRightRegular c

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
/-
**IsRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Mul R] → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular element is an element `c` such that multiplication by `c` both on the 
left and
on the right is injective.
-/
structure IsRegular (c : R) : Prop where
  /-- A regular element `c` is left-regular -/
  left : IsLeftRegular c
  /-- A regular element `c` is right-regular -/
  right : IsRightRegular c

attribute [simp] IsRegular.left IsRegular.right

attribute [to_additive] IsRegular

@[to_additive]
/-
**isRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
