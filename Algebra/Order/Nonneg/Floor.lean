/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Nonneg.Basic

/-!
# Nonnegative elements are archimedean

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `FloorSemiring` if `α` is.
-/

public section

assert_not_exists Finset Field

namespace Nonneg

variable {α : Type*}

/-
**Nonneg.floorSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：floorSemiring [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiri
ng α] : FloorSemiring { r : α // 0 <= r } where floor a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
instance floorSemiring [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α] :
    FloorSemiring { r : α // 0 ≤ r } where
  floor a := ⌊(a : α)⌋₊
  ceil a := ⌈(a : α)⌉₊
  floor_of_neg ha := FloorSemiring.floor_of_neg ha
  gc_floor ha := FloorSemiring.gc_floor (Subtype.coe_le_coe.2 ha)
  gc_ceil a n := FloorSemiring.gc_ceil (a : α) n

@[norm_cast]
/-
**Nonneg.nat_floor_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：nat_floor_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiri
ng α] (a : { r : α // 0 <= r }) : ⌊(a : α)⌋₊ = ⌊a⌋₊
参数：a : { r : α // 0 <= r }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nat_floor_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α]
    (a : { r : α // 0 ≤ r }) :
    ⌊(a : α)⌋₊ = ⌊a⌋₊ :=
  rfl

@[norm_cast]
/-
**Nonneg.nat_ceil_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：nat_ceil_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemirin
g α] (a : { r : α // 0 <= r }) : ⌈(a : α)⌉₊ = ⌈a⌉₊
参数：a : { r : α // 0 <= r }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nat_ceil_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α]
    (a : { r : α // 0 ≤ r }) :
    ⌈(a : α)⌉₊ = ⌈a⌉₊ :=
  rfl

end Nonneg

