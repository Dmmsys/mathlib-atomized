/-
Copyright (c) 2021 Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lutz, Oliver Nash
-/
module

public import Mathlib.Init

/-!
# Bracket Notation

This file provides notation which can be used for the Lie bracket, for the commutator of two
subgroups, and for other similar operations.

## Main Definitions

* `Bracket L M` for a binary operation that takes something in `L` and something in `M` and
  produces something in `M`.
  Defining an instance of this structure gives access to the notation `⁅ ⁆`

## Notation

We introduce the notation `⁅x, y⁆` for the `bracket` of any `Bracket` structure. Note that
these are the Unicode "square with quill" brackets rather than the usual square brackets.
-/

public section

/-- The `Bracket` class has three intended uses:
  1. for certain binary operations on structures, like the product `⁅x, y⁆` of two elements
    `x`, `y` in a Lie algebra or the commutator of two elements `x` and `y` in a group.
  2. for certain actions of one structure on another, like the action `⁅x, m⁆` of an element `x`
    of a Lie algebra on an element `m` in one of its modules (analogous to `SMul` in the
    associative setting).
  3. for binary operations on substructures, like the commutator `⁅H, K⁆` of two subgroups `H` and
     `K` of a group.
-/
/-
**Bracket** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_2 → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Bracket` class has three intended uses:
  1. for certain binary operations on structures, like the product `⁅x, y⁆` of t
wo elements
    `x`, `y` in a Lie algebra or the commutator of two elements `x` and `y` in a
 group.
  2. for certain actions of one structure on another, like the action `⁅x, m⁆` o
f an element `x`
    of a Lie algebra on an element `m` in one of its modules (analogous to `SMul
` in the
    associative setting).
  3. for binary operations on substructures, like the commutator `⁅H, K⁆` of two
 subgroups `H` and
     `K` of a group.
-/
class Bracket (L M : Type*) where
  /-- `⁅x, y⁆` is the result of a bracket operation on elements `x` and `y`.
  It is supported by the `Bracket` typeclass. -/
  bracket : L → M → M

@[inherit_doc] notation "⁅" x ", " y "⁆" => Bracket.bracket x y
