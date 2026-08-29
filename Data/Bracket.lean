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

/--
Definition of `Bracket` / `Bracket` 的定义

English:
class Bracket
  parameters: (L M : Type*)
  axioms and operations (1):
    - bracket : L -> M -> M

中文:
类 Bracket
  参数: (L M : 类型)
  公理与运算 (1 个):
    - bracket : L -> M -> M
-/
class Bracket (L M : Type*) where
  /-- `⁅x, y⁆` is the result of a bracket operation on elements `x` and `y`.
  It is supported by the `Bracket` typeclass. -/
  bracket : L -> M -> M

@[inherit_doc] notation "⁅" x ", " y "⁆" => Bracket.bracket x y
