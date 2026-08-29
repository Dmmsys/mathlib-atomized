/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Tactic.FBinop

/-!
# Set Product Notation

This file provides notation for a product of sets, and other similar types.

## Main Definitions

* `SProd α β γ` for a binary operation `(· ×ˢ ·) : α → β → γ`.

## Notation

We introduce the notation `x ×ˢ y` for the `sprod` of any `SProd` structure. Ideally, `x × y`
notation is desirable but this notation is defined in core for `Prod` so replacing `x ×ˢ y` with
`x × y` seems difficult.
-/

public section

universe u v w

/--
Definition of `SProd` / `SProd` 的定义

English:
class SProd
  parameters: (α : Type u) (β : Type v) (γ : outParam (Type w))
  axioms and operations (1):
    - sprod : α -> β -> γ

中文:
类 SProd
  参数: (α : 类型u) (β : 类型v) (γ : outParam (Type w))
  公理与运算 (1 个):
    - sprod : α -> β -> γ
-/
class SProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The Cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
  sprod : α -> β -> γ

-- This notation binds more strongly than (pre)images, unions and intersections.
@[inherit_doc SProd.sprod] infixr:82 " ×ˢ " => SProd.sprod
macro_rules | `($x ×ˢ $y) => `(fbinop% SProd.sprod $x $y)
