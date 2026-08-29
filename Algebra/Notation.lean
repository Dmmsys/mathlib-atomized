/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.Translate.ToAdditive

/-!
# Notations for operations involving order and algebraic structure

## Notation

* `a⁺ᵐ = a ⊔ 1`: *Positive component* of an element `a` of a multiplicative lattice ordered group
* `a⁻ᵐ = a⁻¹ ⊔ 1`: *Negative component* of an element `a` of a multiplicative lattice ordered group
* `a⁺ = a ⊔ 0`: *Positive component* of an element `a` of a lattice ordered group
* `a⁻ = (-a) ⊔ 0`: *Negative component* of an element `a` of a lattice ordered group
-/

public section

/--
Definition of `PosPart` / `PosPart` 的定义

English:
class PosPart
  parameters: (α : Type*)
  axioms and operations (1):
    - posPart : α -> α

中文:
类 PosPart
  参数: (α : 类型)
  公理与运算 (1 个):
    - posPart : α -> α
-/
class PosPart (α : Type*) where
  /-- The *positive part* of an element `a`. -/
  posPart : α -> α

/-- A notation class for the *positive part* function (multiplicative version): `a⁺ᵐ`. -/
@[to_additive]
/--
Definition of `OneLePart` / `OneLePart` 的定义

English:
class OneLePart
  parameters: (α : Type*)
  axioms and operations (1):
    - oneLePart : α -> α

中文:
类 OneLePart
  参数: (α : 类型)
  公理与运算 (1 个):
    - oneLePart : α -> α
-/
class OneLePart (α : Type*) where
  /-- The *positive part* of an element `a`. -/
  oneLePart : α -> α

/--
Definition of `NegPart` / `NegPart` 的定义

English:
class NegPart
  parameters: (α : Type*)
  axioms and operations (1):
    - negPart : α -> α

中文:
类 NegPart
  参数: (α : 类型)
  公理与运算 (1 个):
    - negPart : α -> α
-/
class NegPart (α : Type*) where
  /-- The *negative part* of an element `a`. -/
  negPart : α -> α

/-- A notation class for the *negative part* function (multiplicative version): `a⁻ᵐ`. -/
@[to_additive]
/--
Definition of `LeOnePart` / `LeOnePart` 的定义

English:
class LeOnePart
  parameters: (α : Type*)
  axioms and operations (1):
    - leOnePart : α -> α

中文:
类 LeOnePart
  参数: (α : 类型)
  公理与运算 (1 个):
    - leOnePart : α -> α
-/
class LeOnePart (α : Type*) where
  /-- The *negative part* of an element `a`. -/
  leOnePart : α -> α

export OneLePart (oneLePart)
export LeOnePart (leOnePart)
export PosPart (posPart)
export NegPart (negPart)

@[inherit_doc] postfix:max "⁺ᵐ" => OneLePart.oneLePart
@[inherit_doc] postfix:max "⁻ᵐ" => LeOnePart.leOnePart
@[inherit_doc] postfix:max "⁺" => PosPart.posPart
@[inherit_doc] postfix:max "⁻" => NegPart.negPart
