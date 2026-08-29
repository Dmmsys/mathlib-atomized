/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Data.Nat.Cast.Defs

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into an
additive group with a one (typically a `Ring`). In additive groups with a one
element, there exists a unique such homomorphism and we store it in the
`intCast : ℤ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `Int.cast`: Canonical homomorphism `ℤ → R`.
* `AddGroupWithOne`: Type class for `Int.cast`.
-/

@[expose] public section


universe u

/--
Definition of `Int.castDef` / `Int.castDef` 的定义

English:
definition Int.castDef
  signature: {R : Type u} [NatCast R] [Neg R]

中文:
定义 Int.castDef
  签名: {R : 类型u} [自然数Cast R] [Neg R]
-/
protected def Int.castDef {R : Type u} [NatCast R] [Neg R] : Int -> R
  | (n : Nat) => n
  | Int.negSucc n => -(n + 1 : Nat)

/-! ### Additive groups with one -/

/--
Definition of `AddGroupWithOne` / `AddGroupWithOne` 的定义

English:
class AddGroupWithOne
  parameters: (R : Type u)
  extends: IntCast R, AddMonoidWithOne R, AddGroup R
  axioms and operations (3):
    - intCast : = Int.castDef
    - intCast_ofNat : forall n : Nat, intCast (n : Nat) = Nat.cast n  [default: by intros; rfl]
    - intCast_negSucc : forall n : Nat, intCast (Int.negSucc n) = -Nat.cast (n + 1)  [default: by intros; rfl]

中文:
类 AddGroupWithOne
  参数: (R : 类型u)
  继承: IntCast R, AddMonoidWithOne R, AddGroup R
  公理与运算 (3 个):
    - intCast : = 整数.castDef
    - intCast_ofNat : 对任意 n : 自然数, intCast (n : 自然数) = 自然数.cast n  [默认: by intros; rfl]
    - intCast_negSucc : 对任意 n : 自然数, intCast (整数.negSucc n) = -自然数.cast (n + 1)  [默认: by intros; rfl]

Depends on / 依赖: Int.castDef, castDef
-/
class AddGroupWithOne (R : Type u) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  /-- The canonical homomorphism `ℤ → R`. -/
  intCast := Int.castDef
  /-- The canonical homomorphism `ℤ → R` agrees with the one from `ℕ → R` on `ℕ`. -/
  intCast_ofNat : forall n : Nat, intCast (n : Nat) = Nat.cast n := by intros; rfl
  /-- The canonical homomorphism `ℤ → R` for negative values is just the negation of the values
  of the canonical homomorphism `ℕ → R`. -/
  intCast_negSucc : forall n : Nat, intCast (Int.negSucc n) = -Nat.cast (n + 1) := by intros; rfl

/--
Definition of `AddCommGroupWithOne` / `AddCommGroupWithOne` 的定义

English:
class AddCommGroupWithOne
  parameters: (R : Type u)
  extends: AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R
  (no additional axioms)

中文:
类 AddCommGroupWithOne
  参数: (R : 类型u)
  继承: AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R
  (无附加公理)
-/
class AddCommGroupWithOne (R : Type u)
  extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R
