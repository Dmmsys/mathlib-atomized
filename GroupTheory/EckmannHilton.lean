/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Eckmann-Hilton argument

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `EckmannHilton.commMonoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `EckmannHilton.commGroup`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/

public section

universe u

namespace EckmannHilton

variable {X : Type u}

/-- Local notation for `m a b`. -/
local notation a " <" m:51 "> " b => m a b

/--
Definition of `IsUnital` / `IsUnital` 的定义

English:
structure IsUnital
  parameters: (m : X -> X -> X) (e : X)
  extends: Std.LawfulIdentity m e
  (no additional axioms)

中文:
结构 是Unital
  参数: (m : X -> X -> X) (e : X)
  继承: Std.LawfulIdentity m e
  (无附加公理)
-/
structure IsUnital (m : X -> X -> X) (e : X) : Prop extends Std.LawfulIdentity m e

@[to_additive EckmannHilton.AddZeroClass.IsUnital]
/--
theorem `MulOneClass.isUnital` / 定理 `MulOneClass.isUnital`

English:
theorem MulOneClass.isUnital
  given: [_G : MulOneClass X]
  statement: IsUnital (· * ·) (1 : X)
  proof: IsUnital.mk { left_id := MulOneClass.one_mul,
                right_id := MulOneClass.mul_one }

中文:
定理 MulOne类.isUnital
  条件: [_G : MulOne类 X]
  结论: 是Unital (· * ·) (1 : X)
  证明: IsUnital.mk { left_id := MulOneClass.one_mul,
                right_id := MulOneClass.mul_one }

Depends on / 依赖: IsUnital, IsUnital.mk, MulOneClass, MulOneClass.mul_one, MulOneClass.one_mul, left_id, mul_one, one_mul, right_id
-/
theorem MulOneClass.isUnital [_G : MulOneClass X] : IsUnital (· * ·) (1 : X) :=
  IsUnital.mk { left_id := MulOneClass.one_mul,
                right_id := MulOneClass.mul_one }

variable {m₁ m₂ : X -> X -> X} {e₁ e₂ : X}
variable (h₁ : IsUnital m₁ e₁) (h₂ : IsUnital m₂ e₂)
variable (distrib : forall a b c d, ((a <m₂> b) <m₁> c <m₂> d) = (a <m₁> c) <m₂> b <m₁> d)

include h₁ h₂ distrib

/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: e₁ = e₂
  proof: by
  simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using distrib e₂ e₁ e₁ e₂

中文:
定理 one
  结论: e₁ = e₂
  证明: by
  simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using distrib e₂ e₁ e₁ e₂

Depends on / 依赖: distrib, left_id, right_id
-/
theorem one : e₁ = e₂ := by
  simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using distrib e₂ e₁ e₁ e₂

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: m₁ = m₂
  proof: by
  funext a b
  calc
    m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      { simp only [one h₁ h₂ distrib, h₂.left_id, h₂.right_id] }
    _ = m₂ a b := by simp only [distrib, h₁.left_id, h₁.right_id]

中文:
定理 mul
  结论: m₁ = m₂
  证明: by
  funext a b
  calc
    m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      { simp only [one h₁ h₂ distrib, h₂.left_id, h₂.right_id] }
    _ = m₂ a b := by simp only [distrib, h₁.left_id, h₁.right_id]

Depends on / 依赖: distrib, left_id, right_id
-/
theorem mul : m₁ = m₂ := by
  funext a b
  calc
    m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      { simp only [one h₁ h₂ distrib, h₂.left_id, h₂.right_id] }
    _ = m₂ a b := by simp only [distrib, h₁.left_id, h₁.right_id]

/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  statement: Std.Commutative m₂
  proof: ⟨fun a b => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib e₂ a b e₂⟩

中文:
定理 mul_comm
  结论: Std.交换 m₂
  证明: ⟨fun a b => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib e₂ a b e₂⟩

Depends on / 依赖: distrib, left_id, right_id
-/
theorem mul_comm : Std.Commutative m₂ :=
  ⟨fun a b => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib e₂ a b e₂⟩

/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  statement: Std.Associative m₂
  proof: ⟨fun a b c => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib a b e₂ c⟩

中文:
定理 mul_assoc
  结论: Std.结合 m₂
  证明: ⟨fun a b c => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib a b e₂ c⟩

Depends on / 依赖: distrib, left_id, right_id
-/
theorem mul_assoc : Std.Associative m₂ :=
  ⟨fun a b c => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib a b e₂ c⟩

/-- If a type carries a unital magma structure that distributes over a unital binary
operation, then the magma structure is a commutative monoid. -/
@[to_additive
      /-- If a type carries a unital additive magma structure that distributes over a unital binary
      operation, then the additive magma structure is a commutative additive monoid. -/]
/--
Definition of `commMonoid` / `commMonoid` 的定义

English:
abbreviation commMonoid
  signature: [h : MulOneClass X]
  body: { h with
      mul_comm := (mul_comm h₁ MulOneClass.isUnital distrib).comm,
      mul_assoc := (mul_assoc h₁ MulOneClass.isUnital distrib).assoc }

中文:
缩写 commMonoid
  签名: [h : MulOne类 X]
  定义体: { h with
      mul_comm := (mul_comm h₁ MulOneClass.isUnital distrib).comm,
      mul_assoc := (mul_assoc h₁ MulOneClass.isUnital distrib).assoc }

Depends on / 依赖: MulOneClass, MulOneClass.isUnital, distrib, isUnital, mul_assoc, mul_comm
-/
abbrev commMonoid [h : MulOneClass X]
    (distrib : forall a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d) : CommMonoid X :=
  { h with
      mul_comm := (mul_comm h₁ MulOneClass.isUnital distrib).comm,
      mul_assoc := (mul_assoc h₁ MulOneClass.isUnital distrib).assoc }

/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
@[to_additive
      /-- If a type carries an additive group structure that distributes over a unital binary
      operation, then the additive group is commutative. -/]
/--
Definition of `commGroup` / `commGroup` 的定义

English:
abbreviation commGroup
  signature: [G : Group X]
  body: { G, EckmannHilton.commMonoid h₁ distrib with .. }

中文:
缩写 commGroup
  签名: [G : 群 X]
  定义体: { G, EckmannHilton.commMonoid h₁ distrib with .. }

Depends on / 依赖: EckmannHilton, EckmannHilton.commMonoid, commMonoid, distrib
-/
abbrev commGroup [G : Group X]
    (distrib : forall a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d) : CommGroup X :=
  { G, EckmannHilton.commMonoid h₁ distrib with .. }

end EckmannHilton
