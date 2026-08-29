/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson, Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Tactic.Common
public import Batteries.Tactic.SeqFocus

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(Comm)` `Monoid`s.

## Main definitions

* `semigroupDvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/

@[expose] public section


variable {α : Type*}

section Semigroup

variable [Semigroup α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `CommMonoid`.
This matches the convention for ordinals. -/
instance (priority := 100) semigroupDvd : Dvd α :=
  Dvd.mk fun a b => exists c, b = a * c

-- TODO: this used to not have `c` explicit, but that seems to be important
-- for use with tactics, similar to `Exists.intro`
/--
theorem `Dvd.intro` / 定理 `Dvd.intro`

English:
theorem Dvd.intro
  given: (c : α) (h : a * c = b)
  statement: a ∣ b
  proof: Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro

中文:
定理 Dvd.intro
  条件: (c : α) (h : a * c = b)
  结论: a ∣ b
  证明: Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro

Depends on / 依赖: Exists, Exists.intro, h.symm
-/
theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
  Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro

/--
theorem `exists_eq_mul_right_of_dvd` / 定理 `exists_eq_mul_right_of_dvd`

English:
theorem exists_eq_mul_right_of_dvd
  given: (h : a ∣ b)
  statement: exists c, b = a * c
  proof: h

中文:
定理 存在_eq_mul_right_of_dvd
  条件: (h : a ∣ b)
  结论: 存在 c, b = a * c
  证明: h
-/
theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : exists c, b = a * c :=
  h

/--
theorem `dvd_def` / 定理 `dvd_def`

English:
theorem dvd_def
  statement: a ∣ b ↔ exists c, b = a * c
  proof: Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

中文:
定理 dvd_def
  结论: a ∣ b ↔ 存在 c, b = a * c
  证明: Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

Depends on / 依赖: Iff.rfl
-/
theorem dvd_def : a ∣ b ↔ exists c, b = a * c :=
  Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

/--
theorem `Dvd.elim` / 定理 `Dvd.elim`

English:
theorem Dvd.elim
  given: {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b = a * c -> P)
  statement: P
  proof: Exists.elim H₁ H₂

中文:
定理 Dvd.elim
  条件: {P : 命题} {a b : α} (H₁ : a ∣ b) (H₂ : 对任意 c, b = a * c -> P)
  结论: P
  证明: Exists.elim H₁ H₂

Depends on / 依赖: Exists, Exists.elim
-/
theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b = a * c -> P) : P :=
  Exists.elim H₁ H₂

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[trans]
/--
theorem `dvd_trans` / 定理 `dvd_trans`

English:
theorem dvd_trans
  statement: a ∣ b -> b ∣ c -> a ∣ c
  proof: dvd_trans

中文:
定理 dvd_trans
  结论: a ∣ b -> b ∣ c -> a ∣ c
  证明: dvd_trans

Depends on / 依赖: dvd_trans
-/
theorem dvd_trans : a ∣ b -> b ∣ c -> a ∣ c
| ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans mul_assoc a d e⟩

alias Dvd.dvd.trans := dvd_trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans α Dvd.dvd
  body: ⟨fun _ _ _ => dvd_trans⟩

@[simp]

中文:
实例 :
  签名: 是Trans α Dvd.dvd
  定义体: ⟨fun _ _ _ => dvd_trans⟩

@[simp]

Depends on / 依赖: dvd_trans
-/
instance : IsTrans α Dvd.dvd :=
  ⟨fun _ _ _ => dvd_trans⟩

@[simp]
/--
theorem `dvd_mul_right` / 定理 `dvd_mul_right`

English:
theorem dvd_mul_right
  given: (a b : α)
  statement: a ∣ a * b
  proof: Dvd.intro b rfl

中文:
定理 dvd_mul_right
  条件: (a b : α)
  结论: a ∣ a * b
  证明: Dvd.intro b rfl

Depends on / 依赖: Dvd.intro
-/
theorem dvd_mul_right (a b : α) : a ∣ a * b :=
  Dvd.intro b rfl

/--
theorem `dvd_mul_of_dvd_left` / 定理 `dvd_mul_of_dvd_left`

English:
theorem dvd_mul_of_dvd_left
  given: (h : a ∣ b) (c : α)
  statement: a ∣ b * c
  proof: h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

中文:
定理 dvd_mul_of_dvd_left
  条件: (h : a ∣ b) (c : α)
  结论: a ∣ b * c
  证明: h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

Depends on / 依赖: dvd_mul_right, h.trans
-/
theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
  h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

/--
theorem `dvd_of_mul_right_dvd` / 定理 `dvd_of_mul_right_dvd`

English:
theorem dvd_of_mul_right_dvd
  given: (h : a * b ∣ c)
  statement: a ∣ c
  proof: (dvd_mul_right a b).trans h

中文:
定理 dvd_of_mul_right_dvd
  条件: (h : a * b ∣ c)
  结论: a ∣ c
  证明: (dvd_mul_right a b).trans h

Depends on / 依赖: dvd_mul_right
-/
theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
  (dvd_mul_right a b).trans h

/--
Definition of `IsPrimal` / `IsPrimal` 的定义

English:
definition IsPrimal
  signature: (a : α)
  body: forall ⦃b c⦄, a ∣ b * c -> exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂

中文:
定义 IsPrimal
  签名: (a : α)
  定义体: forall ⦃b c⦄, a ∣ b * c -> exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂
-/
def IsPrimal (a : α) : Prop := forall ⦃b c⦄, a ∣ b * c -> exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂

variable (α) in
/--
Definition of `DecompositionMonoid` / `DecompositionMonoid` 的定义

English:
class DecompositionMonoid
  parameters: : Prop where
  axioms and operations (1):
    - primal((a : α)) : IsPrimal a

中文:
类 分解幺半群
  参数: : 命题 where
  公理与运算 (1 个):
    - primal((a : α)) : IsPrimal a
-/
@[mk_iff] class DecompositionMonoid : Prop where
  primal (a : α) : IsPrimal a

/--
theorem `exists_dvd_and_dvd_of_dvd_mul` / 定理 `exists_dvd_and_dvd_of_dvd_mul`

English:
theorem exists_dvd_and_dvd_of_dvd_mul
  given: [DecompositionMonoid α] {b c a : α} (H : a ∣ b * c)
  proof: DecompositionMonoid.primal a H

@[gcongr]

中文:
定理 存在_dvd_and_dvd_of_dvd_mul
  条件: [分解幺半群 α] {b c a : α} (H : a ∣ b * c)
  证明: DecompositionMonoid.primal a H

@[gcongr]

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, primal
-/
theorem exists_dvd_and_dvd_of_dvd_mul [DecompositionMonoid α] {b c a : α} (H : a ∣ b * c) :
    exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂ := DecompositionMonoid.primal a H

@[gcongr]
/--
theorem `mul_dvd_mul_left` / 定理 `mul_dvd_mul_left`

English:
theorem mul_dvd_mul_left
  given: (a : α) (h : b ∣ c)
  statement: a * b ∣ a * c
  proof: by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

中文:
定理 mul_dvd_mul_left
  条件: (a : α) (h : b ∣ c)
  结论: a * b ∣ a * c
  证明: by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

/--
theorem `IsLeftRegular.dvd_cancel_left` / 定理 `IsLeftRegular.dvd_cancel_left`

English:
theorem IsLeftRegular.dvd_cancel_left
  given: (h : IsLeftRegular a)
  statement: a * b ∣ a * c ↔ b ∣ c
  proof: ⟨fun dvd => have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

中文:
定理 IsLeftRegular.dvd_cancel_left
  条件: (h : IsLeftRegular a)
  结论: a * b ∣ a * c ↔ b ∣ c
  证明: ⟨fun dvd => have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

Depends on / 依赖: eq.trans, mul_assoc, mul_dvd_mul_left
-/
theorem IsLeftRegular.dvd_cancel_left (h : IsLeftRegular a) : a * b ∣ a * c ↔ b ∣ c :=
  ⟨fun dvd => have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

/--
Definition of `RightDvd` / `RightDvd` 的定义

English:
definition RightDvd
  signature: (a b : α)
  body: exists c, b = c * a

@[inherit_doc]
infix:50 " ∣ᵣ " => RightDvd

@[trans]

中文:
定义 RightDvd
  签名: (a b : α)
  定义体: exists c, b = c * a

@[inherit_doc]
infix:50 " ∣ᵣ " => RightDvd

@[trans]
-/
def RightDvd (a b : α) : Prop := exists c, b = c * a

@[inherit_doc]
infix:50 " ∣ᵣ " => RightDvd

@[trans]
/--
theorem `RightDvd.trans` / 定理 `RightDvd.trans`

English:
theorem RightDvd.trans
  statement: a ∣ᵣ b -> b ∣ᵣ c -> a ∣ᵣ c

中文:
定理 RightDvd.trans
  结论: a ∣ᵣ b -> b ∣ᵣ c -> a ∣ᵣ c
-/
protected theorem RightDvd.trans : a ∣ᵣ b -> b ∣ᵣ c -> a ∣ᵣ c
| ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨e * d, h₁ ▸ h₂.trans (mul_assoc e d a).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans α RightDvd
  body: ⟨fun _ _ _ => RightDvd.trans⟩

@[simp]

中文:
实例 :
  签名: 是Trans α RightDvd
  定义体: ⟨fun _ _ _ => RightDvd.trans⟩

@[simp]

Depends on / 依赖: RightDvd, RightDvd.trans
-/
instance : IsTrans α RightDvd :=
  ⟨fun _ _ _ => RightDvd.trans⟩

@[simp]
/--
theorem `RightDvd.mul_self` / 定理 `RightDvd.mul_self`

English:
theorem RightDvd.mul_self
  given: (a b : α)
  statement: a ∣ᵣ b * a
  proof: ⟨b, rfl⟩

中文:
定理 RightDvd.mul_self
  条件: (a b : α)
  结论: a ∣ᵣ b * a
  证明: ⟨b, rfl⟩
-/
theorem RightDvd.mul_self (a b : α) : a ∣ᵣ b * a :=
  ⟨b, rfl⟩

/--
theorem `RightDvd.mul_left` / 定理 `RightDvd.mul_left`

English:
theorem RightDvd.mul_left
  given: (h : a ∣ᵣ b) (c : α)
  statement: a ∣ᵣ c * b
  proof: h.trans (RightDvd.mul_self b c)

中文:
定理 RightDvd.mul_left
  条件: (h : a ∣ᵣ b) (c : α)
  结论: a ∣ᵣ c * b
  证明: h.trans (RightDvd.mul_self b c)

Depends on / 依赖: RightDvd, RightDvd.mul_self, h.trans, mul_self
-/
theorem RightDvd.mul_left (h : a ∣ᵣ b) (c : α) : a ∣ᵣ c * b :=
  h.trans (RightDvd.mul_self b c)

/--
theorem `RightDvd.of_mul_left` / 定理 `RightDvd.of_mul_left`

English:
theorem RightDvd.of_mul_left
  given: (h : b * a ∣ᵣ c)
  statement: a ∣ᵣ c
  proof: (RightDvd.mul_self a b).trans h

@[gcongr]

中文:
定理 RightDvd.of_mul_left
  条件: (h : b * a ∣ᵣ c)
  结论: a ∣ᵣ c
  证明: (RightDvd.mul_self a b).trans h

@[gcongr]

Depends on / 依赖: RightDvd, RightDvd.mul_self, mul_self
-/
theorem RightDvd.of_mul_left (h : b * a ∣ᵣ c) : a ∣ᵣ c :=
  (RightDvd.mul_self a b).trans h

@[gcongr]
/--
theorem `RightDvd.mul_const` / 定理 `RightDvd.mul_const`

English:
theorem RightDvd.mul_const
  given: (a : α) (h : b ∣ᵣ c)
  statement: b * a ∣ᵣ c * a
  proof: by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

中文:
定理 RightDvd.mul_const
  条件: (a : α) (h : b ∣ᵣ c)
  结论: b * a ∣ᵣ c * a
  证明: by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem RightDvd.mul_const (a : α) (h : b ∣ᵣ c) : b * a ∣ᵣ c * a := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

/--
theorem `IsRightRegular.rightDvd_cancel_right` / 定理 `IsRightRegular.rightDvd_cancel_right`

English:
theorem IsRightRegular.rightDvd_cancel_right
  given: (h : IsRightRegular a)
  proof: ⟨fun dvd => have ⟨d, eq⟩ := dvd
    ⟨d, h (eq.trans <| (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

中文:
定理 IsRightRegular.rightDvd_cancel_right
  条件: (h : IsRightRegular a)
  证明: ⟨fun dvd => have ⟨d, eq⟩ := dvd
    ⟨d, h (eq.trans <| (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

Depends on / 依赖: RightDvd, RightDvd.mul_const, eq.trans, mul_assoc, mul_const
-/
theorem IsRightRegular.rightDvd_cancel_right (h : IsRightRegular a) :
    b * a ∣ᵣ c * a ↔ b ∣ᵣ c :=
  ⟨fun dvd => have ⟨d, eq⟩ := dvd
    ⟨d, h (eq.trans <| (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

/--
theorem `rightDvd_iff_op_dvd_op` / 定理 `rightDvd_iff_op_dvd_op`

English:
theorem rightDvd_iff_op_dvd_op
  statement: a ∣ᵣ b ↔ MulOpposite.op a ∣ MulOpposite.op b
  proof: ⟨fun ⟨c, hc⟩ => ⟨MulOpposite.op c, by simp [hc]⟩,
   fun ⟨c, hc⟩ => ⟨MulOpposite.unop c, by simpa using congrArg MulOpposite.unop hc⟩⟩

中文:
定理 rightDvd_iff_op_dvd_op
  结论: a ∣ᵣ b ↔ MulOpposite.op a ∣ MulOpposite.op b
  证明: ⟨fun ⟨c, hc⟩ => ⟨MulOpposite.op c, by simp [hc]⟩,
   fun ⟨c, hc⟩ => ⟨MulOpposite.unop c, by simpa using congrArg MulOpposite.unop hc⟩⟩

Depends on / 依赖: MulOpposite, MulOpposite.op, MulOpposite.unop
-/
theorem rightDvd_iff_op_dvd_op : a ∣ᵣ b ↔ MulOpposite.op a ∣ MulOpposite.op b :=
  ⟨fun ⟨c, hc⟩ => ⟨MulOpposite.op c, by simp [hc]⟩,
   fun ⟨c, hc⟩ => ⟨MulOpposite.unop c, by simpa using congrArg MulOpposite.unop hc⟩⟩

end Semigroup

section RightCancelSemigroup

variable [RightCancelSemigroup α] {a b c : α}

@[simp]
/--
theorem `mul_rightDvd_mul_iff_left` / 定理 `mul_rightDvd_mul_iff_left`

English:
theorem mul_rightDvd_mul_iff_left
  statement: b * a ∣ᵣ c * a ↔ b ∣ᵣ c
  proof: ⟨fun ⟨d, eq⟩ => ⟨d, mul_right_cancel (eq.trans (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

中文:
定理 mul_rightDvd_mul_iff_left
  结论: b * a ∣ᵣ c * a ↔ b ∣ᵣ c
  证明: ⟨fun ⟨d, eq⟩ => ⟨d, mul_right_cancel (eq.trans (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

Depends on / 依赖: RightDvd, RightDvd.mul_const, eq.trans, mul_assoc, mul_const, mul_right_cancel
-/
theorem mul_rightDvd_mul_iff_left : b * a ∣ᵣ c * a ↔ b ∣ᵣ c :=
  ⟨fun ⟨d, eq⟩ => ⟨d, mul_right_cancel (eq.trans (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

end RightCancelSemigroup

section Monoid
variable [Monoid α] {a b c : α} {m n : Nat}

@[refl, simp]
/--
theorem `dvd_refl` / 定理 `dvd_refl`

English:
theorem dvd_refl
  given: (a : α)
  statement: a ∣ a
  proof: Dvd.intro 1 (mul_one a)

中文:
定理 dvd_refl
  条件: (a : α)
  结论: a ∣ a
  证明: Dvd.intro 1 (mul_one a)

Depends on / 依赖: Dvd.intro, mul_one
-/
theorem dvd_refl (a : α) : a ∣ a :=
  Dvd.intro 1 (mul_one a)

/--
theorem `dvd_rfl` / 定理 `dvd_rfl`

English:
theorem dvd_rfl
  statement: forall {a : α}, a ∣ a
  proof: fun {a} => dvd_refl a

中文:
定理 dvd_rfl
  结论: 对任意 {a : α}, a ∣ a
  证明: fun {a} => dvd_refl a

Depends on / 依赖: dvd_refl
-/
theorem dvd_rfl : forall {a : α}, a ∣ a := fun {a} => dvd_refl a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl α (· ∣ ·)
  body: ⟨dvd_refl⟩

中文:
实例 :
  签名: @Std.Refl α (· ∣ ·)
  定义体: ⟨dvd_refl⟩

Depends on / 依赖: dvd_refl
-/
instance : @Std.Refl α (· ∣ ·) :=
  ⟨dvd_refl⟩

/--
theorem `one_dvd` / 定理 `one_dvd`

English:
theorem one_dvd
  given: (a : α)
  statement: 1 ∣ a
  proof: Dvd.intro a (one_mul a)

中文:
定理 one_dvd
  条件: (a : α)
  结论: 1 ∣ a
  证明: Dvd.intro a (one_mul a)

Depends on / 依赖: Dvd.intro, one_mul
-/
theorem one_dvd (a : α) : 1 ∣ a :=
  Dvd.intro a (one_mul a)

/--
theorem `dvd_of_eq` / 定理 `dvd_of_eq`

English:
theorem dvd_of_eq
  given: (h : a = b)
  statement: a ∣ b
  proof: by rw [h]

alias Eq.dvd := dvd_of_eq

@[gcongr]

中文:
定理 dvd_of_eq
  条件: (h : a = b)
  结论: a ∣ b
  证明: by rw [h]

alias Eq.dvd := dvd_of_eq

@[gcongr]
-/
theorem dvd_of_eq (h : a = b) : a ∣ b := by rw [h]

alias Eq.dvd := dvd_of_eq

@[gcongr]
/--
lemma `pow_dvd_pow` / 引理 `pow_dvd_pow`

English:
lemma pow_dvd_pow
  given: (a : α) (h : m <= n)
  statement: a ^ m ∣ a ^ n
  proof: ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩

中文:
引理 pow_dvd_pow
  条件: (a : α) (h : m <= n)
  结论: a ^ m ∣ a ^ n
  证明: ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩

Depends on / 依赖: Nat.add_comm, Nat.sub_add_cancel, add_comm, pow_add, sub_add_cancel
-/
lemma pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n :=
  ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩

/--
lemma `dvd_pow` / 引理 `dvd_pow`

English:
lemma dvd_pow
  given: (hab : a ∣ b)
  statement: forall {n : Nat} (_ : n != 0), a ∣ b ^ n
  proof: dvd_pow

中文:
引理 dvd_pow
  条件: (hab : a ∣ b)
  结论: 对任意 {n : 自然数} (_ : n != 0), a ∣ b ^ n
  证明: dvd_pow

Depends on / 依赖: dvd_pow
-/
lemma dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ n
  | 0, hn => (hn rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact hab.mul_right _

alias Dvd.dvd.pow := dvd_pow

/--
lemma `dvd_pow_self` / 引理 `dvd_pow_self`

English:
lemma dvd_pow_self
  given: (a : α) {n : Nat} (hn : n != 0)
  statement: a ∣ a ^ n
  proof: dvd_rfl.pow hn

@[refl, simp]

中文:
引理 dvd_pow_self
  条件: (a : α) {n : 自然数} (hn : n != 0)
  结论: a ∣ a ^ n
  证明: dvd_rfl.pow hn

@[refl, simp]

Depends on / 依赖: dvd_rfl, dvd_rfl.pow
-/
lemma dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n := dvd_rfl.pow hn

@[refl, simp]
/--
theorem `RightDvd.refl` / 定理 `RightDvd.refl`

English:
theorem RightDvd.refl
  given: (a : α)
  statement: a ∣ᵣ a
  proof: ⟨1, (one_mul a).symm⟩

中文:
定理 RightDvd.refl
  条件: (a : α)
  结论: a ∣ᵣ a
  证明: ⟨1, (one_mul a).symm⟩
-/
protected theorem RightDvd.refl (a : α) : a ∣ᵣ a :=
  ⟨1, (one_mul a).symm⟩

/--
theorem `RightDvd.rfl` / 定理 `RightDvd.rfl`

English:
theorem RightDvd.rfl
  given: {a : α}
  statement: a ∣ᵣ a
  proof: .refl _

中文:
定理 RightDvd.rfl
  条件: {a : α}
  结论: a ∣ᵣ a
  证明: .refl _
-/
protected theorem RightDvd.rfl {a : α} : a ∣ᵣ a := .refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreorder α RightDvd
  body: .refl

中文:
实例 :
  签名: 是预序 α RightDvd
  定义体: .refl
-/
instance : IsPreorder α RightDvd where
  refl := .refl

/--
theorem `RightDvd.of_eq` / 定理 `RightDvd.of_eq`

English:
theorem RightDvd.of_eq
  given: (h : a = b)
  statement: a ∣ᵣ b
  proof: by rw [h]

alias Eq.rightDvd := RightDvd.of_eq

中文:
定理 RightDvd.of_eq
  条件: (h : a = b)
  结论: a ∣ᵣ b
  证明: by rw [h]

alias Eq.rightDvd := RightDvd.of_eq
-/
theorem RightDvd.of_eq (h : a = b) : a ∣ᵣ b := by rw [h]

alias Eq.rightDvd := RightDvd.of_eq

end Monoid

section CommSemigroup

variable [CommSemigroup α] {a b c : α}

/--
theorem `Dvd.intro_left` / 定理 `Dvd.intro_left`

English:
theorem Dvd.intro_left
  given: (c : α) (h : c * a = b)
  statement: a ∣ b
  proof: Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left

中文:
定理 Dvd.intro_left
  条件: (c : α) (h : c * a = b)
  结论: a ∣ b
  证明: Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left

Depends on / 依赖: Dvd.intro, mul_comm
-/
theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
  Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left

/--
theorem `exists_eq_mul_left_of_dvd` / 定理 `exists_eq_mul_left_of_dvd`

English:
theorem exists_eq_mul_left_of_dvd
  given: (h : a ∣ b)
  statement: exists c, b = c * a
  proof: Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))

中文:
定理 存在_eq_mul_left_of_dvd
  条件: (h : a ∣ b)
  结论: 存在 c, b = c * a
  证明: Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))

Depends on / 依赖: Dvd.elim, Eq.trans, Exists, Exists.intro, mul_comm
-/
theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : exists c, b = c * a :=
  Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))

/--
theorem `dvd_iff_exists_eq_mul_left` / 定理 `dvd_iff_exists_eq_mul_left`

English:
theorem dvd_iff_exists_eq_mul_left
  statement: a ∣ b ↔ exists c, b = c * a
  proof: ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

中文:
定理 dvd_iff_存在_eq_mul_left
  结论: a ∣ b ↔ 存在 c, b = c * a
  证明: ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

Depends on / 依赖: exists_eq_mul_left_of_dvd, mul_comm
-/
theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ exists c, b = c * a :=
  ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

/--
theorem `Dvd.elim_left` / 定理 `Dvd.elim_left`

English:
theorem Dvd.elim_left
  given: {P : Prop} (h₁ : a ∣ b) (h₂ : forall c, b = c * a -> P)
  statement: P
  proof: Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

@[simp]

中文:
定理 Dvd.elim_left
  条件: {P : 命题} (h₁ : a ∣ b) (h₂ : 对任意 c, b = c * a -> P)
  结论: P
  证明: Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

@[simp]

Depends on / 依赖: Exists, Exists.elim, exists_eq_mul_left_of_dvd
-/
theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : forall c, b = c * a -> P) : P :=
  Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

@[simp]
/--
theorem `dvd_mul_left` / 定理 `dvd_mul_left`

English:
theorem dvd_mul_left
  given: (a b : α)
  statement: a ∣ b * a
  proof: Dvd.intro b (mul_comm a b)

中文:
定理 dvd_mul_left
  条件: (a b : α)
  结论: a ∣ b * a
  证明: Dvd.intro b (mul_comm a b)

Depends on / 依赖: Dvd.intro, mul_comm
-/
theorem dvd_mul_left (a b : α) : a ∣ b * a :=
  Dvd.intro b (mul_comm a b)

/--
theorem `dvd_mul_of_dvd_right` / 定理 `dvd_mul_of_dvd_right`

English:
theorem dvd_mul_of_dvd_right
  given: (h : a ∣ b) (c : α)
  statement: a ∣ c * b
  proof: by
  rw [mul_comm]; exact h.mul_right _

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

中文:
定理 dvd_mul_of_dvd_right
  条件: (h : a ∣ b) (c : α)
  结论: a ∣ c * b
  证明: by
  rw [mul_comm]; exact h.mul_right _

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

Depends on / 依赖: h.mul_right, mul_comm, mul_right
-/
theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by
  rw [mul_comm]; exact h.mul_right _

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[gcongr]
/--
theorem `mul_dvd_mul` / 定理 `mul_dvd_mul`

English:
theorem mul_dvd_mul
  statement: forall {a b c d : α}, a ∣ b -> c ∣ d -> a * c ∣ b * d

中文:
定理 mul_dvd_mul
  结论: 对任意 {a b c d : α}, a ∣ b -> c ∣ d -> a * c ∣ b * d
-/
theorem mul_dvd_mul : forall {a b c d : α}, a ∣ b -> c ∣ d -> a * c ∣ b * d
  | a, _, c, _, ⟨e, rfl⟩, ⟨f, rfl⟩ => ⟨e * f, by simp⟩

/--
theorem `dvd_of_mul_left_dvd` / 定理 `dvd_of_mul_left_dvd`

English:
theorem dvd_of_mul_left_dvd
  given: (h : a * b ∣ c)
  statement: b ∣ c
  proof: Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])

中文:
定理 dvd_of_mul_left_dvd
  条件: (h : a * b ∣ c)
  结论: b ∣ c
  证明: Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])

Depends on / 依赖: Dvd.elim, Dvd.intro
-/
theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
  Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])

/--
theorem `dvd_mul` / 定理 `dvd_mul`

English:
theorem dvd_mul
  given: [DecompositionMonoid α] {k m n : α}
  proof: by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  gcongr

@[simp]

中文:
定理 dvd_mul
  条件: [分解幺半群 α] {k m n : α}
  证明: by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  gcongr

@[simp]

Depends on / 依赖: exists_dvd_and_dvd_of_dvd_mul
-/
theorem dvd_mul [DecompositionMonoid α] {k m n : α} :
    k ∣ m * n ↔ exists d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  gcongr

@[simp]
/--
theorem `rightDvd_iff_dvd` / 定理 `rightDvd_iff_dvd`

English:
theorem rightDvd_iff_dvd
  statement: a ∣ᵣ b ↔ a ∣ b
  proof: exists_congr fun c => by rw [mul_comm]

中文:
定理 rightDvd_iff_dvd
  结论: a ∣ᵣ b ↔ a ∣ b
  证明: exists_congr fun c => by rw [mul_comm]

Depends on / 依赖: exists_congr, mul_comm
-/
theorem rightDvd_iff_dvd : a ∣ᵣ b ↔ a ∣ b :=
  exists_congr fun c => by rw [mul_comm]

end CommSemigroup

section CommMonoid

variable [CommMonoid α] {a b : α}

/--
theorem `mul_dvd_mul_right` / 定理 `mul_dvd_mul_right`

English:
theorem mul_dvd_mul_right
  given: (h : a ∣ b) (c : α)
  statement: a * c ∣ b * c
  proof: by
  gcongr

中文:
定理 mul_dvd_mul_right
  条件: (h : a ∣ b) (c : α)
  结论: a * c ∣ b * c
  证明: by
  gcongr
-/
theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c := by
  gcongr

/--
theorem `pow_dvd_pow_of_dvd` / 定理 `pow_dvd_pow_of_dvd`

English:
theorem pow_dvd_pow_of_dvd
  given: (h : a ∣ b) (n : Nat)
  statement: a ^ n ∣ b ^ n
  proof: by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ]; rw [pow_succ]
    gcongr

@[gcongr]

中文:
定理 pow_dvd_pow_of_dvd
  条件: (h : a ∣ b) (n : 自然数)
  结论: a ^ n ∣ b ^ n
  证明: by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ]; rw [pow_succ]
    gcongr

@[gcongr]

Depends on / 依赖: pow_succ
-/
theorem pow_dvd_pow_of_dvd (h : a ∣ b) (n : Nat) : a ^ n ∣ b ^ n := by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ]; rw [pow_succ]
    gcongr

@[gcongr]
/--
lemma `pow_dvd_pow_of_dvd_of_le` / 引理 `pow_dvd_pow_of_dvd_of_le`

English:
lemma pow_dvd_pow_of_dvd_of_le
  given: {m n : Nat} (hab : a ∣ b) (hmn : m <= n)
  statement: a ^ m ∣ b ^ n
  proof: by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

中文:
引理 pow_dvd_pow_of_dvd_of_le
  条件: {m n : 自然数} (hab : a ∣ b) (hmn : m <= n)
  结论: a ^ m ∣ b ^ n
  证明: by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

Depends on / 依赖: apply_rules, pow_dvd_pow_of_dvd
-/
lemma pow_dvd_pow_of_dvd_of_le {m n : Nat} (hab : a ∣ b) (hmn : m <= n) : a ^ m ∣ b ^ n := by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

end CommMonoid
