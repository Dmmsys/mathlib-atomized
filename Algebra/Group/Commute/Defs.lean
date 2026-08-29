/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs

/-!
# Commuting pairs of elements in monoids

We define the predicate `Commute a b := a * b = b * a` and provide some operations on terms
`(h : Commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that
`hb : Commute a b` and `hc : Commute a c`. Then `hb.pow_left 5` proves `Commute (a ^ 5) b` and
`(hb.pow_right 2).add_right (hb.mul_right hc)` proves `Commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc). Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `SemiconjBy`.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {G M S : Type*}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive /-- Two elements additively commute if `a + b = b + a` -/]
/--
Definition of `Commute` / `Commute` 的定义

English:
definition Commute
  signature: [Mul S] (a b : S)
  body: SemiconjBy a b b

中文:
定义 Commute
  签名: [Mul S] (a b : S)
  定义体: SemiconjBy a b b

Depends on / 依赖: SemiconjBy
-/
def Commute [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b

/--
Two elements `a` and `b` commute if `a * b = b * a`.
-/
@[to_additive]
/--
theorem `commute_iff_eq` / 定理 `commute_iff_eq`

English:
theorem commute_iff_eq
  given: [Mul S] (a b : S)
  statement: Commute a b ↔ a * b = b * a
  proof: Iff.rfl

中文:
定理 commute_iff_eq
  条件: [Mul S] (a b : S)
  结论: Commute a b ↔ a * b = b * a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b = b * a := Iff.rfl

namespace Commute

section Mul

variable [Mul S]

/-- Equality behind `Commute a b`; useful for rewriting. -/
@[to_additive (attr := grind ->) /-- Equality behind `AddCommute a b`; useful for rewriting. -/]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {a b : S} (h : Commute a b)
  statement: a * b = b * a
  proof: h

中文:
定理 eq
  条件: {a b : S} (h : Commute a b)
  结论: a * b = b * a
  证明: h
-/
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h

/-- Any element commutes with itself. -/
@[to_additive (attr := refl, simp) /-- Any element commutes with itself. -/]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (a : S)
  statement: Commute a a
  proof: Eq.refl (a * a)

中文:
定理 refl
  条件: (a : S)
  结论: Commute a a
  证明: Eq.refl (a * a)
-/
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[to_additive (attr := symm) /-- If `a` commutes with `b`, then `b` commutes with `a`. -/]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {a b : S} (h : Commute a b)
  statement: Commute b a
  proof: Eq.symm h

@[to_additive]

中文:
定理 symm
  条件: {a b : S} (h : Commute a b)
  结论: Commute b a
  证明: Eq.symm h

@[to_additive]
-/
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h

@[to_additive]
/--
theorem `semiconjBy` / 定理 `semiconjBy`

English:
theorem semiconjBy
  given: {a b : S} (h : Commute a b)
  statement: SemiconjBy a b b
  proof: h

@[to_additive (attr := grind =)]

中文:
定理 semiconjBy
  条件: {a b : S} (h : Commute a b)
  结论: SemiconjBy a b b
  证明: h

@[to_additive (attr := grind =)]
-/
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h

@[to_additive (attr := grind =)]
/--
theorem `symm_iff` / 定理 `symm_iff`

English:
theorem symm_iff
  given: {a b : S}
  statement: Commute a b ↔ Commute b a
  proof: ⟨Commute.symm, Commute.symm⟩

@[to_additive]

中文:
定理 symm_iff
  条件: {a b : S}
  结论: Commute a b ↔ Commute b a
  证明: ⟨Commute.symm, Commute.symm⟩

@[to_additive]
-/
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl S Commute
  body: ⟨Commute.refl⟩

@[to_additive]

中文:
实例 :
  签名: @Std.Refl S Commute
  定义体: ⟨Commute.refl⟩

@[to_additive]

Depends on / 依赖: Commute, Commute.refl
-/
instance : @Std.Refl S Commute :=
  ⟨Commute.refl⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Symm S Commute
  body: .symm

中文:
实例 :
  签名: @Std.Symm S Commute
  定义体: .symm
-/
instance : @Std.Symm S Commute where
  symm _ _ := .symm

-- This instance is useful for `Finset.noncommProd`
@[to_additive]
/--
Instance `on_refl` / 实例 `on_refl`

English:
instance on_refl
  signature: {f : G -> S}
  body: ⟨fun _ => Commute.refl _⟩

中文:
实例 on_refl
  签名: {f : G -> S}
  定义体: ⟨fun _ => Commute.refl _⟩

Depends on / 依赖: Commute, Commute.refl
-/
instance on_refl {f : G -> S} : Std.Refl fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩

end Mul

section Semigroup

variable [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[to_additive (attr := simp)
/-- If `a` commutes with both `b` and `c`, then it commutes with their sum. -/]
/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (hab : Commute a b) (hac : Commute a c)
  statement: Commute a (b * c)
  proof: SemiconjBy.mul_right hab hac

中文:
定理 mul_right
  条件: (hab : Commute a b) (hac : Commute a c)
  结论: Commute a (b * c)
  证明: SemiconjBy.mul_right hab hac

Depends on / 依赖: SemiconjBy, SemiconjBy.mul_right, mul_right
-/
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[to_additive (attr := simp)
/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/]
/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (hac : Commute a c) (hbc : Commute b c)
  statement: Commute (a * b) c
  proof: SemiconjBy.mul_left hac hbc

@[to_additive]

中文:
定理 mul_left
  条件: (hac : Commute a c) (hbc : Commute b c)
  结论: Commute (a * b) c
  证明: SemiconjBy.mul_left hac hbc

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.mul_left, mul_left
-/
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc

@[to_additive]
/--
theorem `right_comm` / 定理 `right_comm`

English:
theorem right_comm
  given: (h : Commute b c) (a : S)
  statement: a * b * c = a * c * b
  proof: by
  simp only [mul_assoc, h.eq]

@[to_additive]

中文:
定理 right_comm
  条件: (h : Commute b c) (a : S)
  结论: a * b * c = a * c * b
  证明: by
  simp only [mul_assoc, h.eq]

@[to_additive]
-/
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, h.eq]

@[to_additive]
/--
theorem `left_comm` / 定理 `left_comm`

English:
theorem left_comm
  given: (h : Commute a b) (c)
  statement: a * (b * c) = b * (a * c)
  proof: by
  simp only [← mul_assoc, h.eq]

@[to_additive]

中文:
定理 left_comm
  条件: (h : Commute a b) (c)
  结论: a * (b * c) = b * (a * c)
  证明: by
  simp only [← mul_assoc, h.eq]

@[to_additive]
-/
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, h.eq]

@[to_additive]
/--
theorem `mul_mul_mul_comm` / 定理 `mul_mul_mul_comm`

English:
theorem mul_mul_mul_comm
  given: (hbc : Commute b c) (a d : S)
  proof: by simp only [hbc.left_comm, mul_assoc]

中文:
定理 mul_mul_mul_comm
  条件: (hbc : Commute b c) (a d : S)
  证明: by simp only [hbc.left_comm, mul_assoc]
-/
protected theorem mul_mul_mul_comm (hbc : Commute b c) (a d : S) :
    a * b * (c * d) = a * c * (b * d) := by simp only [hbc.left_comm, mul_assoc]

end Semigroup

@[to_additive]
/--
theorem `all` / 定理 `all`

English:
theorem all
  given: [CommMagma S] (a b : S)
  statement: Commute a b
  proof: mul_comm a b

中文:
定理 all
  条件: [CommMagma S] (a b : S)
  结论: Commute a b
  证明: mul_comm a b
-/
protected theorem all [CommMagma S] (a b : S) : Commute a b :=
  mul_comm a b

section MulOneClass

variable [MulOneClass M]

@[to_additive (attr := simp)]
/--
theorem `one_right` / 定理 `one_right`

English:
theorem one_right
  given: (a : M)
  statement: Commute a 1
  proof: SemiconjBy.one_right a

@[to_additive (attr := simp)]

中文:
定理 one_right
  条件: (a : M)
  结论: Commute a 1
  证明: SemiconjBy.one_right a

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.one_right, one_right
-/
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a

@[to_additive (attr := simp)]
/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  given: (a : M)
  statement: Commute 1 a
  proof: SemiconjBy.one_left a

中文:
定理 one_left
  条件: (a : M)
  结论: Commute 1 a
  证明: SemiconjBy.one_left a

Depends on / 依赖: SemiconjBy, SemiconjBy.one_left, one_left
-/
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a

end MulOneClass

section Monoid

variable [Monoid M] {a b : M}

@[to_additive (attr := simp)]
/--
theorem `pow_right` / 定理 `pow_right`

English:
theorem pow_right
  given: (h : Commute a b) (n : Nat)
  statement: Commute a (b ^ n)
  proof: SemiconjBy.pow_right h n

@[to_additive (attr := simp)]

中文:
定理 pow_right
  条件: (h : Commute a b) (n : 自然数)
  结论: Commute a (b ^ n)
  证明: SemiconjBy.pow_right h n

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.pow_right, pow_right
-/
theorem pow_right (h : Commute a b) (n : Nat) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n

@[to_additive (attr := simp)]
/--
theorem `pow_left` / 定理 `pow_left`

English:
theorem pow_left
  given: (h : Commute a b) (n : Nat)
  statement: Commute (a ^ n) b
  proof: (h.symm.pow_right n).symm

中文:
定理 pow_left
  条件: (h : Commute a b) (n : 自然数)
  结论: Commute (a ^ n) b
  证明: (h.symm.pow_right n).symm

Depends on / 依赖: h.symm.pow_right, pow_right
-/
theorem pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm

-- todo: should nat power be called `nsmul` here?
@[to_additive]
/--
theorem `pow_pow` / 定理 `pow_pow`

English:
theorem pow_pow
  given: (h : Commute a b) (m n : Nat)
  statement: Commute (a ^ m) (b ^ n)
  proof: by
  simp [h]

@[to_additive]

中文:
定理 pow_pow
  条件: (h : Commute a b) (m n : 自然数)
  结论: Commute (a ^ m) (b ^ n)
  证明: by
  simp [h]

@[to_additive]
-/
theorem pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m) (b ^ n) := by
  simp [h]

@[to_additive]
/--
theorem `self_pow` / 定理 `self_pow`

English:
theorem self_pow
  given: (a : M) (n : Nat)
  statement: Commute a (a ^ n)
  proof: (Commute.refl a).pow_right n

@[to_additive]

中文:
定理 self_pow
  条件: (a : M) (n : 自然数)
  结论: Commute a (a ^ n)
  证明: (Commute.refl a).pow_right n

@[to_additive]

Depends on / 依赖: Commute, Commute.refl, pow_right
-/
theorem self_pow (a : M) (n : Nat) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n

@[to_additive]
/--
theorem `pow_self` / 定理 `pow_self`

English:
theorem pow_self
  given: (a : M) (n : Nat)
  statement: Commute (a ^ n) a
  proof: (Commute.refl a).pow_left n

@[to_additive]

中文:
定理 pow_self
  条件: (a : M) (n : 自然数)
  结论: Commute (a ^ n) a
  证明: (Commute.refl a).pow_left n

@[to_additive]

Depends on / 依赖: Commute, Commute.refl, pow_left
-/
theorem pow_self (a : M) (n : Nat) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n

@[to_additive]
/--
theorem `pow_pow_self` / 定理 `pow_pow_self`

English:
theorem pow_pow_self
  given: (a : M) (m n : Nat)
  statement: Commute (a ^ m) (a ^ n)
  proof: (Commute.refl a).pow_pow m n

中文:
定理 pow_pow_self
  条件: (a : M) (m n : 自然数)
  结论: Commute (a ^ m) (a ^ n)
  证明: (Commute.refl a).pow_pow m n

Depends on / 依赖: Commute, Commute.refl, pow_pow
-/
theorem pow_pow_self (a : M) (m n : Nat) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n

/--
lemma `mul_pow` / 引理 `mul_pow`

English:
lemma mul_pow
  given: (h : Commute a b)
  statement: forall n, (a * b) ^ n = a ^ n * b ^ n

中文:
引理 mul_pow
  条件: (h : Commute a b)
  结论: 对任意 n, (a * b) ^ n = a ^ n * b ^ n
-/
@[to_additive] lemma mul_pow (h : Commute a b) : forall n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by simp only [pow_succ', h.mul_pow n, ← mul_assoc, (h.pow_left n).right_comm]

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive]
/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  given: (hab : Commute a b)
  statement: (a * b)⁻¹ = a⁻¹ * b⁻¹
  proof: by rw [hab.eq, mul_inv_rev]

@[to_additive]

中文:
定理 mul_inv
  条件: (hab : Commute a b)
  结论: (a * b)⁻¹ = a⁻¹ * b⁻¹
  证明: by rw [hab.eq, mul_inv_rev]

@[to_additive]
-/
protected theorem mul_inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]

@[to_additive]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: (hab : Commute a b)
  statement: (a * b)⁻¹ = a⁻¹ * b⁻¹
  proof: by rw [hab.eq, mul_inv_rev]

@[to_additive AddCommute.zsmul_add]

中文:
定理 inv
  条件: (hab : Commute a b)
  结论: (a * b)⁻¹ = a⁻¹ * b⁻¹
  证明: by rw [hab.eq, mul_inv_rev]

@[to_additive AddCommute.zsmul_add]
-/
protected theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]

@[to_additive AddCommute.zsmul_add]
/--
lemma `mul_zpow` / 引理 `mul_zpow`

English:
lemma mul_zpow
  given: (h : Commute a b)
  statement: forall n : Int, (a * b) ^ n = a ^ n * b ^ n

中文:
引理 mul_zpow
  条件: (h : Commute a b)
  结论: 对任意 n : 整数, (a * b) ^ n = a ^ n * b ^ n
-/
protected lemma mul_zpow (h : Commute a b) : forall n : Int, (a * b) ^ n = a ^ n * b ^ n
  | (n : Nat) => by simp [zpow_natCast, h.mul_pow n]
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]

end DivisionMonoid

section Group

variable [Group G] {a b : G}

@[to_additive]
/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (h : Commute a b)
  statement: a * b * a⁻¹ = b
  proof: by
  rw [h.eq]; rw [mul_inv_cancel_right]

@[to_additive]

中文:
定理 mul_inv_cancel
  条件: (h : Commute a b)
  结论: a * b * a⁻¹ = b
  证明: by
  rw [h.eq]; rw [mul_inv_cancel_right]

@[to_additive]
-/
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq]; rw [mul_inv_cancel_right]

@[to_additive]
/--
theorem `mul_inv_cancel_assoc` / 定理 `mul_inv_cancel_assoc`

English:
theorem mul_inv_cancel_assoc
  given: (h : Commute a b)
  statement: a * (b * a⁻¹) = b
  proof: by
  rw [← mul_assoc]; rw [h.mul_inv_cancel]

中文:
定理 mul_inv_cancel_assoc
  条件: (h : Commute a b)
  结论: a * (b * a⁻¹) = b
  证明: by
  rw [← mul_assoc]; rw [h.mul_inv_cancel]

Depends on / 依赖: h.mul_inv_cancel, mul_assoc, mul_inv_cancel
-/
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc]; rw [h.mul_inv_cancel]

end Group

end Commute

/--
lemma `IsLeftRegular.commute_mul_left_iff` / 引理 `IsLeftRegular.commute_mul_left_iff`

English:
lemma IsLeftRegular.commute_mul_left_iff
  statement: [Semigroup S] {a b : S}
  proof: by
  simp [commute_iff_eq, mul_assoc, reg.eq_iff, eq_comm]

中文:
引理 IsLeftRegular.commute_mul_left_iff
  结论: [Semigroup S] {a b : S}
  证明: by
  simp [commute_iff_eq, mul_assoc, reg.eq_iff, eq_comm]
-/
@[to_additive] protected lemma IsLeftRegular.commute_mul_left_iff [Semigroup S] {a b : S}
    (reg : IsLeftRegular a) : Commute (a * b) a ↔ Commute a b := by
  simp [commute_iff_eq, mul_assoc, reg.eq_iff, eq_comm]

/--
lemma `IsRightRegular.commute_mul_right_iff` / 引理 `IsRightRegular.commute_mul_right_iff`

English:
lemma IsRightRegular.commute_mul_right_iff
  statement: [Semigroup S] {a b : S}
  proof: by
  simp [commute_iff_eq, ← mul_assoc, reg.eq_iff, eq_comm]

中文:
引理 IsRightRegular.commute_mul_right_iff
  结论: [Semigroup S] {a b : S}
  证明: by
  simp [commute_iff_eq, ← mul_assoc, reg.eq_iff, eq_comm]
-/
@[to_additive] protected lemma IsRightRegular.commute_mul_right_iff [Semigroup S] {a b : S}
    (reg : IsRightRegular a) : Commute (b * a) a ↔ Commute a b := by
  simp [commute_iff_eq, ← mul_assoc, reg.eq_iff, eq_comm]
