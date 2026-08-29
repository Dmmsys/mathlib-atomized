/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.Conv

/-!
# Idempotents

This file defines idempotents for an arbitrary multiplication and proves some basic results,
including:

* `IsIdempotentElem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `IsIdempotentElem.pow_succ_eq`: In a monoid `a ^ (n+1) = a` for `a` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/

@[expose] public section

assert_not_exists GroupWithZero

variable {M N S : Type*}

/--
Definition of `IsIdempotentElem` / `IsIdempotentElem` 的定义

English:
definition IsIdempotentElem
  signature: [Mul M] (a : M)
  body: a * a = a

中文:
定义 IsIdempotentElem
  签名: [Mul M] (a : M)
  定义体: a * a = a
-/
def IsIdempotentElem [Mul M] (a : M) : Prop := a * a = a

/--
lemma `isIdempotentElem_iff` / 引理 `isIdempotentElem_iff`

English:
lemma isIdempotentElem_iff
  given: [Mul M] {a : M}
  statement: IsIdempotentElem a ↔ a * a = a
  proof: Iff.rfl

中文:
引理 isIdempotentElem_iff
  条件: [Mul M] {a : M}
  结论: IsIdempotentElem a ↔ a * a = a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isIdempotentElem_iff [Mul M] {a : M} : IsIdempotentElem a ↔ a * a = a := Iff.rfl

namespace IsIdempotentElem
section Mul
variable [Mul M] {a : M}

/--
lemma `of_isIdempotent` / 引理 `of_isIdempotent`

English:
lemma of_isIdempotent
  given: [Std.IdempotentOp (α := M) (· * ·)] (a : M)
  statement: IsIdempotentElem a
  proof: Std.IdempotentOp.idempotent a

中文:
引理 of_isIdempotent
  条件: [Std.IdempotentOp (α := M) (· * ·)] (a : M)
  结论: IsIdempotentElem a
  证明: Std.IdempotentOp.idempotent a

Depends on / 依赖: IsIdempotentElem
-/
lemma of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a

/--
lemma `eq` / 引理 `eq`

English:
lemma eq
  given: (ha : IsIdempotentElem a)
  statement: a * a = a
  proof: ha

中文:
引理 eq
  条件: (ha : IsIdempotentElem a)
  结论: a * a = a
  证明: ha
-/
lemma eq (ha : IsIdempotentElem a) : a * a = a := ha

end Mul

section Semigroup
variable [Semigroup S] {a b : S}

/--
lemma `mul_of_commute` / 引理 `mul_of_commute`

English:
lemma mul_of_commute
  given: (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
  proof: by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, ha.eq, hb.eq]

中文:
引理 mul_of_commute
  条件: (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
  证明: by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, ha.eq, hb.eq]

Depends on / 依赖: IsIdempotentElem, ha.eq, hab.symm.mul_mul_mul_comm, hb.eq, mul_mul_mul_comm
-/
lemma mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, ha.eq, hb.eq]

end Semigroup

section CommSemigroup
variable [CommSemigroup S] {a b : S}

/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  given: (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
  statement: IsIdempotentElem (a * b)
  proof: ha.mul_of_commute (.all ..) hb

中文:
引理 mul
  条件: (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
  结论: IsIdempotentElem (a * b)
  证明: ha.mul_of_commute (.all ..) hb

Depends on / 依赖: ha.mul_of_commute, mul_of_commute
-/
lemma mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b) :=
  ha.mul_of_commute (.all ..) hb

end CommSemigroup

section MulOneClass
variable [MulOneClass M] {a : M}

/--
lemma `one` / 引理 `one`

English:
lemma one
  statement: IsIdempotentElem (1 : M)
  proof: mul_one _

中文:
引理 one
  结论: IsIdempotentElem (1 : M)
  证明: mul_one _

Depends on / 依赖: mul_one
-/
lemma one : IsIdempotentElem (1 : M) := mul_one _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One {a : M // IsIdempotentElem a}
  body: ⟨1, one⟩

中文:
实例 :
  签名: One {a : M // IsIdempotentElem a}
  定义体: ⟨1, one⟩
-/
instance : One {a : M // IsIdempotentElem a} where one := ⟨1, one⟩

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ↑(1 : {a : M // IsIdempotentElem a}) = (1 : M)
  proof: rfl

中文:
引理 coe_one
  结论: ↑(1 : {a : M // IsIdempotentElem a}) = (1 : M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ↑(1 : {a : M // IsIdempotentElem a}) = (1 : M) := rfl

end MulOneClass

section Monoid
variable [Monoid M] {a : M}

/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: (n : Nat) (h : IsIdempotentElem a)
  statement: IsIdempotentElem (a ^ n)
  proof: Nat.recOn n ((pow_zero a).symm ▸ one) fun n _ =>
    show a ^ n.succ * a ^ n.succ = a ^ n.succ by
      conv_rhs => rw [← h.eq]
      rw [← sq]; rw [← sq]; rw [← pow_mul]; rw [← pow_mul']

中文:
引理 pow
  条件: (n : 自然数) (h : IsIdempotentElem a)
  结论: IsIdempotentElem (a ^ n)
  证明: Nat.recOn n ((pow_zero a).symm ▸ one) fun n _ =>
    show a ^ n.succ * a ^ n.succ = a ^ n.succ by
      conv_rhs => rw [← h.eq]
      rw [← sq]; rw [← sq]; rw [← pow_mul]; rw [← pow_mul']

Depends on / 依赖: Nat.recOn, conv_rhs, h.eq, n.succ, pow_mul, pow_zero
-/
lemma pow (n : Nat) (h : IsIdempotentElem a) : IsIdempotentElem (a ^ n) :=
  Nat.recOn n ((pow_zero a).symm ▸ one) fun n _ =>
    show a ^ n.succ * a ^ n.succ = a ^ n.succ by
      conv_rhs => rw [← h.eq]
      rw [← sq]; rw [← sq]; rw [← pow_mul]; rw [← pow_mul']

/--
lemma `pow_succ_eq` / 引理 `pow_succ_eq`

English:
lemma pow_succ_eq
  given: (n : Nat) (h : IsIdempotentElem a)
  statement: a ^ (n + 1) = a
  proof: Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, h.eq]

中文:
引理 pow_succ_eq
  条件: (n : 自然数) (h : IsIdempotentElem a)
  结论: a ^ (n + 1) = a
  证明: Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, h.eq]

Depends on / 依赖: Nat.recOn, Nat.zero_add, h.eq, pow_one, pow_succ, zero_add
-/
lemma pow_succ_eq (n : Nat) (h : IsIdempotentElem a) : a ^ (n + 1) = a :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, h.eq]

/--
theorem `pow_eq` / 定理 `pow_eq`

English:
theorem pow_eq
  given: (h : IsIdempotentElem a) {n : Nat} (hn : n != 0)
  statement: a ^ n = a
  proof: by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact h.pow_succ_eq _

中文:
定理 pow_eq
  条件: (h : IsIdempotentElem a) {n : 自然数} (hn : n != 0)
  结论: a ^ n = a
  证明: by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact h.pow_succ_eq _

Depends on / 依赖: Nat.exists_eq_add_one_of_ne_zero, exists_eq_add_one_of_ne_zero, h.pow_succ_eq, pow_succ_eq
-/
theorem pow_eq (h : IsIdempotentElem a) {n : Nat} (hn : n != 0) : a ^ n = a := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact h.pow_succ_eq _

/--
theorem `iff_eq_one_of_isUnit` / 定理 `iff_eq_one_of_isUnit`

English:
theorem iff_eq_one_of_isUnit
  given: (h : IsUnit a)
  statement: IsIdempotentElem a ↔ a = 1 where
  proof: by
    have ⟨q, eq⟩ := h.exists_left_inv
    rw [← eq]; rw [← idem.eq]; rw [← mul_assoc]; rw [eq]; rw [one_mul]; rw [idem.eq]
  mpr := by rintro rfl; exact .one

中文:
定理 iff_eq_one_of_isUnit
  条件: (h : IsUnit a)
  结论: IsIdempotentElem a ↔ a = 1 where
  证明: by
    have ⟨q, eq⟩ := h.exists_left_inv
    rw [← eq]; rw [← idem.eq]; rw [← mul_assoc]; rw [eq]; rw [one_mul]; rw [idem.eq]
  mpr := by rintro rfl; exact .one

Depends on / 依赖: exists_left_inv, h.exists_left_inv, idem.eq, mul_assoc, one_mul
-/
theorem iff_eq_one_of_isUnit (h : IsUnit a) : IsIdempotentElem a ↔ a = 1 where
  mp idem := by
    have ⟨q, eq⟩ := h.exists_left_inv
    rw [← eq]; rw [← idem.eq]; rw [← mul_assoc]; rw [eq]; rw [one_mul]; rw [idem.eq]
  mpr := by rintro rfl; exact .one

end Monoid

section CancelMonoid
variable [CancelMonoid M] {a : M}

/--
lemma `iff_eq_one` / 引理 `iff_eq_one`

English:
lemma iff_eq_one
  statement: IsIdempotentElem a ↔ a = 1
  proof: by simp [IsIdempotentElem]

中文:
引理 iff_eq_one
  结论: IsIdempotentElem a ↔ a = 1
  证明: by simp [IsIdempotentElem]
-/
@[simp] lemma iff_eq_one : IsIdempotentElem a ↔ a = 1 := by simp [IsIdempotentElem]

end CancelMonoid

/--
lemma `map` / 引理 `map`

English:
lemma map
  statement: {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
  proof: by
  rw [IsIdempotentElem]; rw [← map_mul]; rw [he.eq]

中文:
引理 map
  结论: {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
  证明: by
  rw [IsIdempotentElem]; rw [← map_mul]; rw [he.eq]

Depends on / 依赖: IsIdempotentElem, he.eq, map_mul
-/
lemma map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem]; rw [← map_mul]; rw [he.eq]

/--
lemma `mul_mul_self` / 引理 `mul_mul_self`

English:
lemma mul_mul_self
  statement: {M : Type*} [Semigroup M] {x : M}
  proof: mul_assoc y x x ▸ congrArg (y * ·) hx.eq

中文:
引理 mul_mul_self
  结论: {M : 类型} [Semigroup M] {x : M}
  证明: mul_assoc y x x ▸ congrArg (y * ·) hx.eq

Depends on / 依赖: hx.eq, mul_assoc
-/
lemma mul_mul_self {M : Type*} [Semigroup M] {x : M}
    (hx : IsIdempotentElem x) (y : M) : y * x * x = y * x :=
  mul_assoc y x x ▸ congrArg (y * ·) hx.eq

/--
lemma `mul_self_mul` / 引理 `mul_self_mul`

English:
lemma mul_self_mul
  statement: {M : Type*} [Semigroup M] {x : M}
  proof: mul_assoc x x y ▸ congrArg (· * y) hx.eq

中文:
引理 mul_self_mul
  结论: {M : 类型} [Semigroup M] {x : M}
  证明: mul_assoc x x y ▸ congrArg (· * y) hx.eq

Depends on / 依赖: hx.eq, mul_assoc
-/
lemma mul_self_mul {M : Type*} [Semigroup M] {x : M}
    (hx : IsIdempotentElem x) (y : M) : x * (x * y) = x * y :=
  mul_assoc x x y ▸ congrArg (· * y) hx.eq

end IsIdempotentElem
