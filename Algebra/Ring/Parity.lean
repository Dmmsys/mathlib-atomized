/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Iterate

/-!
# Even and odd elements in rings

This file defines odd elements and proves some general facts about even and odd elements of rings.

As opposed to `Even`, `Odd` does not have a multiplicative counterpart.

## TODO

Try to generalize `Even` lemmas further. For example, there are still a few lemmas whose `Semiring`
assumptions I (DT) am not convinced are necessary. If that turns out to be true, they could be moved
to `Mathlib/Algebra/Group/Even.lean`.

## See also

`Mathlib/Algebra/Group/Even.lean` for the definition of even elements.
-/

@[expose] public section

assert_not_exists DenselyOrdered IsOrderedRing

open MulOpposite

variable {F α β : Type*}

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : Nat} {a : α}

/--
lemma `Even.neg_pow` / 引理 `Even.neg_pow`

English:
lemma Even.neg_pow
  statement: Even n -> forall a : α, (-a) ^ n = a ^ n
  proof: by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]

中文:
引理 Even.neg_pow
  结论: Even n -> 对任意 a : α, (-a) ^ n = a ^ n
  证明: by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]
-/
@[simp] lemma Even.neg_pow : Even n -> forall a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]

/--
lemma `Even.neg_one_pow` / 引理 `Even.neg_one_pow`

English:
lemma Even.neg_one_pow
  given: (h : Even n)
  statement: (-1 : α) ^ n = 1
  proof: by rw [h.neg_pow, one_pow]

中文:
引理 Even.neg_one_pow
  条件: (h : Even n)
  结论: (-1 : α) ^ n = 1
  证明: by rw [h.neg_pow, one_pow]

Depends on / 依赖: h.neg_pow, neg_pow, one_pow
-/
lemma Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]

end Monoid

/--
lemma `IsSquare.zero` / 引理 `IsSquare.zero`

English:
lemma IsSquare.zero
  given: [MulZeroClass α]
  statement: IsSquare (0 : α)
  proof: ⟨0, (mul_zero _).symm⟩

中文:
引理 IsSquare.zero
  条件: [MulZeroClass α]
  结论: IsSquare (0 : α)
  证明: ⟨0, (mul_zero _).symm⟩
-/
@[simp] lemma IsSquare.zero [MulZeroClass α] : IsSquare (0 : α) := ⟨0, (mul_zero _).symm⟩

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/--
lemma `even_two` / 引理 `even_two`

English:
lemma even_two
  statement: Even (2 : α)
  proof: ⟨1, by rw [one_add_one_eq_two]⟩

中文:
引理 even_two
  结论: Even (2 : α)
  证明: ⟨1, by rw [one_add_one_eq_two]⟩
-/
@[simp] lemma even_two : Even (2 : α) := ⟨1, by rw [one_add_one_eq_two]⟩

end AddMonoidWithOne

section Distrib
variable [Add α] [Mul α] {a : α}

/--
lemma `Even.mul_left` / 引理 `Even.mul_left`

English:
lemma Even.mul_left
  given: [LeftDistribClass α] (ha : Even a) (b : α)
  statement: Even (b * a)
  proof: by
  rcases ha with ⟨k, rfl⟩
  use b * k
  rw [mul_add]

中文:
引理 Even.mul_left
  条件: [LeftDistribClass α] (ha : Even a) (b : α)
  结论: Even (b * a)
  证明: by
  rcases ha with ⟨k, rfl⟩
  use b * k
  rw [mul_add]
-/
@[simp] lemma Even.mul_left [LeftDistribClass α] (ha : Even a) (b : α) : Even (b * a) := by
  rcases ha with ⟨k, rfl⟩
  use b * k
  rw [mul_add]

/--
lemma `Even.mul_right` / 引理 `Even.mul_right`

English:
lemma Even.mul_right
  given: [RightDistribClass α] (ha : Even a) (b : α)
  statement: Even (a * b)
  proof: by
  rcases ha with ⟨k, rfl⟩
  use k * b
  rw [add_mul]

中文:
引理 Even.mul_right
  条件: [RightDistribClass α] (ha : Even a) (b : α)
  结论: Even (a * b)
  证明: by
  rcases ha with ⟨k, rfl⟩
  use k * b
  rw [add_mul]
-/
@[simp] lemma Even.mul_right [RightDistribClass α] (ha : Even a) (b : α) : Even (a * b) := by
  rcases ha with ⟨k, rfl⟩
  use k * b
  rw [add_mul]

end Distrib

section Semiring
variable [Semiring α] [Semiring β] {a b : α} {m n : Nat}

/--
lemma `even_iff_exists_two_mul` / 引理 `even_iff_exists_two_mul`

English:
lemma even_iff_exists_two_mul
  statement: Even a ↔ exists b, a = 2 * b
  proof: by simp [even_iff_exists_two_nsmul]

中文:
引理 even_iff_exists_two_mul
  结论: Even a ↔ 存在 b, a = 2 * b
  证明: by simp [even_iff_exists_two_nsmul]

Depends on / 依赖: even_iff_exists_two_nsmul
-/
lemma even_iff_exists_two_mul : Even a ↔ exists b, a = 2 * b := by simp [even_iff_exists_two_nsmul]

/--
lemma `even_iff_two_dvd` / 引理 `even_iff_two_dvd`

English:
lemma even_iff_two_dvd
  statement: Even a ↔ 2 ∣ a
  proof: by simp [Even, Dvd.dvd, two_mul]

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd

中文:
引理 even_iff_two_dvd
  结论: Even a ↔ 2 ∣ a
  证明: by simp [Even, Dvd.dvd, two_mul]

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd

Depends on / 依赖: Dvd.dvd, two_mul
-/
lemma even_iff_two_dvd : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd

/--
lemma `Even.trans_dvd` / 引理 `Even.trans_dvd`

English:
lemma Even.trans_dvd
  given: (ha : Even a) (hab : a ∣ b)
  statement: Even b
  proof: even_iff_two_dvd.2 ha.two_dvd.trans hab

中文:
引理 Even.trans_dvd
  条件: (ha : Even a) (hab : a ∣ b)
  结论: Even b
  证明: even_iff_two_dvd.2 ha.two_dvd.trans hab

Depends on / 依赖: even_iff_two_dvd, ha.two_dvd.trans, two_dvd
-/
lemma Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b :=
even_iff_two_dvd.2 ha.two_dvd.trans hab

/--
lemma `Dvd.dvd.even` / 引理 `Dvd.dvd.even`

English:
lemma Dvd.dvd.even
  given: (hab : a ∣ b) (ha : Even a)
  statement: Even b
  proof: ha.trans_dvd hab

中文:
引理 Dvd.dvd.even
  条件: (hab : a ∣ b) (ha : Even a)
  结论: Even b
  证明: ha.trans_dvd hab

Depends on / 依赖: ha.trans_dvd, trans_dvd
-/
lemma Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b := ha.trans_dvd hab

/--
lemma `range_two_mul` / 引理 `range_two_mul`

English:
lemma range_two_mul
  given: (α) [NonAssocSemiring α]
  proof: by
  ext x
  simp [eq_comm, two_mul, Even]

中文:
引理 range_two_mul
  条件: (α) [NonAssocSemiring α]
  证明: by
  ext x
  simp [eq_comm, two_mul, Even]
-/
@[simp] lemma range_two_mul (α) [NonAssocSemiring α] :
    Set.range (fun x : α => 2 * x) = {a | Even a} := by
  ext x
  simp [eq_comm, two_mul, Even]


/--
lemma `even_two_mul` / 引理 `even_two_mul`

English:
lemma even_two_mul
  given: (a : α)
  statement: Even (2 * a)
  proof: ⟨a, two_mul _⟩

中文:
引理 even_two_mul
  条件: (a : α)
  结论: Even (2 * a)
  证明: ⟨a, two_mul _⟩

Depends on / 依赖: two_mul
-/
lemma even_two_mul (a : α) : Even (2 * a) := ⟨a, two_mul _⟩

/--
lemma `Even.pow_of_ne_zero` / 引理 `Even.pow_of_ne_zero`

English:
lemma Even.pow_of_ne_zero
  given: (ha : Even a)
  statement: forall {n : Nat}, n != 0 -> Even (a ^ n)

中文:
引理 Even.pow_of_ne_zero
  条件: (ha : Even a)
  结论: 对任意 {n : 自然数}, n != 0 -> Even (a ^ n)
-/
lemma Even.pow_of_ne_zero (ha : Even a) : forall {n : Nat}, n != 0 -> Even (a ^ n)
  | n + 1, _ => by rw [pow_succ]; exact ha.mul_left _

/--
Definition of `Odd` / `Odd` 的定义

English:
definition Odd
  signature: (a : α)
  body: exists k, a = 2 * k + 1

中文:
定义 Odd
  签名: (a : α)
  定义体: exists k, a = 2 * k + 1
-/
def Odd (a : α) : Prop := exists k, a = 2 * k + 1

/--
lemma `odd_iff_exists_bit1` / 引理 `odd_iff_exists_bit1`

English:
lemma odd_iff_exists_bit1
  statement: Odd a ↔ exists b, a = 2 * b + 1
  proof: exists_congr fun b => by rw [two_mul]

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1

中文:
引理 odd_iff_exists_bit1
  结论: Odd a ↔ 存在 b, a = 2 * b + 1
  证明: exists_congr fun b => by rw [two_mul]

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1

Depends on / 依赖: exists_congr, two_mul
-/
lemma odd_iff_exists_bit1 : Odd a ↔ exists b, a = 2 * b + 1 := exists_congr fun b => by rw [two_mul]

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1

/--
lemma `range_two_mul_add_one` / 引理 `range_two_mul_add_one`

English:
lemma range_two_mul_add_one
  given: (α : Type*) [Semiring α]
  proof: by ext x; simp [Odd, eq_comm]

中文:
引理 range_two_mul_add_one
  条件: (α : 类型) [Semiring α]
  证明: by ext x; simp [Odd, eq_comm]
-/
@[simp] lemma range_two_mul_add_one (α : Type*) [Semiring α] :
    Set.range (fun x : α => 2 * x + 1) = {a | Odd a} := by ext x; simp [Odd, eq_comm]

/--
lemma `Even.add_odd` / 引理 `Even.add_odd`

English:
lemma Even.add_odd
  statement: Even a -> Odd b -> Odd (a + b)
  proof: by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩

中文:
引理 Even.add_odd
  结论: Even a -> Odd b -> Odd (a + b)
  证明: by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩

Depends on / 依赖: add_assoc, mul_add, two_mul
-/
lemma Even.add_odd : Even a -> Odd b -> Odd (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩

/--
lemma `Even.odd_add` / 引理 `Even.odd_add`

English:
lemma Even.odd_add
  given: (ha : Even a) (hb : Odd b)
  statement: Odd (b + a)
  proof: add_comm a b ▸ ha.add_odd hb

中文:
引理 Even.odd_add
  条件: (ha : Even a) (hb : Odd b)
  结论: Odd (b + a)
  证明: add_comm a b ▸ ha.add_odd hb

Depends on / 依赖: add_comm, add_odd, ha.add_odd
-/
lemma Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a) := add_comm a b ▸ ha.add_odd hb
/--
lemma `Odd.add_even` / 引理 `Odd.add_even`

English:
lemma Odd.add_even
  given: (ha : Odd a) (hb : Even b)
  statement: Odd (a + b)
  proof: add_comm a b ▸ hb.add_odd ha

中文:
引理 Odd.add_even
  条件: (ha : Odd a) (hb : Even b)
  结论: Odd (a + b)
  证明: add_comm a b ▸ hb.add_odd ha

Depends on / 依赖: add_comm, add_odd, hb.add_odd
-/
lemma Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b) := add_comm a b ▸ hb.add_odd ha

/--
lemma `Odd.add_odd` / 引理 `Odd.add_odd`

English:
lemma Odd.add_odd
  statement: Odd a -> Odd b -> Even (a + b)
  proof: by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨a + b + 1, ?_⟩
  rw [two_mul]; rw [two_mul]
  ac_rfl

中文:
引理 Odd.add_odd
  结论: Odd a -> Odd b -> Even (a + b)
  证明: by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨a + b + 1, ?_⟩
  rw [two_mul]; rw [two_mul]
  ac_rfl

Depends on / 依赖: two_mul
-/
lemma Odd.add_odd : Odd a -> Odd b -> Even (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨a + b + 1, ?_⟩
  rw [two_mul]; rw [two_mul]
  ac_rfl

/--
lemma `odd_one` / 引理 `odd_one`

English:
lemma odd_one
  statement: Odd (1 : α)
  proof: ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩

中文:
引理 odd_one
  结论: Odd (1 : α)
  证明: ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
-/
@[simp] lemma odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩

/--
lemma `Even.add_one` / 引理 `Even.add_one`

English:
lemma Even.add_one
  given: (h : Even a)
  statement: Odd (a + 1)
  proof: h.add_odd odd_one

中文:
引理 Even.add_one
  条件: (h : Even a)
  结论: Odd (a + 1)
  证明: h.add_odd odd_one
-/
@[simp] lemma Even.add_one (h : Even a) : Odd (a + 1) := h.add_odd odd_one
/--
lemma `Even.one_add` / 引理 `Even.one_add`

English:
lemma Even.one_add
  given: (h : Even a)
  statement: Odd (1 + a)
  proof: h.odd_add odd_one

中文:
引理 Even.one_add
  条件: (h : Even a)
  结论: Odd (1 + a)
  证明: h.odd_add odd_one
-/
@[simp] lemma Even.one_add (h : Even a) : Odd (1 + a) := h.odd_add odd_one
/--
lemma `Odd.add_one` / 引理 `Odd.add_one`

English:
lemma Odd.add_one
  given: (h : Odd a)
  statement: Even (a + 1)
  proof: h.add_odd odd_one

中文:
引理 Odd.add_one
  条件: (h : Odd a)
  结论: Even (a + 1)
  证明: h.add_odd odd_one
-/
@[simp] lemma Odd.add_one (h : Odd a) : Even (a + 1) := h.add_odd odd_one
/--
lemma `Odd.one_add` / 引理 `Odd.one_add`

English:
lemma Odd.one_add
  given: (h : Odd a)
  statement: Even (1 + a)
  proof: odd_one.add_odd h

中文:
引理 Odd.one_add
  条件: (h : Odd a)
  结论: Even (1 + a)
  证明: odd_one.add_odd h
-/
@[simp] lemma Odd.one_add (h : Odd a) : Even (1 + a) := odd_one.add_odd h

/--
lemma `odd_two_mul_add_one` / 引理 `odd_two_mul_add_one`

English:
lemma odd_two_mul_add_one
  given: (a : α)
  statement: Odd (2 * a + 1)
  proof: ⟨_, rfl⟩

中文:
引理 odd_two_mul_add_one
  条件: (a : α)
  结论: Odd (2 * a + 1)
  证明: ⟨_, rfl⟩
-/
lemma odd_two_mul_add_one (a : α) : Odd (2 * a + 1) := ⟨_, rfl⟩

/--
lemma `odd_add_self_one'` / 引理 `odd_add_self_one'`

English:
lemma odd_add_self_one'
  statement: Odd (a + (a + 1))
  proof: by simp [← add_assoc]

中文:
引理 odd_add_self_one'
  结论: Odd (a + (a + 1))
  证明: by simp [← add_assoc]
-/
@[simp] lemma odd_add_self_one' : Odd (a + (a + 1)) := by simp [← add_assoc]
/--
lemma `odd_add_one_self` / 引理 `odd_add_one_self`

English:
lemma odd_add_one_self
  statement: Odd (a + 1 + a)
  proof: by simp [add_comm _ a]

中文:
引理 odd_add_one_self
  结论: Odd (a + 1 + a)
  证明: by simp [add_comm _ a]
-/
@[simp] lemma odd_add_one_self : Odd (a + 1 + a) := by simp [add_comm _ a]
/--
lemma `odd_add_one_self'` / 引理 `odd_add_one_self'`

English:
lemma odd_add_one_self'
  statement: Odd (a + (1 + a))
  proof: by simp [add_comm 1 a]

中文:
引理 odd_add_one_self'
  结论: Odd (a + (1 + a))
  证明: by simp [add_comm 1 a]
-/
@[simp] lemma odd_add_one_self' : Odd (a + (1 + a)) := by simp [add_comm 1 a]

/--
lemma `Odd.map` / 引理 `Odd.map`

English:
lemma Odd.map
  given: [FunLike F α β] [RingHomClass F α β] (f : F)
  statement: Odd a -> Odd (f a)
  proof: by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩

中文:
引理 Odd.map
  条件: [FunLike F α β] [RingHomClass F α β] (f : F)
  结论: Odd a -> Odd (f a)
  证明: by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩

Depends on / 依赖: two_mul
-/
lemma Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a -> Odd (f a) := by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩

/--
lemma `Odd.natCast` / 引理 `Odd.natCast`

English:
lemma Odd.natCast
  given: {R : Type*} [Semiring R] {n : Nat} (hn : Odd n)
  statement: Odd (n : R)
  proof: hn.map Nat.castRingHom R

中文:
引理 Odd.natCast
  条件: {R : 类型} [Semiring R] {n : 自然数} (hn : Odd n)
  结论: Odd (n : R)
  证明: hn.map Nat.castRingHom R

Depends on / 依赖: Nat.castRingHom, castRingHom, hn.map
-/
lemma Odd.natCast {R : Type*} [Semiring R] {n : Nat} (hn : Odd n) : Odd (n : R) :=
hn.map Nat.castRingHom R

/--
lemma `Odd.mul` / 引理 `Odd.mul`

English:
lemma Odd.mul
  statement: Odd a -> Odd b -> Odd (a * b)
  proof: by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  rw [mul_add]; rw [add_mul]; rw [mul_one]; rw [← add_assoc]; rw [one_mul]; rw [mul_assoc]; rw [← mul_add]; rw [← mul_add]; rw [← mul_assoc]; rw [← Nat.cast_two]; rw [← Nat.cast_comm]

中文:
引理 Odd.mul
  结论: Odd a -> Odd b -> Odd (a * b)
  证明: by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  rw [mul_add]; rw [add_mul]; rw [mul_one]; rw [← add_assoc]; rw [one_mul]; rw [mul_assoc]; rw [← mul_add]; rw [← mul_add]; rw [← mul_assoc]; rw [← Nat.cast_two]; rw [← Nat.cast_comm]
-/
@[simp] lemma Odd.mul : Odd a -> Odd b -> Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  rw [mul_add]; rw [add_mul]; rw [mul_one]; rw [← add_assoc]; rw [one_mul]; rw [mul_assoc]; rw [← mul_add]; rw [← mul_add]; rw [← mul_assoc]; rw [← Nat.cast_two]; rw [← Nat.cast_comm]

/--
lemma `Odd.pow` / 引理 `Odd.pow`

English:
lemma Odd.pow
  given: {n : Nat} (ha : Odd a)
  statement: Odd (a ^ n)
  proof: by
  induction n with
  | zero => simp [pow_zero]
  | succ n hrec => rw [pow_succ]; exact hrec.mul ha

中文:
引理 Odd.pow
  条件: {n : 自然数} (ha : Odd a)
  结论: Odd (a ^ n)
  证明: by
  induction n with
  | zero => simp [pow_zero]
  | succ n hrec => rw [pow_succ]; exact hrec.mul ha

Depends on / 依赖: hrec.mul, pow_succ, pow_zero
-/
lemma Odd.pow {n : Nat} (ha : Odd a) : Odd (a ^ n) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hrec => rw [pow_succ]; exact hrec.mul ha

/--
lemma `Odd.pow_add_pow_eq_zero` / 引理 `Odd.pow_add_pow_eq_zero`

English:
lemma Odd.pow_add_pow_eq_zero
  given: [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0)
  proof: by
  obtain ⟨k, rfl⟩ := hn
  induction k with | zero => simpa | succ k ih => ?_
have : a ^ 2 = b ^ 2 := add_right_cancel
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := 

中文:
引理 Odd.pow_add_pow_eq_zero
  条件: [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0)
  证明: by
  obtain ⟨k, rfl⟩ := hn
  induction k with | zero => simpa | succ k ih => ?_
have : a ^ 2 = b ^ 2 := add_right_cancel
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := 

Depends on / 依赖: add_comm, add_mul, add_right_cancel, add_right_comm, mul_add, mul_zero, pow_, pow_add, zero_add, zero_mul
-/
lemma Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) :
    a ^ n + b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with | zero => simpa | succ k ih => ?_
have : a ^ 2 = b ^ 2 := add_right_cancel
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := b ^ (2 * k + 1) * a ^ 2) ?_
  calc
    _ = (a ^ (2 * k + 1) + b ^ (2 * k + 1)) * a ^ 2 + b ^ (2 * k + 3) := by
      rw [add_mul]; rw [← pow_add]; rw [add_right_comm]; rfl
    _ = _ := by rw [ih, zero_mul, zero_add, zero_add, this, ← pow_add]

/--
theorem `Even.of_isUnit_two` / 定理 `Even.of_isUnit_two`

English:
theorem Even.of_isUnit_two
  given: (h : IsUnit (2 : α)) (a : α)
  statement: Even a
  proof: let ⟨u, hu⟩ := h; ⟨u⁻¹ * a, by rw [← mul_add, ← two_mul, ← hu, Units.inv_mul_cancel_left]⟩

中文:
定理 Even.of_isUnit_two
  条件: (h : IsUnit (2 : α)) (a : α)
  结论: Even a
  证明: let ⟨u, hu⟩ := h; ⟨u⁻¹ * a, by rw [← mul_add, ← two_mul, ← hu, Units.inv_mul_cancel_left]⟩

Depends on / 依赖: IsAffine, PrespectralSpace, PrimeSpectrum, Scheme, Units.inv_mul_cancel_left, X.affineCover.f, X.affineCover.isOpenCover_opensRange, Y.isoSpec.hom.homeomorph.isClosedEmbedding, affineCover, homeomorph, inv_mul_cancel_left, isAffineOpen_opensRange, isClosedEmbedding, isOpenCover_opensRange, isoSpec, mul_add, of_isClosedEmbedding, of_isOpenCover, opensRange, two_mul
-/
theorem Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Even a :=
  let ⟨u, hu⟩ := h; ⟨u⁻¹ * a, by rw [← mul_add, ← two_mul, ← hu, Units.inv_mul_cancel_left]⟩

/--
theorem `isUnit_two_iff_forall_even` / 定理 `isUnit_two_iff_forall_even`

English:
theorem isUnit_two_iff_forall_even
  statement: IsUnit (2 : α) ↔ forall a : α, Even a
  proof: by
  refine ⟨Even.of_isUnit_two, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h 1
  rw [← two_mul]; rw [eq_comm] at ha
  exact ⟨⟨2, a, ha, .trans (Commute.ofNat_right _ _).eq ha⟩, rfl⟩

中文:
定理 isUnit_two_iff_forall_even
  结论: IsUnit (2 : α) ↔ 对任意 a : α, Even a
  证明: by
  refine ⟨Even.of_isUnit_two, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h 1
  rw [← two_mul]; rw [eq_comm] at ha
  exact ⟨⟨2, a, ha, .trans (Commute.ofNat_right _ _).eq ha⟩, rfl⟩

Depends on / 依赖: Commute, Commute.ofNat_right, Even.of_isUnit_two, eq_comm, ofNat_right, of_isUnit_two, two_mul
-/
theorem isUnit_two_iff_forall_even : IsUnit (2 : α) ↔ forall a : α, Even a := by
  refine ⟨Even.of_isUnit_two, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h 1
  rw [← two_mul]; rw [eq_comm] at ha
  exact ⟨⟨2, a, ha, .trans (Commute.ofNat_right _ _).eq ha⟩, rfl⟩

end Semiring

section Ring
variable [Ring α]

/--
theorem `Odd.of_isUnit_two` / 定理 `Odd.of_isUnit_two`

English:
theorem Odd.of_isUnit_two
  given: (h : IsUnit (2 : α)) (a : α)
  statement: Odd a
  proof: by
  rw [← sub_add_cancel a 1]
  exact (Even.of_isUnit_two h _).add_one

中文:
定理 Odd.of_isUnit_two
  条件: (h : IsUnit (2 : α)) (a : α)
  结论: Odd a
  证明: by
  rw [← sub_add_cancel a 1]
  exact (Even.of_isUnit_two h _).add_one

Depends on / 依赖: Even.of_isUnit_two, add_one, of_isUnit_two, sub_add_cancel
-/
theorem Odd.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Odd a := by
  rw [← sub_add_cancel a 1]
  exact (Even.of_isUnit_two h _).add_one

end Ring

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : Nat}

/--
lemma `Odd.neg_pow` / 引理 `Odd.neg_pow`

English:
lemma Odd.neg_pow
  statement: Odd n -> forall a : α, (-a) ^ n = -a ^ n
  proof: by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]

中文:
引理 Odd.neg_pow
  结论: Odd n -> 对任意 a : α, (-a) ^ n = -a ^ n
  证明: by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]

Depends on / 依赖: mul_neg, neg_sq, pow_add, pow_mul, pow_one, simp_rw
-/
lemma Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]

/--
lemma `Odd.neg_one_pow` / 引理 `Odd.neg_one_pow`

English:
lemma Odd.neg_one_pow
  given: (h : Odd n)
  statement: (-1 : α) ^ n = -1
  proof: by rw [h.neg_pow, one_pow]

中文:
引理 Odd.neg_one_pow
  条件: (h : Odd n)
  结论: (-1 : α) ^ n = -1
  证明: by rw [h.neg_pow, one_pow]
-/
@[simp] lemma Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]

end Monoid

section Ring
variable [Ring α] {a b : α} {n : Nat}

/--
lemma `even_neg_two` / 引理 `even_neg_two`

English:
lemma even_neg_two
  statement: Even (-2 : α)
  proof: by simp only [even_neg, even_two]

中文:
引理 even_neg_two
  结论: Even (-2 : α)
  证明: by simp only [even_neg, even_two]

Depends on / 依赖: even_neg, even_two
-/
lemma even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]

/--
lemma `Odd.neg` / 引理 `Odd.neg`

English:
lemma Odd.neg
  given: (hp : Odd a)
  statement: Odd (-a)
  proof: by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg]; rw [mul_add]; rw [neg_add]; rw [add_assoc]; rw [two_mul (1 : α)]; rw [neg_add]; rw [neg_add_cancel_right]; rw [← neg_add]; rw [hk]

中文:
引理 Odd.neg
  条件: (hp : Odd a)
  结论: Odd (-a)
  证明: by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg]; rw [mul_add]; rw [neg_add]; rw [add_assoc]; rw [two_mul (1 : α)]; rw [neg_add]; rw [neg_add_cancel_right]; rw [← neg_add]; rw [hk]

Depends on / 依赖: add_assoc, mul_add, mul_neg, neg_add, neg_add_cancel_right, two_mul
-/
lemma Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg]; rw [mul_add]; rw [neg_add]; rw [add_assoc]; rw [two_mul (1 : α)]; rw [neg_add]; rw [neg_add_cancel_right]; rw [← neg_add]; rw [hk]

/--
lemma `odd_neg` / 引理 `odd_neg`

English:
lemma odd_neg
  statement: Odd (-a) ↔ Odd a
  proof: ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩

中文:
引理 odd_neg
  结论: Odd (-a) ↔ Odd a
  证明: ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩

Depends on / 依赖: isReduced_of_isOpenImmersion
-/
@[simp] lemma odd_neg : Odd (-a) ↔ Odd a := ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩

/--
lemma `odd_neg_one` / 引理 `odd_neg_one`

English:
lemma odd_neg_one
  statement: Odd (-1 : α)
  proof: by simp

中文:
引理 odd_neg_one
  结论: Odd (-1 : α)
  证明: by simp

Depends on / 依赖: isReduced_of_isOpenImmersion
-/
lemma odd_neg_one : Odd (-1 : α) := by simp

/--
lemma `Odd.sub_even` / 引理 `Odd.sub_even`

English:
lemma Odd.sub_even
  given: (ha : Odd a) (hb : Even b)
  statement: Odd (a - b)
  proof: by
  rw [sub_eq_add_neg]; exact ha.add_even hb.neg

中文:
引理 Odd.sub_even
  条件: (ha : Odd a) (hb : Even b)
  结论: Odd (a - b)
  证明: by
  rw [sub_eq_add_neg]; exact ha.add_even hb.neg

Depends on / 依赖: add_even, ha.add_even, hb.neg, sub_eq_add_neg
-/
lemma Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_even hb.neg

/--
lemma `Even.sub_odd` / 引理 `Even.sub_odd`

English:
lemma Even.sub_odd
  given: (ha : Even a) (hb : Odd b)
  statement: Odd (a - b)
  proof: by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

中文:
引理 Even.sub_odd
  条件: (ha : Even a) (hb : Odd b)
  结论: Odd (a - b)
  证明: by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

Depends on / 依赖: AtPrime, CommRingCat, CommRingCat.of, IsReduced, Localization, Localization.AtPrime, PrimeSpectrum, PrimeSpectrum.asIdeal, Spec.stalkIso, _root_, _root_.IsReduced, add_odd, allowSynthFailures, asIdeal, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.injective, ha.add_odd, hb.neg, hom.hom, infer_instance
-/
lemma Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

/--
lemma `Odd.sub_odd` / 引理 `Odd.sub_odd`

English:
lemma Odd.sub_odd
  given: (ha : Odd a) (hb : Odd b)
  statement: Even (a - b)
  proof: by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

@[simp]

中文:
引理 Odd.sub_odd
  条件: (ha : Odd a) (hb : Odd b)
  结论: Even (a - b)
  证明: by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

@[simp]

Depends on / 依赖: add_odd, ha.add_odd, hb.neg, sub_eq_add_neg
-/
lemma Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

@[simp]
/--
lemma `even_add_one` / 引理 `even_add_one`

English:
lemma even_add_one
  statement: Even (a + 1) ↔ Odd a
  proof: ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]

中文:
引理 even_add_one
  结论: Even (a + 1) ↔ Odd a
  证明: ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]

Depends on / 依赖: add_one, convert, eq_sub_iff_add_eq, odd_one, sub_odd
-/
lemma even_add_one : Even (a + 1) ↔ Odd a :=
  ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]
/--
lemma `even_sub_one` / 引理 `even_sub_one`

English:
lemma even_sub_one
  statement: Even (a - 1) ↔ Odd a
  proof: ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]

中文:
引理 even_sub_one
  结论: Even (a - 1) ↔ Odd a
  证明: ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]

Depends on / 依赖: add_odd, convert, odd_one, sub_add_cancel, sub_odd
-/
lemma even_sub_one : Even (a - 1) ↔ Odd a :=
  ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]
/--
lemma `even_add_two` / 引理 `even_add_two`

English:
lemma even_add_two
  statement: Even (a + 2) ↔ Even a
  proof: ⟨(by convert! ·.sub even_two; rw [eq_sub_iff_add_eq]), (·.add even_two)⟩

@[simp]

中文:
引理 even_add_two
  结论: Even (a + 2) ↔ Even a
  证明: ⟨(by convert! ·.sub even_two; rw [eq_sub_iff_add_eq]), (·.add even_two)⟩

@[simp]

Depends on / 依赖: convert, eq_sub_iff_add_eq, even_two
-/
lemma even_add_two : Even (a + 2) ↔ Even a :=
  ⟨(by convert! ·.sub even_two; rw [eq_sub_iff_add_eq]), (·.add even_two)⟩

@[simp]
/--
lemma `even_sub_two` / 引理 `even_sub_two`

English:
lemma even_sub_two
  statement: Even (a - 2) ↔ Even a
  proof: ⟨(by convert! ·.add even_two; rw [sub_add_cancel]), (·.sub even_two)⟩

@[simp]

中文:
引理 even_sub_two
  结论: Even (a - 2) ↔ Even a
  证明: ⟨(by convert! ·.add even_two; rw [sub_add_cancel]), (·.sub even_two)⟩

@[simp]

Depends on / 依赖: convert, even_two, sub_add_cancel
-/
lemma even_sub_two : Even (a - 2) ↔ Even a :=
  ⟨(by convert! ·.add even_two; rw [sub_add_cancel]), (·.sub even_two)⟩

@[simp]
/--
lemma `odd_add_one` / 引理 `odd_add_one`

English:
lemma odd_add_one
  statement: Odd (a + 1) ↔ Even a
  proof: ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]

中文:
引理 odd_add_one
  结论: Odd (a + 1) ↔ Even a
  证明: ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]

Depends on / 依赖: add_one, convert, eq_sub_iff_add_eq, odd_one, sub_odd
-/
lemma odd_add_one : Odd (a + 1) ↔ Even a :=
  ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]
/--
lemma `odd_sub_one` / 引理 `odd_sub_one`

English:
lemma odd_sub_one
  statement: Odd (a - 1) ↔ Even a
  proof: ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]

中文:
引理 odd_sub_one
  结论: Odd (a - 1) ↔ Even a
  证明: ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]

Depends on / 依赖: add_odd, convert, odd_one, sub_add_cancel, sub_odd
-/
lemma odd_sub_one : Odd (a - 1) ↔ Even a :=
  ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]
/--
lemma `odd_add_two` / 引理 `odd_add_two`

English:
lemma odd_add_two
  statement: Odd (a + 2) ↔ Odd a
  proof: by
  rw [← one_add_one_eq_two]; rw [← add_assoc]; rw [odd_add_one]; rw [even_add_one]

@[simp]

中文:
引理 odd_add_two
  结论: Odd (a + 2) ↔ Odd a
  证明: by
  rw [← one_add_one_eq_two]; rw [← add_assoc]; rw [odd_add_one]; rw [even_add_one]

@[simp]

Depends on / 依赖: add_assoc, even_add_one, odd_add_one, one_add_one_eq_two
-/
lemma odd_add_two : Odd (a + 2) ↔ Odd a := by
  rw [← one_add_one_eq_two]; rw [← add_assoc]; rw [odd_add_one]; rw [even_add_one]

@[simp]
/--
lemma `odd_sub_two` / 引理 `odd_sub_two`

English:
lemma odd_sub_two
  statement: Odd (a - 2) ↔ Odd a
  proof: by
  rw [← odd_add_two (a := a - 2)]; rw [add_comm_sub]; rw [sub_self]; rw [add_zero]

中文:
引理 odd_sub_two
  结论: Odd (a - 2) ↔ Odd a
  证明: by
  rw [← odd_add_two (a := a - 2)]; rw [add_comm_sub]; rw [sub_self]; rw [add_zero]

Depends on / 依赖: add_comm_sub, add_zero, odd_add_two, sub_self
-/
lemma odd_sub_two : Odd (a - 2) ↔ Odd a := by
  rw [← odd_add_two (a := a - 2)]; rw [add_comm_sub]; rw [sub_self]; rw [add_zero]

end Ring

namespace Nat
variable {m n : Nat}

@[grind =]
/--
lemma `odd_iff` / 引理 `odd_iff`

English:
lemma odd_iff
  statement: Odd n ↔ n % 2 = 1
  proof: ⟨fun ⟨m, hm⟩ => by lia, fun h => ⟨n / 2, by lia⟩⟩

中文:
引理 odd_iff
  结论: Odd n ↔ n % 2 = 1
  证明: ⟨fun ⟨m, hm⟩ => by lia, fun h => ⟨n / 2, by lia⟩⟩
-/
lemma odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by lia, fun h => ⟨n / 2, by lia⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (Odd : Nat -> Prop)
  body: fun _ => decidable_of_iff _ odd_iff.symm

中文:
实例 :
  签名: DecidablePred (Odd : 自然数 -> 命题)
  定义体: fun _ => decidable_of_iff _ odd_iff.symm

Depends on / 依赖: decidable_of_iff, odd_iff, odd_iff.symm
-/
instance : DecidablePred (Odd : Nat -> Prop) := fun _ => decidable_of_iff _ odd_iff.symm

/--
lemma `not_odd_iff` / 引理 `not_odd_iff`

English:
lemma not_odd_iff
  statement: ¬Odd n ↔ n % 2 = 0
  proof: by grind

中文:
引理 not_odd_iff
  结论: ¬Odd n ↔ n % 2 = 0
  证明: by grind

Depends on / 依赖: CommRingCat, CommRingCat.subsingleton_of_isTerminal, IsIntegral, IsReduced, Nonempty, SetLike, SetLike.ext, Subsingleton, X.sheaf.isTerminalOfEqEmpty, eq_empty_or_nonempty, infer_instance, isReduced_of_isIntegral, isTerminalOfEqEmpty, subsingleton_of_isTerminal
-/
lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind

/--
lemma `not_odd_iff_even` / 引理 `not_odd_iff_even`

English:
lemma not_odd_iff_even
  statement: ¬Odd n ↔ Even n
  proof: by grind

中文:
引理 not_odd_iff_even
  结论: ¬Odd n ↔ Even n
  证明: by grind
-/
@[simp, grind =] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by grind
/--
lemma `not_even_iff_odd` / 引理 `not_even_iff_odd`

English:
lemma not_even_iff_odd
  statement: ¬Even n ↔ Odd n
  proof: by grind

中文:
引理 not_even_iff_odd
  结论: ¬Even n ↔ Odd n
  证明: by grind
-/
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by grind

/--
lemma `not_odd_zero` / 引理 `not_odd_zero`

English:
lemma not_odd_zero
  statement: ¬Odd 0
  proof: by grind

中文:
引理 not_odd_zero
  结论: ¬Odd 0
  证明: by grind
-/
@[simp] lemma not_odd_zero : ¬Odd 0 := by grind

/--
lemma `_root_.Odd.not_two_dvd_nat` / 引理 `_root_.Odd.not_two_dvd_nat`

English:
lemma _root_.Odd.not_two_dvd_nat
  given: (h : Odd n)
  statement: ¬(2 ∣ n)
  proof: by grind

中文:
引理 _root_.Odd.not_two_dvd_nat
  条件: (h : Odd n)
  结论: ¬(2 ∣ n)
  证明: by grind
-/
lemma _root_.Odd.not_two_dvd_nat (h : Odd n) : ¬(2 ∣ n) := by grind

/--
lemma `even_xor_odd` / 引理 `even_xor_odd`

English:
lemma even_xor_odd
  given: (n : Nat)
  statement: Xor (Even n) (Odd n)
  proof: by grind

中文:
引理 even_xor_odd
  条件: (n : 自然数)
  结论: Xor (Even n) (Odd n)
  证明: by grind
-/
lemma even_xor_odd (n : Nat) : Xor (Even n) (Odd n) := by grind

/--
lemma `even_or_odd` / 引理 `even_or_odd`

English:
lemma even_or_odd
  given: (n : Nat)
  statement: Even n ∨ Odd n
  proof: (even_xor_odd n).or

中文:
引理 even_or_odd
  条件: (n : 自然数)
  结论: Even n ∨ Odd n
  证明: (even_xor_odd n).or

Depends on / 依赖: even_xor_odd
-/
lemma even_or_odd (n : Nat) : Even n ∨ Odd n := (even_xor_odd n).or

/--
lemma `even_or_odd'` / 引理 `even_or_odd'`

English:
lemma even_or_odd'
  given: (n : Nat)
  statement: exists k, n = 2 * k ∨ n = 2 * k + 1
  proof: by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n

中文:
引理 even_or_odd'
  条件: (n : 自然数)
  结论: 存在 k, n = 2 * k ∨ n = 2 * k + 1
  证明: by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.irreducibleSpace, convert, even_or_odd, exists_or, irreducibleSpace, two_mul
-/
lemma even_or_odd' (n : Nat) : exists k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n

/--
lemma `even_xor_odd'` / 引理 `even_xor_odd'`

English:
lemma even_xor_odd'
  given: (n : Nat)
  statement: exists k, Xor (n = 2 * k) (n = 2 * k + 1)
  proof: by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;>
  · use k
    grind

中文:
引理 even_xor_odd'
  条件: (n : 自然数)
  结论: 存在 k, Xor (n = 2 * k) (n = 2 * k + 1)
  证明: by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;>
  · use k
    grind

Depends on / 依赖: even_or_odd, isIntegral_of_irreducibleSpace_of_isReduced
-/
lemma even_xor_odd' (n : Nat) : exists k, Xor (n = 2 * k) (n = 2 * k + 1) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;>
  · use k
    grind

/--
lemma `odd_add_one` / 引理 `odd_add_one`

English:
lemma odd_add_one
  given: {n : Nat}
  statement: Odd (n + 1) ↔ ¬ Odd n
  proof: by grind

中文:
引理 odd_add_one
  条件: {n : 自然数}
  结论: Odd (n + 1) ↔ ¬ Odd n
  证明: by grind
-/
lemma odd_add_one {n : Nat} : Odd (n + 1) ↔ ¬ Odd n := by grind

/--
lemma `mod_two_add_add_odd_mod_two` / 引理 `mod_two_add_add_odd_mod_two`

English:
lemma mod_two_add_add_odd_mod_two
  given: (m : Nat) {n : Nat} (hn : Odd n)
  statement: m % 2 + (m + n) % 2 = 1
  proof: by grind

中文:
引理 mod_two_add_add_odd_mod_two
  条件: (m : 自然数) {n : 自然数} (hn : Odd n)
  结论: m % 2 + (m + n) % 2 = 1
  证明: by grind
-/
lemma mod_two_add_add_odd_mod_two (m : Nat) {n : Nat} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 := by grind

/--
lemma `mod_two_add_succ_mod_two` / 引理 `mod_two_add_succ_mod_two`

English:
lemma mod_two_add_succ_mod_two
  given: (m : Nat)
  statement: m % 2 + (m + 1) % 2 = 1
  proof: by lia

中文:
引理 mod_two_add_succ_mod_two
  条件: (m : 自然数)
  结论: m % 2 + (m + 1) % 2 = 1
  证明: by lia
-/
@[simp] lemma mod_two_add_succ_mod_two (m : Nat) : m % 2 + (m + 1) % 2 = 1 := by lia

/--
lemma `succ_mod_two_add_mod_two` / 引理 `succ_mod_two_add_mod_two`

English:
lemma succ_mod_two_add_mod_two
  given: (m : Nat)
  statement: (m + 1) % 2 + m % 2 = 1
  proof: by lia

中文:
引理 succ_mod_two_add_mod_two
  条件: (m : 自然数)
  结论: (m + 1) % 2 + m % 2 = 1
  证明: by lia
-/
@[simp] lemma succ_mod_two_add_mod_two (m : Nat) : (m + 1) % 2 + m % 2 = 1 := by lia

/--
lemma `even_add'` / 引理 `even_add'`

English:
lemma even_add'
  statement: Even (m + n) ↔ (Odd m ↔ Odd n)
  proof: by grind

中文:
引理 even_add'
  结论: Even (m + n) ↔ (Odd m ↔ Odd n)
  证明: by grind
-/
lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind

/--
lemma `not_even_bit1` / 引理 `not_even_bit1`

English:
lemma not_even_bit1
  given: (n : Nat)
  statement: ¬Even (2 * n + 1)
  proof: by simp [parity_simps]

中文:
引理 not_even_bit1
  条件: (n : 自然数)
  结论: ¬Even (2 * n + 1)
  证明: by simp [parity_simps]
-/
@[simp] lemma not_even_bit1 (n : Nat) : ¬Even (2 * n + 1) := by simp [parity_simps]

/--
lemma `not_even_two_mul_add_one` / 引理 `not_even_two_mul_add_one`

English:
lemma not_even_two_mul_add_one
  given: (n : Nat)
  statement: ¬ Even (2 * n + 1)
  proof: by grind

中文:
引理 not_even_two_mul_add_one
  条件: (n : 自然数)
  结论: ¬ Even (2 * n + 1)
  证明: by grind
-/
lemma not_even_two_mul_add_one (n : Nat) : ¬ Even (2 * n + 1) := by grind

/--
lemma `even_sub'` / 引理 `even_sub'`

English:
lemma even_sub'
  given: (h : n <= m)
  statement: Even (m - n) ↔ (Odd m ↔ Odd n)
  proof: by grind

中文:
引理 even_sub'
  条件: (h : n <= m)
  结论: Even (m - n) ↔ (Odd m ↔ Odd n)
  证明: by grind
-/
lemma even_sub' (h : n <= m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind

/--
lemma `Odd.sub_odd` / 引理 `Odd.sub_odd`

English:
lemma Odd.sub_odd
  given: (hm : Odd m) (hn : Odd n)
  statement: Even (m - n)
  proof: by grind

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd

中文:
引理 Odd.sub_odd
  条件: (hm : Odd m) (hn : Odd n)
  结论: Even (m - n)
  证明: by grind

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd
-/
lemma Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) := by grind

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd

/--
lemma `odd_mul` / 引理 `odd_mul`

English:
lemma odd_mul
  statement: Odd (m * n) ↔ Odd m ∧ Odd n
  proof: by grind

中文:
引理 odd_mul
  结论: Odd (m * n) ↔ Odd m ∧ Odd n
  证明: by grind
-/
lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by grind

/--
lemma `Odd.of_mul_left` / 引理 `Odd.of_mul_left`

English:
lemma Odd.of_mul_left
  given: (h : Odd (m * n))
  statement: Odd m
  proof: (odd_mul.mp h).1

中文:
引理 Odd.of_mul_left
  条件: (h : Odd (m * n))
  结论: Odd m
  证明: (odd_mul.mp h).1

Depends on / 依赖: odd_mul, odd_mul.mp
-/
lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1

/--
lemma `Odd.of_mul_right` / 引理 `Odd.of_mul_right`

English:
lemma Odd.of_mul_right
  given: (h : Odd (m * n))
  statement: Odd n
  proof: (odd_mul.mp h).2

中文:
引理 Odd.of_mul_right
  条件: (h : Odd (m * n))
  结论: Odd n
  证明: (odd_mul.mp h).2

Depends on / 依赖: CommRingCat, CommRingCat.nontrivial_of_isPushout_of_isField, Field.toIsField, IsPushout, IsPushout.of_hasPushout, nontrivial_of_isPushout_of_isField, odd_mul, odd_mul.mp, of_hasPushout, toIsField
-/
lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2

/--
lemma `odd_pow_iff` / 引理 `odd_pow_iff`

English:
lemma odd_pow_iff
  given: {e : Nat} (he : e != 0)
  statement: Odd (n ^ e) ↔ Odd n
  proof: by grind

中文:
引理 odd_pow_iff
  条件: {e : 自然数} (he : e != 0)
  结论: Odd (n ^ e) ↔ Odd n
  证明: by grind
-/
lemma odd_pow_iff {e : Nat} (he : e != 0) : Odd (n ^ e) ↔ Odd n := by grind

/--
lemma `even_div` / 引理 `even_div`

English:
lemma even_div
  statement: Even (m / n) ↔ m % (2 * n) / n = 0
  proof: by
  rw [even_iff_two_dvd]; rw [dvd_iff_mod_eq_zero]; rw [← Nat.mod_mul_right_div_self]; rw [mul_comm]

中文:
引理 even_div
  结论: Even (m / n) ↔ m % (2 * n) / n = 0
  证明: by
  rw [even_iff_two_dvd]; rw [dvd_iff_mod_eq_zero]; rw [← Nat.mod_mul_right_div_self]; rw [mul_comm]

Depends on / 依赖: Nat.mod_mul_right_div_self, dvd_iff_mod_eq_zero, even_iff_two_dvd, mod_mul_right_div_self, mul_comm
-/
lemma even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd]; rw [dvd_iff_mod_eq_zero]; rw [← Nat.mod_mul_right_div_self]; rw [mul_comm]

/--
lemma `odd_add` / 引理 `odd_add`

English:
lemma odd_add
  statement: Odd (m + n) ↔ (Odd m ↔ Even n)
  proof: by grind

中文:
引理 odd_add
  结论: Odd (m + n) ↔ (Odd m ↔ Even n)
  证明: by grind
-/
@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by grind

/--
lemma `odd_add'` / 引理 `odd_add'`

English:
lemma odd_add'
  statement: Odd (m + n) ↔ (Odd n ↔ Even m)
  proof: by grind

中文:
引理 odd_add'
  结论: Odd (m + n) ↔ (Odd n ↔ Even m)
  证明: by grind
-/
lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind

/--
lemma `ne_of_odd_add` / 引理 `ne_of_odd_add`

English:
lemma ne_of_odd_add
  given: (h : Odd (m + n))
  statement: m != n
  proof: by grind

中文:
引理 ne_of_odd_add
  条件: (h : Odd (m + n))
  结论: m != n
  证明: by grind
-/
lemma ne_of_odd_add (h : Odd (m + n)) : m != n := by grind

/--
lemma `odd_sub` / 引理 `odd_sub`

English:
lemma odd_sub
  given: (h : n <= m)
  statement: Odd (m - n) ↔ (Odd m ↔ Even n)
  proof: by grind

中文:
引理 odd_sub
  条件: (h : n <= m)
  结论: Odd (m - n) ↔ (Odd m ↔ Even n)
  证明: by grind
-/
@[parity_simps] lemma odd_sub (h : n <= m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by grind

/--
lemma `Odd.sub_even` / 引理 `Odd.sub_even`

English:
lemma Odd.sub_even
  given: (h : n <= m) (hm : Odd m) (hn : Even n)
  statement: Odd (m - n)
  proof: by grind

中文:
引理 Odd.sub_even
  条件: (h : n <= m) (hm : Odd m) (hn : Even n)
  结论: Odd (m - n)
  证明: by grind
-/
lemma Odd.sub_even (h : n <= m) (hm : Odd m) (hn : Even n) : Odd (m - n) := by grind

/--
lemma `odd_sub'` / 引理 `odd_sub'`

English:
lemma odd_sub'
  given: (h : n <= m)
  statement: Odd (m - n) ↔ (Odd n ↔ Even m)
  proof: by grind

中文:
引理 odd_sub'
  条件: (h : n <= m)
  结论: Odd (m - n) ↔ (Odd n ↔ Even m)
  证明: by grind
-/
lemma odd_sub' (h : n <= m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind

/--
lemma `Even.sub_odd` / 引理 `Even.sub_odd`

English:
lemma Even.sub_odd
  given: (h : n <= m) (hm : Even m) (hn : Odd n)
  statement: Odd (m - n)
  proof: by grind

中文:
引理 Even.sub_odd
  条件: (h : n <= m) (hm : Even m) (hn : Odd n)
  结论: Odd (m - n)
  证明: by grind
-/
lemma Even.sub_odd (h : n <= m) (hm : Even m) (hn : Odd n) : Odd (m - n) := by grind

/--
lemma `two_mul_div_two_add_one_of_odd` / 引理 `two_mul_div_two_add_one_of_odd`

English:
lemma two_mul_div_two_add_one_of_odd
  given: (h : Odd n)
  statement: 2 * (n / 2) + 1 = n
  proof: by grind

中文:
引理 two_mul_div_two_add_one_of_odd
  条件: (h : Odd n)
  结论: 2 * (n / 2) + 1 = n
  证明: by grind
-/
lemma two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by grind

/--
lemma `div_two_mul_two_add_one_of_odd` / 引理 `div_two_mul_two_add_one_of_odd`

English:
lemma div_two_mul_two_add_one_of_odd
  given: (h : Odd n)
  statement: n / 2 * 2 + 1 = n
  proof: by grind

中文:
引理 div_two_mul_two_add_one_of_odd
  条件: (h : Odd n)
  结论: n / 2 * 2 + 1 = n
  证明: by grind
-/
lemma div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n := by grind

/--
lemma `one_add_div_two_mul_two_of_odd` / 引理 `one_add_div_two_mul_two_of_odd`

English:
lemma one_add_div_two_mul_two_of_odd
  given: (h : Odd n)
  statement: 1 + n / 2 * 2 = n
  proof: by grind

中文:
引理 one_add_div_two_mul_two_of_odd
  条件: (h : Odd n)
  结论: 1 + n / 2 * 2 = n
  证明: by grind
-/
lemma one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n := by grind

/--
lemma `two_dvd_mul_add_one` / 引理 `two_dvd_mul_add_one`

English:
lemma two_dvd_mul_add_one
  given: (k : Nat)
  statement: 2 ∣ k * (k + 1)
  proof: even_iff_two_dvd.mp (even_mul_succ_self k)

中文:
引理 two_dvd_mul_add_one
  条件: (k : 自然数)
  结论: 2 ∣ k * (k + 1)
  证明: even_iff_two_dvd.mp (even_mul_succ_self k)

Depends on / 依赖: even_iff_two_dvd, even_iff_two_dvd.mp, even_mul_succ_self
-/
lemma two_dvd_mul_add_one (k : Nat) : 2 ∣ k * (k + 1) :=
  even_iff_two_dvd.mp (even_mul_succ_self k)

/--
lemma `two_dvd_mul_sub_one` / 引理 `two_dvd_mul_sub_one`

English:
lemma two_dvd_mul_sub_one
  given: (k : Nat)
  statement: 2 ∣ k * (k - 1)
  proof: by
  rcases k with rfl | k; · simp
  simpa [mul_comm (k + 1)] using k.two_dvd_mul_add_one

中文:
引理 two_dvd_mul_sub_one
  条件: (k : 自然数)
  结论: 2 ∣ k * (k - 1)
  证明: by
  rcases k with rfl | k; · simp
  simpa [mul_comm (k + 1)] using k.two_dvd_mul_add_one

Depends on / 依赖: k.two_dvd_mul_add_one, mul_comm, two_dvd_mul_add_one
-/
lemma two_dvd_mul_sub_one (k : Nat) : 2 ∣ k * (k - 1) := by
  rcases k with rfl | k; · simp
  simpa [mul_comm (k + 1)] using k.two_dvd_mul_add_one

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : Nat) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, parity_simps]

example : ¬Even 25394535 := by decide

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type*} {f : α -> α} {n : Nat}

/--
lemma `iterate_two_mul` / 引理 `iterate_two_mul`

English:
lemma iterate_two_mul
  given: (hf : Involutive f) (n : Nat)
  statement: f^[2 * n] = id
  proof: by
  rw [iterate_mul]; rw [involutive_iff_iter_2_eq_id.1 hf]; rw [iterate_id]

中文:
引理 iterate_two_mul
  条件: (hf : Involutive f) (n : 自然数)
  结论: f^[2 * n] = id
  证明: by
  rw [iterate_mul]; rw [involutive_iff_iter_2_eq_id.1 hf]; rw [iterate_id]

Depends on / 依赖: involutive_iff_iter_2_eq_id, iterate_id, iterate_mul
-/
lemma iterate_two_mul (hf : Involutive f) (n : Nat) : f^[2 * n] = id := by
  rw [iterate_mul]; rw [involutive_iff_iter_2_eq_id.1 hf]; rw [iterate_id]

/--
lemma `iterate_two_mul_add_one` / 引理 `iterate_two_mul_add_one`

English:
lemma iterate_two_mul_add_one
  given: (hf : Involutive f) (n : Nat)
  statement: f^[2 * n + 1] = f
  proof: by
  rw [iterate_succ]; rw [hf.iterate_two_mul]; rw [id_comp]

中文:
引理 iterate_two_mul_add_one
  条件: (hf : Involutive f) (n : 自然数)
  结论: f^[2 * n + 1] = f
  证明: by
  rw [iterate_succ]; rw [hf.iterate_two_mul]; rw [id_comp]

Depends on / 依赖: hf.iterate_two_mul, id_comp, iterate_succ, iterate_two_mul
-/
lemma iterate_two_mul_add_one (hf : Involutive f) (n : Nat) : f^[2 * n + 1] = f := by
  rw [iterate_succ]; rw [hf.iterate_two_mul]; rw [id_comp]

/--
lemma `iterate_even` / 引理 `iterate_even`

English:
lemma iterate_even
  given: (hf : Involutive f) (hn : Even n)
  statement: f^[n] = id
  proof: by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul]; rw [hf.iterate_two_mul]

中文:
引理 iterate_even
  条件: (hf : Involutive f) (hn : Even n)
  结论: f^[n] = id
  证明: by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul]; rw [hf.iterate_two_mul]

Depends on / 依赖: hf.iterate_two_mul, iterate_two_mul, two_mul
-/
lemma iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul]; rw [hf.iterate_two_mul]

/--
lemma `iterate_odd` / 引理 `iterate_odd`

English:
lemma iterate_odd
  given: (hf : Involutive f) (hn : Odd n)
  statement: f^[n] = f
  proof: by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add]; rw [hf.iterate_two_mul]; rw [id_comp]; rw [iterate_one]

中文:
引理 iterate_odd
  条件: (hf : Involutive f) (hn : Odd n)
  结论: f^[n] = f
  证明: by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add]; rw [hf.iterate_two_mul]; rw [id_comp]; rw [iterate_one]

Depends on / 依赖: hf.iterate_two_mul, id_comp, iterate_add, iterate_one, iterate_two_mul
-/
lemma iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f := by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add]; rw [hf.iterate_two_mul]; rw [id_comp]; rw [iterate_one]

/--
lemma `iterate_eq_self` / 引理 `iterate_eq_self`

English:
lemma iterate_eq_self
  given: (hf : Involutive f) (hne : f != id)
  statement: f^[n] = f ↔ Odd n
  proof: ⟨fun H => not_even_iff_odd.1 fun hn => hne by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩

中文:
引理 iterate_eq_self
  条件: (hf : Involutive f) (hne : f != id)
  结论: f^[n] = f ↔ Odd n
  证明: ⟨fun H => not_even_iff_odd.1 fun hn => hne by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩

Depends on / 依赖: eq_comm, hf.iterate_even, hf.iterate_odd, iterate_even, iterate_odd, not_even_iff_odd
-/
lemma iterate_eq_self (hf : Involutive f) (hne : f != id) : f^[n] = f ↔ Odd n :=
⟨fun H => not_even_iff_odd.1 fun hn => hne by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩

/--
lemma `iterate_eq_id` / 引理 `iterate_eq_id`

English:
lemma iterate_eq_id
  given: (hf : Involutive f) (hne : f != id)
  statement: f^[n] = id ↔ Even n
  proof: ⟨fun H => not_odd_iff_even.1 fun hn => hne by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

中文:
引理 iterate_eq_id
  条件: (hf : Involutive f) (hne : f != id)
  结论: f^[n] = id ↔ Even n
  证明: ⟨fun H => not_odd_iff_even.1 fun hn => hne by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

Depends on / 依赖: hf.iterate_even, hf.iterate_odd, iterate_even, iterate_odd, not_odd_iff_even
-/
lemma iterate_eq_id (hf : Involutive f) (hne : f != id) : f^[n] = id ↔ Even n :=
⟨fun H => not_odd_iff_even.1 fun hn => hne by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

end Involutive
end Function

section DistribNeg

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : Nat}

/--
lemma `neg_one_pow_eq_ite` / 引理 `neg_one_pow_eq_ite`

English:
lemma neg_one_pow_eq_ite
  statement: (-1 : R) ^ n = if Even n then 1 else (-1)
  proof: by
  cases even_or_odd n with
  | inl h => rw [h.neg_one_pow, if_pos h]
  | inr h => rw [h.neg_one_pow, if_neg (by simpa using h)]

中文:
引理 neg_one_pow_eq_ite
  结论: (-1 : R) ^ n = if Even n then 1 else (-1)
  证明: by
  cases even_or_odd n with
  | inl h => rw [h.neg_one_pow, if_pos h]
  | inr h => rw [h.neg_one_pow, if_neg (by simpa using h)]

Depends on / 依赖: even_or_odd, h.neg_one_pow, if_neg, if_pos, neg_one_pow
-/
lemma neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1 else (-1) := by
  cases even_or_odd n with
  | inl h => rw [h.neg_one_pow, if_pos h]
  | inr h => rw [h.neg_one_pow, if_neg (by simpa using h)]

/--
lemma `neg_one_pow_congr` / 引理 `neg_one_pow_congr`

English:
lemma neg_one_pow_congr
  given: (h : Even m ↔ Even n)
  statement: (-1 : R) ^ m = (-1) ^ n
  proof: by
  simp [h, neg_one_pow_eq_ite]

中文:
引理 neg_one_pow_congr
  条件: (h : Even m ↔ Even n)
  结论: (-1 : R) ^ m = (-1) ^ n
  证明: by
  simp [h, neg_one_pow_eq_ite]

Depends on / 依赖: neg_one_pow_eq_ite
-/
lemma neg_one_pow_congr (h : Even m ↔ Even n) : (-1 : R) ^ m = (-1) ^ n := by
  simp [h, neg_one_pow_eq_ite]

/--
lemma `neg_one_pow_eq_one_iff_even` / 引理 `neg_one_pow_eq_one_iff_even`

English:
lemma neg_one_pow_eq_one_iff_even
  given: (h : (-1 : R) != 1)
  proof: by simp [neg_one_pow_eq_ite, h]

中文:
引理 neg_one_pow_eq_one_iff_even
  条件: (h : (-1 : R) != 1)
  证明: by simp [neg_one_pow_eq_ite, h]

Depends on / 依赖: neg_one_pow_eq_ite
-/
lemma neg_one_pow_eq_one_iff_even (h : (-1 : R) != 1) :
    (-1 : R) ^ n = 1 ↔ Even n := by simp [neg_one_pow_eq_ite, h]

/--
lemma `neg_one_pow_eq_neg_one_iff_odd` / 引理 `neg_one_pow_eq_neg_one_iff_odd`

English:
lemma neg_one_pow_eq_neg_one_iff_odd
  given: (h : (-1 : R) != 1)
  proof: by simp [neg_one_pow_eq_ite, h.symm]

中文:
引理 neg_one_pow_eq_neg_one_iff_odd
  条件: (h : (-1 : R) != 1)
  证明: by simp [neg_one_pow_eq_ite, h.symm]

Depends on / 依赖: h.symm, neg_one_pow_eq_ite
-/
lemma neg_one_pow_eq_neg_one_iff_odd (h : (-1 : R) != 1) :
    (-1 : R) ^ n = -1 ↔ Odd n := by simp [neg_one_pow_eq_ite, h.symm]

end DistribNeg

section DivisionMonoid
variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : Int}

/--
lemma `Even.neg_zpow` / 引理 `Even.neg_zpow`

English:
lemma Even.neg_zpow
  statement: Even n -> forall a : α, (-a) ^ n = a ^ n
  proof: by
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]

中文:
引理 Even.neg_zpow
  结论: Even n -> 对任意 a : α, (-a) ^ n = a ^ n
  证明: by
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]

Depends on / 依赖: Int.two_mul, neg_mul_neg, simp_rw, two_mul, zpow_mul, zpow_two
-/
lemma Even.neg_zpow : Even n -> forall a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]

/--
lemma `Even.neg_one_zpow` / 引理 `Even.neg_one_zpow`

English:
lemma Even.neg_one_zpow
  given: (h : Even n)
  statement: (-1 : α) ^ n = 1
  proof: by rw [h.neg_zpow, one_zpow]

中文:
引理 Even.neg_one_zpow
  条件: (h : Even n)
  结论: (-1 : α) ^ n = 1
  证明: by rw [h.neg_zpow, one_zpow]

Depends on / 依赖: h.neg_zpow, neg_zpow, one_zpow
-/
lemma Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]

/--
lemma `neg_one_zpow_eq_ite` / 引理 `neg_one_zpow_eq_ite`

English:
lemma neg_one_zpow_eq_ite
  statement: (-1 : α) ^ n = if Even n then 1 else -1
  proof: by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [neg_one_pow_eq_ite]))

中文:
引理 neg_one_zpow_eq_ite
  结论: (-1 : α) ^ n = if Even n then 1 else -1
  证明: by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [neg_one_pow_eq_ite]))

Depends on / 依赖: eq_nat_or_neg, n.eq_nat_or_neg, neg_one_pow_eq_ite
-/
lemma neg_one_zpow_eq_ite : (-1 : α) ^ n = if Even n then 1 else -1 := by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [neg_one_pow_eq_ite]))

end DivisionMonoid

section CharTwo

-- We state the following theorems in terms of the slightly more general `2 = 0` hypothesis.

variable {R : Type*} [AddMonoidWithOne R]

/--
theorem `natCast_eq_zero_or_one_of_two_eq_zero'` / 定理 `natCast_eq_zero_or_one_of_two_eq_zero'`

English:
theorem natCast_eq_zero_or_one_of_two_eq_zero'
  given: (n : Nat) (h : (2 : R) = 0)
  proof: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ _ => simpa [add_assoc, Nat.even_add_one, Nat.odd_add_one, h]

中文:
定理 natCast_eq_zero_or_one_of_two_eq_zero'
  条件: (n : 自然数) (h : (2 : R) = 0)
  证明: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ _ => simpa [add_assoc, Nat.even_add_one, Nat.odd_add_one, h]
-/
private theorem natCast_eq_zero_or_one_of_two_eq_zero' (n : Nat) (h : (2 : R) = 0) :
    (Even n -> (n : R) = 0) ∧ (Odd n -> (n : R) = 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ _ => simpa [add_assoc, Nat.even_add_one, Nat.odd_add_one, h]

/--
theorem `natCast_eq_zero_of_even_of_two_eq_zero` / 定理 `natCast_eq_zero_of_even_of_two_eq_zero`

English:
theorem natCast_eq_zero_of_even_of_two_eq_zero
  given: {n : Nat} (hn : Even n) (h : (2 : R) = 0)
  proof: (natCast_eq_zero_or_one_of_two_eq_zero' n h).1 hn

中文:
定理 natCast_eq_zero_of_even_of_two_eq_zero
  条件: {n : 自然数} (hn : Even n) (h : (2 : R) = 0)
  证明: (natCast_eq_zero_or_one_of_two_eq_zero' n h).1 hn

Depends on / 依赖: natCast_eq_zero_or_one_of_two_eq_zero
-/
theorem natCast_eq_zero_of_even_of_two_eq_zero {n : Nat} (hn : Even n) (h : (2 : R) = 0) :
    (n : R) = 0 :=
  (natCast_eq_zero_or_one_of_two_eq_zero' n h).1 hn

/--
theorem `natCast_eq_one_of_odd_of_two_eq_zero` / 定理 `natCast_eq_one_of_odd_of_two_eq_zero`

English:
theorem natCast_eq_one_of_odd_of_two_eq_zero
  given: {n : Nat} (hn : Odd n) (h : (2 : R) = 0)
  proof: (natCast_eq_zero_or_one_of_two_eq_zero' n h).2 hn

中文:
定理 natCast_eq_one_of_odd_of_two_eq_zero
  条件: {n : 自然数} (hn : Odd n) (h : (2 : R) = 0)
  证明: (natCast_eq_zero_or_one_of_two_eq_zero' n h).2 hn

Depends on / 依赖: natCast_eq_zero_or_one_of_two_eq_zero
-/
theorem natCast_eq_one_of_odd_of_two_eq_zero {n : Nat} (hn : Odd n) (h : (2 : R) = 0) :
    (n : R) = 1 :=
  (natCast_eq_zero_or_one_of_two_eq_zero' n h).2 hn

/--
theorem `natCast_eq_zero_or_one_of_two_eq_zero` / 定理 `natCast_eq_zero_or_one_of_two_eq_zero`

English:
theorem natCast_eq_zero_or_one_of_two_eq_zero
  given: (n : Nat) (h : (2 : R) = 0)
  proof: by
  obtain hn | hn := Nat.even_or_odd n
· exact Or.inl natCast_eq_zero_of_even_of_two_eq_zero hn h
· exact Or.inr natCast_eq_one_of_odd_of_two_eq_zero hn h

中文:
定理 natCast_eq_zero_or_one_of_two_eq_zero
  条件: (n : 自然数) (h : (2 : R) = 0)
  证明: by
  obtain hn | hn := Nat.even_or_odd n
· exact Or.inl natCast_eq_zero_of_even_of_two_eq_zero hn h
· exact Or.inr natCast_eq_one_of_odd_of_two_eq_zero hn h

Depends on / 依赖: Nat.even_or_odd, Or.inl, Or.inr, even_or_odd, natCast_eq_one_of_odd_of_two_eq_zero, natCast_eq_zero_of_even_of_two_eq_zero
-/
theorem natCast_eq_zero_or_one_of_two_eq_zero (n : Nat) (h : (2 : R) = 0) :
    (n : R) = 0 ∨ (n : R) = 1 := by
  obtain hn | hn := Nat.even_or_odd n
· exact Or.inl natCast_eq_zero_of_even_of_two_eq_zero hn h
· exact Or.inr natCast_eq_one_of_odd_of_two_eq_zero hn h

end CharTwo
