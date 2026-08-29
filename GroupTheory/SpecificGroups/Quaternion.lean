/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Quaternion Groups

We define the (generalised) quaternion groups `QuaternionGroup n` of order `4n`, also known as
dicyclic groups, with elements `a i` and `xa i` for `i : ZMod n`. The (generalised) quaternion
groups can be defined by the presentation
$\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We write `a i` for
$a^i$ and `xa i` for $x * a^i$. For `n=2` the quaternion group `QuaternionGroup 2` is isomorphic to
the unit integral quaternions `(Quaternion ℤ)ˣ`.

## Main definition

`QuaternionGroup n`: The (generalised) quaternion group of order `4n`.

## Implementation notes

This file is heavily based on `DihedralGroup` by Shing Tak Lam.

In mathematics, the name "quaternion group" is reserved for the cases `n ≥ 2`. Since it would be
inconvenient to carry around this condition we define `QuaternionGroup` also for `n = 0` and
`n = 1`. `QuaternionGroup 0` is isomorphic to the infinite dihedral group, while
`QuaternionGroup 1` is isomorphic to a cyclic group of order `4`.

## References

* https://en.wikipedia.org/wiki/Dicyclic_group
* https://en.wikipedia.org/wiki/Quaternion_group

## TODO

Show that `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`.

-/

@[expose] public section


/--
Inductive type `QuaternionGroup` / 归纳类型 `QuaternionGroup`

English:
inductive QuaternionGroup
  parameters: (n : Nat)
  constructors (2):
    - a: ZMod (2 * n) -> QuaternionGroup n
    - xa: ZMod (2 * n) -> QuaternionGroup n

中文:
归纳类型 Quaternion群
  参数: (n : 自然数)
  构造子 (2 个):
    - a: ZMod (2 * n) -> Quaternion群 n
    - xa: ZMod (2 * n) -> Quaternion群 n
-/
inductive QuaternionGroup (n : Nat) : Type
  | a : ZMod (2 * n) -> QuaternionGroup n
  | xa : ZMod (2 * n) -> QuaternionGroup n
  deriving DecidableEq

namespace QuaternionGroup

variable {n : Nat}

set_option backward.privateInPublic true in
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : QuaternionGroup n -> QuaternionGroup n -> QuaternionGroup n

中文:
定义 mul
  签名: : Quaternion群 n -> Quaternion群 n -> Quaternion群 n
-/
private def mul : QuaternionGroup n -> QuaternionGroup n -> QuaternionGroup n
  | a i, a j => a (i + j)
  | a i, xa j => xa (j - i)
  | xa i, a j => xa (i + j)
  | xa i, xa j => a (n + j - i)

set_option backward.privateInPublic true in
/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: : QuaternionGroup n
  body: a 0

中文:
定义 one
  签名: : Quaternion群 n
  定义体: a 0
-/
private def one : QuaternionGroup n :=
  a 0

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (QuaternionGroup n)
  body: ⟨one⟩

中文:
实例 :
  签名: 可居 (Quaternion群 n)
  定义体: ⟨one⟩
-/
instance : Inhabited (QuaternionGroup n) :=
  ⟨one⟩

set_option backward.privateInPublic true in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : QuaternionGroup n -> QuaternionGroup n

中文:
定义 inv
  签名: : Quaternion群 n -> Quaternion群 n
-/
private def inv : QuaternionGroup n -> QuaternionGroup n
  | a i => a (-i)
  | xa i => xa (n + i)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (QuaternionGroup n)
  body: mul
  mul_assoc := by
    unfold instHMul
    rintro (i | i) (j | j) (k | k) <;> simp only [mul] <;> ring_nf
    have : (2 * n : ZMod (2 * n)) = 0 := by norm_cast; simp
    grind
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg a (zero_add i)
    · exact congr_arg xa (sub_zero i

中文:
实例 :
  签名: 群 (Quaternion群 n)
  定义体: mul
  mul_assoc := by
    unfold instHMul
    rintro (i | i) (j | j) (k | k) <;> simp only [mul] <;> ring_nf
    have : (2 * n : ZMod (2 * n)) = 0 := by norm_cast; simp
    grind
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg a (zero_add i)
    · exact congr_arg xa (sub_zero i
-/
instance : Group (QuaternionGroup n) where
  mul := mul
  mul_assoc := by
    unfold instHMul
    rintro (i | i) (j | j) (k | k) <;> simp only [mul] <;> ring_nf
    have : (2 * n : ZMod (2 * n)) = 0 := by norm_cast; simp
    grind
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg a (zero_add i)
    · exact congr_arg xa (sub_zero i)
  mul_one := by
    rintro (i | i)
    · exact congr_arg a (add_zero i)
    · exact congr_arg xa (add_zero i)
  inv := inv
  inv_mul_cancel := by
    rintro (i | i)
    · exact congr_arg a (neg_add_cancel i)
    · exact congr_arg a (sub_self (n + i))

@[simp]
/--
theorem `a_mul_a` / 定理 `a_mul_a`

English:
theorem a_mul_a
  given: (i j : ZMod (2 * n))
  statement: a i * a j = a (i + j)
  proof: rfl

@[simp]

中文:
定理 a_mul_a
  条件: (i j : ZMod (2 * n))
  结论: a i * a j = a (i + j)
  证明: rfl

@[simp]
-/
theorem a_mul_a (i j : ZMod (2 * n)) : a i * a j = a (i + j) :=
  rfl

@[simp]
/--
theorem `a_mul_xa` / 定理 `a_mul_xa`

English:
theorem a_mul_xa
  given: (i j : ZMod (2 * n))
  statement: a i * xa j = xa (j - i)
  proof: rfl

@[simp]

中文:
定理 a_mul_xa
  条件: (i j : ZMod (2 * n))
  结论: a i * xa j = xa (j - i)
  证明: rfl

@[simp]
-/
theorem a_mul_xa (i j : ZMod (2 * n)) : a i * xa j = xa (j - i) :=
  rfl

@[simp]
/--
theorem `xa_mul_a` / 定理 `xa_mul_a`

English:
theorem xa_mul_a
  given: (i j : ZMod (2 * n))
  statement: xa i * a j = xa (i + j)
  proof: rfl

@[simp]

中文:
定理 xa_mul_a
  条件: (i j : ZMod (2 * n))
  结论: xa i * a j = xa (i + j)
  证明: rfl

@[simp]
-/
theorem xa_mul_a (i j : ZMod (2 * n)) : xa i * a j = xa (i + j) :=
  rfl

@[simp]
/--
theorem `xa_mul_xa` / 定理 `xa_mul_xa`

English:
theorem xa_mul_xa
  given: (i j : ZMod (2 * n))
  statement: xa i * xa j = a ((n : ZMod (2 * n)) + j - i)
  proof: rfl

@[simp]

中文:
定理 xa_mul_xa
  条件: (i j : ZMod (2 * n))
  结论: xa i * xa j = a ((n : ZMod (2 * n)) + j - i)
  证明: rfl

@[simp]
-/
theorem xa_mul_xa (i j : ZMod (2 * n)) : xa i * xa j = a ((n : ZMod (2 * n)) + j - i) :=
  rfl

@[simp]
/--
theorem `a_zero` / 定理 `a_zero`

English:
theorem a_zero
  statement: a 0 = (1 : QuaternionGroup n)
  proof: by
  rfl

中文:
定理 a_zero
  结论: a 0 = (1 : Quaternion群 n)
  证明: by
  rfl
-/
theorem a_zero : a 0 = (1 : QuaternionGroup n) := by
  rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : QuaternionGroup n) = a 0
  proof: rfl

中文:
定理 one_def
  结论: (1 : Quaternion群 n) = a 0
  证明: rfl
-/
theorem one_def : (1 : QuaternionGroup n) = a 0 :=
  rfl

set_option backward.privateInPublic true in
/--
Definition of `fintypeHelper` / `fintypeHelper` 的定义

English:
definition fintypeHelper
  signature: : ZMod (2 * n) oplus ZMod (2 * n) ≃ QuaternionGroup n where
  body: match i with
    | a j => Sum.inl j
    | xa j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => a j
    | Sum.inr j => xa j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

中文:
定义 fintypeHelper
  签名: : ZMod (2 * n) oplus ZMod (2 * n) ≃ Quaternion群 n where
  定义体: match i with
    | a j => Sum.inl j
    | xa j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => a j
    | Sum.inr j => xa j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl
-/
private def fintypeHelper : ZMod (2 * n) oplus ZMod (2 * n) ≃ QuaternionGroup n where
  invFun i :=
    match i with
    | a j => Sum.inl j
    | xa j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => a j
    | Sum.inr j => xa j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/--
Definition of `quaternionGroupZeroEquivDihedralGroupZero` / `quaternionGroupZeroEquivDihedralGroupZero` 的定义

English:
definition quaternionGroupZeroEquivDihedralGroupZero
  signature: : QuaternionGroup 0 ≃* DihedralGroup 0 where
  body: by rintro (k | k) <;> rfl
  right_inv := by rintro (k | k) <;> rfl
  map_mul' := by rintro (k | k) (l | l) <;> simp

中文:
定义 quaternionGroupZeroEquivDihedralGroupZero
  签名: : Quaternion群 0 ≃* Dihedral群 0 where
  定义体: by rintro (k | k) <;> rfl
  right_inv := by rintro (k | k) <;> rfl
  map_mul' := by rintro (k | k) (l | l) <;> simp

Depends on / 依赖: map_mul, right_inv
-/
def quaternionGroupZeroEquivDihedralGroupZero : QuaternionGroup 0 ≃* DihedralGroup 0 where
  toFun
    | a j => DihedralGroup.r j
    | xa j => DihedralGroup.sr j
  invFun
    | DihedralGroup.r j => a j
    | DihedralGroup.sr j => xa j
  left_inv := by rintro (k | k) <;> rfl
  right_inv := by rintro (k | k) <;> rfl
  map_mul' := by rintro (k | k) (l | l) <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: n] : Fintype (QuaternionGroup n)
  body: Fintype.ofEquiv _ fintypeHelper

中文:
实例 [NeZero
  签名: n] : 有限类型 (Quaternion群 n)
  定义体: Fintype.ofEquiv _ fintypeHelper

Depends on / 依赖: Fintype, Fintype.ofEquiv, fintypeHelper, ofEquiv
-/
instance [NeZero n] : Fintype (QuaternionGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (QuaternionGroup n)
  body: ⟨⟨a 0, xa 0, by simp [-a_zero]⟩⟩

中文:
实例 :
  签名: 非平凡 (Quaternion群 n)
  定义体: ⟨⟨a 0, xa 0, by simp [-a_zero]⟩⟩

Depends on / 依赖: a_zero
-/
instance : Nontrivial (QuaternionGroup n) :=
  ⟨⟨a 0, xa 0, by simp [-a_zero]⟩⟩

/--
theorem `card` / 定理 `card`

English:
theorem card
  given: [NeZero n]
  statement: Fintype.card (QuaternionGroup n) = 4 * n
  proof: by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩]; rw [Fintype.card_sum]; rw [ZMod.card]; rw [two_mul]
  ring

@[simp]

中文:
定理 card
  条件: [NeZero n]
  结论: 有限类型.card (Quaternion群 n) = 4 * n
  证明: by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩]; rw [Fintype.card_sum]; rw [ZMod.card]; rw [two_mul]
  ring

@[simp]

Depends on / 依赖: Fintype, Fintype.card_eq.mpr, Fintype.card_sum, ZMod.card, card_eq, card_sum, fintypeHelper, two_mul
-/
theorem card [NeZero n] : Fintype.card (QuaternionGroup n) = 4 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩]; rw [Fintype.card_sum]; rw [ZMod.card]; rw [two_mul]
  ring

@[simp]
/--
theorem `a_one_pow` / 定理 `a_one_pow`

English:
theorem a_one_pow
  given: (k : Nat)
  statement: (a 1 : QuaternionGroup n) ^ k = a k
  proof: by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ]; rw [IH]; rw [a_mul_a]
    congr 1
    norm_cast

中文:
定理 a_one_pow
  条件: (k : 自然数)
  结论: (a 1 : Quaternion群 n) ^ k = a k
  证明: by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ]; rw [IH]; rw [a_mul_a]
    congr 1
    norm_cast

Depends on / 依赖: Nat.cast_zero, a_mul_a, cast_zero, pow_succ
-/
theorem a_one_pow (k : Nat) : (a 1 : QuaternionGroup n) ^ k = a k := by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ]; rw [IH]; rw [a_mul_a]
    congr 1
    norm_cast

/--
theorem `a_one_pow_n` / 定理 `a_one_pow_n`

English:
theorem a_one_pow_n
  statement: (a 1 : QuaternionGroup n) ^ (2 * n) = 1
  proof: by
  simp

@[simp]

中文:
定理 a_one_pow_n
  结论: (a 1 : Quaternion群 n) ^ (2 * n) = 1
  证明: by
  simp

@[simp]
-/
theorem a_one_pow_n : (a 1 : QuaternionGroup n) ^ (2 * n) = 1 := by
  simp

@[simp]
/--
theorem `xa_sq` / 定理 `xa_sq`

English:
theorem xa_sq
  given: (i : ZMod (2 * n))
  statement: xa i ^ 2 = a n
  proof: by simp [sq]

@[simp]

中文:
定理 xa_sq
  条件: (i : ZMod (2 * n))
  结论: xa i ^ 2 = a n
  证明: by simp [sq]

@[simp]
-/
theorem xa_sq (i : ZMod (2 * n)) : xa i ^ 2 = a n := by simp [sq]

@[simp]
/--
theorem `xa_pow_four` / 定理 `xa_pow_four`

English:
theorem xa_pow_four
  given: (i : ZMod (2 * n))
  statement: xa i ^ 4 = 1
  proof: by
  calc xa i ^ 4
      = a (n + n) := by simp [pow_succ, add_sub_assoc, sub_sub_cancel]
    _ = a ↑(2 * n) := by simp [Nat.cast_add, two_mul]
    _ = 1 := by simp

中文:
定理 xa_pow_four
  条件: (i : ZMod (2 * n))
  结论: xa i ^ 4 = 1
  证明: by
  calc xa i ^ 4
      = a (n + n) := by simp [pow_succ, add_sub_assoc, sub_sub_cancel]
    _ = a ↑(2 * n) := by simp [Nat.cast_add, two_mul]
    _ = 1 := by simp

Depends on / 依赖: Nat.cast_add, add_sub_assoc, cast_add, pow_succ, sub_sub_cancel, two_mul
-/
theorem xa_pow_four (i : ZMod (2 * n)) : xa i ^ 4 = 1 := by
  calc xa i ^ 4
      = a (n + n) := by simp [pow_succ, add_sub_assoc, sub_sub_cancel]
    _ = a ↑(2 * n) := by simp [Nat.cast_add, two_mul]
    _ = 1 := by simp

/-- If `0 < n`, then `xa i` has order 4.
-/
@[simp]
/--
theorem `orderOf_xa` / 定理 `orderOf_xa`

English:
theorem orderOf_xa
  given: [NeZero n] (i : ZMod (2 * n))
  statement: orderOf (xa i) = 4
  proof: by
  change _ = 2 ^ 2
  have : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  apply orderOf_eq_prime_pow
  · intro h
    simp only [pow_one, xa_sq] at h
    injection h with h'
    apply_fun ZMod.val at h'
    apply_fun (· / n) at h'
    simp only [ZMod.val_natCast, ZMod.val_zero, Nat.zero_div, Nat.m

中文:
定理 orderOf_xa
  条件: [NeZero n] (i : ZMod (2 * n))
  结论: orderOf (xa i) = 4
  证明: by
  change _ = 2 ^ 2
  have : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  apply orderOf_eq_prime_pow
  · intro h
    simp only [pow_one, xa_sq] at h
    injection h with h'
    apply_fun ZMod.val at h'
    apply_fun (· / n) at h'
    simp only [ZMod.val_natCast, ZMod.val_zero, Nat.zero_div, Nat.m

Depends on / 依赖: Fact.mk, Nat.Prime, Nat.div_self, Nat.mod_mul_left_div_self, Nat.prime_two, Nat.zero_div, NeZero, NeZero.pos, ZMod.val, ZMod.val_natCast, ZMod.val_zero, apply_fun, div_self, injection, mod_mul_left_div_self, orderOf_eq_prime_pow, pow_one, prime_two, reduceCtorEq, val_natCast
-/
theorem orderOf_xa [NeZero n] (i : ZMod (2 * n)) : orderOf (xa i) = 4 := by
  change _ = 2 ^ 2
  have : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  apply orderOf_eq_prime_pow
  · intro h
    simp only [pow_one, xa_sq] at h
    injection h with h'
    apply_fun ZMod.val at h'
    apply_fun (· / n) at h'
    simp only [ZMod.val_natCast, ZMod.val_zero, Nat.zero_div, Nat.mod_mul_left_div_self,
      Nat.div_self (NeZero.pos n), reduceCtorEq] at h'
  · simp

/--
theorem `quaternionGroup_one_isCyclic` / 定理 `quaternionGroup_one_isCyclic`

English:
theorem quaternionGroup_one_isCyclic
  statement: IsCyclic (QuaternionGroup 1)
  proof: by
  apply isCyclic_of_orderOf_eq_card
  · rw [Nat.card_eq_fintype_card, card, mul_one]
    exact orderOf_xa 0

中文:
定理 quaternionGroup_one_isCyclic
  结论: 是循环 (Quaternion群 1)
  证明: by
  apply isCyclic_of_orderOf_eq_card
  · rw [Nat.card_eq_fintype_card, card, mul_one]
    exact orderOf_xa 0

Depends on / 依赖: Nat.card_eq_fintype_card, card_eq_fintype_card, isCyclic_of_orderOf_eq_card, mul_one, orderOf_xa
-/
theorem quaternionGroup_one_isCyclic : IsCyclic (QuaternionGroup 1) := by
  apply isCyclic_of_orderOf_eq_card
  · rw [Nat.card_eq_fintype_card, card, mul_one]
    exact orderOf_xa 0

/-- If `0 < n`, then `a 1` has order `2 * n`.
-/
@[simp]
/--
theorem `orderOf_a_one` / 定理 `orderOf_a_one`

English:
theorem orderOf_a_one
  statement: orderOf (a 1 : QuaternionGroup n) = 2 * n
  proof: by
  rcases eq_zero_or_neZero n with rfl | hn
  · simp_rw [mul_zero, orderOf_eq_zero_iff']
    intro n h
    rw [one_def]; rw [a_one_pow]
    apply mt a.inj
    have : CharZero (ZMod (2 * 0)) := ZMod.charZero
    simpa using h.ne'
  apply (Nat.le_of_dvd
    (NeZero.pos _) (orderOf_dvd_of_pow_eq_one 

中文:
定理 orderOf_a_one
  结论: orderOf (a 1 : Quaternion群 n) = 2 * n
  证明: by
  rcases eq_zero_or_neZero n with rfl | hn
  · simp_rw [mul_zero, orderOf_eq_zero_iff']
    intro n h
    rw [one_def]; rw [a_one_pow]
    apply mt a.inj
    have : CharZero (ZMod (2 * 0)) := ZMod.charZero
    simpa using h.ne'
  apply (Nat.le_of_dvd
    (NeZero.pos _) (orderOf_dvd_of_pow_eq_one 

Depends on / 依赖: CharZero, Nat.le_of_dvd, Nat.mod, NeZero, NeZero.pos, QuaternionGroup, ZMod.charZero, ZMod.val_eq_zero, ZMod.val_natCast, a.inj, a_one_pow, a_one_pow_n, charZero, eq_zero_or_neZero, h.ne, injection, le_of_dvd, lt_or_eq, lt_or_eq.resolve_left, mul_zero
-/
theorem orderOf_a_one : orderOf (a 1 : QuaternionGroup n) = 2 * n := by
  rcases eq_zero_or_neZero n with rfl | hn
  · simp_rw [mul_zero, orderOf_eq_zero_iff']
    intro n h
    rw [one_def]; rw [a_one_pow]
    apply mt a.inj
    have : CharZero (ZMod (2 * 0)) := ZMod.charZero
    simpa using h.ne'
  apply (Nat.le_of_dvd
    (NeZero.pos _) (orderOf_dvd_of_pow_eq_one (@a_one_pow_n n))).lt_or_eq.resolve_left
  intro h
  have h1 : (a 1 : QuaternionGroup n) ^ orderOf (a 1) = 1 := pow_orderOf_eq_one _
  rw [a_one_pow] at h1
  injection h1 with h2
  rw [← ZMod.val_eq_zero]; rw [ZMod.val_natCast]; rw [Nat.mod_eq_of_lt h] at h2
  exact absurd h2.symm (orderOf_pos _).ne

/--
theorem `orderOf_a` / 定理 `orderOf_a`

English:
theorem orderOf_a
  given: [NeZero n] (i : ZMod (2 * n))
  proof: by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← a_one_pow]; rw [orderOf_pow]; rw [orderOf_a_one]

中文:
定理 orderOf_a
  条件: [NeZero n] (i : ZMod (2 * n))
  证明: by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← a_one_pow]; rw [orderOf_pow]; rw [orderOf_a_one]

Depends on / 依赖: ZMod.natCast_zmod_val, a_one_pow, conv_lhs, natCast_zmod_val, orderOf_a_one, orderOf_pow
-/
theorem orderOf_a [NeZero n] (i : ZMod (2 * n)) :
    orderOf (a i) = 2 * n / Nat.gcd (2 * n) i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← a_one_pow]; rw [orderOf_pow]; rw [orderOf_a_one]

/--
theorem `exponent` / 定理 `exponent`

English:
theorem exponent
  statement: Monoid.exponent (QuaternionGroup n) = 2 * lcm n 2
  proof: by
  rw [← normalize_eq 2]; rw [← lcm_mul_left]; rw [normalize_eq]
  simp only [Nat.reduceMul]
  rcases eq_zero_or_neZero n with rfl | hn
  · simp only [lcm_zero_left, mul_zero]
    exact Monoid.exponent_eq_zero_of_order_zero orderOf_a_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_fo

中文:
定理 exponent
  结论: 幺半群.exponent (Quaternion群 n) = 2 * 最小公倍数 n 2
  证明: by
  rw [← normalize_eq 2]; rw [← lcm_mul_left]; rw [normalize_eq]
  simp only [Nat.reduceMul]
  rcases eq_zero_or_neZero n with rfl | hn
  · simp only [lcm_zero_left, mul_zero]
    exact Monoid.exponent_eq_zero_of_order_zero orderOf_a_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_fo

Depends on / 依赖: Monoid, Monoid.exponent_dvd_of_forall_pow_eq_one, Monoid.exponent_eq_zero_of_order_zero, Nat.div_mul_cancel, Nat.dvd_antisymm, Nat.dvd_trans, Nat.gcd_dvd_left, Nat.reduceMul, div_mul_cancel, dvd_antisymm, dvd_lcm_left, dvd_trans, eq_zero_or_neZero, exponent_dvd_of_forall_pow_eq_one, exponent_eq_zero_of_order_zero, gcd_dvd_left, lcm_mul_left, lcm_zero_left, m.val, mul_zero
-/
theorem exponent : Monoid.exponent (QuaternionGroup n) = 2 * lcm n 2 := by
  rw [← normalize_eq 2]; rw [← lcm_mul_left]; rw [normalize_eq]
  simp only [Nat.reduceMul]
  rcases eq_zero_or_neZero n with rfl | hn
  · simp only [lcm_zero_left, mul_zero]
    exact Monoid.exponent_eq_zero_of_order_zero orderOf_a_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_a]
      refine Nat.dvd_trans ⟨gcd (2 * n) m.val, ?_⟩ (dvd_lcm_left (2 * n) 4)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * n) m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_xa]
      exact dvd_lcm_right (2 * n) 4
  · apply lcm_dvd
    · convert! Monoid.order_dvd_exponent (a 1)
      exact orderOf_a_one.symm
    · convert! Monoid.order_dvd_exponent (xa (0 : ZMod (2 * n)))
      exact (orderOf_xa 0).symm

end QuaternionGroup
