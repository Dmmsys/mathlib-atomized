/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Periodic

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`Nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/

@[expose] public section

assert_not_exists Algebra LinearMap

open Finset

namespace Nat

/--
Definition of `totient` / `totient` 的定义

English:
definition totient
  signature: (n : Nat)
  body: #{a in range n | n.Coprime a}

@[inherit_doc]
scoped notation "φ" => Nat.totient

@[simp]

中文:
定义 totient
  签名: (n : 自然数)
  定义体: #{a in range n | n.Coprime a}

@[inherit_doc]
scoped notation "φ" => Nat.totient

@[simp]

Depends on / 依赖: Coprime, n.Coprime
-/
def totient (n : Nat) : Nat := #{a in range n | n.Coprime a}

@[inherit_doc]
scoped notation "φ" => Nat.totient

@[simp]
/--
theorem `totient_zero` / 定理 `totient_zero`

English:
theorem totient_zero
  statement: φ 0 = 0
  proof: rfl

@[simp]

中文:
定理 totient_zero
  结论: φ 0 = 0
  证明: rfl

@[simp]
-/
theorem totient_zero : φ 0 = 0 :=
  rfl

@[simp]
/--
theorem `totient_one` / 定理 `totient_one`

English:
theorem totient_one
  statement: φ 1 = 1
  proof: rfl

中文:
定理 totient_one
  结论: φ 1 = 1
  证明: rfl
-/
theorem totient_one : φ 1 = 1 := rfl

/--
theorem `totient_eq_card_coprime` / 定理 `totient_eq_card_coprime`

English:
theorem totient_eq_card_coprime
  given: (n : Nat)
  statement: φ n = #{a in range n | n.Coprime a}
  proof: rfl

中文:
定理 totient_eq_card_coprime
  条件: (n : 自然数)
  结论: φ n = #{a in range n | n.Coprime a}
  证明: rfl
-/
theorem totient_eq_card_coprime (n : Nat) : φ n = #{a in range n | n.Coprime a} := rfl

/--
theorem `totient_eq_card_lt_and_coprime` / 定理 `totient_eq_card_lt_and_coprime`

English:
theorem totient_eq_card_lt_and_coprime
  given: (n : Nat)
  statement: φ n = Nat.card { m | m < n ∧ n.Coprime m }
  proof: by
  let e : { m | m < n ∧ n.Coprime m } ≃ {x in range n | n.Coprime x} :=
    { toFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      invFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      left_inv := fun m =>

中文:
定理 totient_eq_card_lt_and_coprime
  条件: (n : 自然数)
  结论: φ n = 自然数.card { m | m < n ∧ n.Coprime m }
  证明: by
  let e : { m | m < n ∧ n.Coprime m } ≃ {x in range n | n.Coprime x} :=
    { toFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      invFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      left_inv := fun m =>

Depends on / 依赖: Coprime, Finset, Finset.mem_filter, Finset.mem_range, Fintype, Fintype.card_coe, Subtype, Subtype.coe_eta, card_coe, card_congr, card_eq_fintype_card, coe_eta, invFun, left_inv, m.property, mem_filter, mem_range, n.Coprime, property, right_inv
-/
theorem totient_eq_card_lt_and_coprime (n : Nat) : φ n = Nat.card { m | m < n ∧ n.Coprime m } := by
  let e : { m | m < n ∧ n.Coprime m } ≃ {x in range n | n.Coprime x} :=
    { toFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      invFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      left_inv := fun m => by simp only [Subtype.coe_eta]
      right_inv := fun m => by simp only }
  rw [totient_eq_card_coprime]; rw [card_congr e]; rw [card_eq_fintype_card]; rw [Fintype.card_coe]

/--
theorem `totient_le` / 定理 `totient_le`

English:
theorem totient_le
  given: (n : Nat)
  statement: φ n <= n
  proof: ((range n).card_filter_le _).trans_eq (card_range n)

中文:
定理 totient_le
  条件: (n : 自然数)
  结论: φ n <= n
  证明: ((range n).card_filter_le _).trans_eq (card_range n)

Depends on / 依赖: card_filter_le, card_range, trans_eq
-/
theorem totient_le (n : Nat) : φ n <= n :=
  ((range n).card_filter_le _).trans_eq (card_range n)

/--
theorem `totient_lt` / 定理 `totient_lt`

English:
theorem totient_lt
  given: (n : Nat) (hn : 1 < n)
  statement: φ n < n
  proof: (card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)

@[simp]

中文:
定理 totient_lt
  条件: (n : 自然数) (hn : 1 < n)
  结论: φ n < n
  证明: (card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)

@[simp]

Depends on / 依赖: card_lt_card, card_range, filter_ssubset, hn.ne, pos_of_gt, trans_eq
-/
theorem totient_lt (n : Nat) (hn : 1 < n) : φ n < n :=
  (card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)

@[simp]
/--
theorem `totient_eq_zero` / 定理 `totient_eq_zero`

English:
theorem totient_eq_zero
  statement: forall {n : Nat}, φ n = 0 ↔ n = 0

中文:
定理 totient_eq_zero
  结论: 对任意 {n : 自然数}, φ n = 0 ↔ n = 0
-/
theorem totient_eq_zero : forall {n : Nat}, φ n = 0 ↔ n = 0
  | 0 => by decide
  | n + 1 =>
    suffices exists x < n + 1, (n + 1).gcd x = 1 by simpa [totient, filter_eq_empty_iff]
    ⟨1 % (n + 1), mod_lt _ n.succ_pos, by rw [gcd_comm, ← gcd_rec, gcd_one_right]⟩

/--
theorem `totient_pos` / 定理 `totient_pos`

English:
theorem totient_pos
  given: {n : Nat}
  statement: 0 < φ n ↔ 0 < n
  proof: by simp [pos_iff_ne_zero]

中文:
定理 totient_pos
  条件: {n : 自然数}
  结论: 0 < φ n ↔ 0 < n
  证明: by simp [pos_iff_ne_zero]
-/
@[simp] theorem totient_pos {n : Nat} : 0 < φ n ↔ 0 < n := by simp [pos_iff_ne_zero]

/--
Instance `neZero_totient` / 实例 `neZero_totient`

English:
instance neZero_totient
  signature: {n : Nat} [NeZero n]
  body: ⟨(totient_pos.mpr <| NeZero.pos n).ne'⟩

中文:
实例 neZero_totient
  签名: {n : 自然数} [NeZero n]
  定义体: ⟨(totient_pos.mpr <| NeZero.pos n).ne'⟩

Depends on / 依赖: NeZero, NeZero.pos, totient_pos, totient_pos.mpr
-/
instance neZero_totient {n : Nat} [NeZero n] : NeZero n.totient :=
  ⟨(totient_pos.mpr <| NeZero.pos n).ne'⟩

/--
theorem `filter_coprime_Ico_eq_totient` / 定理 `filter_coprime_Ico_eq_totient`

English:
theorem filter_coprime_Ico_eq_totient
  given: (a n : Nat)
  proof: by
  rw [totient]; rw [filter_Ico_card_eq_of_periodic]; rw [count_eq_card_filter_range]
  exact periodic_coprime a

中文:
定理 filter_coprime_Ico_eq_totient
  条件: (a n : 自然数)
  证明: by
  rw [totient]; rw [filter_Ico_card_eq_of_periodic]; rw [count_eq_card_filter_range]
  exact periodic_coprime a

Depends on / 依赖: count_eq_card_filter_range, filter_Ico_card_eq_of_periodic, periodic_coprime, totient
-/
theorem filter_coprime_Ico_eq_totient (a n : Nat) :
    #{x in Ico n (n + a) | a.Coprime x} = totient a := by
  rw [totient]; rw [filter_Ico_card_eq_of_periodic]; rw [count_eq_card_filter_range]
  exact periodic_coprime a

/--
theorem `Ico_filter_coprime_le` / 定理 `Ico_filter_coprime_le`

English:
theorem Ico_filter_coprime_le
  given: {a : Nat} (k n : Nat) (a_ne_zero : a != 0)
  proof: by
  conv_lhs => rw [← Nat.mod_add_div n a]
  induction n / a with
  | zero =>
    rw [← filter_coprime_Ico_eq_totient a k]
    simp only [add_zero, mul_one, mul_zero, zero_add]
    gcongr
    exact le_of_lt (mod_lt n (pos_iff_ne_zero.mpr a_ne_zero))
  | succ i ih => ?_
  simp only [mul_succ]
  simp

中文:
定理 Ico_filter_coprime_le
  条件: {a : 自然数} (k n : 自然数) (a_ne_zero : a != 0)
  证明: by
  conv_lhs => rw [← Nat.mod_add_div n a]
  induction n / a with
  | zero =>
    rw [← filter_coprime_Ico_eq_totient a k]
    simp only [add_zero, mul_one, mul_zero, zero_add]
    gcongr
    exact le_of_lt (mod_lt n (pos_iff_ne_zero.mpr a_ne_zero))
  | succ i ih => ?_
  simp only [mul_succ]
  simp

Depends on / 依赖: Coprime, Ico_subset_Ico_union_, Nat.mod_add_div, a.Coprime, a_ne_zero, add_assoc, add_zero, conv_lhs, filter_coprime_Ico_eq_totient, le_of_lt, mod_add_div, mod_lt, mul_one, mul_succ, mul_zero, pos_iff_ne_zero, pos_iff_ne_zero.mpr, simp_rw, zero_add
-/
theorem Ico_filter_coprime_le {a : Nat} (k n : Nat) (a_ne_zero : a != 0) :
    #{x in Ico k (k + n) | a.Coprime x} <= totient a * (n / a + 1) := by
  conv_lhs => rw [← Nat.mod_add_div n a]
  induction n / a with
  | zero =>
    rw [← filter_coprime_Ico_eq_totient a k]
    simp only [add_zero, mul_one, mul_zero, zero_add]
    gcongr
    exact le_of_lt (mod_lt n (pos_iff_ne_zero.mpr a_ne_zero))
  | succ i ih => ?_
  simp only [mul_succ]
  simp_rw [← add_assoc] at ih ⊢
  calc
    #{x in Ico k (k + n % a + a * i + a) | a.Coprime x}
      <= #{x in Ico k (k + n % a + a * i) union
        Ico (k + n % a + a * i) (k + n % a + a * i + a) | a.Coprime x} := by
      gcongr
      apply Ico_subset_Ico_union_Ico
    _ <= #{x in Ico k (k + n % a + a * i) | a.Coprime x} + a.totient := by
      rw [filter_union]; rw [← filter_coprime_Ico_eq_totient a (k + n % a + a * i)]
      apply card_union_le
    _ <= a.totient * i + a.totient + a.totient := by grw [← mul_add_one, ih]

open ZMod

/-- Note this takes an explicit `Fintype ((ZMod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp]
/--
theorem `_root_.ZMod.card_units_eq_totient` / 定理 `_root_.ZMod.card_units_eq_totient`

English:
theorem _root_.ZMod.card_units_eq_totient
  given: (n : Nat) [NeZero n] [Fintype (ZMod n)ˣ]
  proof: calc
    Fintype.card (ZMod n)ˣ = Fintype.card { x : ZMod n // x.val.Coprime n } :=
      Fintype.card_congr ZMod.unitsEquivCoprime
    _ = φ n := by
      obtain ⟨m, rfl⟩ : exists m, n = m + 1 := exists_eq_succ_of_ne_zero NeZero.out
      simp only [totient, Finset.card_eq_sum_ones, Fintype.card_su

中文:
定理 _root_.ZMod.card_units_eq_totient
  条件: (n : 自然数) [NeZero n] [有限类型 (ZMod n)ˣ]
  证明: calc
    Fintype.card (ZMod n)ˣ = Fintype.card { x : ZMod n // x.val.Coprime n } :=
      Fintype.card_congr ZMod.unitsEquivCoprime
    _ = φ n := by
      obtain ⟨m, rfl⟩ : exists m, n = m + 1 := exists_eq_succ_of_ne_zero NeZero.out
      simp only [totient, Finset.card_eq_sum_ones, Fintype.card_su

Depends on / 依赖: Coprime, Fin.sum_univ_eq_sum_range, Finset, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype, Fintype.card, Fintype.card_congr, Fintype.card_subtype, Nat.coprime_comm, NeZero, NeZero.out, ZMod.unitsEquivCoprime, card_congr, card_eq_sum_ones, card_subtype, coprime_comm, exists_eq_succ_of_ne_zero, sum_filter, sum_univ_eq_sum_range
-/
theorem _root_.ZMod.card_units_eq_totient (n : Nat) [NeZero n] [Fintype (ZMod n)ˣ] :
    Fintype.card (ZMod n)ˣ = φ n :=
  calc
    Fintype.card (ZMod n)ˣ = Fintype.card { x : ZMod n // x.val.Coprime n } :=
      Fintype.card_congr ZMod.unitsEquivCoprime
    _ = φ n := by
      obtain ⟨m, rfl⟩ : exists m, n = m + 1 := exists_eq_succ_of_ne_zero NeZero.out
      simp only [totient, Finset.card_eq_sum_ones, Fintype.card_subtype, Finset.sum_filter, ←
        Fin.sum_univ_eq_sum_range, @Nat.coprime_comm (m + 1)]
      rfl

/--
theorem `totient_even` / 定理 `totient_even`

English:
theorem totient_even
  given: {n : Nat} (hn : 2 < n)
  statement: Even n.totient
  proof: by
  have : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  have : NeZero n := NeZero.of_gt hn
  suffices 2 = orderOf (-1 : (ZMod n)ˣ) by
    rw [← ZMod.card_units_eq_totient]; rw [even_iff_two_dvd]; rw [this]
    exact orderOf_dvd_card
  rw [← orderOf_units]; rw [Units.coe_neg_one]; rw [orderOf_neg_one]; r

中文:
定理 totient_even
  条件: {n : 自然数} (hn : 2 < n)
  结论: Even n.totient
  证明: by
  have : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  have : NeZero n := NeZero.of_gt hn
  suffices 2 = orderOf (-1 : (ZMod n)ˣ) by
    rw [← ZMod.card_units_eq_totient]; rw [even_iff_two_dvd]; rw [this]
    exact orderOf_dvd_card
  rw [← orderOf_units]; rw [Units.coe_neg_one]; rw [orderOf_neg_one]; r

Depends on / 依赖: NeZero, NeZero.of_gt, Units.coe_neg_one, ZMod.card_units_eq_totient, card_units_eq_totient, coe_neg_one, even_iff_two_dvd, hn.ne, if_neg, of_gt, one_lt_two, one_lt_two.trans, orderOf, orderOf_dvd_card, orderOf_neg_one, orderOf_units, ringChar, ringChar.eq
-/
theorem totient_even {n : Nat} (hn : 2 < n) : Even n.totient := by
  have : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  have : NeZero n := NeZero.of_gt hn
  suffices 2 = orderOf (-1 : (ZMod n)ˣ) by
    rw [← ZMod.card_units_eq_totient]; rw [even_iff_two_dvd]; rw [this]
    exact orderOf_dvd_card
  rw [← orderOf_units]; rw [Units.coe_neg_one]; rw [orderOf_neg_one]; rw [ringChar.eq (ZMod n) n]; rw [if_neg hn.ne']

/--
theorem `totient_mul` / 定理 `totient_mul`

English:
theorem totient_mul
  given: {m n : Nat} (h : m.Coprime n)
  statement: φ (m * n) = φ m * φ n
  proof: if hmn0 : m * n = 0 then by
    rcases Nat.mul_eq_zero.1 hmn0 with h | h <;>
      simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    have : NeZero (m * n) := ⟨hmn0⟩
    have : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    have : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    simp only [← ZMod.

中文:
定理 totient_mul
  条件: {m n : 自然数} (h : m.Coprime n)
  结论: φ (m * n) = φ m * φ n
  证明: if hmn0 : m * n = 0 then by
    rcases Nat.mul_eq_zero.1 hmn0 with h | h <;>
      simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    have : NeZero (m * n) := ⟨hmn0⟩
    have : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    have : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    simp only [← ZMod.

Depends on / 依赖: Fintype, Fintype.card_congr, Fintype.card_prod, MulEquiv, MulEquiv.prodUnits, Nat.mul_eq_zero, NeZero, Units.mapEquiv, ZMod.card_units_eq_totient, ZMod.chineseRemainder, card_congr, card_prod, card_units_eq_totient, chineseRemainder, left_ne_zero_of_mul, mapEquiv, mul_eq_zero, mul_zero, prodUnits, right_ne_zero_of_mul
-/
theorem totient_mul {m n : Nat} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then by
    rcases Nat.mul_eq_zero.1 hmn0 with h | h <;>
      simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    have : NeZero (m * n) := ⟨hmn0⟩
    have : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    have : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    simp only [← ZMod.card_units_eq_totient]
    rw [Fintype.card_congr (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv]; rw [Fintype.card_congr (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv]; rw [Fintype.card_prod]

/--
theorem `totient_div_of_dvd` / 定理 `totient_div_of_dvd`

English:
theorem totient_div_of_dvd
  given: {n d : Nat} (hnd : d ∣ n)
  proof: by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [eq_zero_of_zero_dvd hnd]
  rcases hnd with ⟨x, rfl⟩
  rw [Nat.mul_div_cancel_left x hd0]
  apply Finset.card_bij fun k _ => d * k
  · simp only [mem_filter, mem_range, and_imp, Coprime]
    refine fun a ha1 ha2 => ⟨by gcongr, ?_⟩
    rw [gcd_mul

中文:
定理 totient_div_of_dvd
  条件: {n d : 自然数} (hnd : d ∣ n)
  证明: by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [eq_zero_of_zero_dvd hnd]
  rcases hnd with ⟨x, rfl⟩
  rw [Nat.mul_div_cancel_left x hd0]
  apply Finset.card_bij fun k _ => d * k
  · simp only [mem_filter, mem_range, and_imp, Coprime]
    refine fun a ha1 ha2 => ⟨by gcongr, ?_⟩
    rw [gcd_mul

Depends on / 依赖: Coprime, Finset, Finset.card_bij, Nat.mul_div_cancel_left, and_imp, card_bij, d.eq_zero_or_pos, eq_zero_of_zero_dvd, eq_zero_or_pos, exists_prop, gcd_dvd_right, gcd_mul_left, hd0.ne, mem_filter, mem_range, mul_div_cancel_left, mul_lt, mul_one
-/
theorem totient_div_of_dvd {n d : Nat} (hnd : d ∣ n) :
    φ (n / d) = #{k in range n | n.gcd k = d} := by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [eq_zero_of_zero_dvd hnd]
  rcases hnd with ⟨x, rfl⟩
  rw [Nat.mul_div_cancel_left x hd0]
  apply Finset.card_bij fun k _ => d * k
  · simp only [mem_filter, mem_range, and_imp, Coprime]
    refine fun a ha1 ha2 => ⟨by gcongr, ?_⟩
    rw [gcd_mul_left]; rw [ha2]; rw [mul_one]
  · simp [hd0.ne']
  · simp only [mem_filter, mem_range, exists_prop, and_imp]
    intro b hb1 hb2
    have : d ∣ b := by
      rw [← hb2]
      apply gcd_dvd_right
    rcases this with ⟨q, rfl⟩
    refine ⟨q, ⟨⟨(mul_lt_mul_iff_right₀ hd0).1 hb1, ?_⟩, rfl⟩⟩
    rwa [gcd_mul_left, mul_eq_left hd0.ne'] at hb2

/--
theorem `sum_totient` / 定理 `sum_totient`

English:
theorem sum_totient
  given: (n : Nat)
  statement: n.divisors.sum φ = n
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← sum_div_divisors n φ]
  have : n = ∑ d in n.divisors, #{k in range n | n.gcd k = d} := by
    nth_rw 1 [← card_range n]
    refine card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨?_, hn.ne'⟩
    apply gcd_dvd_left
  nth_rw 3 [this]


中文:
定理 sum_totient
  条件: (n : 自然数)
  结论: n.divisors.求和 φ = n
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← sum_div_divisors n φ]
  have : n = ∑ d in n.divisors, #{k in range n | n.gcd k = d} := by
    nth_rw 1 [← card_range n]
    refine card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨?_, hn.ne'⟩
    apply gcd_dvd_left
  nth_rw 3 [this]


Depends on / 依赖: card_eq_sum_card_fiberwise, card_range, divisors, dvd_of_mem_divisors, eq_zero_or_pos, gcd_dvd_left, hn.ne, mem_divisors, n.divisors, n.eq_zero_or_pos, n.gcd, nth_rw, sum_congr, sum_div_divisors, totient_div_of_dvd
-/
theorem sum_totient (n : Nat) : n.divisors.sum φ = n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← sum_div_divisors n φ]
  have : n = ∑ d in n.divisors, #{k in range n | n.gcd k = d} := by
    nth_rw 1 [← card_range n]
    refine card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨?_, hn.ne'⟩
    apply gcd_dvd_left
  nth_rw 3 [this]
  exact sum_congr rfl fun x hx => totient_div_of_dvd (dvd_of_mem_divisors hx)

/--
theorem `sum_totient'` / 定理 `sum_totient'`

English:
theorem sum_totient'
  given: (n : Nat)
  statement: ∑ m in range n.succ with m ∣ n, φ m = n
  proof: by
  convert! sum_totient _ using 1
  simp only [Nat.divisors, sum_filter, range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot] <;> simp

中文:
定理 sum_totient'
  条件: (n : 自然数)
  结论: ∑ m in range n.succ with m ∣ n, φ m = n
  证明: by
  convert! sum_totient _ using 1
  simp only [Nat.divisors, sum_filter, range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot] <;> simp

Depends on / 依赖: Nat.divisors, convert, divisors, range_eq_Ico, sum_eq_sum_Ico_succ_bot, sum_filter, sum_totient
-/
theorem sum_totient' (n : Nat) : ∑ m in range n.succ with m ∣ n, φ m = n := by
  convert! sum_totient _ using 1
  simp only [Nat.divisors, sum_filter, range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot] <;> simp

/--
theorem `totient_prime_pow_succ` / 定理 `totient_prime_pow_succ`

English:
theorem totient_prime_pow_succ
  given: {p : Nat} (hp : p.Prime) (n : Nat)
  statement: φ (p ^ (n + 1)) = p ^ n * (p - 1)
  proof: calc
    φ (p ^ (n + 1)) = #{a in range (p ^ (n + 1)) | (p ^ (n + 1)).Coprime a} :=
      totient_eq_card_coprime _
    _ = #(range (p ^ (n + 1)) \ (range (p ^ n)).image (· * p)) :=
      congr_arg card
        (by
          rw [sdiff_eq_filter]
          apply filter_congr
          simp only [mem_

中文:
定理 totient_prime_pow_succ
  条件: {p : 自然数} (hp : p.素) (n : 自然数)
  结论: φ (p ^ (n + 1)) = p ^ n * (p - 1)
  证明: calc
    φ (p ^ (n + 1)) = #{a in range (p ^ (n + 1)) | (p ^ (n + 1)).Coprime a} :=
      totient_eq_card_coprime _
    _ = #(range (p ^ (n + 1)) \ (range (p ^ n)).image (· * p)) :=
      congr_arg card
        (by
          rw [sdiff_eq_filter]
          apply filter_congr
          simp only [mem_

Depends on / 依赖: Coprime, congr_arg, coprime_iff_not_dvd, coprime_pow_left_iff, dvd_mul_left, filter_congr, hp.coprime_iff_not_dvd, lt_of_mul_lt_mul_left, mem_image, mem_range, n.succ_pos, not_exists, pow_succ, sdiff_eq_filter, succ_pos, totient_eq_card_coprime
-/
theorem totient_prime_pow_succ {p : Nat} (hp : p.Prime) (n : Nat) : φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
  calc
    φ (p ^ (n + 1)) = #{a in range (p ^ (n + 1)) | (p ^ (n + 1)).Coprime a} :=
      totient_eq_card_coprime _
    _ = #(range (p ^ (n + 1)) \ (range (p ^ n)).image (· * p)) :=
      congr_arg card
        (by
          rw [sdiff_eq_filter]
          apply filter_congr
          simp only [mem_range, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
            hp.coprime_iff_not_dvd]
          intro a ha
          constructor
          · intro hap b h; rcases h with ⟨_, rfl⟩
            exact hap (dvd_mul_left _ _)
          · rintro h ⟨b, rfl⟩
            rw [pow_succ'] at ha
            exact h b ⟨lt_of_mul_lt_mul_left ha (zero_le _), mul_comm _ _⟩)
    _ = _ := by
      have h1 : Function.Injective (· * p) := mul_left_injective₀ hp.ne_zero
      have h2 : (range (p ^ n)).image (· * p) subseteq range (p ^ (n + 1)) := fun a => by
        simp only [mem_image, mem_range, exists_imp]
        rintro b ⟨h, rfl⟩
        rw [Nat.pow_succ]
        exact (mul_lt_mul_iff_left₀ hp.pos).2 h
      rw [card_sdiff_of_subset h2]; rw [Finset.card_image_of_injective _ h1]; rw [card_range]; rw [card_range]; rw [←
        one_mul (p ^ n)]; rw [pow_succ']; rw [← tsub_mul]; rw [one_mul]; rw [mul_comm]

/--
theorem `totient_prime_pow` / 定理 `totient_prime_pow`

English:
theorem totient_prime_pow
  given: {p : Nat} (hp : p.Prime) {n : Nat} (hn : 0 < n)
  proof: by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩
  exact totient_prime_pow_succ hp _

中文:
定理 totient_prime_pow
  条件: {p : 自然数} (hp : p.素) {n : 自然数} (hn : 0 < n)
  证明: by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩
  exact totient_prime_pow_succ hp _

Depends on / 依赖: exists_eq_succ_of_ne_zero, pos_iff_ne_zero, totient_prime_pow_succ
-/
theorem totient_prime_pow {p : Nat} (hp : p.Prime) {n : Nat} (hn : 0 < n) :
    φ (p ^ n) = p ^ (n - 1) * (p - 1) := by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩
  exact totient_prime_pow_succ hp _

/--
theorem `totient_prime` / 定理 `totient_prime`

English:
theorem totient_prime
  given: {p : Nat} (hp : p.Prime)
  statement: φ p = p - 1
  proof: by
  rw [← pow_one p]; rw [totient_prime_pow hp] <;> simp

中文:
定理 totient_prime
  条件: {p : 自然数} (hp : p.素)
  结论: φ p = p - 1
  证明: by
  rw [← pow_one p]; rw [totient_prime_pow hp] <;> simp

Depends on / 依赖: pow_one, totient_prime_pow
-/
theorem totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1 := by
  rw [← pow_one p]; rw [totient_prime_pow hp] <;> simp

/--
theorem `totient_eq_iff_prime` / 定理 `totient_eq_iff_prime`

English:
theorem totient_eq_iff_prime
  given: {p : Nat} (hp : 0 < p)
  statement: p.totient = p - 1 ↔ p.Prime
  proof: by
  refine ⟨fun h => ?_, totient_prime⟩
  replace hp : 1 < p := by
    apply lt_of_le_of_ne
    · rwa [succ_le_iff]
    · rintro rfl
      rw [totient_one]; rw [tsub_self] at h
      exact one_ne_zero h
  rw [totient_eq_card_coprime]; rw [range_eq_Ico]; rw [← Finset.insert_Ico_add_one_left_eq_Ico h

中文:
定理 totient_eq_iff_prime
  条件: {p : 自然数} (hp : 0 < p)
  结论: p.totient = p - 1 ↔ p.素
  证明: by
  refine ⟨fun h => ?_, totient_prime⟩
  replace hp : 1 < p := by
    apply lt_of_le_of_ne
    · rwa [succ_le_iff]
    · rintro rfl
      rw [totient_one]; rw [tsub_self] at h
      exact one_ne_zero h
  rw [totient_eq_card_coprime]; rw [range_eq_Ico]; rw [← Finset.insert_Ico_add_one_left_eq_Ico h

Depends on / 依赖: Finset, Finset.filter_card_eq, Finset.filter_insert, Finset.insert_Ico_add_one_left_eq_Ico, Finset.mem_Ico.mpr, Nat.card_Ico, card_Ico, dvd_refl, dvd_zero, filter_card_eq, filter_insert, hp.le, if_neg, insert_Ico_add_one_left_eq_Ico, lt_of_le_of_ne, mem_Ico, not_coprime_of_dvd_of_dvd, one_ne_zero, p.prime_of_coprime, prime_of_coprime
-/
theorem totient_eq_iff_prime {p : Nat} (hp : 0 < p) : p.totient = p - 1 ↔ p.Prime := by
  refine ⟨fun h => ?_, totient_prime⟩
  replace hp : 1 < p := by
    apply lt_of_le_of_ne
    · rwa [succ_le_iff]
    · rintro rfl
      rw [totient_one]; rw [tsub_self] at h
      exact one_ne_zero h
  rw [totient_eq_card_coprime]; rw [range_eq_Ico]; rw [← Finset.insert_Ico_add_one_left_eq_Ico hp.le]; rw [Finset.filter_insert]; rw [if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p))]; rw [← Nat.card_Ico 1 p] at h
  refine
p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n Finset.mem_Ico.mpr ⟨?_, hn⟩
  lia

/--
theorem `card_units_zmod_lt_sub_one` / 定理 `card_units_zmod_lt_sub_one`

English:
theorem card_units_zmod_lt_sub_one
  given: {p : Nat} (hp : 1 < p) [Fintype (ZMod p)ˣ]
  proof: by
  have : NeZero p := ⟨(pos_of_gt hp).ne'⟩
  rw [ZMod.card_units_eq_totient p]
  exact Nat.le_sub_one_of_lt (Nat.totient_lt p hp)

中文:
定理 card_units_zmod_lt_sub_one
  条件: {p : 自然数} (hp : 1 < p) [有限类型 (ZMod p)ˣ]
  证明: by
  have : NeZero p := ⟨(pos_of_gt hp).ne'⟩
  rw [ZMod.card_units_eq_totient p]
  exact Nat.le_sub_one_of_lt (Nat.totient_lt p hp)

Depends on / 依赖: Nat.le_sub_one_of_lt, Nat.totient_lt, NeZero, ZMod.card_units_eq_totient, card_units_eq_totient, le_sub_one_of_lt, pos_of_gt, totient_lt
-/
theorem card_units_zmod_lt_sub_one {p : Nat} (hp : 1 < p) [Fintype (ZMod p)ˣ] :
    Fintype.card (ZMod p)ˣ <= p - 1 := by
  have : NeZero p := ⟨(pos_of_gt hp).ne'⟩
  rw [ZMod.card_units_eq_totient p]
  exact Nat.le_sub_one_of_lt (Nat.totient_lt p hp)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `prime_iff_card_units` / 定理 `prime_iff_card_units`

English:
theorem prime_iff_card_units
  given: (p : Nat) [Fintype (ZMod p)ˣ]
  proof: by
  rcases eq_zero_or_neZero p with rfl | hp
  · simp [ZMod, not_prime_zero, zero_tsub]
  rw [ZMod.card_units_eq_totient]; rw [Nat.totient_eq_iff_prime <| NeZero.pos p]

@[simp]

中文:
定理 prime_iff_card_units
  条件: (p : 自然数) [有限类型 (ZMod p)ˣ]
  证明: by
  rcases eq_zero_or_neZero p with rfl | hp
  · simp [ZMod, not_prime_zero, zero_tsub]
  rw [ZMod.card_units_eq_totient]; rw [Nat.totient_eq_iff_prime <| NeZero.pos p]

@[simp]

Depends on / 依赖: Nat.totient_eq_iff_prime, NeZero, NeZero.pos, ZMod.card_units_eq_totient, card_units_eq_totient, eq_zero_or_neZero, not_prime_zero, totient_eq_iff_prime, zero_tsub
-/
theorem prime_iff_card_units (p : Nat) [Fintype (ZMod p)ˣ] :
    p.Prime ↔ Fintype.card (ZMod p)ˣ = p - 1 := by
  rcases eq_zero_or_neZero p with rfl | hp
  · simp [ZMod, not_prime_zero, zero_tsub]
  rw [ZMod.card_units_eq_totient]; rw [Nat.totient_eq_iff_prime <| NeZero.pos p]

@[simp]
/--
theorem `totient_two` / 定理 `totient_two`

English:
theorem totient_two
  statement: φ 2 = 1
  proof: (totient_prime prime_two).trans rfl

中文:
定理 totient_two
  结论: φ 2 = 1
  证明: (totient_prime prime_two).trans rfl

Depends on / 依赖: prime_two, totient_prime
-/
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans rfl

/--
theorem `odd_totient_iff` / 定理 `odd_totient_iff`

English:
theorem odd_totient_iff
  given: {n : Nat}
  proof: by
  rcases n with _ | _ | _ | _ <;> simp [Nat.totient_even]

中文:
定理 odd_totient_iff
  条件: {n : 自然数}
  证明: by
  rcases n with _ | _ | _ | _ <;> simp [Nat.totient_even]

Depends on / 依赖: Nat.totient_even, totient_even
-/
theorem odd_totient_iff {n : Nat} :
    Odd (φ n) ↔ n = 1 ∨ n = 2 := by
  rcases n with _ | _ | _ | _ <;> simp [Nat.totient_even]

/--
theorem `totient_eq_one_iff` / 定理 `totient_eq_one_iff`

English:
theorem totient_eq_one_iff
  statement: forall {n : Nat}, n.totient = 1 ↔ n = 1 ∨ n = 2
  proof: le_add_self
    simp only [succ_succ_ne_one, false_or]
exact ⟨fun h => not_even_one.elim h ▸ totient_even this, by rintro ⟨⟩⟩

中文:
定理 totient_eq_one_iff
  结论: 对任意 {n : 自然数}, n.totient = 1 ↔ n = 1 ∨ n = 2
  证明: le_add_self
    simp only [succ_succ_ne_one, false_or]
exact ⟨fun h => not_even_one.elim h ▸ totient_even this, by rintro ⟨⟩⟩

Depends on / 依赖: le_add_self
-/
theorem totient_eq_one_iff : forall {n : Nat}, n.totient = 1 ↔ n = 1 ∨ n = 2
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    have : 3 <= n + 3 := le_add_self
    simp only [succ_succ_ne_one, false_or]
exact ⟨fun h => not_even_one.elim h ▸ totient_even this, by rintro ⟨⟩⟩

/--
theorem `dvd_two_of_totient_le_one` / 定理 `dvd_two_of_totient_le_one`

English:
theorem dvd_two_of_totient_le_one
  given: {a : Nat} (han : 0 < a) (ha : a.totient <= 1)
  statement: a ∣ 2
  proof: by
rcases totient_eq_one_iff.mp le_antisymm ha totient_pos.2 han with rfl | rfl <;> norm_num

中文:
定理 dvd_two_of_totient_le_one
  条件: {a : 自然数} (han : 0 < a) (ha : a.totient <= 1)
  结论: a ∣ 2
  证明: by
rcases totient_eq_one_iff.mp le_antisymm ha totient_pos.2 han with rfl | rfl <;> norm_num

Depends on / 依赖: le_antisymm, totient_eq_one_iff, totient_eq_one_iff.mp, totient_pos
-/
theorem dvd_two_of_totient_le_one {a : Nat} (han : 0 < a) (ha : a.totient <= 1) : a ∣ 2 := by
rcases totient_eq_one_iff.mp le_antisymm ha totient_pos.2 han with rfl | rfl <;> norm_num

/--
theorem `odd_totient_iff_eq_one` / 定理 `odd_totient_iff_eq_one`

English:
theorem odd_totient_iff_eq_one
  given: {n : Nat}
  proof: by
  simp [Nat.odd_totient_iff, Nat.totient_eq_one_iff]

中文:
定理 odd_totient_iff_eq_one
  条件: {n : 自然数}
  证明: by
  simp [Nat.odd_totient_iff, Nat.totient_eq_one_iff]

Depends on / 依赖: Nat.odd_totient_iff, Nat.totient_eq_one_iff, odd_totient_iff, totient_eq_one_iff
-/
theorem odd_totient_iff_eq_one {n : Nat} :
    Odd (φ n) ↔ φ n = 1 := by
  simp [Nat.odd_totient_iff, Nat.totient_eq_one_iff]

/--
theorem `totient_coprime_totient_iff` / 定理 `totient_coprime_totient_iff`

English:
theorem totient_coprime_totient_iff
  given: (m n : Nat)
  proof: by
  constructor
  · rw [← not_imp_not]
    simp_rw [← odd_totient_iff, not_or, not_odd_iff_even, even_iff_two_dvd]
    exact fun h => Nat.not_coprime_of_dvd_of_dvd one_lt_two h.1 h.2
  · simp_rw [← totient_eq_one_iff]
    rintro (h | h) <;> rw [h]
    exacts [Nat.coprime_one_left _, Nat.coprime_one

中文:
定理 totient_coprime_totient_iff
  条件: (m n : 自然数)
  证明: by
  constructor
  · rw [← not_imp_not]
    simp_rw [← odd_totient_iff, not_or, not_odd_iff_even, even_iff_two_dvd]
    exact fun h => Nat.not_coprime_of_dvd_of_dvd one_lt_two h.1 h.2
  · simp_rw [← totient_eq_one_iff]
    rintro (h | h) <;> rw [h]
    exacts [Nat.coprime_one_left _, Nat.coprime_one

Depends on / 依赖: Nat.coprime_one_left, Nat.coprime_one_right, Nat.not_coprime_of_dvd_of_dvd, coprime_one_left, coprime_one_right, even_iff_two_dvd, exacts, not_coprime_of_dvd_of_dvd, not_imp_not, not_odd_iff_even, not_or, odd_totient_iff, one_lt_two, simp_rw, totient_eq_one_iff
-/
theorem totient_coprime_totient_iff (m n : Nat) :
    (φ m).Coprime (φ n) ↔ (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2) := by
  constructor
  · rw [← not_imp_not]
    simp_rw [← odd_totient_iff, not_or, not_odd_iff_even, even_iff_two_dvd]
    exact fun h => Nat.not_coprime_of_dvd_of_dvd one_lt_two h.1 h.2
  · simp_rw [← totient_eq_one_iff]
    rintro (h | h) <;> rw [h]
    exacts [Nat.coprime_one_left _, Nat.coprime_one_right _]

/-! ### Euler's product formula for the totient function

We prove several different statements of this formula. -/


/--
theorem `totient_eq_prod_factorization` / 定理 `totient_eq_prod_factorization`

English:
theorem totient_eq_prod_factorization
  given: {n : Nat} (hn : n != 0)
  proof: by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  apply Finsupp.prod_congr _
  intro p hp
  have h := zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hp)
  rw [totient_prime_pow (prime_of_mem_primeFactors hp) h]

中文:
定理 totient_eq_prod_factorization
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  apply Finsupp.prod_congr _
  intro p hp
  have h := zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hp)
  rw [totient_prime_pow (prime_of_mem_primeFactors hp) h]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff.mp, Finsupp.prod_congr, mem_support_iff, multiplicative_factorization, prime_of_mem_primeFactors, prod_congr, totient_mul, totient_one, totient_prime_pow, zero_lt_iff, zero_lt_iff.mpr
-/
theorem totient_eq_prod_factorization {n : Nat} (hn : n != 0) :
    φ n = n.factorization.prod fun p k => p ^ (k - 1) * (p - 1) := by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  apply Finsupp.prod_congr _
  intro p hp
  have h := zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hp)
  rw [totient_prime_pow (prime_of_mem_primeFactors hp) h]

/--
theorem `totient_mul_prod_primeFactors` / 定理 `totient_mul_prod_primeFactors`

English:
theorem totient_mul_prod_primeFactors
  given: (n : Nat)
  proof: by
  by_cases hn : n = 0; · simp [hn]
  rw [totient_eq_prod_factorization hn]
  nth_rw 3 [← prod_factorization_pow_eq_self hn]
  simp only [prod_primeFactors_prod_factorization, ← Finsupp.prod_mul]
  refine Finsupp.prod_congr (M := Nat) (N := Nat) fun p hp => ?_
  rw [Finsupp.mem_support_iff]; rw [←

中文:
定理 totient_mul_prod_primeFactors
  条件: (n : 自然数)
  证明: by
  by_cases hn : n = 0; · simp [hn]
  rw [totient_eq_prod_factorization hn]
  nth_rw 3 [← prod_factorization_pow_eq_self hn]
  simp only [prod_primeFactors_prod_factorization, ← Finsupp.prod_mul]
  refine Finsupp.prod_congr (M := Nat) (N := Nat) fun p hp => ?_
  rw [Finsupp.mem_support_iff]; rw [←

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Finsupp.prod_congr, Finsupp.prod_mul, Nat.sub_one, Nat.succ_pred_eq_of_pos, mem_support_iff, mul_assoc, mul_comm, nth_rw, pow_succ, prod_congr, prod_factorization_pow_eq_self, prod_mul, prod_primeFactors_prod_factorization, sub_one, succ_pred_eq_of_pos, totient_eq_prod_factorization, zero_lt_iff
-/
theorem totient_mul_prod_primeFactors (n : Nat) :
    (φ n * ∏ p in n.primeFactors, p) = n * ∏ p in n.primeFactors, (p - 1) := by
  by_cases hn : n = 0; · simp [hn]
  rw [totient_eq_prod_factorization hn]
  nth_rw 3 [← prod_factorization_pow_eq_self hn]
  simp only [prod_primeFactors_prod_factorization, ← Finsupp.prod_mul]
  refine Finsupp.prod_congr (M := Nat) (N := Nat) fun p hp => ?_
  rw [Finsupp.mem_support_iff]; rw [← zero_lt_iff] at hp
  rw [mul_comm]; rw [← mul_assoc]; rw [← pow_succ']; rw [Nat.sub_one]; rw [Nat.succ_pred_eq_of_pos hp]

/--
theorem `totient_eq_div_primeFactors_mul` / 定理 `totient_eq_div_primeFactors_mul`

English:
theorem totient_eq_div_primeFactors_mul
  given: (n : Nat)
  proof: by
  rw [← mul_div_left n.totient]; rw [totient_mul_prod_primeFactors]; rw [mul_comm]; rw [Nat.mul_div_assoc _ (prod_primeFactors_dvd n)]; rw [mul_comm]
  exact prod_pos (fun p => pos_of_mem_primeFactors)

中文:
定理 totient_eq_div_primeFactors_mul
  条件: (n : 自然数)
  证明: by
  rw [← mul_div_left n.totient]; rw [totient_mul_prod_primeFactors]; rw [mul_comm]; rw [Nat.mul_div_assoc _ (prod_primeFactors_dvd n)]; rw [mul_comm]
  exact prod_pos (fun p => pos_of_mem_primeFactors)

Depends on / 依赖: Nat.mul_div_assoc, mul_comm, mul_div_assoc, mul_div_left, n.totient, pos_of_mem_primeFactors, prod_pos, prod_primeFactors_dvd, totient, totient_mul_prod_primeFactors
-/
theorem totient_eq_div_primeFactors_mul (n : Nat) :
    φ n = (n / ∏ p in n.primeFactors, p) * ∏ p in n.primeFactors, (p - 1) := by
  rw [← mul_div_left n.totient]; rw [totient_mul_prod_primeFactors]; rw [mul_comm]; rw [Nat.mul_div_assoc _ (prod_primeFactors_dvd n)]; rw [mul_comm]
  exact prod_pos (fun p => pos_of_mem_primeFactors)

/--
theorem `totient_eq_mul_prod_factors` / 定理 `totient_eq_mul_prod_factors`

English:
theorem totient_eq_mul_prod_factors
  given: (n : Nat)
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : Rat) != 0 := by simp [hn]
  have hpQ : (∏ p in n.primeFactors, (p : Rat)) != 0 := by
    rw [← cast_prod]; rw [cast_ne_zero]; rw [← zero_lt_iff]; rw [prod_primeFactors_prod_factorization]
    exact prod_pos fun p hp => pos_of_mem_primeFactors 

中文:
定理 totient_eq_mul_prod_factors
  条件: (n : 自然数)
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : Rat) != 0 := by simp [hn]
  have hpQ : (∏ p in n.primeFactors, (p : Rat)) != 0 := by
    rw [← cast_prod]; rw [cast_ne_zero]; rw [← zero_lt_iff]; rw [prod_primeFactors_prod_factorization]
    exact prod_pos fun p hp => pos_of_mem_primeFactors 

Depends on / 依赖: cast_div_charZero, cast_mul, cast_ne_zero, cast_prod, div_eq_iff, mul_comm_div, mul_right_inj, n.primeFactors, pos_of_mem_primeFactors, primeFactors, prod_congr, prod_mul_distrib, prod_pos, prod_primeFactors_dvd, prod_primeFactors_prod_factorization, totient_eq_div_primeFactors_mul, zero_lt_iff
-/
theorem totient_eq_mul_prod_factors (n : Nat) :
    (φ n : Rat) = n * ∏ p in n.primeFactors, (1 - (p : Rat)⁻¹) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : Rat) != 0 := by simp [hn]
  have hpQ : (∏ p in n.primeFactors, (p : Rat)) != 0 := by
    rw [← cast_prod]; rw [cast_ne_zero]; rw [← zero_lt_iff]; rw [prod_primeFactors_prod_factorization]
    exact prod_pos fun p hp => pos_of_mem_primeFactors hp
  simp only [totient_eq_div_primeFactors_mul n, prod_primeFactors_dvd n, cast_mul, cast_prod,
    cast_div_charZero, mul_comm_div, mul_right_inj' hn', div_eq_iff hpQ, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp := pos_of_mem_primeFactorsList (List.mem_toFinset.mp hp)
  have hp' : (p : Rat) != 0 := cast_ne_zero.mpr hp.ne.symm
  rw [sub_mul]; rw [one_mul]; rw [mul_comm]; rw [mul_inv_cancel₀ hp']; rw [cast_pred hp]

/--
theorem `totient_gcd_mul_totient_mul` / 定理 `totient_gcd_mul_totient_mul`

English:
theorem totient_gcd_mul_totient_mul
  given: (a b : Nat)
  statement: φ (a.gcd b) * φ (a * b) = φ a * φ b * a.gcd b
  proof: by
  have shuffle :
    forall a1 a2 b1 b2 c1 c2 : Nat,
      b1 ∣ a1 -> b2 ∣ a2 -> a1 / b1 * c1 * (a2 / b2 * c2) = a1 * a2 / (b1 * b2) * (c1 * c2) := by
    intro a1 a2 b1 b2 c1 c2 h1 h2
    calc
      a1 / b1 * c1 * (a2 / b2 * c2) = a1 / b1 * (a2 / b2) * (c1 * c2) := by apply mul_mul_mul_comm
    

中文:
定理 totient_gcd_mul_totient_mul
  条件: (a b : 自然数)
  结论: φ (a.最大公约数 b) * φ (a * b) = φ a * φ b * a.最大公约数 b
  证明: by
  have shuffle :
    forall a1 a2 b1 b2 c1 c2 : Nat,
      b1 ∣ a1 -> b2 ∣ a2 -> a1 / b1 * c1 * (a2 / b2 * c2) = a1 * a2 / (b1 * b2) * (c1 * c2) := by
    intro a1 a2 b1 b2 c1 c2 h1 h2
    calc
      a1 / b1 * c1 * (a2 / b2 * c2) = a1 / b1 * (a2 / b2) * (c1 * c2) := by apply mul_mul_mul_comm
    

Depends on / 依赖: div_mul_div_comm, mul_mul_mul_comm, prod_primeFactors_dvd, prod_primeFactors_gcd, repeat, rotate_left, shuffle, totient_eq_div_primeFactors_mul
-/
theorem totient_gcd_mul_totient_mul (a b : Nat) : φ (a.gcd b) * φ (a * b) = φ a * φ b * a.gcd b := by
  have shuffle :
    forall a1 a2 b1 b2 c1 c2 : Nat,
      b1 ∣ a1 -> b2 ∣ a2 -> a1 / b1 * c1 * (a2 / b2 * c2) = a1 * a2 / (b1 * b2) * (c1 * c2) := by
    intro a1 a2 b1 b2 c1 c2 h1 h2
    calc
      a1 / b1 * c1 * (a2 / b2 * c2) = a1 / b1 * (a2 / b2) * (c1 * c2) := by apply mul_mul_mul_comm
      _ = a1 * a2 / (b1 * b2) * (c1 * c2) := by
        congr 1
        exact div_mul_div_comm h1 h2
  simp only [totient_eq_div_primeFactors_mul]
  rw [shuffle]; rw [shuffle]
  rotate_left
  repeat' apply prod_primeFactors_dvd
  simp only [prod_primeFactors_gcd_mul_prod_primeFactors_mul]
  rw [eq_comm]; rw [mul_comm]; rw [← mul_assoc]; rw [← Nat.mul_div_assoc]
  exact mul_dvd_mul (prod_primeFactors_dvd a) (prod_primeFactors_dvd b)

/--
theorem `totient_super_multiplicative` / 定理 `totient_super_multiplicative`

English:
theorem totient_super_multiplicative
  given: (a b : Nat)
  statement: φ a * φ b <= φ (a * b)
  proof: by
  let d := a.gcd b
  rcases eq_zero_or_pos a with (rfl | ha0)
  · simp
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
  apply le_of_mul_le_mul_right _ hd0
  grw [← totient_gcd_mul_totient_mul a b, mul_comm, d.totient_le]

@[gcongr]

中文:
定理 totient_super_multiplicative
  条件: (a b : 自然数)
  结论: φ a * φ b <= φ (a * b)
  证明: by
  let d := a.gcd b
  rcases eq_zero_or_pos a with (rfl | ha0)
  · simp
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
  apply le_of_mul_le_mul_right _ hd0
  grw [← totient_gcd_mul_totient_mul a b, mul_comm, d.totient_le]

@[gcongr]

Depends on / 依赖: Nat.gcd_pos_of_pos_left, a.gcd, d.totient_le, eq_zero_or_pos, gcd_pos_of_pos_left, le_of_mul_le_mul_right, mul_comm, totient_gcd_mul_totient_mul, totient_le
-/
theorem totient_super_multiplicative (a b : Nat) : φ a * φ b <= φ (a * b) := by
  let d := a.gcd b
  rcases eq_zero_or_pos a with (rfl | ha0)
  · simp
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
  apply le_of_mul_le_mul_right _ hd0
  grw [← totient_gcd_mul_totient_mul a b, mul_comm, d.totient_le]

@[gcongr]
/--
theorem `totient_dvd_of_dvd` / 定理 `totient_dvd_of_dvd`

English:
theorem totient_dvd_of_dvd
  given: {a b : Nat} (h : a ∣ b)
  statement: φ a ∣ φ b
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha0)
  · simp [zero_dvd_iff.1 h]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  have hab' := primeFactors_mono h hb0
  rw [totient_eq_prod_factorization ha0]; rw [totient_eq_prod_factorization hb0]
  refine Finsupp.prod_dvd_prod_of_subset_of_dvd hab' fun p _ =

中文:
定理 totient_dvd_of_dvd
  条件: {a b : 自然数} (h : a ∣ b)
  结论: φ a ∣ φ b
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha0)
  · simp [zero_dvd_iff.1 h]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  have hab' := primeFactors_mono h hb0
  rw [totient_eq_prod_factorization ha0]; rw [totient_eq_prod_factorization hb0]
  refine Finsupp.prod_dvd_prod_of_subset_of_dvd hab' fun p _ =

Depends on / 依赖: Finsupp, Finsupp.prod_dvd_prod_of_subset_of_dvd, dvd_rfl, eq_or_ne, factorization_le_iff_dvd, mul_dvd_mul, pow_dvd_pow, primeFactors_mono, prod_dvd_prod_of_subset_of_dvd, totient_eq_prod_factorization, tsub_le_tsub_right, zero_dvd_iff
-/
theorem totient_dvd_of_dvd {a b : Nat} (h : a ∣ b) : φ a ∣ φ b := by
  rcases eq_or_ne a 0 with (rfl | ha0)
  · simp [zero_dvd_iff.1 h]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  have hab' := primeFactors_mono h hb0
  rw [totient_eq_prod_factorization ha0]; rw [totient_eq_prod_factorization hb0]
  refine Finsupp.prod_dvd_prod_of_subset_of_dvd hab' fun p _ => mul_dvd_mul ?_ dvd_rfl
  exact pow_dvd_pow p (tsub_le_tsub_right ((factorization_le_iff_dvd ha0 hb0).2 h p) 1)

/--
theorem `totient_mul_of_prime_of_dvd` / 定理 `totient_mul_of_prime_of_dvd`

English:
theorem totient_mul_of_prime_of_dvd
  given: {p n : Nat} (hp : p.Prime) (h : p ∣ n)
  proof: by
  have h1 := totient_gcd_mul_totient_mul p n
  rw [gcd_eq_left h]; rw [mul_assoc] at h1
  simpa [(totient_pos.2 hp.pos).ne', mul_comm] using h1

中文:
定理 totient_mul_of_prime_of_dvd
  条件: {p n : 自然数} (hp : p.素) (h : p ∣ n)
  证明: by
  have h1 := totient_gcd_mul_totient_mul p n
  rw [gcd_eq_left h]; rw [mul_assoc] at h1
  simpa [(totient_pos.2 hp.pos).ne', mul_comm] using h1

Depends on / 依赖: gcd_eq_left, hp.pos, mul_assoc, mul_comm, totient_gcd_mul_totient_mul, totient_pos
-/
theorem totient_mul_of_prime_of_dvd {p n : Nat} (hp : p.Prime) (h : p ∣ n) :
    (p * n).totient = p * n.totient := by
  have h1 := totient_gcd_mul_totient_mul p n
  rw [gcd_eq_left h]; rw [mul_assoc] at h1
  simpa [(totient_pos.2 hp.pos).ne', mul_comm] using h1

/--
theorem `totient_mul_of_prime_of_not_dvd` / 定理 `totient_mul_of_prime_of_not_dvd`

English:
theorem totient_mul_of_prime_of_not_dvd
  given: {p n : Nat} (hp : p.Prime) (h : ¬p ∣ n)
  proof: by
  rw [totient_mul _]; rw [totient_prime hp]
  simpa [h] using coprime_or_dvd_of_prime hp n

中文:
定理 totient_mul_of_prime_of_not_dvd
  条件: {p n : 自然数} (hp : p.素) (h : ¬p ∣ n)
  证明: by
  rw [totient_mul _]; rw [totient_prime hp]
  simpa [h] using coprime_or_dvd_of_prime hp n

Depends on / 依赖: coprime_or_dvd_of_prime, totient_mul, totient_prime
-/
theorem totient_mul_of_prime_of_not_dvd {p n : Nat} (hp : p.Prime) (h : ¬p ∣ n) :
    (p * n).totient = (p - 1) * n.totient := by
  rw [totient_mul _]; rw [totient_prime hp]
  simpa [h] using coprime_or_dvd_of_prime hp n

/--
theorem `totient_two_mul_of_even` / 定理 `totient_two_mul_of_even`

English:
theorem totient_two_mul_of_even
  given: {n : Nat} (hn : Even n)
  statement: (2 * n).totient = 2 * n.totient
  proof: totient_mul_of_prime_of_dvd prime_two hn.two_dvd

中文:
定理 totient_two_mul_of_even
  条件: {n : 自然数} (hn : Even n)
  结论: (2 * n).totient = 2 * n.totient
  证明: totient_mul_of_prime_of_dvd prime_two hn.two_dvd

Depends on / 依赖: hn.two_dvd, prime_two, totient_mul_of_prime_of_dvd, two_dvd
-/
theorem totient_two_mul_of_even {n : Nat} (hn : Even n) : (2 * n).totient = 2 * n.totient :=
  totient_mul_of_prime_of_dvd prime_two hn.two_dvd

/--
theorem `totient_two_mul_of_odd` / 定理 `totient_two_mul_of_odd`

English:
theorem totient_two_mul_of_odd
  given: {n : Nat} (hn : Odd n)
  statement: (2 * n).totient = n.totient
  proof: by
  rw [totient_mul_of_prime_of_not_dvd prime_two hn.not_two_dvd_nat]; rw [Nat.add_one_sub_one 1]; rw [one_mul]

中文:
定理 totient_two_mul_of_odd
  条件: {n : 自然数} (hn : Odd n)
  结论: (2 * n).totient = n.totient
  证明: by
  rw [totient_mul_of_prime_of_not_dvd prime_two hn.not_two_dvd_nat]; rw [Nat.add_one_sub_one 1]; rw [one_mul]

Depends on / 依赖: Nat.add_one_sub_one, add_one_sub_one, hn.not_two_dvd_nat, not_two_dvd_nat, one_mul, prime_two, totient_mul_of_prime_of_not_dvd
-/
theorem totient_two_mul_of_odd {n : Nat} (hn : Odd n) : (2 * n).totient = n.totient := by
  rw [totient_mul_of_prime_of_not_dvd prime_two hn.not_two_dvd_nat]; rw [Nat.add_one_sub_one 1]; rw [one_mul]

/--
theorem `eq_or_eq_of_totient_eq_totient` / 定理 `eq_or_eq_of_totient_eq_totient`

English:
theorem eq_or_eq_of_totient_eq_totient
  given: {a b : Nat} (h : a ∣ b) (h' : a.totient = b.totient)
  proof: by
  by_cases ha : a = 0
  · rw [ha, totient_zero, eq_comm, totient_eq_zero] at h'
    simp [ha, h']
  by_cases hb : b = 0
  · rw [hb, totient_zero, totient_eq_zero] at h'
    exact False.elim (ha h')
  obtain ⟨c, rfl⟩ := h
  suffices a.Coprime c by
    rw [totient_mul this]; rw [eq_comm]; rw [mul_e

中文:
定理 eq_or_eq_of_totient_eq_totient
  条件: {a b : 自然数} (h : a ∣ b) (h' : a.totient = b.totient)
  证明: by
  by_cases ha : a = 0
  · rw [ha, totient_zero, eq_comm, totient_eq_zero] at h'
    simp [ha, h']
  by_cases hb : b = 0
  · rw [hb, totient_zero, totient_eq_zero] at h'
    exact False.elim (ha h')
  obtain ⟨c, rfl⟩ := h
  suffices a.Coprime c by
    rw [totient_mul this]; rw [eq_comm]; rw [mul_e

Depends on / 依赖: Coprime, False.elim, a.Coprime, a.totient, coprime_of_dvd, eq_comm, mul_comm, mul_eq_left, totient, totient_eq_one_iff, totient_eq_zero, totient_eq_zero.not.mpr, totient_mul, totient_zero
-/
theorem eq_or_eq_of_totient_eq_totient {a b : Nat} (h : a ∣ b) (h' : a.totient = b.totient) :
    a = b ∨ 2 * a = b := by
  by_cases ha : a = 0
  · rw [ha, totient_zero, eq_comm, totient_eq_zero] at h'
    simp [ha, h']
  by_cases hb : b = 0
  · rw [hb, totient_zero, totient_eq_zero] at h'
    exact False.elim (ha h')
  obtain ⟨c, rfl⟩ := h
  suffices a.Coprime c by
    rw [totient_mul this]; rw [eq_comm]; rw [mul_eq_left (totient_eq_zero.not.mpr ha)]; rw [totient_eq_one_iff] at h'
    obtain rfl | rfl := h'
    · simp
    · simp [mul_comm]
  refine coprime_of_dvd fun p hp hap => ?_
  rintro ⟨d, rfl⟩
  suffices a.totient < (p * a * d).totient by
    rw [← mul_assoc]; rw [mul_comm a] at h'
    exact h'.not_lt this
  rw [mul_comm p]
  refine lt_of_lt_of_le ?_ (Nat.le_of_dvd ?_ (totient_dvd_of_dvd ⟨d, rfl⟩))
  · rw [mul_comm, totient_mul_of_prime_of_dvd hp hap, Nat.lt_mul_iff_one_lt_left]
    · exact hp.one_lt
· exact totient_pos.mpr pos_of_ne_zero ha
· exact totient_pos.mpr zero_lt_of_ne_zero (by rwa [mul_assoc])

/--
theorem `_root_.Even.eq_of_totient_eq_totient` / 定理 `_root_.Even.eq_of_totient_eq_totient`

English:
theorem _root_.Even.eq_of_totient_eq_totient
  statement: {a b : Nat} (h : a ∣ b) (ha : Even a)
  proof: by
  by_cases ha' : a = 0
  · rw [ha', totient_zero, eq_comm, totient_eq_zero] at h'
    rw [h']; rw [ha']
  refine (eq_or_eq_of_totient_eq_totient h h').resolve_right fun h => ?_
  rw [← h]; rw [totient_mul_of_prime_of_dvd (prime_two) (even_iff_two_dvd.mp ha)]; rw [eq_comm]; rw [mul_eq_right (totie

中文:
定理 _root_.Even.eq_of_totient_eq_totient
  结论: {a b : 自然数} (h : a ∣ b) (ha : Even a)
  证明: by
  by_cases ha' : a = 0
  · rw [ha', totient_zero, eq_comm, totient_eq_zero] at h'
    rw [h']; rw [ha']
  refine (eq_or_eq_of_totient_eq_totient h h').resolve_right fun h => ?_
  rw [← h]; rw [totient_mul_of_prime_of_dvd (prime_two) (even_iff_two_dvd.mp ha)]; rw [eq_comm]; rw [mul_eq_right (totie

Depends on / 依赖: eq_comm, eq_or_eq_of_totient_eq_totient, even_iff_two_dvd, even_iff_two_dvd.mp, mul_eq_right, prime_two, resolve_right, totient_eq_zero, totient_eq_zero.not.mpr, totient_mul_of_prime_of_dvd, totient_zero
-/
theorem _root_.Even.eq_of_totient_eq_totient {a b : Nat} (h : a ∣ b) (ha : Even a)
    (h' : a.totient = b.totient) : a = b := by
  by_cases ha' : a = 0
  · rw [ha', totient_zero, eq_comm, totient_eq_zero] at h'
    rw [h']; rw [ha']
  refine (eq_or_eq_of_totient_eq_totient h h').resolve_right fun h => ?_
  rw [← h]; rw [totient_mul_of_prime_of_dvd (prime_two) (even_iff_two_dvd.mp ha)]; rw [eq_comm]; rw [mul_eq_right (totient_eq_zero.not.mpr ha')] at h'
  lia

/--
theorem `prime_pow_pow_totient_ediv_prod` / 定理 `prime_pow_pow_totient_ediv_prod`

English:
theorem prime_pow_pow_totient_ediv_prod
  given: {p k : Nat} (hp : p.Prime) (hk : 0 < k)
  proof: by
  have h : p ^ (k - 1) <= k * (p ^ (k - 1) * (p - 1)) := by
    rw [mul_left_comm]
    refine le_mul_of_one_le_right (Nat.zero_le _) ?_
exact Right.one_le_mul hk Nat.le_sub_one_of_lt hp.one_lt
  simp_rw [Nat.totient_prime_pow hp hk, Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton,
   

中文:
定理 prime_pow_pow_totient_ediv_prod
  条件: {p k : 自然数} (hp : p.素) (hk : 0 < k)
  证明: by
  have h : p ^ (k - 1) <= k * (p ^ (k - 1) * (p - 1)) := by
    rw [mul_left_comm]
    refine le_mul_of_one_le_right (Nat.zero_le _) ?_
exact Right.one_le_mul hk Nat.le_sub_one_of_lt hp.one_lt
  simp_rw [Nat.totient_prime_pow hp hk, Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton,
   

Depends on / 依赖: Finset, Finset.prod_singleton, Nat.le_sub_one_of_lt, Nat.mul_div_left, Nat.mul_sub, Nat.pow_div, Nat.primeFactors_prime_pow, Nat.sub_mul, Nat.sub_pos_of_lt, Nat.totient_prime_pow, Nat.zero_le, Right.one_le_mul, hk.ne, hp.one_lt, hp.pos, le_mul_of_one_le_right, le_sub_one_of_lt, mul_div_left, mul_left_comm, mul_one
-/
theorem prime_pow_pow_totient_ediv_prod {p k : Nat} (hp : p.Prime) (hk : 0 < k) :
      (p ^ k : Nat) ^ φ (p ^ k) / ∏ q in (p ^ k).primeFactors, q ^ (φ (p ^ k) / (q - 1)) =
        p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have h : p ^ (k - 1) <= k * (p ^ (k - 1) * (p - 1)) := by
    rw [mul_left_comm]
    refine le_mul_of_one_le_right (Nat.zero_le _) ?_
exact Right.one_le_mul hk Nat.le_sub_one_of_lt hp.one_lt
  simp_rw [Nat.totient_prime_pow hp hk, Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton,
    Nat.mul_div_left _ (Nat.sub_pos_of_lt hp.one_lt), ← pow_mul]
  rw [Nat.pow_div h hp.pos]
  simp_rw [Nat.sub_mul, one_mul, Nat.mul_sub, mul_one]
  ring_nf

/--
theorem `prod_primeFactors_pow_totient_ediv_dvd` / 定理 `prod_primeFactors_pow_totient_ediv_dvd`

English:
theorem prod_primeFactors_pow_totient_ediv_dvd
  given: {n : Nat} (hn : 0 < n)
  proof: by
  have := Nat.prod_primeFactors_dvd n
  rw [← Nat.pow_dvd_pow_iff (Nat.totient_pos.mpr hn).ne']; rw [← Finset.prod_pow] at this
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_) this
exact Nat.pow_dvd_pow p Nat.div_le_self _ _

中文:
定理 prod_primeFactors_pow_totient_ediv_dvd
  条件: {n : 自然数} (hn : 0 < n)
  证明: by
  have := Nat.prod_primeFactors_dvd n
  rw [← Nat.pow_dvd_pow_iff (Nat.totient_pos.mpr hn).ne']; rw [← Finset.prod_pow] at this
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_) this
exact Nat.pow_dvd_pow p Nat.div_le_self _ _

Depends on / 依赖: Algebra, Finite, Finset, Finset.prod_dvd_prod_of_dvd, Finset.prod_pow, Nat.div_le_self, Nat.pow_dvd_pow, Nat.pow_dvd_pow_iff, Nat.prod_primeFactors_dvd, Nat.totient_pos.mpr, div_le_self, dvd_trans, pow_dvd_pow, pow_dvd_pow_iff, prod_dvd_prod_of_dvd, prod_pow, prod_primeFactors_dvd, totient_pos
-/
theorem prod_primeFactors_pow_totient_ediv_dvd {n : Nat} (hn : 0 < n) :
    ∏ p in n.primeFactors, p ^ (φ n / (p - 1)) ∣ n ^ φ n := by
  have := Nat.prod_primeFactors_dvd n
  rw [← Nat.pow_dvd_pow_iff (Nat.totient_pos.mpr hn).ne']; rw [← Finset.prod_pow] at this
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_) this
exact Nat.pow_dvd_pow p Nat.div_le_self _ _

end Nat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `Nat.totient`. -/
@[positivity Nat.totient _]
meta def evalNatTotient : PositivityExt where eval {u α} z p e :=
  match p with | none => pure .none | some p => do
  match u, α, e with
  | 0, ~q(Nat), ~q(Nat.totient $n) =>
    match ← core z p n with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Nat.totient_pos.mpr $pa)
    | _ => failure
  | _, _, _ => throwError "not Nat.totient"

end Mathlib.Meta.Positivity
