/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Emirhan Duysak, Adem Alp Gök, Junyan Xu
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# The integers form a linear ordered ring

This file contains:
* instances on `ℤ`. The stronger one is `Int.instLinearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Nat

namespace Int

/--
Instance `instIsStrictOrderedRing` / 实例 `instIsStrictOrderedRing`

English:
instance instIsStrictOrderedRing
  signature: : IsStrictOrderedRing Int
  body: .of_mul_pos @Int.mul_pos

中文:
实例 instIsStrictOrderedRing
  签名: : 是StrictOrdered环 整数
  定义体: .of_mul_pos @Int.mul_pos

Depends on / 依赖: Int.mul_pos, mul_pos, of_mul_pos
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing Int := .of_mul_pos @Int.mul_pos


/--
lemma `isCompl_even_odd` / 引理 `isCompl_even_odd`

English:
lemma isCompl_even_odd
  statement: IsCompl { n : Int | Even n } { n | Odd n }
  proof: by
  simp [← not_even_iff_odd, ← Set.compl_ofPred, isCompl_compl]

@[simp]

中文:
引理 isCompl_even_odd
  结论: 是补集 { n : 整数 | Even n } { n | Odd n }
  证明: by
  simp [← not_even_iff_odd, ← Set.compl_ofPred, isCompl_compl]

@[simp]

Depends on / 依赖: Set.compl_ofPred, compl_ofPred, isCompl_compl, not_even_iff_odd
-/
lemma isCompl_even_odd : IsCompl { n : Int | Even n } { n | Odd n } := by
  simp [← not_even_iff_odd, ← Set.compl_ofPred, isCompl_compl]

@[simp]
/--
lemma `_root_.Nat.cast_natAbs` / 引理 `_root_.Nat.cast_natAbs`

English:
lemma _root_.Nat.cast_natAbs
  given: {α : Type*} [AddGroupWithOne α] (n : Int)
  statement: (n.natAbs : α) = |n|
  proof: by
  rw [← natCast_natAbs]; rw [Int.cast_natCast]

中文:
引理 _root_.自然数.cast_natAbs
  条件: {α : 类型} [加法带幺群 α] (n : 整数)
  结论: (n.natAbs : α) = |n|
  证明: by
  rw [← natCast_natAbs]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, cast_natCast, natCast_natAbs
-/
lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : Int) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs]; rw [Int.cast_natCast]

/--
lemma `two_le_iff_pos_of_even` / 引理 `two_le_iff_pos_of_even`

English:
lemma two_le_iff_pos_of_even
  given: {m : Int} (even : Even m)
  statement: 2 <= m ↔ 0 < m
  proof: le_iff_pos_of_dvd (by decide) even.two_dvd

中文:
引理 two_le_iff_pos_of_even
  条件: {m : 整数} (even : Even m)
  结论: 2 <= m ↔ 0 < m
  证明: le_iff_pos_of_dvd (by decide) even.two_dvd

Depends on / 依赖: even.two_dvd, le_iff_pos_of_dvd, two_dvd
-/
lemma two_le_iff_pos_of_even {m : Int} (even : Even m) : 2 <= m ↔ 0 < m :=
  le_iff_pos_of_dvd (by decide) even.two_dvd

/--
lemma `add_two_le_iff_lt_of_even_sub` / 引理 `add_two_le_iff_lt_of_even_sub`

English:
lemma add_two_le_iff_lt_of_even_sub
  given: {m n : Int} (even : Even (n - m))
  statement: m + 2 <= n ↔ m < n
  proof: by
  grind

中文:
引理 add_two_le_iff_lt_of_even_sub
  条件: {m n : 整数} (even : Even (n - m))
  结论: m + 2 <= n ↔ m < n
  证明: by
  grind
-/
lemma add_two_le_iff_lt_of_even_sub {m n : Int} (even : Even (n - m)) : m + 2 <= n ↔ m < n := by
  grind

end Int

/--
theorem `Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le` / 定理 `Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le`

English:
theorem Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le
  statement: (p q n : Nat) (dvd : p.gcd q ∣ n)
  proof: by
  obtain _ | p := p
  · have ⟨b, eq⟩ := q.gcd_zero_left ▸ dvd
    exact ⟨0, b, by simpa [mul_comm, eq_comm] using eq⟩
  obtain _ | q := q
  · have ⟨a, eq⟩ := p.gcd_zero_right ▸ dvd
    exact ⟨a, 0, by simpa [mul_comm, eq_comm] using eq⟩
  rw [← Int.gcd_natCast_natCast]; rw [Int.gcd_dvd_iff] at dv

中文:
定理 自然数.存在_add_mul_eq_of_gcd_dvd_of_mul_pred_le
  结论: (p q n : 自然数) (dvd : p.最大公约数 q ∣ n)
  证明: by
  obtain _ | p := p
  · have ⟨b, eq⟩ := q.gcd_zero_left ▸ dvd
    exact ⟨0, b, by simpa [mul_comm, eq_comm] using eq⟩
  obtain _ | q := q
  · have ⟨a, eq⟩ := p.gcd_zero_right ▸ dvd
    exact ⟨a, 0, by simpa [mul_comm, eq_comm] using eq⟩
  rw [← Int.gcd_natCast_natCast]; rw [Int.gcd_dvd_iff] at dv

Depends on / 依赖: Int.gcd_dvd_iff, Int.gcd_natCast_natCast, Nat.cast_injective, a.toNat, add_assoc, add_mul, b.toNat, cast_injective, eq_comm, gcd_dvd_iff, gcd_natCast_natCast, gcd_zero_left, gcd_zero_right, mul_comm, p.gcd_zero_right, p.succ, q.gcd_zero_left, q.succ
-/
theorem Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (p q n : Nat) (dvd : p.gcd q ∣ n)
    (le : p.pred * q.pred <= n) : exists a b : Nat, a * p + b * q = n := by
  obtain _ | p := p
  · have ⟨b, eq⟩ := q.gcd_zero_left ▸ dvd
    exact ⟨0, b, by simpa [mul_comm, eq_comm] using eq⟩
  obtain _ | q := q
  · have ⟨a, eq⟩ := p.gcd_zero_right ▸ dvd
    exact ⟨a, 0, by simpa [mul_comm, eq_comm] using eq⟩
  rw [← Int.gcd_natCast_natCast]; rw [Int.gcd_dvd_iff] at dvd
  have ⟨a_n, b_n, eq⟩ := dvd
  let a := a_n % q.succ
  let b := b_n + a_n / q.succ * p.succ
  refine ⟨a.toNat, b.toNat, Nat.cast_injective (R := Int) ?_⟩
  have : a * p.succ + b * q.succ = n := by rw [add_mul, ← add_assoc,
    add_right_comm, mul_right_comm, ← add_mul, Int.emod_add_ediv_mul, eq, mul_comm, mul_comm b_n]
  rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [Int.natCast_toNat_eq_self.mpr
    (Int.emod_nonneg _ <| by lia)]; rw [Int.natCast_toNat_eq_self.mpr]; rw [this]
  -- show b ≥ 0 by contradiction
  by_contra hb
  replace hb : b <= -1 := by lia
  apply lt_irrefl (n : Int)
  have ha := Int.emod_lt a_n (by lia : (q.succ : Int) != 0)
  rw [p.pred_succ]; rw [q.pred_succ] at le
  calc n = a * p.succ + b * q.succ := this.symm
       _ <= q * p.succ + -1 * q.succ := by gcongr <;> lia
       _ = p * q - 1 := by simp_rw [Nat.cast_succ, mul_add, mul_comm]; lia
       _ <= n - 1 := by rwa [sub_le_sub_iff_right, ← Nat.cast_mul, Nat.cast_le]
       _ < n := by lia
