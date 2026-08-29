/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Data.Nat.Fib.Basic

/-!

# Fibonacci numbers extended onto the integers

This file defines the Fibonacci sequence on the integers.

Definition of the sequence: `F₀ = 0`, `F₁ = 1`, and `Fₙ₊₂ = Fₙ₊₁ + Fₙ`
(same as the natural number version `Nat.fib`, but here `n` is an integer).

-/

@[expose] public section

namespace Int

/-- The Fibonacci sequence for integers. This satisfies `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`.

This is an extension of `Nat.fib`. -/
@[pp_nodot]
/--
Definition of `fib` / `fib` 的定义

English:
definition fib
  signature: (n : Int)
  body: if 0 <= n then n.toNat.fib else
  if Even n then -(-n).toNat.fib else (-n).toNat.fib

中文:
定义 fib
  签名: (n : 整数)
  定义体: if 0 <= n then n.toNat.fib else
  if Even n then -(-n).toNat.fib else (-n).toNat.fib

Depends on / 依赖: n.toNat.fib, toNat.fib
-/
def fib (n : Int) : Int :=
  if 0 <= n then n.toNat.fib else
  if Even n then -(-n).toNat.fib else (-n).toNat.fib

/--
theorem `fib_natCast` / 定理 `fib_natCast`

English:
theorem fib_natCast
  given: (n : Nat)
  statement: fib n = Nat.fib n
  proof: rfl

中文:
定理 fib_natCast
  条件: (n : 自然数)
  结论: fib n = 自然数.fib n
  证明: rfl
-/
@[simp] theorem fib_natCast (n : Nat) : fib n = Nat.fib n := rfl
/--
theorem `fib_zero` / 定理 `fib_zero`

English:
theorem fib_zero
  statement: fib 0 = 0
  proof: rfl

中文:
定理 fib_zero
  结论: fib 0 = 0
  证明: rfl
-/
@[simp] theorem fib_zero : fib 0 = 0 := rfl
/--
theorem `fib_one` / 定理 `fib_one`

English:
theorem fib_one
  statement: fib 1 = 1
  proof: rfl

中文:
定理 fib_one
  结论: fib 1 = 1
  证明: rfl
-/
@[simp] theorem fib_one : fib 1 = 1 := rfl
/--
theorem `fib_two` / 定理 `fib_two`

English:
theorem fib_two
  statement: fib 2 = 1
  proof: rfl

中文:
定理 fib_two
  结论: fib 2 = 1
  证明: rfl
-/
@[simp] theorem fib_two : fib 2 = 1 := rfl
/--
theorem `fib_neg_one` / 定理 `fib_neg_one`

English:
theorem fib_neg_one
  statement: fib (-1) = 1
  proof: rfl

中文:
定理 fib_neg_one
  结论: fib (-1) = 1
  证明: rfl
-/
@[simp] theorem fib_neg_one : fib (-1) = 1 := rfl
/--
theorem `fib_neg_two` / 定理 `fib_neg_two`

English:
theorem fib_neg_two
  statement: fib (-2) = -1
  proof: rfl

中文:
定理 fib_neg_two
  结论: fib (-2) = -1
  证明: rfl
-/
@[simp] theorem fib_neg_two : fib (-2) = -1 := rfl

/--
theorem `fib_of_nonneg` / 定理 `fib_of_nonneg`

English:
theorem fib_of_nonneg
  given: {n : Int} (hn : 0 <= n)
  statement: fib n = n.toNat.fib
  proof: by simp [fib, hn]

中文:
定理 fib_of_nonneg
  条件: {n : 整数} (hn : 0 <= n)
  结论: fib n = n.to自然数.fib
  证明: by simp [fib, hn]
-/
theorem fib_of_nonneg {n : Int} (hn : 0 <= n) : fib n = n.toNat.fib := by simp [fib, hn]

/--
theorem `fib_of_odd` / 定理 `fib_of_odd`

English:
theorem fib_of_odd
  given: {n : Int} (hn : Odd n)
  statement: fib n = (natAbs n).fib
  proof: by grind [fib]

中文:
定理 fib_of_odd
  条件: {n : 整数} (hn : Odd n)
  结论: fib n = (natAbs n).fib
  证明: by grind [fib]
-/
theorem fib_of_odd {n : Int} (hn : Odd n) : fib n = (natAbs n).fib := by grind [fib]

/--
theorem `fib_two_mul_add_one_eq_natFib_natAbs` / 定理 `fib_two_mul_add_one_eq_natFib_natAbs`

English:
theorem fib_two_mul_add_one_eq_natFib_natAbs
  given: {n : Int}
  statement: fib (2 * n + 1) = (natAbs (2 * n + 1)).fib
  proof: fib_of_odd odd_two_mul_add_one n

中文:
定理 fib_two_mul_add_one_eq_natFib_natAbs
  条件: {n : 整数}
  结论: fib (2 * n + 1) = (natAbs (2 * n + 1)).fib
  证明: fib_of_odd odd_two_mul_add_one n

Depends on / 依赖: fib_of_odd, odd_two_mul_add_one
-/
theorem fib_two_mul_add_one_eq_natFib_natAbs {n : Int} : fib (2 * n + 1) = (natAbs (2 * n + 1)).fib :=
fib_of_odd odd_two_mul_add_one n

/--
theorem `fib_two_mul_add_one_pos` / 定理 `fib_two_mul_add_one_pos`

English:
theorem fib_two_mul_add_one_pos
  given: {n : Int}
  statement: 0 < fib (2 * n + 1)
  proof: by
  grind [fib_two_mul_add_one_eq_natFib_natAbs, Nat.fib_pos]

中文:
定理 fib_two_mul_add_one_pos
  条件: {n : 整数}
  结论: 0 < fib (2 * n + 1)
  证明: by
  grind [fib_two_mul_add_one_eq_natFib_natAbs, Nat.fib_pos]

Depends on / 依赖: Nat.fib_pos, fib_pos, fib_two_mul_add_one_eq_natFib_natAbs
-/
theorem fib_two_mul_add_one_pos {n : Int} : 0 < fib (2 * n + 1) := by
  grind [fib_two_mul_add_one_eq_natFib_natAbs, Nat.fib_pos]

/--
theorem `fib_neg_natCast` / 定理 `fib_neg_natCast`

English:
theorem fib_neg_natCast
  given: (n : Nat)
  statement: fib (-n) = (-1) ^ (n + 1) * n.fib
  proof: by
  rcases n.even_or_odd with (hn | hn)
  · simp [fib, hn, pow_add]
  · simp [fib_of_odd, hn]

中文:
定理 fib_neg_natCast
  条件: (n : 自然数)
  结论: fib (-n) = (-1) ^ (n + 1) * n.fib
  证明: by
  rcases n.even_or_odd with (hn | hn)
  · simp [fib, hn, pow_add]
  · simp [fib_of_odd, hn]

Depends on / 依赖: even_or_odd, fib_of_odd, n.even_or_odd, pow_add
-/
theorem fib_neg_natCast (n : Nat) : fib (-n) = (-1) ^ (n + 1) * n.fib := by
  rcases n.even_or_odd with (hn | hn)
  · simp [fib, hn, pow_add]
  · simp [fib_of_odd, hn]

/--
theorem `fib_neg` / 定理 `fib_neg`

English:
theorem fib_neg
  given: (n : Int)
  statement: fib (-n) = if Even n then -fib n else fib n
  proof: by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [fib_neg_natCast]))

中文:
定理 fib_neg
  条件: (n : 整数)
  结论: fib (-n) = if Even n then -fib n else fib n
  证明: by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [fib_neg_natCast]))

Depends on / 依赖: eq_nat_or_neg, fib_neg_natCast, n.eq_nat_or_neg
-/
theorem fib_neg (n : Int) : fib (-n) = if Even n then -fib n else fib n := by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [fib_neg_natCast]))

/--
theorem `coe_fib_neg` / 定理 `coe_fib_neg`

English:
theorem coe_fib_neg
  given: (n : Int)
  statement: (fib (-n) : Rat) = (-1) ^ (n + 1) * fib n
  proof: by
  aesop (add safe (by rw [fib_neg, neg_one_zpow_eq_ite]))

中文:
定理 coe_fib_neg
  条件: (n : 整数)
  结论: (fib (-n) : 有理数) = (-1) ^ (n + 1) * fib n
  证明: by
  aesop (add safe (by rw [fib_neg, neg_one_zpow_eq_ite]))

Depends on / 依赖: fib_neg, neg_one_zpow_eq_ite
-/
theorem coe_fib_neg (n : Int) : (fib (-n) : Rat) = (-1) ^ (n + 1) * fib n := by
  aesop (add safe (by rw [fib_neg, neg_one_zpow_eq_ite]))

/--
theorem `fib_add_two` / 定理 `fib_add_two`

English:
theorem fib_add_two
  given: (n : Int)
  statement: fib (n + 2) = fib n + fib (n + 1)
  proof: by
  rcases n with (n | n)
  · dsimp
    rw [← Nat.cast_ofNat]; rw [← Nat.cast_add]; rw [← Nat.cast_add_one]; rw [fib_natCast]; rw [fib_natCast]; rw [Nat.fib_add_two]; rw [Nat.cast_add]
  · rw [negSucc_eq, ← Nat.cast_add_one, fib_neg_natCast]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, reduceNeg, add_comm,
      add_assoc, reduceAdd, add_neg_cancel_comm_assoc, fib_neg_natCast]
    if hn0 : n = 0 then simp [hn0] else
    symm
    calc _ = (-1) ^ (n + 1) * ((n.fib - (n + 1).fib : Int)) := by grind
      _ = _ := by
        have : -(n : Int) + 1 = -((n - 1 : Nat) : Int) := by grind
        obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add, ← two_mul,
            Nat.sub_add_cancel (by grind)]
          simp
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add]
          simp

中文:
定理 fib_add_two
  条件: (n : 整数)
  结论: fib (n + 2) = fib n + fib (n + 1)
  证明: by
  rcases n with (n | n)
  · dsimp
    rw [← Nat.cast_ofNat]; rw [← Nat.cast_add]; rw [← Nat.cast_add_one]; rw [fib_natCast]; rw [fib_natCast]; rw [Nat.fib_add_two]; rw [Nat.cast_add]
  · rw [negSucc_eq, ← Nat.cast_add_one, fib_neg_natCast]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, reduceNeg, add_comm,
      add_assoc, reduceAdd, add_neg_cancel_comm_assoc, fib_neg_natCast]
    if hn0 : n = 0 then simp [hn0] else
    symm
    calc _ = (-1) ^ (n + 1) * ((n.fib - (n + 1).fib : Int)) := by grind
      _ = _ := by
        have : -(n : Int) + 1 = -((n - 1 : Nat) : Int) := by grind
        obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add, ← two_mul,
            Nat.sub_add_cancel (by grind)]
          simp
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add]
          simp

Depends on / 依赖: Nat.cast_add, Nat.cast_add_one, Nat.cast_ofNat, Nat.cast_one, Nat.fib_add_two, add_assoc, add_comm, add_neg_cancel_comm_assoc, cast_add, cast_add_one, cast_ofNat, cast_one, fib_add_two, fib_natCast, fib_neg_natCast, n.fib, negSucc_eq, neg_add_rev, reduceAdd, reduceNeg
-/
theorem fib_add_two (n : Int) : fib (n + 2) = fib n + fib (n + 1) := by
  rcases n with (n | n)
  · dsimp
    rw [← Nat.cast_ofNat]; rw [← Nat.cast_add]; rw [← Nat.cast_add_one]; rw [fib_natCast]; rw [fib_natCast]; rw [Nat.fib_add_two]; rw [Nat.cast_add]
  · rw [negSucc_eq, ← Nat.cast_add_one, fib_neg_natCast]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, reduceNeg, add_comm,
      add_assoc, reduceAdd, add_neg_cancel_comm_assoc, fib_neg_natCast]
    if hn0 : n = 0 then simp [hn0] else
    symm
    calc _ = (-1) ^ (n + 1) * ((n.fib - (n + 1).fib : Int)) := by grind
      _ = _ := by
        have : -(n : Int) + 1 = -((n - 1 : Nat) : Int) := by grind
        obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add, ← two_mul,
            Nat.sub_add_cancel (by grind)]
          simp
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add]
          simp

/--
theorem `fib_eq_fib_add_two_sub_fib_add_one` / 定理 `fib_eq_fib_add_two_sub_fib_add_one`

English:
theorem fib_eq_fib_add_two_sub_fib_add_one
  given: (n : Int)
  proof: by
  simp only [fib_add_two, add_sub_cancel_right]

中文:
定理 fib_eq_fib_add_two_sub_fib_add_one
  条件: (n : 整数)
  证明: by
  simp only [fib_add_two, add_sub_cancel_right]

Depends on / 依赖: add_sub_cancel_right, fib_add_two
-/
theorem fib_eq_fib_add_two_sub_fib_add_one (n : Int) :
    fib n = fib (n + 2) - fib (n + 1) := by
  simp only [fib_add_two, add_sub_cancel_right]

/--
theorem `fib_add_one` / 定理 `fib_add_one`

English:
theorem fib_add_one
  given: (n : Int)
  statement: fib (n + 1) = fib (n + 2) - fib n
  proof: by
  simp only [fib_add_two, add_sub_cancel_left]

中文:
定理 fib_add_one
  条件: (n : 整数)
  结论: fib (n + 1) = fib (n + 2) - fib n
  证明: by
  simp only [fib_add_two, add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, fib_add_two
-/
theorem fib_add_one (n : Int) : fib (n + 1) = fib (n + 2) - fib n := by
  simp only [fib_add_two, add_sub_cancel_left]

/--
theorem `fib_eq_zero` / 定理 `fib_eq_zero`

English:
theorem fib_eq_zero
  given: {n : Int}
  statement: fib n = 0 ↔ n = 0
  proof: by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg <;> simp [fib_neg_natCast]

中文:
定理 fib_eq_zero
  条件: {n : 整数}
  结论: fib n = 0 ↔ n = 0
  证明: by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg <;> simp [fib_neg_natCast]
-/
@[simp] theorem fib_eq_zero {n : Int} : fib n = 0 ↔ n = 0 := by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg <;> simp [fib_neg_natCast]

-- auxiliary for `fib_add`
/--
theorem `fib_natCast_add` / 定理 `fib_natCast_add`

English:
theorem fib_natCast_add
  proof: by grind [fib_add_two]
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : Nat) + n) := by
        rw [fib_natCast_add]; grind
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
          fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
      _ = _ := by grind [fib_add_two]

中文:
定理 fib_natCast_add
  证明: by grind [fib_add_two]
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : Nat) + n) := by
        rw [fib_natCast_add]; grind
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
          fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
      _ = _ := by grind [fib_add_two]
-/
private theorem fib_natCast_add :
    forall (m : Nat) (n : Int), fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1)
  | 0, _ => by simp
  | 1, _ => by simp [add_comm]
  | m + 2, n => by
    calc _ = fib (m + n) + fib (m + n + 1) := by grind [fib_add_two]
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : Nat) + n) := by
        rw [fib_natCast_add]; grind
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
          fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
      _ = _ := by grind [fib_add_two]

-- auxiliary for `fib_add`
/--
theorem `fib_add_natCast` / 定理 `fib_add_natCast`

English:
theorem fib_add_natCast
  proof: by grind [fib_add_two]
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : Nat) + n) := by
        rw [fib_natCast_add]; grind
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
          fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
      _ = _ := by grind [fib_add_two]

中文:
定理 fib_add_natCast
  证明: by grind [fib_add_two]
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : Nat) + n) := by
        rw [fib_natCast_add]; grind
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
          fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
      _ = _ := by grind [fib_add_two]
-/
private theorem fib_add_natCast :
    forall (m : Int) (n : Nat), fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1)
  | _, 0 => by simp
  | _, 1 => by grind [fib_add_two, fib_two, fib_one]
  | n, m + 2 =>
    calc _ = fib (m + n) + fib (m + n + 1) := by grind [fib_add_two]
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : Nat) + n) := by
        rw [fib_natCast_add]; grind
      _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
          fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
      _ = _ := by grind [fib_add_two]

-- auxiliary for `fib_add`
/--
theorem `fib_neg_natCast_add_neg_natCast` / 定理 `fib_neg_natCast_add_neg_natCast`

English:
theorem fib_neg_natCast_add_neg_natCast
  proof: by grind [fib_add_two]
      _ = fib (-m - 1) * fib (-n) + fib (-m) * fib (-n + 1) -
          fib (-m - 1) * fib (-n - 1) - fib (-m) * fib (-n) := by
        conv_lhs => rw [fib_neg_natCast_add_neg_natCast, fib_neg_natCast_add_neg_natCast]
        grind
      _ = _ := by grind [fib_add_two]

中文:
定理 fib_neg_natCast_add_neg_natCast
  证明: by grind [fib_add_two]
      _ = fib (-m - 1) * fib (-n) + fib (-m) * fib (-n + 1) -
          fib (-m - 1) * fib (-n - 1) - fib (-m) * fib (-n) := by
        conv_lhs => rw [fib_neg_natCast_add_neg_natCast, fib_neg_natCast_add_neg_natCast]
        grind
      _ = _ := by grind [fib_add_two]
-/
private theorem fib_neg_natCast_add_neg_natCast :
    forall (m n : Nat), fib (-m + -n) = fib (-m - 1) * fib (-n) + fib (-m) * fib (-n + 1)
  | _, 0 => by simp
  | _, 1 => by simp [sub_eq_neg_add, add_comm]
  | m, n + 2 =>
    calc _ = fib (-m + -n) - fib (-m + -(n + 1 : Nat)) := by grind [fib_add_two]
      _ = fib (-m - 1) * fib (-n) + fib (-m) * fib (-n + 1) -
          fib (-m - 1) * fib (-n - 1) - fib (-m) * fib (-n) := by
        conv_lhs => rw [fib_neg_natCast_add_neg_natCast, fib_neg_natCast_add_neg_natCast]
        grind
      _ = _ := by grind [fib_add_two]

/--
theorem `fib_add` / 定理 `fib_add`

English:
theorem fib_add
  given: (m n : Int)
  statement: fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1)
  proof: by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
  · exact fib_natCast_add _ _
  · obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
    · exact fib_add_natCast _ _
    · exact fib_neg_natCast_add_neg_natCast _ _

中文:
定理 fib_add
  条件: (m n : 整数)
  结论: fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1)
  证明: by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
  · exact fib_natCast_add _ _
  · obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
    · exact fib_add_natCast _ _
    · exact fib_neg_natCast_add_neg_natCast _ _

Depends on / 依赖: eq_nat_or_neg, fib_add_natCast, fib_natCast_add, fib_neg_natCast_add_neg_natCast, m.eq_nat_or_neg, n.eq_nat_or_neg
-/
theorem fib_add (m n : Int) : fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1) := by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
  · exact fib_natCast_add _ _
  · obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
    · exact fib_add_natCast _ _
    · exact fib_neg_natCast_add_neg_natCast _ _

/--
theorem `fib_two_mul` / 定理 `fib_two_mul`

English:
theorem fib_two_mul
  given: (n : Int)
  statement: fib (2 * n) = fib n * (2 * fib (n + 1) - fib n)
  proof: by
  rw [two_mul]; rw [fib_add]
  grind [fib_add_two]

中文:
定理 fib_two_mul
  条件: (n : 整数)
  结论: fib (2 * n) = fib n * (2 * fib (n + 1) - fib n)
  证明: by
  rw [two_mul]; rw [fib_add]
  grind [fib_add_two]

Depends on / 依赖: fib_add, fib_add_two, two_mul
-/
theorem fib_two_mul (n : Int) : fib (2 * n) = fib n * (2 * fib (n + 1) - fib n) := by
  rw [two_mul]; rw [fib_add]
  grind [fib_add_two]

/--
theorem `fib_two_mul_add_one` / 定理 `fib_two_mul_add_one`

English:
theorem fib_two_mul_add_one
  given: (n : Int)
  statement: fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2
  proof: by
  have := fib_add (n + 1) n
  grind

中文:
定理 fib_two_mul_add_one
  条件: (n : 整数)
  结论: fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2
  证明: by
  have := fib_add (n + 1) n
  grind

Depends on / 依赖: fib_add
-/
theorem fib_two_mul_add_one (n : Int) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  have := fib_add (n + 1) n
  grind

/--
theorem `fib_two_mul_add_two` / 定理 `fib_two_mul_add_two`

English:
theorem fib_two_mul_add_two
  given: (n : Int)
  proof: by
  rw [← mul_add_one]; rw [fib_two_mul]
  grind [fib_add_two]

中文:
定理 fib_two_mul_add_two
  条件: (n : 整数)
  证明: by
  rw [← mul_add_one]; rw [fib_two_mul]
  grind [fib_add_two]

Depends on / 依赖: fib_add_two, fib_two_mul, mul_add_one
-/
theorem fib_two_mul_add_two (n : Int) :
    fib (2 * n + 2) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [← mul_add_one]; rw [fib_two_mul]
  grind [fib_add_two]

/--
theorem `gcd_fib` / 定理 `gcd_fib`

English:
theorem gcd_fib
  given: (m n : Int)
  statement: gcd (fib m) (fib n) = Nat.fib (gcd m n)
  proof: by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
    <;> obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
    <;> simp [fib_neg, Nat.fib_gcd, apply_ite, apply_ite_left]

中文:
定理 gcd_fib
  条件: (m n : 整数)
  结论: 最大公约数 (fib m) (fib n) = 自然数.fib (最大公约数 m n)
  证明: by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
    <;> obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
    <;> simp [fib_neg, Nat.fib_gcd, apply_ite, apply_ite_left]

Depends on / 依赖: Nat.fib_gcd, apply_ite, apply_ite_left, eq_nat_or_neg, fib_gcd, fib_neg, m.eq_nat_or_neg, n.eq_nat_or_neg
-/
theorem gcd_fib (m n : Int) : gcd (fib m) (fib n) = Nat.fib (gcd m n) := by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
    <;> obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
    <;> simp [fib_neg, Nat.fib_gcd, apply_ite, apply_ite_left]

/--
theorem `fib_natCast_dvd` / 定理 `fib_natCast_dvd`

English:
theorem fib_natCast_dvd
  given: {m : Nat} {n : Int} (h : (m : Int) ∣ n)
  statement: fib m ∣ fib n
  proof: by
  rwa [← gcd_eq_left_iff_dvd (by simp), gcd_fib, ← fib_natCast, (gcd_eq_left_iff_dvd (by simp)).mpr]

中文:
定理 fib_natCast_dvd
  条件: {m : 自然数} {n : 整数} (h : (m : 整数) ∣ n)
  结论: fib m ∣ fib n
  证明: by
  rwa [← gcd_eq_left_iff_dvd (by simp), gcd_fib, ← fib_natCast, (gcd_eq_left_iff_dvd (by simp)).mpr]
-/
private theorem fib_natCast_dvd {m : Nat} {n : Int} (h : (m : Int) ∣ n) : fib m ∣ fib n := by
  rwa [← gcd_eq_left_iff_dvd (by simp), gcd_fib, ← fib_natCast, (gcd_eq_left_iff_dvd (by simp)).mpr]

/--
theorem `fib_dvd` / 定理 `fib_dvd`

English:
theorem fib_dvd
  given: (m n : Int) (h : m ∣ n)
  statement: fib m ∣ fib n
  proof: by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
  · exact fib_natCast_dvd h
  · simp [fib_neg_natCast, ← fib_natCast, fib_natCast_dvd <| Int.neg_dvd.mp h]

中文:
定理 fib_dvd
  条件: (m n : 整数) (h : m ∣ n)
  结论: fib m ∣ fib n
  证明: by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
  · exact fib_natCast_dvd h
  · simp [fib_neg_natCast, ← fib_natCast, fib_natCast_dvd <| Int.neg_dvd.mp h]

Depends on / 依赖: Int.neg_dvd.mp, eq_nat_or_neg, fib_natCast, fib_natCast_dvd, fib_neg_natCast, m.eq_nat_or_neg, neg_dvd
-/
theorem fib_dvd (m n : Int) (h : m ∣ n) : fib m ∣ fib n := by
  obtain ⟨m, (rfl | rfl)⟩ := m.eq_nat_or_neg
  · exact fib_natCast_dvd h
  · simp [fib_neg_natCast, ← fib_natCast, fib_natCast_dvd <| Int.neg_dvd.mp h]

end Int
