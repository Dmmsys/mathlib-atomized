/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.
For the proof that the factorial of `n` counts the permutations of an `n`-element set,
see `Fintype.card_perm`.

## Main declarations

* `Nat.factorial`: The factorial.
* `Nat.ascFactorial`: The ascending factorial. It is the product of natural numbers from `n` to
  `n + k - 1`.
* `Nat.descFactorial`: The descending factorial. It is the product of natural numbers from
  `n - k + 1` to `n`.
-/

@[expose] public section


namespace Nat

/-- `Nat.factorial n` is the factorial of `n`. -/
@[wikidata Q120976]
/--
Definition of `factorial` / `factorial` 的定义

English:
definition factorial
  signature: : Nat -> Nat

中文:
定义 factorial
  签名: : 自然数 -> 自然数
-/
def factorial : Nat -> Nat
  | 0 => 1
  | succ n => succ n * factorial n

/-- factorial notation `(n)!` for `Nat.factorial n`.
In Lean, names can end with exclamation marks (e.g. `List.get!`), so you cannot write
`n!` in Lean, but must write `(n)!` or `n !` instead. The former is preferred, since
Lean can confuse the `!` in `n !` as the (prefix) Boolean negation operation in some
cases.
For numerals the parentheses are not required, so e.g. `0!` or `1!` work fine. -/
scoped notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : Nat}

/--
theorem `factorial_zero` / 定理 `factorial_zero`

English:
theorem factorial_zero
  statement: 0! = 1
  proof: rfl

中文:
定理 factorial_zero
  结论: 0! = 1
  证明: rfl
-/
@[simp] theorem factorial_zero : 0! = 1 :=
  rfl

/--
theorem `factorial_succ` / 定理 `factorial_succ`

English:
theorem factorial_succ
  given: (n : Nat)
  statement: (n + 1)! = (n + 1) * n !
  proof: rfl

中文:
定理 factorial_succ
  条件: (n : 自然数)
  结论: (n + 1)! = (n + 1) * n !
  证明: rfl
-/
theorem factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n ! :=
  rfl


/--
theorem `factorial_one` / 定理 `factorial_one`

English:
theorem factorial_one
  statement: 1! = 1
  proof: rfl

中文:
定理 factorial_one
  结论: 1! = 1
  证明: rfl
-/
@[simp] theorem factorial_one : 1! = 1 :=
  rfl

/--
theorem `factorial_two` / 定理 `factorial_two`

English:
theorem factorial_two
  statement: 2! = 2
  proof: rfl

中文:
定理 factorial_two
  结论: 2! = 2
  证明: rfl
-/
@[simp] theorem factorial_two : 2! = 2 :=
  rfl

/--
theorem `mul_factorial_pred` / 定理 `mul_factorial_pred`

English:
theorem mul_factorial_pred
  given: (hn : n != 0)
  statement: n * (n - 1)! = n !
  proof: Nat.sub_add_cancel (one_le_iff_ne_zero.mpr hn) ▸ rfl

中文:
定理 mul_factorial_pred
  条件: (hn : n != 0)
  结论: n * (n - 1)! = n !
  证明: Nat.sub_add_cancel (one_le_iff_ne_zero.mpr hn) ▸ rfl

Depends on / 依赖: Nat.sub_add_cancel, one_le_iff_ne_zero, one_le_iff_ne_zero.mpr, sub_add_cancel
-/
theorem mul_factorial_pred (hn : n != 0) : n * (n - 1)! = n ! :=
  Nat.sub_add_cancel (one_le_iff_ne_zero.mpr hn) ▸ rfl

/--
theorem `factorial_pos` / 定理 `factorial_pos`

English:
theorem factorial_pos
  statement: forall n, 0 < n !

中文:
定理 factorial_pos
  结论: 对任意 n, 0 < n !
-/
theorem factorial_pos : forall n, 0 < n !
  | 0 => Nat.zero_lt_one
  | succ n => Nat.mul_pos (succ_pos _) (factorial_pos n)

/--
theorem `factorial_ne_zero` / 定理 `factorial_ne_zero`

English:
theorem factorial_ne_zero
  given: (n : Nat)
  statement: n ! != 0
  proof: ne_of_gt (factorial_pos _)

@[gcongr]

中文:
定理 factorial_ne_zero
  条件: (n : 自然数)
  结论: n ! != 0
  证明: ne_of_gt (factorial_pos _)

@[gcongr]

Depends on / 依赖: factorial_pos, ne_of_gt
-/
theorem factorial_ne_zero (n : Nat) : n ! != 0 :=
  ne_of_gt (factorial_pos _)

@[gcongr]
/--
theorem `factorial_dvd_factorial` / 定理 `factorial_dvd_factorial`

English:
theorem factorial_dvd_factorial
  given: {m n} (h : m <= n)
  statement: m ! ∣ n !
  proof: by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

中文:
定理 factorial_dvd_factorial
  条件: {m n} (h : m <= n)
  结论: m ! ∣ n !
  证明: by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

Depends on / 依赖: Nat.dvd_mul_left, Nat.dvd_refl, Nat.dvd_trans, dvd_mul_left, dvd_refl, dvd_trans
-/
theorem factorial_dvd_factorial {m n} (h : m <= n) : m ! ∣ n ! := by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

/--
theorem `dvd_factorial` / 定理 `dvd_factorial`

English:
theorem dvd_factorial
  statement: forall {m n}, 0 < m -> m <= n -> m ∣ n !

中文:
定理 dvd_factorial
  结论: 对任意 {m n}, 0 < m -> m <= n -> m ∣ n !
-/
theorem dvd_factorial : forall {m n}, 0 < m -> m <= n -> m ∣ n !
  | succ _, _, _, h => Nat.dvd_trans (Nat.dvd_mul_right _ _) (factorial_dvd_factorial h)

@[mono, gcongr]
/--
theorem `factorial_le` / 定理 `factorial_le`

English:
theorem factorial_le
  given: {m n} (h : m <= n)
  statement: m ! <= n !
  proof: le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)

中文:
定理 factorial_le
  条件: {m n} (h : m <= n)
  结论: m ! <= n !
  证明: le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)

Depends on / 依赖: factorial_dvd_factorial, factorial_pos, le_of_dvd
-/
theorem factorial_le {m n} (h : m <= n) : m ! <= n ! :=
  le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)

/--
theorem `factorial_mul_pow_le_factorial` / 定理 `factorial_mul_pow_le_factorial`

English:
theorem factorial_mul_pow_le_factorial
  statement: forall {m n : Nat}, m ! * (m + 1) ^ n <= (m + n)!

中文:
定理 factorial_mul_pow_le_factorial
  结论: 对任意 {m n : 自然数}, m ! * (m + 1) ^ n <= (m + n)!
-/
theorem factorial_mul_pow_le_factorial : forall {m n : Nat}, m ! * (m + 1) ^ n <= (m + n)!
  | m, 0 => by simp
  | m, n + 1 => by
    rw [← Nat.add_assoc]; rw [factorial_succ]; rw [Nat.mul_comm (_ + 1)]; rw [Nat.pow_succ]; rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul factorial_mul_pow_le_factorial (succ_le_succ (le_add_right _ _))

/--
theorem `factorial_lt` / 定理 `factorial_lt`

English:
theorem factorial_lt
  given: (hn : 0 < n)
  statement: n ! < m ! ↔ n < m
  proof: by
  refine ⟨fun h => not_le.mp fun hmn => Nat.not_le_of_gt h (factorial_le hmn), fun h => ?_⟩
  have : forall {n}, 0 < n -> n ! < (n + 1)! := by
    intro k hk
    rw [factorial_succ]; rw [succ_mul]; rw [Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos hk k.factorial_pos
  induction h generalizing hn with
  | refl => exact this hn
| step hnk ih => exact lt_trans (ih hn) this lt_trans hn lt_of_succ_le hnk

@[gcongr]

中文:
定理 factorial_lt
  条件: (hn : 0 < n)
  结论: n ! < m ! ↔ n < m
  证明: by
  refine ⟨fun h => not_le.mp fun hmn => Nat.not_le_of_gt h (factorial_le hmn), fun h => ?_⟩
  have : forall {n}, 0 < n -> n ! < (n + 1)! := by
    intro k hk
    rw [factorial_succ]; rw [succ_mul]; rw [Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos hk k.factorial_pos
  induction h generalizing hn with
  | refl => exact this hn
| step hnk ih => exact lt_trans (ih hn) this lt_trans hn lt_of_succ_le hnk

@[gcongr]

Depends on / 依赖: Nat.lt_add_left_iff_pos, Nat.mul_pos, Nat.not_le_of_gt, factorial_le, factorial_pos, factorial_succ, generalizing, k.factorial_pos, lt_add_left_iff_pos, lt_of_succ_le, lt_trans, mul_pos, not_le, not_le.mp, not_le_of_gt, succ_mul
-/
theorem factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m := by
  refine ⟨fun h => not_le.mp fun hmn => Nat.not_le_of_gt h (factorial_le hmn), fun h => ?_⟩
  have : forall {n}, 0 < n -> n ! < (n + 1)! := by
    intro k hk
    rw [factorial_succ]; rw [succ_mul]; rw [Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos hk k.factorial_pos
  induction h generalizing hn with
  | refl => exact this hn
| step hnk ih => exact lt_trans (ih hn) this lt_trans hn lt_of_succ_le hnk

@[gcongr]
/--
lemma `factorial_lt_of_lt` / 引理 `factorial_lt_of_lt`

English:
lemma factorial_lt_of_lt
  given: {m n : Nat} (hn : 0 < n) (h : n < m)
  statement: n ! < m !
  proof: (factorial_lt hn).mpr h

中文:
引理 factorial_lt_of_lt
  条件: {m n : 自然数} (hn : 0 < n) (h : n < m)
  结论: n ! < m !
  证明: (factorial_lt hn).mpr h

Depends on / 依赖: factorial_lt
-/
lemma factorial_lt_of_lt {m n : Nat} (hn : 0 < n) (h : n < m) : n ! < m ! := (factorial_lt hn).mpr h

/--
lemma `one_lt_factorial` / 引理 `one_lt_factorial`

English:
lemma one_lt_factorial
  statement: 1 < n ! ↔ 1 < n
  proof: factorial_lt Nat.one_pos

@[simp]

中文:
引理 one_lt_factorial
  结论: 1 < n ! ↔ 1 < n
  证明: factorial_lt Nat.one_pos

@[simp]
-/
@[simp] lemma one_lt_factorial : 1 < n ! ↔ 1 < n := factorial_lt Nat.one_pos

@[simp]
/--
theorem `factorial_eq_one` / 定理 `factorial_eq_one`

English:
theorem factorial_eq_one
  statement: n ! = 1 ↔ n <= 1
  proof: by
  constructor
  · intro h
    rw [← not_lt]; rw [← one_lt_factorial]; rw [h]
    apply lt_irrefl
  · rintro (_ | _ | _) <;> rfl

中文:
定理 factorial_eq_one
  结论: n ! = 1 ↔ n <= 1
  证明: by
  constructor
  · intro h
    rw [← not_lt]; rw [← one_lt_factorial]; rw [h]
    apply lt_irrefl
  · rintro (_ | _ | _) <;> rfl

Depends on / 依赖: lt_irrefl, not_lt, one_lt_factorial
-/
theorem factorial_eq_one : n ! = 1 ↔ n <= 1 := by
  constructor
  · intro h
    rw [← not_lt]; rw [← one_lt_factorial]; rw [h]
    apply lt_irrefl
  · rintro (_ | _ | _) <;> rfl

/--
theorem `factorial_inj` / 定理 `factorial_inj`

English:
theorem factorial_inj
  given: (hn : 1 < n)
  statement: n ! = m ! ↔ n = m
  proof: by
  refine ⟨fun h => ?_, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomy n m
  · rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
    cases lt_irrefl _ hnm
  · rfl
  rw [← one_lt_factorial]; rw [h]; rw [one_lt_factorial] at hn
  rw [← factorial_lt <| lt_of_succ_lt hn]; rw [h] at hnm
  cases lt_irrefl _ hnm

中文:
定理 factorial_inj
  条件: (hn : 1 < n)
  结论: n ! = m ! ↔ n = m
  证明: by
  refine ⟨fun h => ?_, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomy n m
  · rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
    cases lt_irrefl _ hnm
  · rfl
  rw [← one_lt_factorial]; rw [h]; rw [one_lt_factorial] at hn
  rw [← factorial_lt <| lt_of_succ_lt hn]; rw [h] at hnm
  cases lt_irrefl _ hnm

Depends on / 依赖: congr_arg, factorial_lt, lt_irrefl, lt_of_succ_lt, lt_trichotomy, one_lt_factorial
-/
theorem factorial_inj (hn : 1 < n) : n ! = m ! ↔ n = m := by
  refine ⟨fun h => ?_, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomy n m
  · rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
    cases lt_irrefl _ hnm
  · rfl
  rw [← one_lt_factorial]; rw [h]; rw [one_lt_factorial] at hn
  rw [← factorial_lt <| lt_of_succ_lt hn]; rw [h] at hnm
  cases lt_irrefl _ hnm

/--
theorem `factorial_inj'` / 定理 `factorial_inj'`

English:
theorem factorial_inj'
  given: (h : 1 < n ∨ 1 < m)
  statement: n ! = m ! ↔ n = m
  proof: by
  obtain hn | hm := h
  · exact factorial_inj hn
  · rw [eq_comm, factorial_inj hm, eq_comm]

中文:
定理 factorial_inj'
  条件: (h : 1 < n ∨ 1 < m)
  结论: n ! = m ! ↔ n = m
  证明: by
  obtain hn | hm := h
  · exact factorial_inj hn
  · rw [eq_comm, factorial_inj hm, eq_comm]

Depends on / 依赖: eq_comm, factorial_inj
-/
theorem factorial_inj' (h : 1 < n ∨ 1 < m) : n ! = m ! ↔ n = m := by
  obtain hn | hm := h
  · exact factorial_inj hn
  · rw [eq_comm, factorial_inj hm, eq_comm]

/--
theorem `self_le_factorial` / 定理 `self_le_factorial`

English:
theorem self_le_factorial
  statement: forall n : Nat, n <= n !

中文:
定理 self_le_factorial
  结论: 对任意 n : 自然数, n <= n !
-/
theorem self_le_factorial : forall n : Nat, n <= n !
  | 0 => Nat.zero_le _
  | k + 1 => Nat.le_mul_of_pos_right _ (Nat.one_le_of_lt k.factorial_pos)

/--
theorem `lt_factorial_self` / 定理 `lt_factorial_self`

English:
theorem lt_factorial_self
  given: {n : Nat} (hi : 3 <= n)
  statement: n < n !
  proof: by
  have : 0 < n := by lia
  have hn : 1 < pred n := le_pred_of_lt (succ_le_iff.mp hi)
  rw [← succ_pred_eq_of_pos ‹0 < n›]; rw [factorial_succ]
  exact (Nat.lt_mul_iff_one_lt_right (pred n).succ_pos).2
    ((Nat.lt_of_lt_of_le hn (self_le_factorial _)))

中文:
定理 lt_factorial_self
  条件: {n : 自然数} (hi : 3 <= n)
  结论: n < n !
  证明: by
  have : 0 < n := by lia
  have hn : 1 < pred n := le_pred_of_lt (succ_le_iff.mp hi)
  rw [← succ_pred_eq_of_pos ‹0 < n›]; rw [factorial_succ]
  exact (Nat.lt_mul_iff_one_lt_right (pred n).succ_pos).2
    ((Nat.lt_of_lt_of_le hn (self_le_factorial _)))

Depends on / 依赖: Nat.lt_mul_iff_one_lt_right, Nat.lt_of_lt_of_le, factorial_succ, le_pred_of_lt, lt_mul_iff_one_lt_right, lt_of_lt_of_le, self_le_factorial, succ_le_iff, succ_le_iff.mp, succ_pos, succ_pred_eq_of_pos
-/
theorem lt_factorial_self {n : Nat} (hi : 3 <= n) : n < n ! := by
  have : 0 < n := by lia
  have hn : 1 < pred n := le_pred_of_lt (succ_le_iff.mp hi)
  rw [← succ_pred_eq_of_pos ‹0 < n›]; rw [factorial_succ]
  exact (Nat.lt_mul_iff_one_lt_right (pred n).succ_pos).2
    ((Nat.lt_of_lt_of_le hn (self_le_factorial _)))

/--
theorem `add_factorial_succ_lt_factorial_add_succ` / 定理 `add_factorial_succ_lt_factorial_add_succ`

English:
theorem add_factorial_succ_lt_factorial_add_succ
  given: {i : Nat} (n : Nat) (hi : 2 <= i)
  proof: by
  rw [factorial_succ (i + _)]; rw [Nat.add_mul]; rw [Nat.one_mul]
  have := (i + n).self_le_factorial
  refine Nat.add_lt_add_of_lt_of_le (Nat.lt_of_le_of_lt ?_ ((Nat.lt_mul_iff_one_lt_right ?_).2 ?_))
    (factorial_le ?_) <;> lia

中文:
定理 add_factorial_succ_lt_factorial_add_succ
  条件: {i : 自然数} (n : 自然数) (hi : 2 <= i)
  证明: by
  rw [factorial_succ (i + _)]; rw [Nat.add_mul]; rw [Nat.one_mul]
  have := (i + n).self_le_factorial
  refine Nat.add_lt_add_of_lt_of_le (Nat.lt_of_le_of_lt ?_ ((Nat.lt_mul_iff_one_lt_right ?_).2 ?_))
    (factorial_le ?_) <;> lia

Depends on / 依赖: Nat.add_lt_add_of_lt_of_le, Nat.add_mul, Nat.lt_mul_iff_one_lt_right, Nat.lt_of_le_of_lt, Nat.one_mul, add_lt_add_of_lt_of_le, add_mul, factorial_le, factorial_succ, lt_mul_iff_one_lt_right, lt_of_le_of_lt, one_mul, self_le_factorial
-/
theorem add_factorial_succ_lt_factorial_add_succ {i : Nat} (n : Nat) (hi : 2 <= i) :
    i + (n + 1)! < (i + n + 1)! := by
  rw [factorial_succ (i + _)]; rw [Nat.add_mul]; rw [Nat.one_mul]
  have := (i + n).self_le_factorial
  refine Nat.add_lt_add_of_lt_of_le (Nat.lt_of_le_of_lt ?_ ((Nat.lt_mul_iff_one_lt_right ?_).2 ?_))
    (factorial_le ?_) <;> lia

/--
theorem `add_factorial_lt_factorial_add` / 定理 `add_factorial_lt_factorial_add`

English:
theorem add_factorial_lt_factorial_add
  given: {i n : Nat} (hi : 2 <= i) (hn : 1 <= n)
  proof: by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
  exact add_factorial_succ_lt_factorial_add_succ _ hi

中文:
定理 add_factorial_lt_factorial_add
  条件: {i n : 自然数} (hi : 2 <= i) (hn : 1 <= n)
  证明: by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
  exact add_factorial_succ_lt_factorial_add_succ _ hi

Depends on / 依赖: add_factorial_succ_lt_factorial_add_succ, factorial_one, lt_factorial_self, succ_le_succ
-/
theorem add_factorial_lt_factorial_add {i n : Nat} (hi : 2 <= i) (hn : 1 <= n) :
    i + n ! < (i + n)! := by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
  exact add_factorial_succ_lt_factorial_add_succ _ hi

/--
theorem `add_factorial_succ_le_factorial_add_succ` / 定理 `add_factorial_succ_le_factorial_add_succ`

English:
theorem add_factorial_succ_le_factorial_add_succ
  given: (i : Nat) (n : Nat)
  proof: by
  cases (le_or_gt (2 : Nat) i)
  · rw [← Nat.add_assoc]
    apply Nat.le_of_lt
    apply add_factorial_succ_lt_factorial_add_succ
    assumption
  · match i with
    | 0 => simp
    | 1 =>
      rw [← Nat.add_assoc]; rw [factorial_succ (1 + n)]; rw [Nat.add_mul]; rw [Nat.one_mul]; rw [Nat.add_comm 1 n]; rw [Nat.add_le_add_iff_right]
      exact Nat.mul_pos n.succ_pos n.succ.factorial_pos
    | succ (succ n) => contradiction

中文:
定理 add_factorial_succ_le_factorial_add_succ
  条件: (i : 自然数) (n : 自然数)
  证明: by
  cases (le_or_gt (2 : Nat) i)
  · rw [← Nat.add_assoc]
    apply Nat.le_of_lt
    apply add_factorial_succ_lt_factorial_add_succ
    assumption
  · match i with
    | 0 => simp
    | 1 =>
      rw [← Nat.add_assoc]; rw [factorial_succ (1 + n)]; rw [Nat.add_mul]; rw [Nat.one_mul]; rw [Nat.add_comm 1 n]; rw [Nat.add_le_add_iff_right]
      exact Nat.mul_pos n.succ_pos n.succ.factorial_pos
    | succ (succ n) => contradiction

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.add_le_add_iff_right, Nat.add_mul, Nat.le_of_lt, Nat.mul_pos, Nat.one_mul, add_assoc, add_comm, add_factorial_succ_lt_factorial_add_succ, add_le_add_iff_right, add_mul, factorial_pos, factorial_succ, le_of_lt, le_or_gt, mul_pos, n.succ.factorial_pos, n.succ_pos, one_mul
-/
theorem add_factorial_succ_le_factorial_add_succ (i : Nat) (n : Nat) :
    i + (n + 1)! <= (i + (n + 1))! := by
  cases (le_or_gt (2 : Nat) i)
  · rw [← Nat.add_assoc]
    apply Nat.le_of_lt
    apply add_factorial_succ_lt_factorial_add_succ
    assumption
  · match i with
    | 0 => simp
    | 1 =>
      rw [← Nat.add_assoc]; rw [factorial_succ (1 + n)]; rw [Nat.add_mul]; rw [Nat.one_mul]; rw [Nat.add_comm 1 n]; rw [Nat.add_le_add_iff_right]
      exact Nat.mul_pos n.succ_pos n.succ.factorial_pos
    | succ (succ n) => contradiction

/--
theorem `add_factorial_le_factorial_add` / 定理 `add_factorial_le_factorial_add`

English:
theorem add_factorial_le_factorial_add
  given: (i : Nat) {n : Nat} (n1 : 1 <= n)
  statement: i + n ! <= (i + n)!
  proof: by
  rcases n1 with - | @h
  · exact self_le_factorial _
  exact add_factorial_succ_le_factorial_add_succ i h

中文:
定理 add_factorial_le_factorial_add
  条件: (i : 自然数) {n : 自然数} (n1 : 1 <= n)
  结论: i + n ! <= (i + n)!
  证明: by
  rcases n1 with - | @h
  · exact self_le_factorial _
  exact add_factorial_succ_le_factorial_add_succ i h

Depends on / 依赖: add_factorial_succ_le_factorial_add_succ, self_le_factorial
-/
theorem add_factorial_le_factorial_add (i : Nat) {n : Nat} (n1 : 1 <= n) : i + n ! <= (i + n)! := by
  rcases n1 with - | @h
  · exact self_le_factorial _
  exact add_factorial_succ_le_factorial_add_succ i h

/--
theorem `factorial_mul_pow_sub_le_factorial` / 定理 `factorial_mul_pow_sub_le_factorial`

English:
theorem factorial_mul_pow_sub_le_factorial
  given: {n m : Nat} (hnm : n <= m)
  statement: n ! * n ^ (m - n) <= m !
  proof: by
  calc
    _ <= n ! * (n + 1) ^ (m - n) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
    _ <= _ := by simpa [hnm] using @Nat.factorial_mul_pow_le_factorial n (m - n)

中文:
定理 factorial_mul_pow_sub_le_factorial
  条件: {n m : 自然数} (hnm : n <= m)
  结论: n ! * n ^ (m - n) <= m !
  证明: by
  calc
    _ <= n ! * (n + 1) ^ (m - n) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
    _ <= _ := by simpa [hnm] using @Nat.factorial_mul_pow_le_factorial n (m - n)

Depends on / 依赖: Nat.factorial_mul_pow_le_factorial, Nat.mul_le_mul_left, Nat.pow_le_pow_left, factorial_mul_pow_le_factorial, le_succ, mul_le_mul_left, n.le_succ, pow_le_pow_left
-/
theorem factorial_mul_pow_sub_le_factorial {n m : Nat} (hnm : n <= m) : n ! * n ^ (m - n) <= m ! := by
  calc
    _ <= n ! * (n + 1) ^ (m - n) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
    _ <= _ := by simpa [hnm] using @Nat.factorial_mul_pow_le_factorial n (m - n)

/--
lemma `factorial_le_pow` / 引理 `factorial_le_pow`

English:
lemma factorial_le_pow
  statement: forall n, n ! <= n ^ n
  proof: Nat.mul_le_mul_left _ n.factorial_le_pow
      _ <= (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
      _ = _ := by rw [pow_succ']

中文:
引理 factorial_le_pow
  结论: 对任意 n, n ! <= n ^ n
  证明: Nat.mul_le_mul_left _ n.factorial_le_pow
      _ <= (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
      _ = _ := by rw [pow_succ']

Depends on / 依赖: Nat.mul_le_mul_left, factorial_le_pow, mul_le_mul_left, n.factorial_le_pow
-/
lemma factorial_le_pow : forall n, n ! <= n ^ n
  | 0 => le_refl _
  | n + 1 =>
    calc
      _ <= (n + 1) * n ^ n := Nat.mul_le_mul_left _ n.factorial_le_pow
      _ <= (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
      _ = _ := by rw [pow_succ']

end Factorial

/-! ### Ascending and descending factorials -/


section AscFactorial

/--
Definition of `ascFactorial` / `ascFactorial` 的定义

English:
definition ascFactorial
  signature: (n : Nat)

中文:
定义 ascFactorial
  签名: (n : 自然数)
-/
def ascFactorial (n : Nat) : Nat -> Nat
  | 0 => 1
  | k + 1 => (n + k) * ascFactorial n k

@[simp]
/--
theorem `ascFactorial_zero` / 定理 `ascFactorial_zero`

English:
theorem ascFactorial_zero
  given: (n : Nat)
  statement: n.ascFactorial 0 = 1
  proof: rfl

中文:
定理 ascFactorial_zero
  条件: (n : 自然数)
  结论: n.ascFactorial 0 = 1
  证明: rfl
-/
theorem ascFactorial_zero (n : Nat) : n.ascFactorial 0 = 1 :=
  rfl

/--
theorem `ascFactorial_succ` / 定理 `ascFactorial_succ`

English:
theorem ascFactorial_succ
  given: {n k : Nat}
  statement: n.ascFactorial k.succ = (n + k) * n.ascFactorial k
  proof: rfl

中文:
定理 ascFactorial_succ
  条件: {n k : 自然数}
  结论: n.ascFactorial k.succ = (n + k) * n.ascFactorial k
  证明: rfl
-/
theorem ascFactorial_succ {n k : Nat} : n.ascFactorial k.succ = (n + k) * n.ascFactorial k :=
  rfl

/--
theorem `zero_ascFactorial` / 定理 `zero_ascFactorial`

English:
theorem zero_ascFactorial
  statement: forall (k : Nat), (0 : Nat).ascFactorial k.succ = 0

中文:
定理 zero_ascFactorial
  结论: 对任意 (k : 自然数), (0 : 自然数).ascFactorial k.succ = 0
-/
theorem zero_ascFactorial : forall (k : Nat), (0 : Nat).ascFactorial k.succ = 0
  | 0 => by
    rw [ascFactorial_succ]; rw [ascFactorial_zero]; rw [Nat.zero_add]; rw [Nat.zero_mul]
  | (k + 1) => by
    rw [ascFactorial_succ]; rw [zero_ascFactorial k]; rw [Nat.mul_zero]

@[simp]
/--
theorem `one_ascFactorial` / 定理 `one_ascFactorial`

English:
theorem one_ascFactorial
  statement: forall (k : Nat), (1 : Nat).ascFactorial k = k.factorial

中文:
定理 one_ascFactorial
  结论: 对任意 (k : 自然数), (1 : 自然数).ascFactorial k = k.factorial
-/
theorem one_ascFactorial : forall (k : Nat), (1 : Nat).ascFactorial k = k.factorial
  | 0 => ascFactorial_zero 1
  | (k + 1) => by
    rw [ascFactorial_succ]; rw [one_ascFactorial k]; rw [Nat.add_comm]; rw [factorial_succ]

/--
theorem `succ_ascFactorial` / 定理 `succ_ascFactorial`

English:
theorem succ_ascFactorial
  given: (n : Nat)

中文:
定理 succ_ascFactorial
  条件: (n : 自然数)
-/
theorem succ_ascFactorial (n : Nat) :
    forall k, n * n.succ.ascFactorial k = (n + k) * n.ascFactorial k
  | 0 => by rw [Nat.add_zero, ascFactorial_zero, ascFactorial_zero]
  | k + 1 => by rw [ascFactorial, Nat.mul_left_comm, succ_ascFactorial n k, ascFactorial, succ_add,
    ← Nat.add_assoc]

/--
theorem `factorial_mul_ascFactorial` / 定理 `factorial_mul_ascFactorial`

English:
theorem factorial_mul_ascFactorial
  given: (n : Nat)
  statement: forall k, n ! * (n + 1).ascFactorial k = (n + k)!

中文:
定理 factorial_mul_ascFactorial
  条件: (n : 自然数)
  结论: 对任意 k, n ! * (n + 1).ascFactorial k = (n + k)!
-/
theorem factorial_mul_ascFactorial (n : Nat) : forall k, n ! * (n + 1).ascFactorial k = (n + k)!
  | 0 => by rw [ascFactorial_zero, Nat.add_zero, Nat.mul_one]
  | k + 1 => by
    rw [ascFactorial_succ]; rw [← Nat.add_assoc]; rw [factorial_succ]; rw [Nat.mul_comm (n + 1 + k)]; rw [← Nat.mul_assoc]; rw [factorial_mul_ascFactorial n k]; rw [Nat.mul_comm]; rw [Nat.add_right_comm]

/--
theorem `factorial_mul_ascFactorial'` / 定理 `factorial_mul_ascFactorial'`

English:
theorem factorial_mul_ascFactorial'
  given: (n k : Nat) (h : 0 < n)
  proof: by
  rw [Nat.sub_add_comm h]; rw [Nat.sub_one]
  nth_rw 2 [Nat.eq_add_of_sub_eq h rfl]
  rw [Nat.sub_one]; rw [factorial_mul_ascFactorial]

中文:
定理 factorial_mul_ascFactorial'
  条件: (n k : 自然数) (h : 0 < n)
  证明: by
  rw [Nat.sub_add_comm h]; rw [Nat.sub_one]
  nth_rw 2 [Nat.eq_add_of_sub_eq h rfl]
  rw [Nat.sub_one]; rw [factorial_mul_ascFactorial]

Depends on / 依赖: Nat.eq_add_of_sub_eq, Nat.sub_add_comm, Nat.sub_one, eq_add_of_sub_eq, factorial_mul_ascFactorial, nth_rw, sub_add_comm, sub_one
-/
theorem factorial_mul_ascFactorial' (n k : Nat) (h : 0 < n) :
    (n - 1)! * n.ascFactorial k = (n + k - 1)! := by
  rw [Nat.sub_add_comm h]; rw [Nat.sub_one]
  nth_rw 2 [Nat.eq_add_of_sub_eq h rfl]
  rw [Nat.sub_one]; rw [factorial_mul_ascFactorial]

/--
theorem `ascFactorial_mul_ascFactorial` / 定理 `ascFactorial_mul_ascFactorial`

English:
theorem ascFactorial_mul_ascFactorial
  given: (n l k : Nat)
  proof: by
  cases n with
  | zero =>
    cases l
    · simp only [ascFactorial_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
    · simp only [Nat.add_right_comm, zero_ascFactorial, Nat.zero_add, Nat.zero_mul]
  | succ n' =>
    apply Nat.mul_left_cancel (factorial_pos n')
    simp only [Nat.add_assoc, ← Nat.mul_assoc, factorial_mul_ascFactorial]
    rw [Nat.add_comm 1 l]; rw [← Nat.add_assoc]; rw [factorial_mul_ascFactorial]; rw [Nat.add_assoc]

中文:
定理 ascFactorial_mul_ascFactorial
  条件: (n l k : 自然数)
  证明: by
  cases n with
  | zero =>
    cases l
    · simp only [ascFactorial_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
    · simp only [Nat.add_right_comm, zero_ascFactorial, Nat.zero_add, Nat.zero_mul]
  | succ n' =>
    apply Nat.mul_left_cancel (factorial_pos n')
    simp only [Nat.add_assoc, ← Nat.mul_assoc, factorial_mul_ascFactorial]
    rw [Nat.add_comm 1 l]; rw [← Nat.add_assoc]; rw [factorial_mul_ascFactorial]; rw [Nat.add_assoc]

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.add_right_comm, Nat.add_zero, Nat.mul_assoc, Nat.mul_left_cancel, Nat.one_mul, Nat.zero_add, Nat.zero_mul, add_assoc, add_comm, add_right_comm, add_zero, ascFactorial_zero, factorial_mul_ascFactorial, factorial_pos, mul_assoc, mul_left_cancel, one_mul, zero_add
-/
theorem ascFactorial_mul_ascFactorial (n l k : Nat) :
    n.ascFactorial l * (n + l).ascFactorial k = n.ascFactorial (l + k) := by
  cases n with
  | zero =>
    cases l
    · simp only [ascFactorial_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
    · simp only [Nat.add_right_comm, zero_ascFactorial, Nat.zero_add, Nat.zero_mul]
  | succ n' =>
    apply Nat.mul_left_cancel (factorial_pos n')
    simp only [Nat.add_assoc, ← Nat.mul_assoc, factorial_mul_ascFactorial]
    rw [Nat.add_comm 1 l]; rw [← Nat.add_assoc]; rw [factorial_mul_ascFactorial]; rw [Nat.add_assoc]

/--
theorem `ascFactorial_eq_div` / 定理 `ascFactorial_eq_div`

English:
theorem ascFactorial_eq_div
  given: (n k : Nat)
  statement: (n + 1).ascFactorial k = (n + k)! / n !
  proof: Nat.eq_div_of_mul_eq_right n.factorial_ne_zero (factorial_mul_ascFactorial _ _)

中文:
定理 ascFactorial_eq_div
  条件: (n k : 自然数)
  结论: (n + 1).ascFactorial k = (n + k)! / n !
  证明: Nat.eq_div_of_mul_eq_right n.factorial_ne_zero (factorial_mul_ascFactorial _ _)

Depends on / 依赖: Nat.eq_div_of_mul_eq_right, eq_div_of_mul_eq_right, factorial_mul_ascFactorial, factorial_ne_zero, n.factorial_ne_zero
-/
theorem ascFactorial_eq_div (n k : Nat) : (n + 1).ascFactorial k = (n + k)! / n ! :=
  Nat.eq_div_of_mul_eq_right n.factorial_ne_zero (factorial_mul_ascFactorial _ _)

/--
theorem `ascFactorial_eq_div'` / 定理 `ascFactorial_eq_div'`

English:
theorem ascFactorial_eq_div'
  given: (n k : Nat) (h : 0 < n)
  proof: Nat.eq_div_of_mul_eq_right (n - 1).factorial_ne_zero (factorial_mul_ascFactorial' _ _ h)

中文:
定理 ascFactorial_eq_div'
  条件: (n k : 自然数) (h : 0 < n)
  证明: Nat.eq_div_of_mul_eq_right (n - 1).factorial_ne_zero (factorial_mul_ascFactorial' _ _ h)

Depends on / 依赖: Nat.eq_div_of_mul_eq_right, eq_div_of_mul_eq_right, factorial_mul_ascFactorial, factorial_ne_zero
-/
theorem ascFactorial_eq_div' (n k : Nat) (h : 0 < n) :
    n.ascFactorial k = (n + k - 1)! / (n - 1)! :=
  Nat.eq_div_of_mul_eq_right (n - 1).factorial_ne_zero (factorial_mul_ascFactorial' _ _ h)

/--
theorem `ascFactorial_of_sub` / 定理 `ascFactorial_of_sub`

English:
theorem ascFactorial_of_sub
  given: {n k : Nat}
  proof: by
  rw [succ_ascFactorial]; rw [ascFactorial_succ]

@[gcongr]

中文:
定理 ascFactorial_of_sub
  条件: {n k : 自然数}
  证明: by
  rw [succ_ascFactorial]; rw [ascFactorial_succ]

@[gcongr]

Depends on / 依赖: ascFactorial_succ, succ_ascFactorial
-/
theorem ascFactorial_of_sub {n k : Nat} :
    (n - k) * (n - k + 1).ascFactorial k = (n - k).ascFactorial (k + 1) := by
  rw [succ_ascFactorial]; rw [ascFactorial_succ]

@[gcongr]
/--
theorem `ascFactorial_le` / 定理 `ascFactorial_le`

English:
theorem ascFactorial_le
  given: (k : Nat) {n m : Nat} (h : n <= m)
  proof: by
  induction k with
  | zero => rfl
  | succ k ih => exact Nat.mul_le_mul (by lia) ih

中文:
定理 ascFactorial_le
  条件: (k : 自然数) {n m : 自然数} (h : n <= m)
  证明: by
  induction k with
  | zero => rfl
  | succ k ih => exact Nat.mul_le_mul (by lia) ih

Depends on / 依赖: Nat.mul_le_mul, mul_le_mul
-/
theorem ascFactorial_le (k : Nat) {n m : Nat} (h : n <= m) :
    n.ascFactorial k <= m.ascFactorial k := by
  induction k with
  | zero => rfl
  | succ k ih => exact Nat.mul_le_mul (by lia) ih

/--
theorem `pow_succ_le_ascFactorial` / 定理 `pow_succ_le_ascFactorial`

English:
theorem pow_succ_le_ascFactorial
  given: (n : Nat)
  statement: forall k : Nat, n ^ k <= n.ascFactorial k

中文:
定理 pow_succ_le_ascFactorial
  条件: (n : 自然数)
  结论: 对任意 k : 自然数, n ^ k <= n.ascFactorial k
-/
theorem pow_succ_le_ascFactorial (n : Nat) : forall k : Nat, n ^ k <= n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [Nat.pow_succ]; rw [Nat.mul_comm]; rw [ascFactorial_succ]; rw [← succ_ascFactorial]
    exact Nat.mul_le_mul (Nat.le_refl n)
      (Nat.le_trans (Nat.pow_le_pow_left (le_succ n) k) (pow_succ_le_ascFactorial n.succ k))

/--
theorem `pow_lt_ascFactorial'` / 定理 `pow_lt_ascFactorial'`

English:
theorem pow_lt_ascFactorial'
  given: (n k : Nat)
  statement: (n + 1) ^ (k + 2) < (n + 1).ascFactorial (k + 2)
  proof: by
  rw [Nat.pow_succ]; rw [ascFactorial]; rw [Nat.mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le' (Nat.lt_add_of_pos_right k.succ_pos)
    (pow_succ_le_ascFactorial n.succ _) (Nat.pow_pos n.succ_pos)

中文:
定理 pow_lt_ascFactorial'
  条件: (n k : 自然数)
  结论: (n + 1) ^ (k + 2) < (n + 1).ascFactorial (k + 2)
  证明: by
  rw [Nat.pow_succ]; rw [ascFactorial]; rw [Nat.mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le' (Nat.lt_add_of_pos_right k.succ_pos)
    (pow_succ_le_ascFactorial n.succ _) (Nat.pow_pos n.succ_pos)

Depends on / 依赖: Nat.lt_add_of_pos_right, Nat.mul_comm, Nat.mul_lt_mul_of_lt_of_le, Nat.pow_pos, Nat.pow_succ, ascFactorial, k.succ_pos, lt_add_of_pos_right, mul_comm, mul_lt_mul_of_lt_of_le, n.succ, n.succ_pos, pow_pos, pow_succ, pow_succ_le_ascFactorial, succ_pos
-/
theorem pow_lt_ascFactorial' (n k : Nat) : (n + 1) ^ (k + 2) < (n + 1).ascFactorial (k + 2) := by
  rw [Nat.pow_succ]; rw [ascFactorial]; rw [Nat.mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le' (Nat.lt_add_of_pos_right k.succ_pos)
    (pow_succ_le_ascFactorial n.succ _) (Nat.pow_pos n.succ_pos)

/--
theorem `pow_lt_ascFactorial` / 定理 `pow_lt_ascFactorial`

English:
theorem pow_lt_ascFactorial
  given: (n : Nat)
  statement: forall {k : Nat}, 2 <= k -> (n + 1) ^ k < (n + 1).ascFactorial k

中文:
定理 pow_lt_ascFactorial
  条件: (n : 自然数)
  结论: 对任意 {k : 自然数}, 2 <= k -> (n + 1) ^ k < (n + 1).ascFactorial k
-/
theorem pow_lt_ascFactorial (n : Nat) : forall {k : Nat}, 2 <= k -> (n + 1) ^ k < (n + 1).ascFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => pow_lt_ascFactorial' n k

/--
theorem `ascFactorial_le_pow_add` / 定理 `ascFactorial_le_pow_add`

English:
theorem ascFactorial_le_pow_add
  given: (n : Nat)
  statement: forall k : Nat, (n + 1).ascFactorial k <= (n + k) ^ k

中文:
定理 ascFactorial_le_pow_add
  条件: (n : 自然数)
  结论: 对任意 k : 自然数, (n + 1).ascFactorial k <= (n + k) ^ k
-/
theorem ascFactorial_le_pow_add (n : Nat) : forall k : Nat, (n + 1).ascFactorial k <= (n + k) ^ k
  | 0 => by rw [ascFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [ascFactorial_succ]; rw [Nat.pow_succ]; rw [Nat.mul_comm]; rw [← Nat.add_assoc]; rw [Nat.add_right_comm n 1 k]
    exact Nat.mul_le_mul_right _
      (Nat.le_trans (ascFactorial_le_pow_add _ k) (Nat.pow_le_pow_left (le_succ _) _))

/--
theorem `ascFactorial_le_factorial_mul_pow` / 定理 `ascFactorial_le_factorial_mul_pow`

English:
theorem ascFactorial_le_factorial_mul_pow
  given: (n k : Nat)
  statement: n.ascFactorial k <= k ! * n ^ k
  proof: match k with
  | 0 => by simp
  | j + 1 => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [zero_ascFactorial]
    rw [ascFactorial_succ]; rw [factorial_succ]; rw [pow_succ']; rw [Nat.mul_assoc (j + 1)]; rw [Nat.mul_left_comm j !]; rw [← Nat.mul_assoc (j + 1)]
    refine Nat.mul_le_mul ?_ (ascFactorial_le_factorial_mul_pow n j)
    rw [add_one_mul]; rw [Nat.add_comm]; rw [Nat.add_le_add_iff_right]
    exact Nat.le_mul_of_pos_right j hn

中文:
定理 ascFactorial_le_factorial_mul_pow
  条件: (n k : 自然数)
  结论: n.ascFactorial k <= k ! * n ^ k
  证明: match k with
  | 0 => by simp
  | j + 1 => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [zero_ascFactorial]
    rw [ascFactorial_succ]; rw [factorial_succ]; rw [pow_succ']; rw [Nat.mul_assoc (j + 1)]; rw [Nat.mul_left_comm j !]; rw [← Nat.mul_assoc (j + 1)]
    refine Nat.mul_le_mul ?_ (ascFactorial_le_factorial_mul_pow n j)
    rw [add_one_mul]; rw [Nat.add_comm]; rw [Nat.add_le_add_iff_right]
    exact Nat.le_mul_of_pos_right j hn

Depends on / 依赖: Nat.add_comm, Nat.add_le_add_iff_right, Nat.le_mul_of_pos_right, Nat.mul_assoc, Nat.mul_le_mul, Nat.mul_left_comm, add_comm, add_le_add_iff_right, add_one_mul, ascFactorial_le_factorial_mul_pow, ascFactorial_succ, eq_zero_or_pos, factorial_succ, le_mul_of_pos_right, mul_assoc, mul_le_mul, mul_left_comm, n.eq_zero_or_pos, pow_succ, zero_ascFactorial
-/
theorem ascFactorial_le_factorial_mul_pow (n k : Nat) : n.ascFactorial k <= k ! * n ^ k :=
  match k with
  | 0 => by simp
  | j + 1 => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [zero_ascFactorial]
    rw [ascFactorial_succ]; rw [factorial_succ]; rw [pow_succ']; rw [Nat.mul_assoc (j + 1)]; rw [Nat.mul_left_comm j !]; rw [← Nat.mul_assoc (j + 1)]
    refine Nat.mul_le_mul ?_ (ascFactorial_le_factorial_mul_pow n j)
    rw [add_one_mul]; rw [Nat.add_comm]; rw [Nat.add_le_add_iff_right]
    exact Nat.le_mul_of_pos_right j hn

/--
theorem `ascFactorial_lt_pow_add` / 定理 `ascFactorial_lt_pow_add`

English:
theorem ascFactorial_lt_pow_add
  given: (n : Nat)
  statement: forall {k : Nat}, 2 <= k -> (n + 1).ascFactorial k < (n + k) ^ k

中文:
定理 ascFactorial_lt_pow_add
  条件: (n : 自然数)
  结论: 对任意 {k : 自然数}, 2 <= k -> (n + 1).ascFactorial k < (n + k) ^ k
-/
theorem ascFactorial_lt_pow_add (n : Nat) : forall {k : Nat}, 2 <= k -> (n + 1).ascFactorial k < (n + k) ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [Nat.pow_succ]; rw [Nat.mul_comm]; rw [ascFactorial_succ]; rw [succ_add_eq_add_succ n (k + 1)]
    exact Nat.mul_lt_mul_of_le_of_lt (le_refl _) (Nat.lt_of_le_of_lt (ascFactorial_le_pow_add n _)
      (Nat.pow_lt_pow_left (Nat.lt_succ_self _) k.succ_ne_zero)) (succ_pos _)

/--
theorem `ascFactorial_pos` / 定理 `ascFactorial_pos`

English:
theorem ascFactorial_pos
  given: (n k : Nat)
  statement: 0 < (n + 1).ascFactorial k
  proof: Nat.lt_of_lt_of_le (Nat.pow_pos n.succ_pos) (pow_succ_le_ascFactorial (n + 1) k)

中文:
定理 ascFactorial_pos
  条件: (n k : 自然数)
  结论: 0 < (n + 1).ascFactorial k
  证明: Nat.lt_of_lt_of_le (Nat.pow_pos n.succ_pos) (pow_succ_le_ascFactorial (n + 1) k)

Depends on / 依赖: Nat.lt_of_lt_of_le, Nat.pow_pos, lt_of_lt_of_le, n.succ_pos, pow_pos, pow_succ_le_ascFactorial, succ_pos
-/
theorem ascFactorial_pos (n k : Nat) : 0 < (n + 1).ascFactorial k :=
  Nat.lt_of_lt_of_le (Nat.pow_pos n.succ_pos) (pow_succ_le_ascFactorial (n + 1) k)

end AscFactorial

section DescFactorial

/--
Definition of `descFactorial` / `descFactorial` 的定义

English:
definition descFactorial
  signature: (n : Nat)

中文:
定义 descFactorial
  签名: (n : 自然数)
-/
def descFactorial (n : Nat) : Nat -> Nat
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k

@[simp]
/--
theorem `descFactorial_zero` / 定理 `descFactorial_zero`

English:
theorem descFactorial_zero
  given: (n : Nat)
  statement: n.descFactorial 0 = 1
  proof: rfl

@[simp]

中文:
定理 descFactorial_zero
  条件: (n : 自然数)
  结论: n.descFactorial 0 = 1
  证明: rfl

@[simp]
-/
theorem descFactorial_zero (n : Nat) : n.descFactorial 0 = 1 :=
  rfl

@[simp]
/--
theorem `descFactorial_succ` / 定理 `descFactorial_succ`

English:
theorem descFactorial_succ
  given: (n k : Nat)
  statement: n.descFactorial (k + 1) = (n - k) * n.descFactorial k
  proof: rfl

中文:
定理 descFactorial_succ
  条件: (n k : 自然数)
  结论: n.descFactorial (k + 1) = (n - k) * n.descFactorial k
  证明: rfl
-/
theorem descFactorial_succ (n k : Nat) : n.descFactorial (k + 1) = (n - k) * n.descFactorial k :=
  rfl

/--
theorem `zero_descFactorial_succ` / 定理 `zero_descFactorial_succ`

English:
theorem zero_descFactorial_succ
  given: (k : Nat)
  statement: (0 : Nat).descFactorial (k + 1) = 0
  proof: by
  rw [descFactorial_succ]; rw [Nat.zero_sub]; rw [Nat.zero_mul]

中文:
定理 zero_descFactorial_succ
  条件: (k : 自然数)
  结论: (0 : 自然数).descFactorial (k + 1) = 0
  证明: by
  rw [descFactorial_succ]; rw [Nat.zero_sub]; rw [Nat.zero_mul]

Depends on / 依赖: Nat.zero_mul, Nat.zero_sub, descFactorial_succ, zero_mul, zero_sub
-/
theorem zero_descFactorial_succ (k : Nat) : (0 : Nat).descFactorial (k + 1) = 0 := by
  rw [descFactorial_succ]; rw [Nat.zero_sub]; rw [Nat.zero_mul]

/--
theorem `descFactorial_one` / 定理 `descFactorial_one`

English:
theorem descFactorial_one
  given: (n : Nat)
  statement: n.descFactorial 1 = n
  proof: by simp

中文:
定理 descFactorial_one
  条件: (n : 自然数)
  结论: n.descFactorial 1 = n
  证明: by simp
-/
theorem descFactorial_one (n : Nat) : n.descFactorial 1 = n := by simp

/--
theorem `succ_descFactorial_succ` / 定理 `succ_descFactorial_succ`

English:
theorem succ_descFactorial_succ
  given: (n : Nat)

中文:
定理 succ_descFactorial_succ
  条件: (n : 自然数)
-/
theorem succ_descFactorial_succ (n : Nat) :
    forall k : Nat, (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
  | 0 => by rw [descFactorial_zero, descFactorial_one, Nat.mul_one]
  | succ k => by
    rw [descFactorial_succ]; rw [succ_descFactorial_succ _ k]; rw [descFactorial_succ]; rw [succ_sub_succ]; rw [Nat.mul_left_comm]

/--
theorem `succ_descFactorial` / 定理 `succ_descFactorial`

English:
theorem succ_descFactorial
  given: (n : Nat)

中文:
定理 succ_descFactorial
  条件: (n : 自然数)
-/
theorem succ_descFactorial (n : Nat) :
    forall k, (n + 1 - k) * (n + 1).descFactorial k = (n + 1) * n.descFactorial k
  | 0 => by rw [Nat.sub_zero, descFactorial_zero, descFactorial_zero]
  | k + 1 => by
    rw [descFactorial]; rw [succ_descFactorial _ k]; rw [descFactorial_succ]; rw [succ_sub_succ]; rw [Nat.mul_left_comm]

/--
theorem `descFactorial_self` / 定理 `descFactorial_self`

English:
theorem descFactorial_self
  statement: forall n : Nat, n.descFactorial n = n !

中文:
定理 descFactorial_self
  结论: 对任意 n : 自然数, n.descFactorial n = n !
-/
theorem descFactorial_self : forall n : Nat, n.descFactorial n = n !
  | 0 => by rw [descFactorial_zero, factorial_zero]
  | succ n => by rw [succ_descFactorial_succ, descFactorial_self n, factorial_succ]

@[simp]
/--
theorem `descFactorial_eq_zero_iff_lt` / 定理 `descFactorial_eq_zero_iff_lt`

English:
theorem descFactorial_eq_zero_iff_lt
  given: {n : Nat}
  statement: forall {k : Nat}, n.descFactorial k = 0 ↔ n < k

中文:
定理 descFactorial_eq_zero_iff_lt
  条件: {n : 自然数}
  结论: 对任意 {k : 自然数}, n.descFactorial k = 0 ↔ n < k
-/
theorem descFactorial_eq_zero_iff_lt {n : Nat} : forall {k : Nat}, n.descFactorial k = 0 ↔ n < k
  | 0 => by simp only [descFactorial_zero, Nat.one_ne_zero, Nat.not_lt_zero]
  | succ k => by
    rw [descFactorial_succ]; rw [mul_eq_zero]; rw [descFactorial_eq_zero_iff_lt]; rw [Nat.lt_succ_iff]; rw [Nat.sub_eq_zero_iff_le]; rw [Nat.lt_iff_le_and_ne]; rw [or_iff_left_iff_imp]; rw [and_imp]
    exact fun h _ => h

@[simp]
/--
lemma `descFactorial_pos` / 引理 `descFactorial_pos`

English:
lemma descFactorial_pos
  given: {n k : Nat}
  statement: 0 < n.descFactorial k ↔ k <= n
  proof: by simp [Nat.pos_iff_ne_zero]

alias ⟨_, descFactorial_of_lt⟩ := descFactorial_eq_zero_iff_lt

中文:
引理 descFactorial_pos
  条件: {n k : 自然数}
  结论: 0 < n.descFactorial k ↔ k <= n
  证明: by simp [Nat.pos_iff_ne_zero]

alias ⟨_, descFactorial_of_lt⟩ := descFactorial_eq_zero_iff_lt

Depends on / 依赖: Nat.pos_iff_ne_zero, pos_iff_ne_zero
-/
lemma descFactorial_pos {n k : Nat} : 0 < n.descFactorial k ↔ k <= n := by simp [Nat.pos_iff_ne_zero]

alias ⟨_, descFactorial_of_lt⟩ := descFactorial_eq_zero_iff_lt

/--
theorem `add_descFactorial_eq_ascFactorial` / 定理 `add_descFactorial_eq_ascFactorial`

English:
theorem add_descFactorial_eq_ascFactorial
  given: (n : Nat)
  statement: forall k : Nat,

中文:
定理 add_descFactorial_eq_ascFactorial
  条件: (n : 自然数)
  结论: 对任意 k : 自然数,
-/
theorem add_descFactorial_eq_ascFactorial (n : Nat) : forall k : Nat,
    (n + k).descFactorial k = (n + 1).ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [Nat.add_succ]; rw [succ_descFactorial_succ]; rw [ascFactorial_succ]; rw [add_descFactorial_eq_ascFactorial _ k]; rw [Nat.add_right_comm]

/--
theorem `add_descFactorial_eq_ascFactorial'` / 定理 `add_descFactorial_eq_ascFactorial'`

English:
theorem add_descFactorial_eq_ascFactorial'
  given: (n : Nat)

中文:
定理 add_descFactorial_eq_ascFactorial'
  条件: (n : 自然数)
-/
theorem add_descFactorial_eq_ascFactorial' (n : Nat) :
    forall k : Nat, (n + k - 1).descFactorial k = n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [descFactorial_succ]; rw [ascFactorial_succ]; rw [← succ_add_eq_add_succ]; rw [add_descFactorial_eq_ascFactorial' _ k]; rw [← succ_ascFactorial]; rw [succ_add_sub_one]; rw [Nat.add_sub_cancel]

/--
theorem `factorial_mul_descFactorial` / 定理 `factorial_mul_descFactorial`

English:
theorem factorial_mul_descFactorial
  statement: forall {n k : Nat}, k <= n -> (n - k)! * n.descFactorial k = n !

中文:
定理 factorial_mul_descFactorial
  结论: 对任意 {n k : 自然数}, k <= n -> (n - k)! * n.descFactorial k = n !
-/
theorem factorial_mul_descFactorial : forall {n k : Nat}, k <= n -> (n - k)! * n.descFactorial k = n !
  | n, 0 => fun _ => by rw [descFactorial_zero, Nat.mul_one, Nat.sub_zero]
  | 0, succ k => fun h => by
    exfalso
    exact not_succ_le_zero k h
  | succ n, succ k => fun h => by
    rw [succ_descFactorial_succ]; rw [succ_sub_succ]; rw [← Nat.mul_assoc]; rw [Nat.mul_comm (n - k)!]; rw [Nat.mul_assoc]; rw [factorial_mul_descFactorial (Nat.succ_le_succ_iff.1 h)]; rw [factorial_succ]

/--
theorem `descFactorial_mul_descFactorial` / 定理 `descFactorial_mul_descFactorial`

English:
theorem descFactorial_mul_descFactorial
  given: {k m n : Nat} (hkm : k <= m)
  proof: by
  by_cases hmn : m <= n
  · apply Nat.mul_left_cancel (n - m).factorial_pos
    rw [factorial_mul_descFactorial hmn]; rw [show n - m = (n - k) - (m - k) by lia]; rw [← Nat.mul_assoc]; rw [factorial_mul_descFactorial (show m - k <= n - k by lia)]; rw [factorial_mul_descFactorial (le_trans hkm hmn)]
  · rw [descFactorial_eq_zero_iff_lt.mpr (show n < m by lia)]
    by_cases hkn : k <= n
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n - k < m - k by lia), Nat.zero_mul]
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n < k by lia), Nat.mul_zero]

中文:
定理 descFactorial_mul_descFactorial
  条件: {k m n : 自然数} (hkm : k <= m)
  证明: by
  by_cases hmn : m <= n
  · apply Nat.mul_left_cancel (n - m).factorial_pos
    rw [factorial_mul_descFactorial hmn]; rw [show n - m = (n - k) - (m - k) by lia]; rw [← Nat.mul_assoc]; rw [factorial_mul_descFactorial (show m - k <= n - k by lia)]; rw [factorial_mul_descFactorial (le_trans hkm hmn)]
  · rw [descFactorial_eq_zero_iff_lt.mpr (show n < m by lia)]
    by_cases hkn : k <= n
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n - k < m - k by lia), Nat.zero_mul]
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n < k by lia), Nat.mul_zero]

Depends on / 依赖: Nat.mul_assoc, Nat.mul_left_cancel, Nat.zero_mul, descFactorial_eq_zero_iff_lt, descFactorial_eq_zero_iff_lt.mpr, factorial_mul_descFactorial, factorial_pos, le_trans, mul_assoc, mul_left_cancel, zero_mul
-/
theorem descFactorial_mul_descFactorial {k m n : Nat} (hkm : k <= m) :
    (n - k).descFactorial (m - k) * n.descFactorial k = n.descFactorial m := by
  by_cases hmn : m <= n
  · apply Nat.mul_left_cancel (n - m).factorial_pos
    rw [factorial_mul_descFactorial hmn]; rw [show n - m = (n - k) - (m - k) by lia]; rw [← Nat.mul_assoc]; rw [factorial_mul_descFactorial (show m - k <= n - k by lia)]; rw [factorial_mul_descFactorial (le_trans hkm hmn)]
  · rw [descFactorial_eq_zero_iff_lt.mpr (show n < m by lia)]
    by_cases hkn : k <= n
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n - k < m - k by lia), Nat.zero_mul]
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n < k by lia), Nat.mul_zero]

/--
theorem `descFactorial_eq_div` / 定理 `descFactorial_eq_div`

English:
theorem descFactorial_eq_div
  given: {n k : Nat} (h : k <= n)
  statement: n.descFactorial k = n ! / (n - k)!
  proof: by
  apply Nat.mul_left_cancel (n - k).factorial_pos
  rw [factorial_mul_descFactorial h]
  exact (Nat.mul_div_cancel' <| factorial_dvd_factorial <| Nat.sub_le n k).symm

@[gcongr]

中文:
定理 descFactorial_eq_div
  条件: {n k : 自然数} (h : k <= n)
  结论: n.descFactorial k = n ! / (n - k)!
  证明: by
  apply Nat.mul_left_cancel (n - k).factorial_pos
  rw [factorial_mul_descFactorial h]
  exact (Nat.mul_div_cancel' <| factorial_dvd_factorial <| Nat.sub_le n k).symm

@[gcongr]

Depends on / 依赖: Nat.mul_div_cancel, Nat.mul_left_cancel, Nat.sub_le, factorial_dvd_factorial, factorial_mul_descFactorial, factorial_pos, mul_div_cancel, mul_left_cancel, sub_le
-/
theorem descFactorial_eq_div {n k : Nat} (h : k <= n) : n.descFactorial k = n ! / (n - k)! := by
  apply Nat.mul_left_cancel (n - k).factorial_pos
  rw [factorial_mul_descFactorial h]
  exact (Nat.mul_div_cancel' <| factorial_dvd_factorial <| Nat.sub_le n k).symm

@[gcongr]
/--
theorem `descFactorial_le` / 定理 `descFactorial_le`

English:
theorem descFactorial_le
  given: (n : Nat) {k m : Nat} (h : k <= m)
  proof: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [descFactorial_succ]; rw [descFactorial_succ]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right h n) ih

中文:
定理 descFactorial_le
  条件: (n : 自然数) {k m : 自然数} (h : k <= m)
  证明: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [descFactorial_succ]; rw [descFactorial_succ]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right h n) ih

Depends on / 依赖: Nat.mul_le_mul, Nat.sub_le_sub_right, descFactorial_succ, mul_le_mul, sub_le_sub_right
-/
theorem descFactorial_le (n : Nat) {k m : Nat} (h : k <= m) :
    k.descFactorial n <= m.descFactorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [descFactorial_succ]; rw [descFactorial_succ]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right h n) ih

/--
theorem `pow_sub_le_descFactorial` / 定理 `pow_sub_le_descFactorial`

English:
theorem pow_sub_le_descFactorial
  given: (n : Nat)
  statement: forall k : Nat, (n + 1 - k) ^ k <= n.descFactorial k

中文:
定理 pow_sub_le_descFactorial
  条件: (n : 自然数)
  结论: 对任意 k : 自然数, (n + 1 - k) ^ k <= n.descFactorial k
-/
theorem pow_sub_le_descFactorial (n : Nat) : forall k : Nat, (n + 1 - k) ^ k <= n.descFactorial k
  | 0 => by rw [descFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [descFactorial_succ]; rw [Nat.pow_succ]; rw [succ_sub_succ]; rw [Nat.mul_comm]
    apply Nat.mul_le_mul_left
    exact (le_trans (Nat.pow_le_pow_left (Nat.sub_le_sub_right n.le_succ _) k)
      (pow_sub_le_descFactorial n k))

/--
theorem `pow_sub_lt_descFactorial'` / 定理 `pow_sub_lt_descFactorial'`

English:
theorem pow_sub_lt_descFactorial'
  given: {n : Nat}

中文:
定理 pow_sub_lt_descFactorial'
  条件: {n : 自然数}
-/
theorem pow_sub_lt_descFactorial' {n : Nat} :
    forall {k : Nat}, k + 2 <= n -> (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2)
  | 0, h => by
    rw [descFactorial_succ]; rw [Nat.pow_succ]; rw [Nat.pow_one]; rw [descFactorial_one]
    exact Nat.mul_lt_mul_of_pos_left (by lia) (Nat.sub_pos_of_lt h)
  | k + 1, h => by
    rw [descFactorial_succ]; rw [Nat.pow_succ]; rw [Nat.mul_comm]
    refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.sub_pos_of_lt h)
    refine Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.sub_le_sub_right n.le_succ _) _) ?_
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' (Nat.le_trans (le_succ _) h)

/--
theorem `pow_sub_lt_descFactorial` / 定理 `pow_sub_lt_descFactorial`

English:
theorem pow_sub_lt_descFactorial
  given: {n : Nat}

中文:
定理 pow_sub_lt_descFactorial
  条件: {n : 自然数}
-/
theorem pow_sub_lt_descFactorial {n : Nat} :
    forall {k : Nat}, 2 <= k -> k <= n -> (n + 1 - k) ^ k < n.descFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ h => by
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' h

/--
theorem `descFactorial_le_pow` / 定理 `descFactorial_le_pow`

English:
theorem descFactorial_le_pow
  given: (n : Nat)
  statement: forall k : Nat, n.descFactorial k <= n ^ k

中文:
定理 descFactorial_le_pow
  条件: (n : 自然数)
  结论: 对任意 k : 自然数, n.descFactorial k <= n ^ k
-/
theorem descFactorial_le_pow (n : Nat) : forall k : Nat, n.descFactorial k <= n ^ k
  | 0 => by rw [descFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [descFactorial_succ]; rw [Nat.pow_succ]; rw [Nat.mul_comm _ n]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (descFactorial_le_pow _ k)

/--
theorem `descFactorial_lt_pow` / 定理 `descFactorial_lt_pow`

English:
theorem descFactorial_lt_pow
  given: {n : Nat} (hn : n != 0)
  statement: forall {k : Nat}, 2 <= k -> n.descFactorial k < n ^ k

中文:
定理 descFactorial_lt_pow
  条件: {n : 自然数} (hn : n != 0)
  结论: 对任意 {k : 自然数}, 2 <= k -> n.descFactorial k < n ^ k
-/
theorem descFactorial_lt_pow {n : Nat} (hn : n != 0) : forall {k : Nat}, 2 <= k -> n.descFactorial k < n ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [descFactorial_succ]; rw [pow_succ']; rw [Nat.mul_comm]; rw [Nat.mul_comm n]
    exact Nat.mul_lt_mul_of_le_of_lt (descFactorial_le_pow _ _) (by lia) (Nat.pow_pos <| by lia)

end DescFactorial

/--
lemma `factorial_two_mul_le` / 引理 `factorial_two_mul_le`

English:
lemma factorial_two_mul_le
  given: (n : Nat)
  statement: (2 * n)! <= (2 * n) ^ n * n !
  proof: by
  rw [Nat.two_mul]; rw [← factorial_mul_ascFactorial]; rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (ascFactorial_le_pow_add _ _)

中文:
引理 factorial_two_mul_le
  条件: (n : 自然数)
  结论: (2 * n)! <= (2 * n) ^ n * n !
  证明: by
  rw [Nat.two_mul]; rw [← factorial_mul_ascFactorial]; rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (ascFactorial_le_pow_add _ _)

Depends on / 依赖: Nat.mul_comm, Nat.mul_le_mul_right, Nat.two_mul, ascFactorial_le_pow_add, factorial_mul_ascFactorial, mul_comm, mul_le_mul_right, two_mul
-/
lemma factorial_two_mul_le (n : Nat) : (2 * n)! <= (2 * n) ^ n * n ! := by
  rw [Nat.two_mul]; rw [← factorial_mul_ascFactorial]; rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (ascFactorial_le_pow_add _ _)

/--
lemma `two_pow_mul_factorial_le_factorial_two_mul` / 引理 `two_pow_mul_factorial_le_factorial_two_mul`

English:
lemma two_pow_mul_factorial_le_factorial_two_mul
  given: (n : Nat)
  statement: 2 ^ n * n ! <= (2 * n)!
  proof: by
  obtain _ | n := n
  · simp
  rw [Nat.mul_comm]; rw [Nat.two_mul]
  calc
    _ <= (n + 1)! * (n + 2) ^ (n + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_add_left _ _) _)
    _ <= _ := Nat.factorial_mul_pow_le_factorial

中文:
引理 two_pow_mul_factorial_le_factorial_two_mul
  条件: (n : 自然数)
  结论: 2 ^ n * n ! <= (2 * n)!
  证明: by
  obtain _ | n := n
  · simp
  rw [Nat.mul_comm]; rw [Nat.two_mul]
  calc
    _ <= (n + 1)! * (n + 2) ^ (n + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_add_left _ _) _)
    _ <= _ := Nat.factorial_mul_pow_le_factorial

Depends on / 依赖: Nat.factorial_mul_pow_le_factorial, Nat.mul_comm, Nat.mul_le_mul_left, Nat.pow_le_pow_left, Nat.two_mul, factorial_mul_pow_le_factorial, le_add_left, mul_comm, mul_le_mul_left, pow_le_pow_left, two_mul
-/
lemma two_pow_mul_factorial_le_factorial_two_mul (n : Nat) : 2 ^ n * n ! <= (2 * n)! := by
  obtain _ | n := n
  · simp
  rw [Nat.mul_comm]; rw [Nat.two_mul]
  calc
    _ <= (n + 1)! * (n + 2) ^ (n + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_add_left _ _) _)
    _ <= _ := Nat.factorial_mul_pow_le_factorial


/-!
### Factorial via binary splitting.

We prove this is equal to the standard factorial and mark it `@[csimp]`.

We could proceed further, with either Legendre or Luschny methods.
-/

/-!
This is the highest factorial I can `#eval` using the naive implementation without a stack overflow:
```
/-- info: 114716 -/
#guard_msgs in
.log2 #eval 9718 !
```

Similarly, evaluation of `ascFactorial 100 15000` fails with the naive implementation
but works with the binary recursion.

We could implement a tail-recursive version (or just use `Nat.fold`),
but instead let's jump straight to binary splitting.
-/

/--
Definition of `ascFactorialBinary` / `ascFactorialBinary` 的定义

English:
definition ascFactorialBinary
  signature: (n k : Nat)
  body: match k with
  | 0 => 1
  | 1 => n
  | k@(_ + 2) => ascFactorialBinary n (k / 2) * ascFactorialBinary (n + k / 2) ((k + 1) / 2)

@[csimp]

中文:
定义 ascFactorialBinary
  签名: (n k : 自然数)
  定义体: match k with
  | 0 => 1
  | 1 => n
  | k@(_ + 2) => ascFactorialBinary n (k / 2) * ascFactorialBinary (n + k / 2) ((k + 1) / 2)

@[csimp]

Depends on / 依赖: ascFactorialBinary
-/
def ascFactorialBinary (n k : Nat) : Nat :=
  match k with
  | 0 => 1
  | 1 => n
  | k@(_ + 2) => ascFactorialBinary n (k / 2) * ascFactorialBinary (n + k / 2) ((k + 1) / 2)

@[csimp]
/--
lemma `ascFactorial_eq_ascFactorialBinary` / 引理 `ascFactorial_eq_ascFactorialBinary`

English:
lemma ascFactorial_eq_ascFactorialBinary
  statement: ascFactorial = ascFactorialBinary
  proof: by
  ext n k
  fun_induction ascFactorialBinary with
  | case1 => simp
  | case2 => simp [ascFactorial]
  | case3 n k ih₁ ih₂ => grind [ascFactorial_mul_ascFactorial]

中文:
引理 ascFactorial_eq_ascFactorialBinary
  结论: ascFactorial = ascFactorialBinary
  证明: by
  ext n k
  fun_induction ascFactorialBinary with
  | case1 => simp
  | case2 => simp [ascFactorial]
  | case3 n k ih₁ ih₂ => grind [ascFactorial_mul_ascFactorial]

Depends on / 依赖: ascFactorial, ascFactorialBinary, ascFactorial_mul_ascFactorial, fun_induction
-/
lemma ascFactorial_eq_ascFactorialBinary : ascFactorial = ascFactorialBinary := by
  ext n k
  fun_induction ascFactorialBinary with
  | case1 => simp
  | case2 => simp [ascFactorial]
  | case3 n k ih₁ ih₂ => grind [ascFactorial_mul_ascFactorial]

/--
Definition of `factorialBinarySplitting` / `factorialBinarySplitting` 的定义

English:
definition factorialBinarySplitting
  signature: (n : Nat)
  body: ascFactorialBinary 1 n

@[csimp]

中文:
定义 factorialBinarySplitting
  签名: (n : 自然数)
  定义体: ascFactorialBinary 1 n

@[csimp]

Depends on / 依赖: ascFactorialBinary
-/
def factorialBinarySplitting (n : Nat) : Nat :=
  ascFactorialBinary 1 n

@[csimp]
/--
theorem `factorial_eq_factorialBinarySplitting` / 定理 `factorial_eq_factorialBinarySplitting`

English:
theorem factorial_eq_factorialBinarySplitting
  statement: @factorial = @factorialBinarySplitting
  proof: by
  ext n
  simp [factorialBinarySplitting, ← ascFactorial_eq_ascFactorialBinary]

中文:
定理 factorial_eq_factorialBinarySplitting
  结论: @factorial = @factorialBinarySplitting
  证明: by
  ext n
  simp [factorialBinarySplitting, ← ascFactorial_eq_ascFactorialBinary]

Depends on / 依赖: ascFactorial_eq_ascFactorialBinary, factorialBinarySplitting
-/
theorem factorial_eq_factorialBinarySplitting : @factorial = @factorialBinarySplitting := by
  ext n
  simp [factorialBinarySplitting, ← ascFactorial_eq_ascFactorialBinary]

/--
Definition of `descFactorialBinary` / `descFactorialBinary` 的定义

English:
definition descFactorialBinary
  signature: (n k : Nat)
  body: if n < k then 0
  else ascFactorialBinary (n - k + 1) k

@[csimp]

中文:
定义 descFactorialBinary
  签名: (n k : 自然数)
  定义体: if n < k then 0
  else ascFactorialBinary (n - k + 1) k

@[csimp]

Depends on / 依赖: ascFactorialBinary
-/
def descFactorialBinary (n k : Nat) : Nat :=
  if n < k then 0
  else ascFactorialBinary (n - k + 1) k

@[csimp]
/--
theorem `descFactorial_eq_descFactorialBinary` / 定理 `descFactorial_eq_descFactorialBinary`

English:
theorem descFactorial_eq_descFactorialBinary
  statement: descFactorial = descFactorialBinary
  proof: by
  ext n k
  rw [descFactorialBinary]
  split_ifs with h
  · rw [descFactorial_of_lt h]
  · rw [← ascFactorial_eq_ascFactorialBinary, ← add_descFactorial_eq_ascFactorial']
    grind

中文:
定理 descFactorial_eq_descFactorialBinary
  结论: descFactorial = descFactorialBinary
  证明: by
  ext n k
  rw [descFactorialBinary]
  split_ifs with h
  · rw [descFactorial_of_lt h]
  · rw [← ascFactorial_eq_ascFactorialBinary, ← add_descFactorial_eq_ascFactorial']
    grind

Depends on / 依赖: add_descFactorial_eq_ascFactorial, ascFactorial_eq_ascFactorialBinary, descFactorialBinary, descFactorial_of_lt, split_ifs
-/
theorem descFactorial_eq_descFactorialBinary : descFactorial = descFactorialBinary := by
  ext n k
  rw [descFactorialBinary]
  split_ifs with h
  · rw [descFactorial_of_lt h]
  · rw [← ascFactorial_eq_ascFactorialBinary, ← add_descFactorial_eq_ascFactorial']
    grind

/-!
We are now limited by time, not stack space,
and this is much faster than even the tail-recursive version.

```
#time -- Less than 1s. (Tail-recursive version takes longer for `(10^5) !`.)
#eval (10^6) ! |>.log2
```
-/


end Nat
