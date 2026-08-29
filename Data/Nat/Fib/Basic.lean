/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann, Kyle Miller, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Data.Nat.DvdSequence
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fibonacci numbers

This file defines the Fibonacci sequence as `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`. Furthermore, it
proves results about the sequence and introduces methods to compute it quickly.

## Main definitions

- `Nat.fib` returns the stream of Fibonacci numbers.

## Main statements

- `Nat.fib_add_two`: shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁`.
- `Nat.fib_gcd`: `fib n` is a strong divisibility sequence.
- `Nat.fib_succ_eq_sum_choose`: `fib` is given by the sum of `Nat.choose` along an antidiagonal.
- `Nat.fib_succ_eq_succ_sum`: shows that `F₀ + F₁ + ⋯ + Fₙ = Fₙ₊₂ - 1`.
- `Nat.fib_two_mul` and `Nat.fib_two_mul_add_one` are the basis for an efficient algorithm to
  compute `fib` (see `Nat.fastFib`).

## Implementation notes

For efficiency purposes, the sequence is defined using `Stream.iterate`.

## Tags

Fibonacci numbers, Fibonacci sequence
-/

@[expose] public section

namespace Nat



/-- Implementation of the Fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/
@[pp_nodot]
/--
Definition of `fib` / `fib` 的定义

English:
definition fib
  signature: (n : Nat)
  body: ((fun p : Nat × Nat => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

@[simp]

中文:
定义 fib
  签名: (n : 自然数)
  定义体: ((fun p : Nat × Nat => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

@[simp]

Depends on / 依赖: p.fst, p.snd
-/
def fib (n : Nat) : Nat :=
  ((fun p : Nat × Nat => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

@[simp]
/--
theorem `fib_zero` / 定理 `fib_zero`

English:
theorem fib_zero
  statement: fib 0 = 0
  proof: rfl

@[simp]

中文:
定理 fib_zero
  结论: fib 0 = 0
  证明: rfl

@[simp]
-/
theorem fib_zero : fib 0 = 0 :=
  rfl

@[simp]
/--
theorem `fib_one` / 定理 `fib_one`

English:
theorem fib_one
  statement: fib 1 = 1
  proof: rfl

@[simp]

中文:
定理 fib_one
  结论: fib 1 = 1
  证明: rfl

@[simp]
-/
theorem fib_one : fib 1 = 1 :=
  rfl

@[simp]
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
theorem fib_two : fib 2 = 1 :=
  rfl

/--
theorem `fib_add_two` / 定理 `fib_add_two`

English:
theorem fib_add_two
  given: {n : Nat}
  statement: fib (n + 2) = fib n + fib (n + 1)
  proof: by
  simp [fib, Function.iterate_succ_apply']

中文:
定理 fib_add_two
  条件: {n : 自然数}
  结论: fib (n + 2) = fib n + fib (n + 1)
  证明: by
  simp [fib, Function.iterate_succ_apply']

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply
-/
theorem fib_add_two {n : Nat} : fib (n + 2) = fib n + fib (n + 1) := by
  simp [fib, Function.iterate_succ_apply']

/--
lemma `fib_add_one` / 引理 `fib_add_one`

English:
lemma fib_add_one
  statement: forall {n}, n != 0 -> fib (n + 1) = fib (n - 1) + fib n

中文:
引理 fib_add_one
  结论: 对任意 {n}, n != 0 -> fib (n + 1) = fib (n - 1) + fib n
-/
lemma fib_add_one : forall {n}, n != 0 -> fib (n + 1) = fib (n - 1) + fib n
  | _n + 1, _ => fib_add_two

/--
theorem `fib_le_fib_succ` / 定理 `fib_le_fib_succ`

English:
theorem fib_le_fib_succ
  given: {n : Nat}
  statement: fib n <= fib (n + 1)
  proof: by cases n <;> simp [fib_add_two]

@[gcongr, mono]

中文:
定理 fib_le_fib_succ
  条件: {n : 自然数}
  结论: fib n <= fib (n + 1)
  证明: by cases n <;> simp [fib_add_two]

@[gcongr, mono]

Depends on / 依赖: fib_add_two
-/
theorem fib_le_fib_succ {n : Nat} : fib n <= fib (n + 1) := by cases n <;> simp [fib_add_two]

@[gcongr, mono]
/--
theorem `fib_mono` / 定理 `fib_mono`

English:
theorem fib_mono
  statement: Monotone fib
  proof: monotone_nat_of_le_succ fun _ => fib_le_fib_succ

中文:
定理 fib_mono
  结论: 递增 fib
  证明: monotone_nat_of_le_succ fun _ => fib_le_fib_succ

Depends on / 依赖: fib_le_fib_succ, monotone_nat_of_le_succ
-/
theorem fib_mono : Monotone fib :=
  monotone_nat_of_le_succ fun _ => fib_le_fib_succ

/--
lemma `fib_eq_zero` / 引理 `fib_eq_zero`

English:
lemma fib_eq_zero
  statement: forall {n}, fib n = 0 ↔ n = 0

中文:
引理 fib_eq_zero
  结论: 对任意 {n}, fib n = 0 ↔ n = 0
-/
@[simp] lemma fib_eq_zero : forall {n}, fib n = 0 ↔ n = 0
| 0 => Iff.rfl
| 1 => Iff.rfl
| n + 2 => by simp [fib_add_two, fib_eq_zero]

/--
lemma `fib_pos` / 引理 `fib_pos`

English:
lemma fib_pos
  given: {n : Nat}
  statement: 0 < fib n ↔ 0 < n
  proof: by simp [pos_iff_ne_zero]

中文:
引理 fib_pos
  条件: {n : 自然数}
  结论: 0 < fib n ↔ 0 < n
  证明: by simp [pos_iff_ne_zero]
-/
@[simp] lemma fib_pos {n : Nat} : 0 < fib n ↔ 0 < n := by simp [pos_iff_ne_zero]

/--
theorem `fib_add_two_sub_fib_add_one` / 定理 `fib_add_two_sub_fib_add_one`

English:
theorem fib_add_two_sub_fib_add_one
  given: {n : Nat}
  statement: fib (n + 2) - fib (n + 1) = fib n
  proof: by
  rw [fib_add_two]; rw [add_tsub_cancel_right]

中文:
定理 fib_add_two_sub_fib_add_one
  条件: {n : 自然数}
  结论: fib (n + 2) - fib (n + 1) = fib n
  证明: by
  rw [fib_add_two]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, fib_add_two
-/
theorem fib_add_two_sub_fib_add_one {n : Nat} : fib (n + 2) - fib (n + 1) = fib n := by
  rw [fib_add_two]; rw [add_tsub_cancel_right]

/--
theorem `fib_lt_fib_succ` / 定理 `fib_lt_fib_succ`

English:
theorem fib_lt_fib_succ
  given: {n : Nat} (hn : 2 <= n)
  statement: fib n < fib (n + 1)
  proof: by
  rcases exists_add_of_le hn with ⟨n, rfl⟩
  rw [← tsub_pos_iff_lt]; rw [add_comm 2]; rw [add_right_comm]; rw [fib_add_two]; rw [add_tsub_cancel_right]; rw [fib_pos]
  exact succ_pos n

中文:
定理 fib_lt_fib_succ
  条件: {n : 自然数} (hn : 2 <= n)
  结论: fib n < fib (n + 1)
  证明: by
  rcases exists_add_of_le hn with ⟨n, rfl⟩
  rw [← tsub_pos_iff_lt]; rw [add_comm 2]; rw [add_right_comm]; rw [fib_add_two]; rw [add_tsub_cancel_right]; rw [fib_pos]
  exact succ_pos n

Depends on / 依赖: add_comm, add_right_comm, add_tsub_cancel_right, exists_add_of_le, fib_add_two, fib_pos, succ_pos, tsub_pos_iff_lt
-/
theorem fib_lt_fib_succ {n : Nat} (hn : 2 <= n) : fib n < fib (n + 1) := by
  rcases exists_add_of_le hn with ⟨n, rfl⟩
  rw [← tsub_pos_iff_lt]; rw [add_comm 2]; rw [add_right_comm]; rw [fib_add_two]; rw [add_tsub_cancel_right]; rw [fib_pos]
  exact succ_pos n

/--
theorem `fib_add_two_strictMono` / 定理 `fib_add_two_strictMono`

English:
theorem fib_add_two_strictMono
  statement: StrictMono fun n => fib (n + 2)
  proof: by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [add_right_comm]
  exact fib_lt_fib_succ (self_le_add_left _ _)

中文:
定理 fib_add_two_strictMono
  结论: 严格递增 fun n => fib (n + 2)
  证明: by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [add_right_comm]
  exact fib_lt_fib_succ (self_le_add_left _ _)

Depends on / 依赖: add_right_comm, fib_lt_fib_succ, self_le_add_left, strictMono_nat_of_lt_succ
-/
theorem fib_add_two_strictMono : StrictMono fun n => fib (n + 2) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [add_right_comm]
  exact fib_lt_fib_succ (self_le_add_left _ _)

/--
lemma `fib_strictMonoOn` / 引理 `fib_strictMonoOn`

English:
lemma fib_strictMonoOn
  statement: StrictMonoOn fib (Set.Ici 2)

中文:
引理 fib_strictMonoOn
  结论: StrictMonoOn fib (集合.左闭右无界区间 2)
-/
lemma fib_strictMonoOn : StrictMonoOn fib (Set.Ici 2)
| _m + 2, _, _n + 2, _, hmn => fib_add_two_strictMono lt_of_add_lt_add_right hmn

/--
lemma `fib_lt_fib` / 引理 `fib_lt_fib`

English:
lemma fib_lt_fib
  given: {m : Nat} (hm : 2 <= m)
  statement: forall {n}, fib m < fib n ↔ m < n

中文:
引理 fib_lt_fib
  条件: {m : 自然数} (hm : 2 <= m)
  结论: 对任意 {n}, fib m < fib n ↔ m < n
-/
lemma fib_lt_fib {m : Nat} (hm : 2 <= m) : forall {n}, fib m < fib n ↔ m < n
  | 0 => by simp
  | 1 => by simp
| n + 2 => fib_strictMonoOn.lt_iff_lt hm by simp

/--
theorem `le_fib_self` / 定理 `le_fib_self`

English:
theorem le_fib_self
  given: {n : Nat} (five_le_n : 5 <= n)
  statement: n <= fib n
  proof: by
  induction five_le_n with
  | refl => rfl -- 5 ≤ fib 5
  | @step n five_le_n IH => -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    calc
      n <= fib n := IH
      _ < fib (n + 1) := fib_lt_fib_succ (le_trans (by decide) five_le_n)

中文:
定理 le_fib_self
  条件: {n : 自然数} (five_le_n : 5 <= n)
  结论: n <= fib n
  证明: by
  induction five_le_n with
  | refl => rfl -- 5 ≤ fib 5
  | @step n five_le_n IH => -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    calc
      n <= fib n := IH
      _ < fib (n + 1) := fib_lt_fib_succ (le_trans (by decide) five_le_n)

Depends on / 依赖: fib_lt_fib_succ, five_le_n, le_trans, succ_le_iff
-/
theorem le_fib_self {n : Nat} (five_le_n : 5 <= n) : n <= fib n := by
  induction five_le_n with
  | refl => rfl -- 5 ≤ fib 5
  | @step n five_le_n IH => -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    calc
      n <= fib n := IH
      _ < fib (n + 1) := fib_lt_fib_succ (le_trans (by decide) five_le_n)

/--
lemma `le_fib_add_one` / 引理 `le_fib_add_one`

English:
lemma le_fib_add_one
  statement: forall n, n <= fib n + 1

中文:
引理 le_fib_add_one
  结论: 对任意 n, n <= fib n + 1
-/
lemma le_fib_add_one : forall n, n <= fib n + 1
  | 0 => zero_le_one
  | 1 => one_le_two
  | 2 => le_rfl
  | 3 => le_rfl
  | 4 => le_rfl
| _n + 5 => (le_fib_self le_add_self).trans le_succ _

/--
theorem `fib_coprime_fib_succ` / 定理 `fib_coprime_fib_succ`

English:
theorem fib_coprime_fib_succ
  given: (n : Nat)
  statement: Nat.Coprime (fib n) (fib (n + 1))
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp only [fib_add_two, coprime_add_self_right, Coprime, ih.symm]

中文:
定理 fib_coprime_fib_succ
  条件: (n : 自然数)
  结论: 自然数.Coprime (fib n) (fib (n + 1))
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp only [fib_add_two, coprime_add_self_right, Coprime, ih.symm]

Depends on / 依赖: Coprime, coprime_add_self_right, fib_add_two, ih.symm
-/
theorem fib_coprime_fib_succ (n : Nat) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [fib_add_two, coprime_add_self_right, Coprime, ih.symm]

/--
theorem `fib_add` / 定理 `fib_add`

English:
theorem fib_add
  given: (m n : Nat)
  statement: fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
  proof: by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n]; rw [add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

中文:
定理 fib_add
  条件: (m n : 自然数)
  结论: fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
  证明: by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n]; rw [add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

Depends on / 依赖: add_assoc, add_comm, fib_add_two, generalizing, specialize
-/
theorem fib_add (m n : Nat) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n]; rw [add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

/--
theorem `fib_two_mul` / 定理 `fib_two_mul`

English:
theorem fib_two_mul
  given: (n : Nat)
  statement: fib (2 * n) = fib n * (2 * fib (n + 1) - fib n)
  proof: by
  cases n
  · simp
  · rw [two_mul, ← add_assoc, fib_add, fib_add_two, two_mul]
    simp only [← add_assoc, add_tsub_cancel_right]
    ring

中文:
定理 fib_two_mul
  条件: (n : 自然数)
  结论: fib (2 * n) = fib n * (2 * fib (n + 1) - fib n)
  证明: by
  cases n
  · simp
  · rw [two_mul, ← add_assoc, fib_add, fib_add_two, two_mul]
    simp only [← add_assoc, add_tsub_cancel_right]
    ring

Depends on / 依赖: add_assoc, add_tsub_cancel_right, fib_add, fib_add_two, two_mul
-/
theorem fib_two_mul (n : Nat) : fib (2 * n) = fib n * (2 * fib (n + 1) - fib n) := by
  cases n
  · simp
  · rw [two_mul, ← add_assoc, fib_add, fib_add_two, two_mul]
    simp only [← add_assoc, add_tsub_cancel_right]
    ring

/--
theorem `fib_two_mul_add_one` / 定理 `fib_two_mul_add_one`

English:
theorem fib_two_mul_add_one
  given: (n : Nat)
  statement: fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2
  proof: by
  rw [two_mul]; rw [fib_add]
  ring

中文:
定理 fib_two_mul_add_one
  条件: (n : 自然数)
  结论: fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2
  证明: by
  rw [two_mul]; rw [fib_add]
  ring

Depends on / 依赖: fib_add, two_mul
-/
theorem fib_two_mul_add_one (n : Nat) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  rw [two_mul]; rw [fib_add]
  ring

/--
theorem `fib_two_mul_add_two` / 定理 `fib_two_mul_add_two`

English:
theorem fib_two_mul_add_two
  given: (n : Nat)
  proof: by
  rw [fib_add_two]; rw [fib_two_mul]; rw [fib_two_mul_add_one]
  have : fib n <= 2 * fib (n + 1) :=
    le_trans fib_le_fib_succ (mul_comm 2 _ ▸ Nat.le_mul_of_pos_right _ two_pos)
  zify [this]
  ring

中文:
定理 fib_two_mul_add_two
  条件: (n : 自然数)
  证明: by
  rw [fib_add_two]; rw [fib_two_mul]; rw [fib_two_mul_add_one]
  have : fib n <= 2 * fib (n + 1) :=
    le_trans fib_le_fib_succ (mul_comm 2 _ ▸ Nat.le_mul_of_pos_right _ two_pos)
  zify [this]
  ring

Depends on / 依赖: Nat.le_mul_of_pos_right, fib_add_two, fib_le_fib_succ, fib_two_mul, fib_two_mul_add_one, le_mul_of_pos_right, le_trans, mul_comm, two_pos
-/
theorem fib_two_mul_add_two (n : Nat) :
    fib (2 * n + 2) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [fib_add_two]; rw [fib_two_mul]; rw [fib_two_mul_add_one]
  have : fib n <= 2 * fib (n + 1) :=
    le_trans fib_le_fib_succ (mul_comm 2 _ ▸ Nat.le_mul_of_pos_right _ two_pos)
  zify [this]
  ring

/--
Definition of `fastFibAux` / `fastFibAux` 的定义

English:
definition fastFibAux
  signature: : Nat -> Nat × Nat
  body: Nat.binaryRec (fib 0, fib 1) fun b _ p =>
    if b then (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2))
    else (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2)

中文:
定义 fastFibAux
  签名: : 自然数 -> 自然数 × 自然数
  定义体: Nat.binaryRec (fib 0, fib 1) fun b _ p =>
    if b then (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2))
    else (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2)

Depends on / 依赖: Nat.binaryRec, binaryRec
-/
def fastFibAux : Nat -> Nat × Nat :=
  Nat.binaryRec (fib 0, fib 1) fun b _ p =>
    if b then (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2))
    else (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2)

/--
Definition of `fastFib` / `fastFib` 的定义

English:
definition fastFib
  signature: (n : Nat)
  body: (fastFibAux n).1

中文:
定义 fastFib
  签名: (n : 自然数)
  定义体: (fastFibAux n).1

Depends on / 依赖: fastFibAux
-/
def fastFib (n : Nat) : Nat :=
  (fastFibAux n).1

/--
theorem `fastFibAux_bit_false` / 定理 `fastFibAux_bit_false`

English:
theorem fastFibAux_bit_false
  given: (n : Nat)
  proof: fastFibAux n
      (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2) := by
  rw [fastFibAux]; rw [binaryRec_eq]
  · rfl
  · simp

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_bit_ff := fastFibAux_bit_false

中文:
定理 fastFibAux_bit_false
  条件: (n : 自然数)
  证明: fastFibAux n
      (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2) := by
  rw [fastFibAux]; rw [binaryRec_eq]
  · rfl
  · simp

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_bit_ff := fastFibAux_bit_false

Depends on / 依赖: fastFibAux
-/
theorem fastFibAux_bit_false (n : Nat) :
    fastFibAux (bit false n) =
      let p := fastFibAux n
      (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2) := by
  rw [fastFibAux]; rw [binaryRec_eq]
  · rfl
  · simp

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_bit_ff := fastFibAux_bit_false

/--
theorem `fastFibAux_bit_true` / 定理 `fastFibAux_bit_true`

English:
theorem fastFibAux_bit_true
  given: (n : Nat)
  proof: fastFibAux n
      (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2)) := by
  rw [fastFibAux]; rw [binaryRec_eq]
  · rfl
  · simp

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_bit_tt := fastFibAux_bit_true

中文:
定理 fastFibAux_bit_true
  条件: (n : 自然数)
  证明: fastFibAux n
      (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2)) := by
  rw [fastFibAux]; rw [binaryRec_eq]
  · rfl
  · simp

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_bit_tt := fastFibAux_bit_true

Depends on / 依赖: fastFibAux
-/
theorem fastFibAux_bit_true (n : Nat) :
    fastFibAux (bit true n) =
      let p := fastFibAux n
      (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2)) := by
  rw [fastFibAux]; rw [binaryRec_eq]
  · rfl
  · simp

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_bit_tt := fastFibAux_bit_true

/--
theorem `fastFibAux_eq` / 定理 `fastFibAux_eq`

English:
theorem fastFibAux_eq
  given: (n : Nat)
  statement: fastFibAux n = (fib n, fib (n + 1))
  proof: by
  refine Nat.binaryRec ?_ ?_ n
  · simp [fastFibAux]
  · rintro (_ | _) n' ih <;>
      simp only [fastFibAux_bit_false, fastFibAux_bit_true, congr_arg Prod.fst ih,
        congr_arg Prod.snd ih, Prod.mk_inj] <;>
      simp [bit, fib_two_mul, fib_two_mul_add_one, fib_two_mul_add_two]

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_eq := fastFibAux_eq

中文:
定理 fastFibAux_eq
  条件: (n : 自然数)
  结论: fastFibAux n = (fib n, fib (n + 1))
  证明: by
  refine Nat.binaryRec ?_ ?_ n
  · simp [fastFibAux]
  · rintro (_ | _) n' ih <;>
      simp only [fastFibAux_bit_false, fastFibAux_bit_true, congr_arg Prod.fst ih,
        congr_arg Prod.snd ih, Prod.mk_inj] <;>
      simp [bit, fib_two_mul, fib_two_mul_add_one, fib_two_mul_add_two]

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_eq := fastFibAux_eq

Depends on / 依赖: Nat.binaryRec, Prod.fst, Prod.mk_inj, Prod.snd, binaryRec, congr_arg, fastFibAux, fastFibAux_bit_false, fastFibAux_bit_true, fib_two_mul, fib_two_mul_add_one, fib_two_mul_add_two, mk_inj
-/
theorem fastFibAux_eq (n : Nat) : fastFibAux n = (fib n, fib (n + 1)) := by
  refine Nat.binaryRec ?_ ?_ n
  · simp [fastFibAux]
  · rintro (_ | _) n' ih <;>
      simp only [fastFibAux_bit_false, fastFibAux_bit_true, congr_arg Prod.fst ih,
        congr_arg Prod.snd ih, Prod.mk_inj] <;>
      simp [bit, fib_two_mul, fib_two_mul_add_one, fib_two_mul_add_two]

@[deprecated (since := "2026-02-04")] alias fast_fib_aux_eq := fastFibAux_eq

/--
theorem `fastFib_eq` / 定理 `fastFib_eq`

English:
theorem fastFib_eq
  given: (n : Nat)
  statement: fastFib n = fib n
  proof: by rw [fastFib, fastFibAux_eq]

@[deprecated (since := "2026-02-04")] alias fast_fib_eq := fastFib_eq

@[csimp]

中文:
定理 fastFib_eq
  条件: (n : 自然数)
  结论: fastFib n = fib n
  证明: by rw [fastFib, fastFibAux_eq]

@[deprecated (since := "2026-02-04")] alias fast_fib_eq := fastFib_eq

@[csimp]

Depends on / 依赖: fastFib, fastFibAux_eq
-/
theorem fastFib_eq (n : Nat) : fastFib n = fib n := by rw [fastFib, fastFibAux_eq]

@[deprecated (since := "2026-02-04")] alias fast_fib_eq := fastFib_eq

@[csimp]
/--
theorem `fib_eq_fastFib` / 定理 `fib_eq_fastFib`

English:
theorem fib_eq_fastFib
  statement: fib = fastFib
  proof: by ext; rw [fastFib_eq]

中文:
定理 fib_eq_fastFib
  结论: fib = fastFib
  证明: by ext; rw [fastFib_eq]

Depends on / 依赖: fastFib_eq
-/
theorem fib_eq_fastFib : fib = fastFib := by ext; rw [fastFib_eq]

/--
theorem `gcd_fib_add_self` / 定理 `gcd_fib_add_self`

English:
theorem gcd_fib_add_self
  given: (m n : Nat)
  statement: gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)
  proof: by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  replace h := Nat.succ_pred_eq_of_pos h; rw [← h, succ_eq_add_one]
  calc
    gcd (fib m) (fib (n.pred + 1 + m)) =
        gcd (fib m) (fib n.pred * fib m + fib (n.pred + 1) * fib (m + 1)) := by
        rw [← fib_add n.pred _]
        ring_nf
    _ = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) := by
        rw [add_comm]; rw [gcd_add_mul_right_right (fib m) _ (fib n.pred)]
    _ = gcd (fib m) (fib (n.pred + 1)) :=
      Coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (Coprime.symm (fib_coprime_fib_succ m))

中文:
定理 gcd_fib_add_self
  条件: (m n : 自然数)
  结论: 最大公约数 (fib m) (fib (n + m)) = 最大公约数 (fib m) (fib n)
  证明: by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  replace h := Nat.succ_pred_eq_of_pos h; rw [← h, succ_eq_add_one]
  calc
    gcd (fib m) (fib (n.pred + 1 + m)) =
        gcd (fib m) (fib n.pred * fib m + fib (n.pred + 1) * fib (m + 1)) := by
        rw [← fib_add n.pred _]
        ring_nf
    _ = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) := by
        rw [add_comm]; rw [gcd_add_mul_right_right (fib m) _ (fib n.pred)]
    _ = gcd (fib m) (fib (n.pred + 1)) :=
      Coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (Coprime.symm (fib_coprime_fib_succ m))

Depends on / 依赖: Coprime, Coprime.gcd_mul_right_cancel_right, Coprime.symm, Nat.eq_zero_or_pos, Nat.succ_pred_eq_of_pos, add_comm, eq_zero_or_pos, fib_add, fib_copr, gcd_add_mul_right_right, gcd_mul_right_cancel_right, n.pred, replace, ring_nf, succ_eq_add_one, succ_pred_eq_of_pos
-/
theorem gcd_fib_add_self (m n : Nat) : gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  replace h := Nat.succ_pred_eq_of_pos h; rw [← h, succ_eq_add_one]
  calc
    gcd (fib m) (fib (n.pred + 1 + m)) =
        gcd (fib m) (fib n.pred * fib m + fib (n.pred + 1) * fib (m + 1)) := by
        rw [← fib_add n.pred _]
        ring_nf
    _ = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) := by
        rw [add_comm]; rw [gcd_add_mul_right_right (fib m) _ (fib n.pred)]
    _ = gcd (fib m) (fib (n.pred + 1)) :=
      Coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (Coprime.symm (fib_coprime_fib_succ m))

/--
theorem `gcd_fib_add_mul_self` / 定理 `gcd_fib_add_mul_self`

English:
theorem gcd_fib_add_mul_self
  given: (m n : Nat)
  statement: forall k, gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n)

中文:
定理 gcd_fib_add_mul_self
  条件: (m n : 自然数)
  结论: 对任意 k, 最大公约数 (fib m) (fib (n + k * m)) = 最大公约数 (fib m) (fib n)
-/
theorem gcd_fib_add_mul_self (m n : Nat) : forall k, gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n)
  | 0 => by simp
  | k + 1 => by
    rw [← gcd_fib_add_mul_self m n k]; rw [add_mul]; rw [← add_assoc]; rw [one_mul]; rw [gcd_fib_add_self _ _]

/--
theorem `fib_gcd` / 定理 `fib_gcd`

English:
theorem fib_gcd
  given: (m n : Nat)
  statement: fib (gcd m n) = gcd (fib m) (fib n)
  proof: by
  induction m, n using Nat.gcd.induction with
  | H0 => simp
  | H1 m n _ h' =>
    rw [← gcd_rec m n] at h'
    conv_rhs => rw [← mod_add_div' n m]
    rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _]

中文:
定理 fib_gcd
  条件: (m n : 自然数)
  结论: fib (最大公约数 m n) = 最大公约数 (fib m) (fib n)
  证明: by
  induction m, n using Nat.gcd.induction with
  | H0 => simp
  | H1 m n _ h' =>
    rw [← gcd_rec m n] at h'
    conv_rhs => rw [← mod_add_div' n m]
    rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _]

Depends on / 依赖: Nat.gcd.induction, conv_rhs, gcd_comm, gcd_fib_add_mul_self, gcd_rec, mod_add_div
-/
theorem fib_gcd (m n : Nat) : fib (gcd m n) = gcd (fib m) (fib n) := by
  induction m, n using Nat.gcd.induction with
  | H0 => simp
  | H1 m n _ h' =>
    rw [← gcd_rec m n] at h'
    conv_rhs => rw [← mod_add_div' n m]
    rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _]

/--
theorem `isStrongDvdSequence_fib` / 定理 `isStrongDvdSequence_fib`

English:
theorem isStrongDvdSequence_fib
  statement: IsStrongDvdSequence fib
  proof: fun m n => (fib_gcd m n).symm

中文:
定理 isStrongDvdSequence_fib
  结论: IsStrongDvdSequence fib
  证明: fun m n => (fib_gcd m n).symm

Depends on / 依赖: fib_gcd
-/
theorem isStrongDvdSequence_fib : IsStrongDvdSequence fib :=
  fun m n => (fib_gcd m n).symm

/--
theorem `isDvdSequence_fib` / 定理 `isDvdSequence_fib`

English:
theorem isDvdSequence_fib
  statement: IsDvdSequence fib
  proof: isStrongDvdSequence_fib.isDvdSequence

alias fib_dvd := isDvdSequence_fib

中文:
定理 isDvdSequence_fib
  结论: IsDvdSequence fib
  证明: isStrongDvdSequence_fib.isDvdSequence

alias fib_dvd := isDvdSequence_fib

Depends on / 依赖: isDvdSequence, isStrongDvdSequence_fib, isStrongDvdSequence_fib.isDvdSequence
-/
theorem isDvdSequence_fib : IsDvdSequence fib :=
  isStrongDvdSequence_fib.isDvdSequence

alias fib_dvd := isDvdSequence_fib

/--
theorem `fib_succ_eq_sum_choose` / 定理 `fib_succ_eq_sum_choose`

English:
theorem fib_succ_eq_sum_choose
  proof: twoStepInduction rfl rfl fun n h1 h2 => by
    rw [fib_add_two]; rw [h1]; rw [h2]; rw [Finset.Nat.antidiagonal_succ_succ']; rw [Finset.Nat.antidiagonal_succ']
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_comm]

中文:
定理 fib_succ_eq_sum_choose
  证明: twoStepInduction rfl rfl fun n h1 h2 => by
    rw [fib_add_two]; rw [h1]; rw [h2]; rw [Finset.Nat.antidiagonal_succ_succ']; rw [Finset.Nat.antidiagonal_succ']
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_comm]

Depends on / 依赖: Finset, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_succ_succ, Finset.sum_add_distrib, add_left_comm, antidiagonal_succ, antidiagonal_succ_succ, choose_succ_succ, fib_add_two, sum_add_distrib, twoStepInduction
-/
theorem fib_succ_eq_sum_choose :
    forall n : Nat, fib (n + 1) = ∑ p in Finset.antidiagonal n, choose p.1 p.2 :=
  twoStepInduction rfl rfl fun n h1 h2 => by
    rw [fib_add_two]; rw [h1]; rw [h2]; rw [Finset.Nat.antidiagonal_succ_succ']; rw [Finset.Nat.antidiagonal_succ']
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_comm]

/--
theorem `fib_succ_eq_succ_sum` / 定理 `fib_succ_eq_succ_sum`

English:
theorem fib_succ_eq_succ_sum
  given: (n : Nat)
  statement: fib (n + 1) = (∑ k in Finset.range n, fib k) + 1
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      _ = (fib n + ∑ k in Finset.range n, fib k) + 1 := by rw [ih, add_assoc]
      _ = (∑ k in Finset.range (n + 1), fib k) + 1 := by simp [Finset.range_add_one]

中文:
定理 fib_succ_eq_succ_sum
  条件: (n : 自然数)
  结论: fib (n + 1) = (∑ k in 有限集.range n, fib k) + 1
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      _ = (fib n + ∑ k in Finset.range n, fib k) + 1 := by rw [ih, add_assoc]
      _ = (∑ k in Finset.range (n + 1), fib k) + 1 := by simp [Finset.range_add_one]

Depends on / 依赖: Finset, Finset.range, Finset.range_add_one, add_assoc, fib_add_two, range_add_one
-/
theorem fib_succ_eq_succ_sum (n : Nat) : fib (n + 1) = (∑ k in Finset.range n, fib k) + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      _ = (fib n + ∑ k in Finset.range n, fib k) + 1 := by rw [ih, add_assoc]
      _ = (∑ k in Finset.range (n + 1), fib k) + 1 := by simp [Finset.range_add_one]

end Nat
