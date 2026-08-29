/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Bits

/-! Lemmas about `size`. -/

public section

namespace Nat


/--
theorem `shiftLeft_eq_mul_pow` / 定理 `shiftLeft_eq_mul_pow`

English:
theorem shiftLeft_eq_mul_pow
  given: (m)
  statement: forall n, m <<< n = m * 2 ^ n
  proof: shiftLeft_eq _

中文:
定理 shiftLeft_eq_mul_pow
  条件: (m)
  结论: 对任意 n, m <<< n = m * 2 ^ n
  证明: shiftLeft_eq _

Depends on / 依赖: shiftLeft_eq
-/
theorem shiftLeft_eq_mul_pow (m) : forall n, m <<< n = m * 2 ^ n := shiftLeft_eq _

/--
theorem `shiftLeft'_true_eq_mul_pow` / 定理 `shiftLeft'_true_eq_mul_pow`

English:
theorem shiftLeft'_true_eq_mul_pow
  given: (m)
  statement: forall n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  proof: shiftLeft'_true_eq_mul_pow

中文:
定理 shiftLeft'_true_eq_mul_pow
  条件: (m)
  结论: 对任意 n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  证明: shiftLeft'_true_eq_mul_pow
-/
theorem shiftLeft'_true_eq_mul_pow (m) : forall n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftLeft', Nat.pow_zero]
  | k + 1 => by
    rw [shiftLeft']; rw [bit_val]; rw [Bool.toNat_true]; rw [Nat.add_assoc]; rw [← Nat.mul_add_one]; rw [shiftLeft'_true_eq_mul_pow m k]; rw [Nat.mul_left_comm]; rw [Nat.mul_comm 2]; rw [Nat.pow_succ]

@[deprecated (since := "2026-03-22")] alias shiftLeft'_tt_eq_mul_pow := shiftLeft'_true_eq_mul_pow

/--
theorem `shiftLeft'_ne_zero_left` / 定理 `shiftLeft'_ne_zero_left`

English:
theorem shiftLeft'_ne_zero_left
  given: (b) {m} (h : m != 0) (n)
  statement: shiftLeft' b m n != 0
  proof: by
  induction n <;> simp [shiftLeft', *]

中文:
定理 shiftLeft'_ne_zero_left
  条件: (b) {m} (h : m != 0) (n)
  结论: shiftLeft' b m n != 0
  证明: by
  induction n <;> simp [shiftLeft', *]
-/
theorem shiftLeft'_ne_zero_left (b) {m} (h : m != 0) (n) : shiftLeft' b m n != 0 := by
  induction n <;> simp [shiftLeft', *]

/--
theorem `shiftLeft'_true_ne_zero` / 定理 `shiftLeft'_true_ne_zero`

English:
theorem shiftLeft'_true_ne_zero
  given: (m)
  statement: forall {n}, (n != 0) -> shiftLeft' true m n != 0
  proof: shiftLeft'_true_ne_zero

中文:
定理 shiftLeft'_true_ne_zero
  条件: (m)
  结论: 对任意 {n}, (n != 0) -> shiftLeft' true m n != 0
  证明: shiftLeft'_true_ne_zero
-/
theorem shiftLeft'_true_ne_zero (m) : forall {n}, (n != 0) -> shiftLeft' true m n != 0
  | 0, h => absurd rfl h
  | succ _, _ => by simp [shiftLeft', bit]

@[deprecated (since := "2026-03-22")] alias shiftLeft'_tt_ne_zero := shiftLeft'_true_ne_zero

/-! ### `size` -/


@[simp]
/--
theorem `size_zero` / 定理 `size_zero`

English:
theorem size_zero
  statement: size 0 = 0
  proof: rfl

@[simp]

中文:
定理 size_zero
  结论: size 0 = 0
  证明: rfl

@[simp]
-/
theorem size_zero : size 0 = 0 := rfl

@[simp]
/--
theorem `size_bit` / 定理 `size_bit`

English:
theorem size_bit
  given: {b n} (h : bit b n != 0)
  statement: size (bit b n) = succ (size n)
  proof: Nat.binaryRec_eq _ _ (.inr <| Nat.bit_ne_zero_iff.mp h)

@[simp]

中文:
定理 size_bit
  条件: {b n} (h : bit b n != 0)
  结论: size (bit b n) = succ (size n)
  证明: Nat.binaryRec_eq _ _ (.inr <| Nat.bit_ne_zero_iff.mp h)

@[simp]

Depends on / 依赖: Nat.binaryRec_eq, Nat.bit_ne_zero_iff.mp, binaryRec_eq, bit_ne_zero_iff
-/
theorem size_bit {b n} (h : bit b n != 0) : size (bit b n) = succ (size n) :=
  Nat.binaryRec_eq _ _ (.inr <| Nat.bit_ne_zero_iff.mp h)

@[simp]
/--
theorem `size_one` / 定理 `size_one`

English:
theorem size_one
  statement: size 1 = 1
  proof: rfl

@[simp]

中文:
定理 size_one
  结论: size 1 = 1
  证明: rfl

@[simp]
-/
theorem size_one : size 1 = 1 := rfl

@[simp]
/--
theorem `size_shiftLeft'` / 定理 `size_shiftLeft'`

English:
theorem size_shiftLeft'
  given: {b m n} (h : shiftLeft' b m n != 0)
  proof: by
  induction n with
  | zero => simp [shiftLeft']
  | succ n IH =>
    simp only [shiftLeft', ne_eq] at h ⊢
    rw [size_bit h]; rw [Nat.add_succ]
    by_cases s0 : shiftLeft' b m n = 0
    case neg => rw [IH s0]
    rw [s0] at h ⊢
    cases b; · exact absurd rfl h
    have : shiftLeft' true m n + 1 = 1 := congr_arg (· + 1) s0
    rw [shiftLeft'_true_eq_mul_pow] at this
    obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
    simp only [Nat.zero_add, Nat.one_mul, Nat.pow_eq_one, succ_ne_self, false_or] at this
    rw [this]; rw [Nat.add_zero]

@[simp]

中文:
定理 size_shiftLeft'
  条件: {b m n} (h : shiftLeft' b m n != 0)
  证明: by
  induction n with
  | zero => simp [shiftLeft']
  | succ n IH =>
    simp only [shiftLeft', ne_eq] at h ⊢
    rw [size_bit h]; rw [Nat.add_succ]
    by_cases s0 : shiftLeft' b m n = 0
    case neg => rw [IH s0]
    rw [s0] at h ⊢
    cases b; · exact absurd rfl h
    have : shiftLeft' true m n + 1 = 1 := congr_arg (· + 1) s0
    rw [shiftLeft'_true_eq_mul_pow] at this
    obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
    simp only [Nat.zero_add, Nat.one_mul, Nat.pow_eq_one, succ_ne_self, false_or] at this
    rw [this]; rw [Nat.add_zero]

@[simp]

Depends on / 依赖: Nat.add_succ, Nat.one_mul, Nat.pow_eq_one, Nat.zero_add, _true_eq_mul_pow, absurd, add_succ, congr_arg, eq_one_of_dvd_one, false_or, ne_eq, one_mul, pow_eq_one, shiftLeft, size_bit, succ.inj, succ_ne_self, this.symm, zero_add
-/
theorem size_shiftLeft' {b m n} (h : shiftLeft' b m n != 0) :
    size (shiftLeft' b m n) = size m + n := by
  induction n with
  | zero => simp [shiftLeft']
  | succ n IH =>
    simp only [shiftLeft', ne_eq] at h ⊢
    rw [size_bit h]; rw [Nat.add_succ]
    by_cases s0 : shiftLeft' b m n = 0
    case neg => rw [IH s0]
    rw [s0] at h ⊢
    cases b; · exact absurd rfl h
    have : shiftLeft' true m n + 1 = 1 := congr_arg (· + 1) s0
    rw [shiftLeft'_true_eq_mul_pow] at this
    obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
    simp only [Nat.zero_add, Nat.one_mul, Nat.pow_eq_one, succ_ne_self, false_or] at this
    rw [this]; rw [Nat.add_zero]

@[simp]
/--
theorem `size_shiftLeft` / 定理 `size_shiftLeft`

English:
theorem size_shiftLeft
  given: {m} (h : m != 0) (n)
  statement: size (m <<< n) = size m + n
  proof: by
  simp only [size_shiftLeft' (shiftLeft'_ne_zero_left _ h _), ← shiftLeft'_false]

中文:
定理 size_shiftLeft
  条件: {m} (h : m != 0) (n)
  结论: size (m <<< n) = size m + n
  证明: by
  simp only [size_shiftLeft' (shiftLeft'_ne_zero_left _ h _), ← shiftLeft'_false]

Depends on / 依赖: _false, _ne_zero_left, shiftLeft, size_shiftLeft
-/
theorem size_shiftLeft {m} (h : m != 0) (n) : size (m <<< n) = size m + n := by
  simp only [size_shiftLeft' (shiftLeft'_ne_zero_left _ h _), ← shiftLeft'_false]

/--
theorem `lt_size_self` / 定理 `lt_size_self`

English:
theorem lt_size_self
  given: (n : Nat)
  statement: n < 2 ^ size n
  proof: by
  induction n using binaryRec' with
  | zero => simp
  | bit b n h IH =>
    rw [← Nat.bit_ne_zero_iff] at h
    rwa [size_bit h, bit_lt_two_pow_succ_iff]

中文:
定理 lt_size_self
  条件: (n : 自然数)
  结论: n < 2 ^ size n
  证明: by
  induction n using binaryRec' with
  | zero => simp
  | bit b n h IH =>
    rw [← Nat.bit_ne_zero_iff] at h
    rwa [size_bit h, bit_lt_two_pow_succ_iff]

Depends on / 依赖: Nat.bit_ne_zero_iff, binaryRec, bit_lt_two_pow_succ_iff, bit_ne_zero_iff, size_bit
-/
theorem lt_size_self (n : Nat) : n < 2 ^ size n := by
  induction n using binaryRec' with
  | zero => simp
  | bit b n h IH =>
    rw [← Nat.bit_ne_zero_iff] at h
    rwa [size_bit h, bit_lt_two_pow_succ_iff]

/--
theorem `size_le` / 定理 `size_le`

English:
theorem size_le
  given: {m n : Nat}
  statement: size m <= n ↔ m < 2 ^ n
  proof: ⟨fun h => Nat.lt_of_lt_of_le (lt_size_self _) (Nat.pow_le_pow_right (by decide) h), fun h => by
    induction m using binaryRec' generalizing n with
    | zero => simp
    | bit b m e IH =>
      rw [← Nat.bit_ne_zero_iff] at e
      rw [size_bit e]
      cases n with
      | zero => exact (e (Nat.lt_one_iff.mp h)).elim
      | succ n => exact succ_le_succ (IH (bit_lt_two_pow_succ_iff.mp h))⟩

中文:
定理 size_le
  条件: {m n : 自然数}
  结论: size m <= n ↔ m < 2 ^ n
  证明: ⟨fun h => Nat.lt_of_lt_of_le (lt_size_self _) (Nat.pow_le_pow_right (by decide) h), fun h => by
    induction m using binaryRec' generalizing n with
    | zero => simp
    | bit b m e IH =>
      rw [← Nat.bit_ne_zero_iff] at e
      rw [size_bit e]
      cases n with
      | zero => exact (e (Nat.lt_one_iff.mp h)).elim
      | succ n => exact succ_le_succ (IH (bit_lt_two_pow_succ_iff.mp h))⟩

Depends on / 依赖: Nat.bit_ne_zero_iff, Nat.lt_of_lt_of_le, Nat.lt_one_iff.mp, Nat.pow_le_pow_right, binaryRec, bit_lt_two_pow_succ_iff, bit_lt_two_pow_succ_iff.mp, bit_ne_zero_iff, generalizing, lt_of_lt_of_le, lt_one_iff, lt_size_self, pow_le_pow_right, size_bit, succ_le_succ
-/
theorem size_le {m n : Nat} : size m <= n ↔ m < 2 ^ n :=
  ⟨fun h => Nat.lt_of_lt_of_le (lt_size_self _) (Nat.pow_le_pow_right (by decide) h), fun h => by
    induction m using binaryRec' generalizing n with
    | zero => simp
    | bit b m e IH =>
      rw [← Nat.bit_ne_zero_iff] at e
      rw [size_bit e]
      cases n with
      | zero => exact (e (Nat.lt_one_iff.mp h)).elim
      | succ n => exact succ_le_succ (IH (bit_lt_two_pow_succ_iff.mp h))⟩

/--
theorem `lt_size` / 定理 `lt_size`

English:
theorem lt_size
  given: {m n : Nat}
  statement: m < size n ↔ 2 ^ m <= n
  proof: by
  rw [← Nat.not_lt]; rw [Decidable.iff_not_comm]; rw [Nat.not_lt]; rw [size_le]

中文:
定理 lt_size
  条件: {m n : 自然数}
  结论: m < size n ↔ 2 ^ m <= n
  证明: by
  rw [← Nat.not_lt]; rw [Decidable.iff_not_comm]; rw [Nat.not_lt]; rw [size_le]

Depends on / 依赖: Decidable, Decidable.iff_not_comm, Nat.not_lt, iff_not_comm, not_lt, size_le
-/
theorem lt_size {m n : Nat} : m < size n ↔ 2 ^ m <= n := by
  rw [← Nat.not_lt]; rw [Decidable.iff_not_comm]; rw [Nat.not_lt]; rw [size_le]

/--
theorem `size_pos` / 定理 `size_pos`

English:
theorem size_pos
  given: {n : Nat}
  statement: 0 < size n ↔ 0 < n
  proof: by rw [lt_size]; rfl

中文:
定理 size_pos
  条件: {n : 自然数}
  结论: 0 < size n ↔ 0 < n
  证明: by rw [lt_size]; rfl

Depends on / 依赖: lt_size
-/
theorem size_pos {n : Nat} : 0 < size n ↔ 0 < n := by rw [lt_size]; rfl

/--
theorem `size_eq_zero` / 定理 `size_eq_zero`

English:
theorem size_eq_zero
  given: {n : Nat}
  statement: size n = 0 ↔ n = 0
  proof: by
  simpa [Nat.pos_iff_ne_zero, Decidable.not_iff_not] using size_pos

中文:
定理 size_eq_zero
  条件: {n : 自然数}
  结论: size n = 0 ↔ n = 0
  证明: by
  simpa [Nat.pos_iff_ne_zero, Decidable.not_iff_not] using size_pos

Depends on / 依赖: Decidable, Decidable.not_iff_not, Nat.pos_iff_ne_zero, not_iff_not, pos_iff_ne_zero, size_pos
-/
theorem size_eq_zero {n : Nat} : size n = 0 ↔ n = 0 := by
  simpa [Nat.pos_iff_ne_zero, Decidable.not_iff_not] using size_pos

/--
theorem `size_pow` / 定理 `size_pow`

English:
theorem size_pow
  given: {n : Nat}
  statement: size (2 ^ n) = n + 1
  proof: by
  simpa [shiftLeft_eq, Nat.add_comm] using size_shiftLeft (m := 1) (by decide) n

中文:
定理 size_pow
  条件: {n : 自然数}
  结论: size (2 ^ n) = n + 1
  证明: by
  simpa [shiftLeft_eq, Nat.add_comm] using size_shiftLeft (m := 1) (by decide) n

Depends on / 依赖: Nat.add_comm, add_comm, shiftLeft_eq, size_shiftLeft
-/
theorem size_pow {n : Nat} : size (2 ^ n) = n + 1 := by
  simpa [shiftLeft_eq, Nat.add_comm] using size_shiftLeft (m := 1) (by decide) n

/--
theorem `size_le_size` / 定理 `size_le_size`

English:
theorem size_le_size
  given: {m n : Nat} (h : m <= n)
  statement: size m <= size n
  proof: size_le.2 Nat.lt_of_le_of_lt h (lt_size_self _)

中文:
定理 size_le_size
  条件: {m n : 自然数} (h : m <= n)
  结论: size m <= size n
  证明: size_le.2 Nat.lt_of_le_of_lt h (lt_size_self _)

Depends on / 依赖: Nat.lt_of_le_of_lt, lt_of_le_of_lt, lt_size_self, size_le
-/
theorem size_le_size {m n : Nat} (h : m <= n) : size m <= size n :=
size_le.2 Nat.lt_of_le_of_lt h (lt_size_self _)

/--
theorem `size_eq_bits_len` / 定理 `size_eq_bits_len`

English:
theorem size_eq_bits_len
  given: (n : Nat)
  statement: n.bits.length = n.size
  proof: by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h ih =>
    rw [size_bit]; rw [bits_append_bit _ _ h]
    · simp [ih]
    · simpa [bit_eq_zero_iff]

中文:
定理 size_eq_bits_len
  条件: (n : 自然数)
  结论: n.bits.length = n.size
  证明: by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h ih =>
    rw [size_bit]; rw [bits_append_bit _ _ h]
    · simp [ih]
    · simpa [bit_eq_zero_iff]

Depends on / 依赖: Nat.binaryRec, binaryRec, bit_eq_zero_iff, bits_append_bit, size_bit
-/
theorem size_eq_bits_len (n : Nat) : n.bits.length = n.size := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h ih =>
    rw [size_bit]; rw [bits_append_bit _ _ h]
    · simp [ih]
    · simpa [bit_eq_zero_iff]

end Nat
