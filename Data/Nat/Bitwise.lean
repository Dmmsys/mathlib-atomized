/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Alex Keizer
-/
module

public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Bits
public import Mathlib.Order.Basic
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.Common
public import Batteries.Data.Nat.Bitwise
import all Init.Data.Nat.Bitwise.Basic -- for unfolding `bitwise`

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `xor`, which are defined in core.

## Main results
* `eq_of_testBit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_testBit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/

public section

open Function

namespace Nat

section
variable {f : Bool -> Bool -> Bool}

@[simp]
/--
lemma `bitwise_zero_left` / 引理 `bitwise_zero_left`

English:
lemma bitwise_zero_left
  given: (m : Nat)
  statement: bitwise f 0 m = if f false true then m else 0
  proof: by
  simp [bitwise]

@[simp]

中文:
引理 bitwise_zero_left
  条件: (m : 自然数)
  结论: bitwise f 0 m = if f false true then m else 0
  证明: by
  simp [bitwise]

@[simp]

Depends on / 依赖: bitwise
-/
lemma bitwise_zero_left (m : Nat) : bitwise f 0 m = if f false true then m else 0 := by
  simp [bitwise]

@[simp]
/--
lemma `bitwise_zero_right` / 引理 `bitwise_zero_right`

English:
lemma bitwise_zero_right
  given: (n : Nat)
  statement: bitwise f n 0 = if f true false then n else 0
  proof: by
  unfold bitwise
  simp only [ite_self, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl

中文:
引理 bitwise_zero_right
  条件: (n : 自然数)
  结论: bitwise f n 0 = if f true false then n else 0
  证明: by
  unfold bitwise
  simp only [ite_self, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl

Depends on / 依赖: Nat.zero_div, bitwise, ite_eq_right_iff, ite_self, ite_true, split_ifs, zero_div
-/
lemma bitwise_zero_right (n : Nat) : bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  simp only [ite_self, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl

/--
lemma `bitwise_zero` / 引理 `bitwise_zero`

English:
lemma bitwise_zero
  statement: bitwise f 0 0 = 0
  proof: by
  simp only [bitwise_zero_right, ite_self]

中文:
引理 bitwise_zero
  结论: bitwise f 0 0 = 0
  证明: by
  simp only [bitwise_zero_right, ite_self]

Depends on / 依赖: bitwise_zero_right, ite_self
-/
lemma bitwise_zero : bitwise f 0 0 = 0 := by
  simp only [bitwise_zero_right, ite_self]

/--
lemma `bitwise_of_ne_zero` / 引理 `bitwise_of_ne_zero`

English:
lemma bitwise_of_ne_zero
  given: {n m : Nat} (hn : n != 0) (hm : m != 0)
  proof: by
  conv_lhs => unfold bitwise
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp only [mod_two_of_bodd]; cases bodd x <;> rfl
  simp [hn, hm, mod_two_iff_bod, bit, two_mul]

中文:
引理 bitwise_of_ne_zero
  条件: {n m : 自然数} (hn : n != 0) (hm : m != 0)
  证明: by
  conv_lhs => unfold bitwise
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp only [mod_two_of_bodd]; cases bodd x <;> rfl
  simp [hn, hm, mod_two_iff_bod, bit, two_mul]

Depends on / 依赖: bitwise, conv_lhs, mod_two_iff_bod, mod_two_of_bodd, two_mul
-/
lemma bitwise_of_ne_zero {n m : Nat} (hn : n != 0) (hm : m != 0) :
    bitwise f n m = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2)) := by
  conv_lhs => unfold bitwise
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp only [mod_two_of_bodd]; cases bodd x <;> rfl
  simp [hn, hm, mod_two_iff_bod, bit, two_mul]

/--
theorem `binaryRec_of_ne_zero` / 定理 `binaryRec_of_ne_zero`

English:
theorem binaryRec_of_ne_zero
  statement: {C : Nat -> Sort*} (z : C 0) (f : forall b n, C n -> C (bit b n)) {n}
  proof: by
  rw [binaryRec]; rw [dif_neg h]; rw [eqRec_eq_cast]; rw [eqRec_eq_cast]; rfl

@[simp]

中文:
定理 binaryRec_of_ne_zero
  结论: {C : 自然数 -> 类型层*} (z : C 0) (f : 对任意 b n, C n -> C (bit b n)) {n}
  证明: by
  rw [binaryRec]; rw [dif_neg h]; rw [eqRec_eq_cast]; rw [eqRec_eq_cast]; rfl

@[simp]

Depends on / 依赖: binaryRec, dif_neg, eqRec_eq_cast
-/
theorem binaryRec_of_ne_zero {C : Nat -> Sort*} (z : C 0) (f : forall b n, C n -> C (bit b n)) {n}
    (h : n != 0) :
    binaryRec z f n = n.bit_bodd_div2 ▸ f n.bodd n.div2 (binaryRec z f n.div2) := by
  rw [binaryRec]; rw [dif_neg h]; rw [eqRec_eq_cast]; rw [eqRec_eq_cast]; rfl

@[simp]
/--
lemma `bitwise_bit` / 引理 `bitwise_bit`

English:
lemma bitwise_bit
  given: {f : Bool -> Bool -> Bool} (h : f false false = false := by rfl) (a m b n)
  proof: by
  conv_lhs => unfold bitwise
  simp only [bit, Bool.cond_eq_ite]
  have h4 x : (x + x + 1) / 2 = x := by rw [← two_mul, add_comm]; simp [add_mul_div_left]
  cases a <;> cases b <;> simp <;> split_ifs
    <;> simp_all +decide [two_mul]

中文:
引理 bitwise_bit
  条件: {f : 布尔值 -> 布尔值 -> 布尔值} (h : f false false = false := by rfl) (a m b n)
  证明: by
  conv_lhs => unfold bitwise
  simp only [bit, Bool.cond_eq_ite]
  have h4 x : (x + x + 1) / 2 = x := by rw [← two_mul, add_comm]; simp [add_mul_div_left]
  cases a <;> cases b <;> simp <;> split_ifs
    <;> simp_all +decide [two_mul]

Depends on / 依赖: Bool.cond_eq_ite, add_comm, add_mul_div_left, bitwise, cond_eq_ite, conv_lhs, split_ifs, two_mul
-/
lemma bitwise_bit {f : Bool -> Bool -> Bool} (h : f false false = false := by rfl) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  simp only [bit, Bool.cond_eq_ite]
  have h4 x : (x + x + 1) / 2 = x := by rw [← two_mul, add_comm]; simp [add_mul_div_left]
  cases a <;> cases b <;> simp <;> split_ifs
    <;> simp_all +decide [two_mul]

/--
lemma `bit_mod_two_eq_zero_iff` / 引理 `bit_mod_two_eq_zero_iff`

English:
lemma bit_mod_two_eq_zero_iff
  given: (a x)
  proof: by
  simp

中文:
引理 bit_mod_two_eq_zero_iff
  条件: (a x)
  证明: by
  simp
-/
lemma bit_mod_two_eq_zero_iff (a x) :
    bit a x % 2 = 0 ↔ !a := by
  simp

/--
lemma `bit_mod_two_eq_one_iff` / 引理 `bit_mod_two_eq_one_iff`

English:
lemma bit_mod_two_eq_one_iff
  given: (a x)
  proof: by
  simp

@[simp]

中文:
引理 bit_mod_two_eq_one_iff
  条件: (a x)
  证明: by
  simp

@[simp]
-/
lemma bit_mod_two_eq_one_iff (a x) :
    bit a x % 2 = 1 ↔ a := by
  simp

@[simp]
/--
theorem `lor_bit` / 定理 `lor_bit`

English:
theorem lor_bit
  statement: forall a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n)
  proof: bitwise_bit

@[simp]

中文:
定理 lor_bit
  结论: 对任意 a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n)
  证明: bitwise_bit

@[simp]

Depends on / 依赖: bitwise_bit
-/
theorem lor_bit : forall a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n) :=
  bitwise_bit

@[simp]
/--
theorem `land_bit` / 定理 `land_bit`

English:
theorem land_bit
  statement: forall a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n)
  proof: bitwise_bit

@[simp]

中文:
定理 land_bit
  结论: 对任意 a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n)
  证明: bitwise_bit

@[simp]

Depends on / 依赖: bitwise_bit
-/
theorem land_bit : forall a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n) :=
  bitwise_bit

@[simp]
/--
theorem `ldiff_bit` / 定理 `ldiff_bit`

English:
theorem ldiff_bit
  statement: forall a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n)
  proof: bitwise_bit

@[simp]

中文:
定理 ldiff_bit
  结论: 对任意 a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n)
  证明: bitwise_bit

@[simp]

Depends on / 依赖: bitwise_bit
-/
theorem ldiff_bit : forall a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit

@[simp]
/--
theorem `xor_bit` / 定理 `xor_bit`

English:
theorem xor_bit
  statement: forall a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n)
  proof: bitwise_bit

中文:
定理 xor_bit
  结论: 对任意 a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n)
  证明: bitwise_bit

Depends on / 依赖: bitwise_bit
-/
theorem xor_bit : forall a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n) :=
  bitwise_bit

attribute [simp] Nat.testBit_bitwise

/--
theorem `testBit_lor` / 定理 `testBit_lor`

English:
theorem testBit_lor
  statement: forall m n k, testBit (m ||| n) k = (testBit m k || testBit n k)
  proof: testBit_bitwise rfl

中文:
定理 testBit_lor
  结论: 对任意 m n k, testBit (m ||| n) k = (testBit m k || testBit n k)
  证明: testBit_bitwise rfl

Depends on / 依赖: testBit_bitwise
-/
theorem testBit_lor : forall m n k, testBit (m ||| n) k = (testBit m k || testBit n k) :=
  testBit_bitwise rfl

/--
theorem `testBit_land` / 定理 `testBit_land`

English:
theorem testBit_land
  statement: forall m n k, testBit (m &&& n) k = (testBit m k && testBit n k)
  proof: testBit_bitwise rfl

@[simp]

中文:
定理 testBit_land
  结论: 对任意 m n k, testBit (m &&& n) k = (testBit m k && testBit n k)
  证明: testBit_bitwise rfl

@[simp]

Depends on / 依赖: testBit_bitwise
-/
theorem testBit_land : forall m n k, testBit (m &&& n) k = (testBit m k && testBit n k) :=
  testBit_bitwise rfl

@[simp]
/--
theorem `testBit_ldiff` / 定理 `testBit_ldiff`

English:
theorem testBit_ldiff
  statement: forall m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k))
  proof: testBit_bitwise rfl

中文:
定理 testBit_ldiff
  结论: 对任意 m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k))
  证明: testBit_bitwise rfl

Depends on / 依赖: testBit_bitwise
-/
theorem testBit_ldiff : forall m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise rfl

end

/--
lemma `bitwise_bit'` / 引理 `bitwise_bit'`

English:
lemma bitwise_bit'
  statement: {f : Bool -> Bool -> Bool} (a : Bool) (m : Nat) (b : Bool) (n : Nat)
  proof: by
  conv_lhs => unfold bitwise
  rw [← bit_ne_zero_iff] at ham hbn
  simp only [ham, hbn, bit_mod_two_eq_one_iff, Bool.decide_coe, ← div2_val, div2_bit,
    ite_false]
  conv_rhs => simp only [bit, two_mul, Bool.cond_eq_ite]

中文:
引理 bitwise_bit'
  结论: {f : 布尔值 -> 布尔值 -> 布尔值} (a : 布尔值) (m : 自然数) (b : 布尔值) (n : 自然数)
  证明: by
  conv_lhs => unfold bitwise
  rw [← bit_ne_zero_iff] at ham hbn
  simp only [ham, hbn, bit_mod_two_eq_one_iff, Bool.decide_coe, ← div2_val, div2_bit,
    ite_false]
  conv_rhs => simp only [bit, two_mul, Bool.cond_eq_ite]

Depends on / 依赖: Bool.cond_eq_ite, Bool.decide_coe, bit_mod_two_eq_one_iff, bit_ne_zero_iff, bitwise, cond_eq_ite, conv_lhs, conv_rhs, decide_coe, div2_bit, div2_val, ite_false, two_mul
-/
lemma bitwise_bit' {f : Bool -> Bool -> Bool} (a : Bool) (m : Nat) (b : Bool) (n : Nat)
    (ham : m = 0 -> a = true) (hbn : n = 0 -> b = true) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  rw [← bit_ne_zero_iff] at ham hbn
  simp only [ham, hbn, bit_mod_two_eq_one_iff, Bool.decide_coe, ← div2_val, div2_bit,
    ite_false]
  conv_rhs => simp only [bit, two_mul, Bool.cond_eq_ite]

/--
lemma `bitwise_eq_binaryRec` / 引理 `bitwise_eq_binaryRec`

English:
lemma bitwise_eq_binaryRec
  given: (f : Bool -> Bool -> Bool)
  proof: by
  funext x y
  induction x using binaryRec' generalizing y with
  | zero => simp only [bitwise_zero_left, binaryRec_zero, Bool.cond_eq_ite]
  | bit xb x hxb ih =>
    rw [← bit_ne_zero_iff] at hxb
    simp_rw [binaryRec_of_ne_zero _ _ hxb, bodd_bit, div2_bit, eq_rec_constant]
    induction y usin

中文:
引理 bitwise_eq_binaryRec
  条件: (f : 布尔值 -> 布尔值 -> 布尔值)
  证明: by
  funext x y
  induction x using binaryRec' generalizing y with
  | zero => simp only [bitwise_zero_left, binaryRec_zero, Bool.cond_eq_ite]
  | bit xb x hxb ih =>
    rw [← bit_ne_zero_iff] at hxb
    simp_rw [binaryRec_of_ne_zero _ _ hxb, bodd_bit, div2_bit, eq_rec_constant]
    induction y usin

Depends on / 依赖: Bool.cond_eq_ite, binaryRec, binaryRec_of_ne_zero, binaryRec_zero, bit_ne_zero_iff, bitwise_of_ne_zero, bitwise_zero_left, bitwise_zero_right, bodd_bit, cond_eq_ite, div2_bit, eq_rec_constant, generalizing, simp_rw
-/
lemma bitwise_eq_binaryRec (f : Bool -> Bool -> Bool) :
    bitwise f =
    binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
      binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n) := by
  funext x y
  induction x using binaryRec' generalizing y with
  | zero => simp only [bitwise_zero_left, binaryRec_zero, Bool.cond_eq_ite]
  | bit xb x hxb ih =>
    rw [← bit_ne_zero_iff] at hxb
    simp_rw [binaryRec_of_ne_zero _ _ hxb, bodd_bit, div2_bit, eq_rec_constant]
    induction y using binaryRec' with
    | zero => simp only [bitwise_zero_right, binaryRec_zero, Bool.cond_eq_ite]
    | bit yb y hyb =>
      rw [← bit_ne_zero_iff] at hyb
      simp_rw [binaryRec_of_ne_zero _ _ hyb, bitwise_of_ne_zero hxb hyb, bodd_bit, div2_bit,
        bit_div_two, eq_rec_constant, ih]

/--
theorem `zero_of_testBit_eq_false` / 定理 `zero_of_testBit_eq_false`

English:
theorem zero_of_testBit_eq_false
  given: {n : Nat} (h : forall i, testBit n i = false)
  statement: n = 0
  proof: by
  induction n using Nat.binaryRec with | zero => rfl | bit b n hn => ?_
  have : b = false := by simpa using h 0
  rw [this]; rw [bit_false]; rw [hn fun i => by rw [← h (i + 1)]; rw [testBit_bit_succ]]

中文:
定理 zero_of_testBit_eq_false
  条件: {n : 自然数} (h : 对任意 i, testBit n i = false)
  结论: n = 0
  证明: by
  induction n using Nat.binaryRec with | zero => rfl | bit b n hn => ?_
  have : b = false := by simpa using h 0
  rw [this]; rw [bit_false]; rw [hn fun i => by rw [← h (i + 1)]; rw [testBit_bit_succ]]

Depends on / 依赖: Nat.binaryRec, binaryRec, bit_false, testBit_bit_succ
-/
theorem zero_of_testBit_eq_false {n : Nat} (h : forall i, testBit n i = false) : n = 0 := by
  induction n using Nat.binaryRec with | zero => rfl | bit b n hn => ?_
  have : b = false := by simpa using h 0
  rw [this]; rw [bit_false]; rw [hn fun i => by rw [← h (i + 1)]; rw [testBit_bit_succ]]

/--
theorem `testBit_eq_false_of_lt` / 定理 `testBit_eq_false_of_lt`

English:
theorem testBit_eq_false_of_lt
  given: {n i} (h : n < 2 ^ i)
  statement: n.testBit i = false
  proof: by
  simp [testBit, shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

中文:
定理 testBit_eq_false_of_lt
  条件: {n i} (h : n < 2 ^ i)
  结论: n.testBit i = false
  证明: by
  simp [testBit, shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

Depends on / 依赖: Nat.div_eq_of_lt, div_eq_of_lt, shiftRight_eq_div_pow, testBit
-/
theorem testBit_eq_false_of_lt {n i} (h : n < 2 ^ i) : n.testBit i = false := by
  simp [testBit, shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

/--
theorem `testBit_eq_inth` / 定理 `testBit_eq_inth`

English:
theorem testBit_eq_inth
  given: (n i : Nat)
  statement: n.testBit i = n.bits.getI i
  proof: by
  induction i generalizing n with
  | zero =>
    simp only [testBit, shiftRight_zero, one_and_eq_mod_two, mod_two_of_bodd,
      bodd_eq_bits_head, List.getI_zero_eq_headI]
    cases List.headI (bits n) <;> rfl
  | succ i ih =>
    conv_lhs => rw [← bit_bodd_div2 n]
    rw [testBit_bit_succ]; rw

中文:
定理 testBit_eq_inth
  条件: (n i : 自然数)
  结论: n.testBit i = n.bits.getI i
  证明: by
  induction i generalizing n with
  | zero =>
    simp only [testBit, shiftRight_zero, one_and_eq_mod_two, mod_two_of_bodd,
      bodd_eq_bits_head, List.getI_zero_eq_headI]
    cases List.headI (bits n) <;> rfl
  | succ i ih =>
    conv_lhs => rw [← bit_bodd_div2 n]
    rw [testBit_bit_succ]; rw

Depends on / 依赖: List.getI_zero_eq_headI, List.headI, bit_bodd_div2, bodd_eq_bits_head, conv_lhs, div2_bits_eq_tail, generalizing, getI_zero_eq_headI, mod_two_of_bodd, n.bits, n.div2, one_and_eq_mod_two, shiftRight_zero, testBit, testBit_bit_succ
-/
theorem testBit_eq_inth (n i : Nat) : n.testBit i = n.bits.getI i := by
  induction i generalizing n with
  | zero =>
    simp only [testBit, shiftRight_zero, one_and_eq_mod_two, mod_two_of_bodd,
      bodd_eq_bits_head, List.getI_zero_eq_headI]
    cases List.headI (bits n) <;> rfl
  | succ i ih =>
    conv_lhs => rw [← bit_bodd_div2 n]
    rw [testBit_bit_succ]; rw [ih n.div2]; rw [div2_bits_eq_tail]
    cases n.bits <;> simp

/--
theorem `exists_most_significant_bit` / 定理 `exists_most_significant_bit`

English:
theorem exists_most_significant_bit
  given: {n : Nat} (h : n != 0)
  proof: by
  induction n using Nat.binaryRec with | zero => exact False.elim (h rfl) | bit b n hn => ?_
  by_cases h' : n = 0
  · subst h'
    rw [show b = true by
        revert h
        cases b <;> simp]
    refine ⟨0, ⟨by rw [testBit_bit_zero], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_

中文:
定理 存在_most_significant_bit
  条件: {n : 自然数} (h : n != 0)
  证明: by
  induction n using Nat.binaryRec with | zero => exact False.elim (h rfl) | bit b n hn => ?_
  by_cases h' : n = 0
  · subst h'
    rw [show b = true by
        revert h
        cases b <;> simp]
    refine ⟨0, ⟨by rw [testBit_bit_zero], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_

Depends on / 依赖: False.elim, Nat.binaryRec, binaryRec, exists_eq_succ_of_ne_zero, ne_of_gt, revert, testBit_bit_succ, testBit_bit_zero, zero_testBit
-/
theorem exists_most_significant_bit {n : Nat} (h : n != 0) :
    exists i, testBit n i = true ∧ forall j, i < j -> testBit n j = false := by
  induction n using Nat.binaryRec with | zero => exact False.elim (h rfl) | bit b n hn => ?_
  by_cases h' : n = 0
  · subst h'
    rw [show b = true by
        revert h
        cases b <;> simp]
    refine ⟨0, ⟨by rw [testBit_bit_zero], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [testBit_bit_succ]; rw [zero_testBit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine ⟨k + 1, ⟨by rw [testBit_bit_succ, hk], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j != 0 by intro x; subst x; simp at hj)
    exact (testBit_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))

/--
theorem `lt_of_testBit` / 定理 `lt_of_testBit`

English:
theorem lt_of_testBit
  statement: {n m : Nat} (i : Nat) (hn : testBit n i = false) (hm : testBit m i = true)
  proof: by
  induction n using Nat.binaryRec generalizing i m with
  | zero =>
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp at hm
  | bit b n hn' =>
    induction m using Nat.binaryRec generalizing i with
    | zero => exact False.elim (Bool.false_ne_true ((zero_testBit i).symm.trans hm))
    | bit 

中文:
定理 lt_of_testBit
  结论: {n m : 自然数} (i : 自然数) (hn : testBit n i = false) (hm : testBit m i = true)
  证明: by
  induction n using Nat.binaryRec generalizing i m with
  | zero =>
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp at hm
  | bit b n hn' =>
    induction m using Nat.binaryRec generalizing i with
    | zero => exact False.elim (Bool.false_ne_true ((zero_testBit i).symm.trans hm))
    | bit 

Depends on / 依赖: Bool.false_ne_true, False.elim, Nat.binaryRec, Nat.pos_iff_ne_zero, Nat.zero_lt_succ, binaryRec, convert, eq_of_testBit_eq, false_ne_true, generalizing, pos_iff_ne_zero, symm.trans, testBit_bit_succ, testBit_bit_zero, zero_lt_succ, zero_testBit
-/
theorem lt_of_testBit {n m : Nat} (i : Nat) (hn : testBit n i = false) (hm : testBit m i = true)
    (hnm : forall j, i < j -> testBit n j = testBit m j) : n < m := by
  induction n using Nat.binaryRec generalizing i m with
  | zero =>
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp at hm
  | bit b n hn' =>
    induction m using Nat.binaryRec generalizing i with
    | zero => exact False.elim (Bool.false_ne_true ((zero_testBit i).symm.trans hm))
    | bit b' m hm' =>
      by_cases hi : i = 0
      · subst hi
        simp only [testBit_bit_zero] at hn hm
        have : n = m :=
          eq_of_testBit_eq fun i => by convert! hnm (i + 1) (Nat.zero_lt_succ _) using 1
          <;> rw [testBit_bit_succ]
        rw [hn]; rw [hm]; rw [this]; rw [bit_false]; rw [bit_true]
        exact Nat.lt_succ_self _
      · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
        simp only [testBit_bit_succ] at hn hm
        have := hn' _ hn hm fun j hj => by
          convert! hnm j.succ (succ_lt_succ hj) using 1 <;> rw [testBit_bit_succ]
        exact bit_lt_bit b b' this

/--
theorem `bitwise_swap` / 定理 `bitwise_swap`

English:
theorem bitwise_swap
  given: {f : Bool -> Bool -> Bool}
  proof: by
  funext m n
  simp only [Function.swap]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp
  | bit bm m hm ihm =>
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit bn n hn => rw [bitwise_bit' _ _ _ _ hm hn, bitwise_bit' _ _ _ _ hn hm, ihm]

中文:
定理 bitwise_swap
  条件: {f : 布尔值 -> 布尔值 -> 布尔值}
  证明: by
  funext m n
  simp only [Function.swap]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp
  | bit bm m hm ihm =>
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit bn n hn => rw [bitwise_bit' _ _ _ _ hm hn, bitwise_bit' _ _ _ _ hn hm, ihm]

Depends on / 依赖: Function, Function.swap, Nat.binaryRec, binaryRec, bitwise_bit, generalizing
-/
theorem bitwise_swap {f : Bool -> Bool -> Bool} :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n
  simp only [Function.swap]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp
  | bit bm m hm ihm =>
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit bn n hn => rw [bitwise_bit' _ _ _ _ hm hn, bitwise_bit' _ _ _ _ hn hm, ihm]

/--
theorem `bitwise_comm` / 定理 `bitwise_comm`

English:
theorem bitwise_comm
  given: {f : Bool -> Bool -> Bool} (hf : forall b b', f b b' = f b' b) (n m : Nat)
  proof: suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
bitwise f = bitwise (swap f) := congr_arg _ funext fun _ => funext hf _
    _ = swap (bitwise f) := bitwise_swap

中文:
定理 bitwise_comm
  条件: {f : 布尔值 -> 布尔值 -> 布尔值} (hf : 对任意 b b', f b b' = f b' b) (n m : 自然数)
  证明: suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
bitwise f = bitwise (swap f) := congr_arg _ funext fun _ => funext hf _
    _ = swap (bitwise f) := bitwise_swap

Depends on / 依赖: bitwise, bitwise_swap, congr_arg, conv_lhs
-/
theorem bitwise_comm {f : Bool -> Bool -> Bool} (hf : forall b b', f b b' = f b' b) (n m : Nat) :
    bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
bitwise f = bitwise (swap f) := congr_arg _ funext fun _ => funext hf _
    _ = swap (bitwise f) := bitwise_swap

/--
theorem `lor_comm` / 定理 `lor_comm`

English:
theorem lor_comm
  given: (n m : Nat)
  statement: n ||| m = m ||| n
  proof: bitwise_comm Bool.or_comm n m

中文:
定理 lor_comm
  条件: (n m : 自然数)
  结论: n ||| m = m ||| n
  证明: bitwise_comm Bool.or_comm n m

Depends on / 依赖: Bool.or_comm, bitwise_comm, or_comm
-/
theorem lor_comm (n m : Nat) : n ||| m = m ||| n :=
  bitwise_comm Bool.or_comm n m

/--
theorem `land_comm` / 定理 `land_comm`

English:
theorem land_comm
  given: (n m : Nat)
  statement: n &&& m = m &&& n
  proof: bitwise_comm Bool.and_comm n m

中文:
定理 land_comm
  条件: (n m : 自然数)
  结论: n &&& m = m &&& n
  证明: bitwise_comm Bool.and_comm n m

Depends on / 依赖: Bool.and_comm, and_comm, bitwise_comm
-/
theorem land_comm (n m : Nat) : n &&& m = m &&& n :=
  bitwise_comm Bool.and_comm n m

/--
lemma `and_two_pow` / 引理 `and_two_pow`

English:
lemma and_two_pow
  given: (n i : Nat)
  statement: n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i
  proof: by
  refine eq_of_testBit_eq fun j => ?_
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [testBit_two_pow_of_ne hij]
  · simp [testBit_two_pow_of_ne hij]

中文:
引理 and_two_pow
  条件: (n i : 自然数)
  结论: n &&& 2 ^ i = (n.testBit i).to自然数 * 2 ^ i
  证明: by
  refine eq_of_testBit_eq fun j => ?_
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [testBit_two_pow_of_ne hij]
  · simp [testBit_two_pow_of_ne hij]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, eq_of_testBit_eq, eq_or_ne, n.testBit, testBit, testBit_two_pow_of_ne
-/
lemma and_two_pow (n i : Nat) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i := by
  refine eq_of_testBit_eq fun j => ?_
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [testBit_two_pow_of_ne hij]
  · simp [testBit_two_pow_of_ne hij]

/--
lemma `two_pow_and` / 引理 `two_pow_and`

English:
lemma two_pow_and
  given: (n i : Nat)
  statement: 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat
  proof: by
  rw [mul_comm]; rw [land_comm]; rw [and_two_pow]

中文:
引理 two_pow_and
  条件: (n i : 自然数)
  结论: 2 ^ i &&& n = 2 ^ i * (n.testBit i).to自然数
  证明: by
  rw [mul_comm]; rw [land_comm]; rw [and_two_pow]

Depends on / 依赖: and_two_pow, land_comm, mul_comm
-/
lemma two_pow_and (n i : Nat) : 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat := by
  rw [mul_comm]; rw [land_comm]; rw [and_two_pow]

/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
macro "bitwise_assoc_tac" : tactic => set_option hygiene false in `(tactic| (
  induction n using Nat.binaryRec generalizing m k with | zero => simp | bit b n hn => ?_
  induction m using Nat.binaryRec with | zero => simp | bit b' m hm => ?_
  induction k using Nat.binaryRec <;>
    simp [hn, Bool.or_assoc, Bool.and_assoc, Bool.bne_eq_xor]))

/--
theorem `land_assoc` / 定理 `land_assoc`

English:
theorem land_assoc
  given: (n m k : Nat)
  statement: (n &&& m) &&& k = n &&& (m &&& k)
  proof: by bitwise_assoc_tac

中文:
定理 land_assoc
  条件: (n m k : 自然数)
  结论: (n &&& m) &&& k = n &&& (m &&& k)
  证明: by bitwise_assoc_tac

Depends on / 依赖: bitwise_assoc_tac
-/
theorem land_assoc (n m k : Nat) : (n &&& m) &&& k = n &&& (m &&& k) := by bitwise_assoc_tac

/--
theorem `lor_assoc` / 定理 `lor_assoc`

English:
theorem lor_assoc
  given: (n m k : Nat)
  statement: (n ||| m) ||| k = n ||| (m ||| k)
  proof: by bitwise_assoc_tac

中文:
定理 lor_assoc
  条件: (n m k : 自然数)
  结论: (n ||| m) ||| k = n ||| (m ||| k)
  证明: by bitwise_assoc_tac

Depends on / 依赖: bitwise_assoc_tac
-/
theorem lor_assoc (n m k : Nat) : (n ||| m) ||| k = n ||| (m ||| k) := by bitwise_assoc_tac

/--
theorem `xor_trichotomy` / 定理 `xor_trichotomy`

English:
theorem xor_trichotomy
  given: {a b c : Nat} (h : a ^^^ b ^^^ c != 0)
  proof: by
  set v := a ^^^ b ^^^ c with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : a ^^^ b = c ^^^ v := by
    rw [Nat.xor_comm c]; rw [Nat.xor_xor_cancel_right]
  have hbc : b ^^^ c = a ^^^ v := by
    rw [← Nat.xor_assoc]; rw [Nat.xor_xor_cancel_left]
  have

中文:
定理 xor_trichotomy
  条件: {a b c : 自然数} (h : a ^^^ b ^^^ c != 0)
  证明: by
  set v := a ^^^ b ^^^ c with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : a ^^^ b = c ^^^ v := by
    rw [Nat.xor_comm c]; rw [Nat.xor_xor_cancel_right]
  have hbc : b ^^^ c = a ^^^ v := by
    rw [← Nat.xor_assoc]; rw [Nat.xor_xor_cancel_left]
  have
-/
theorem xor_trichotomy {a b c : Nat} (h : a ^^^ b ^^^ c != 0) :
    b ^^^ c < a ∨ c ^^^ a < b ∨ a ^^^ b < c := by
  set v := a ^^^ b ^^^ c with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : a ^^^ b = c ^^^ v := by
    rw [Nat.xor_comm c]; rw [Nat.xor_xor_cancel_right]
  have hbc : b ^^^ c = a ^^^ v := by
    rw [← Nat.xor_assoc]; rw [Nat.xor_xor_cancel_left]
  have hca : c ^^^ a = b ^^^ v := by
    rw [hv]; rw [Nat.xor_assoc]; rw [Nat.xor_comm a]; rw [← Nat.xor_assoc]; rw [Nat.xor_xor_cancel_left]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit h
  have : testBit a i ∨ testBit b i ∨ testBit c i := by
    contrapose! hi
    simp_rw [Bool.eq_false_eq_not_eq_true] at hi ⊢
    rw [testBit_xor]; rw [testBit_xor]; rw [hi.1]; rw [hi.2.1]; rw [hi.2.2]
    rfl
  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
  -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
  obtain h | h | h := this
  on_goal 1 => left; rw [hbc]
  on_goal 2 => right; left; rw [hca]
  on_goal 3 => right; right; rw [hab]
  all_goals
    refine lt_of_testBit i ?_ h fun j hj => ?_
    · rw [testBit_xor, h, hi]
      rfl
    · simp only [testBit_xor, hi' _ hj, Bool.bne_false]

/--
theorem `lt_xor_cases` / 定理 `lt_xor_cases`

English:
theorem lt_xor_cases
  given: {a b c : Nat} (h : a < b ^^^ c)
  statement: a ^^^ c < b ∨ a ^^^ b < c
  proof: by
obtain ha | hb | hc := xor_trichotomy Nat.xor_assoc _ _ _ ▸ xor_ne_zero_iff.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| Nat.xor_comm _ _ ▸ hb, Or.inr hc]

@[simp]

中文:
定理 lt_xor_cases
  条件: {a b c : 自然数} (h : a < b ^^^ c)
  结论: a ^^^ c < b ∨ a ^^^ b < c
  证明: by
obtain ha | hb | hc := xor_trichotomy Nat.xor_assoc _ _ _ ▸ xor_ne_zero_iff.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| Nat.xor_comm _ _ ▸ hb, Or.inr hc]

@[simp]

Depends on / 依赖: Nat.xor_assoc, Nat.xor_comm, Or.inl, Or.inr, exacts, h.asymm, h.ne, xor_assoc, xor_comm, xor_ne_zero_iff, xor_trichotomy
-/
theorem lt_xor_cases {a b c : Nat} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c := by
obtain ha | hb | hc := xor_trichotomy Nat.xor_assoc _ _ _ ▸ xor_ne_zero_iff.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| Nat.xor_comm _ _ ▸ hb, Or.inr hc]

@[simp]
/--
theorem `xor_mod_two_eq` / 定理 `xor_mod_two_eq`

English:
theorem xor_mod_two_eq
  given: {m n : Nat}
  statement: (m ^^^ n) % 2 = (m + n) % 2
  proof: by
  by_cases h : (m + n) % 2 = 0
  · simp only [h, mod_two_eq_zero_iff_testBit_zero, testBit_zero, xor_mod_two_eq_one, decide_not,
      Bool.decide_iff_dist, Bool.not_eq_false', beq_iff_eq, decide_eq_decide]
    lia
  · simp only [mod_two_ne_zero] at h
    simp only [h, xor_mod_two_eq_one]
    lia

中文:
定理 xor_mod_two_eq
  条件: {m n : 自然数}
  结论: (m ^^^ n) % 2 = (m + n) % 2
  证明: by
  by_cases h : (m + n) % 2 = 0
  · simp only [h, mod_two_eq_zero_iff_testBit_zero, testBit_zero, xor_mod_two_eq_one, decide_not,
      Bool.decide_iff_dist, Bool.not_eq_false', beq_iff_eq, decide_eq_decide]
    lia
  · simp only [mod_two_ne_zero] at h
    simp only [h, xor_mod_two_eq_one]
    lia

Depends on / 依赖: Bool.decide_iff_dist, Bool.not_eq_false, beq_iff_eq, decide_eq_decide, decide_iff_dist, decide_not, mod_two_eq_zero_iff_testBit_zero, mod_two_ne_zero, not_eq_false, testBit_zero, xor_mod_two_eq_one
-/
theorem xor_mod_two_eq {m n : Nat} : (m ^^^ n) % 2 = (m + n) % 2 := by
  by_cases h : (m + n) % 2 = 0
  · simp only [h, mod_two_eq_zero_iff_testBit_zero, testBit_zero, xor_mod_two_eq_one, decide_not,
      Bool.decide_iff_dist, Bool.not_eq_false', beq_iff_eq, decide_eq_decide]
    lia
  · simp only [mod_two_ne_zero] at h
    simp only [h, xor_mod_two_eq_one]
    lia

@[simp]
/--
theorem `even_xor` / 定理 `even_xor`

English:
theorem even_xor
  given: {m n : Nat}
  statement: Even (m ^^^ n) ↔ (Even m ↔ Even n)
  proof: by
  simp only [even_iff, xor_mod_two_eq]
  lia

@[simp]

中文:
定理 even_xor
  条件: {m n : 自然数}
  结论: Even (m ^^^ n) ↔ (Even m ↔ Even n)
  证明: by
  simp only [even_iff, xor_mod_two_eq]
  lia

@[simp]

Depends on / 依赖: even_iff, xor_mod_two_eq
-/
theorem even_xor {m n : Nat} : Even (m ^^^ n) ↔ (Even m ↔ Even n) := by
  simp only [even_iff, xor_mod_two_eq]
  lia

@[simp]
/--
theorem `xor_one_of_even` / 定理 `xor_one_of_even`

English:
theorem xor_one_of_even
  given: {n : Nat} (h : Even n)
  statement: n ^^^ 1 = n + 1
  proof: by
  cases n with
  | zero => rfl
  | succ n =>
    simp +instances [HXor.hXor, instXorOp, xor, bitwise, even_iff.mp h, ← mul_two,
      div_two_mul_two_of_even h]

@[simp]

中文:
定理 xor_one_of_even
  条件: {n : 自然数} (h : Even n)
  结论: n ^^^ 1 = n + 1
  证明: by
  cases n with
  | zero => rfl
  | succ n =>
    simp +instances [HXor.hXor, instXorOp, xor, bitwise, even_iff.mp h, ← mul_two,
      div_two_mul_two_of_even h]

@[simp]

Depends on / 依赖: HXor.hXor, bitwise, div_two_mul_two_of_even, even_iff, even_iff.mp, instXorOp, instances, mul_two
-/
theorem xor_one_of_even {n : Nat} (h : Even n) : n ^^^ 1 = n + 1 := by
  cases n with
  | zero => rfl
  | succ n =>
    simp +instances [HXor.hXor, instXorOp, xor, bitwise, even_iff.mp h, ← mul_two,
      div_two_mul_two_of_even h]

@[simp]
/--
theorem `xor_one_of_odd` / 定理 `xor_one_of_odd`

English:
theorem xor_one_of_odd
  given: {n : Nat} (h : Odd n)
  statement: n ^^^ 1 = n - 1
  proof: by
  cases n with
  | zero =>
.elim exact not_odd_zero h
  | succ n =>
    simp +instances only [HXor.hXor, instXorOp, xor, bitwise, reduceDiv, bitwise_zero_right]
    grind

中文:
定理 xor_one_of_odd
  条件: {n : 自然数} (h : Odd n)
  结论: n ^^^ 1 = n - 1
  证明: by
  cases n with
  | zero =>
.elim exact not_odd_zero h
  | succ n =>
    simp +instances only [HXor.hXor, instXorOp, xor, bitwise, reduceDiv, bitwise_zero_right]
    grind

Depends on / 依赖: HXor.hXor, bitwise, bitwise_zero_right, instXorOp, instances, not_odd_zero, reduceDiv
-/
theorem xor_one_of_odd {n : Nat} (h : Odd n) : n ^^^ 1 = n - 1 := by
  cases n with
  | zero =>
.elim exact not_odd_zero h
  | succ n =>
    simp +instances only [HXor.hXor, instXorOp, xor, bitwise, reduceDiv, bitwise_zero_right]
    grind

/--
theorem `xor_range` / 定理 `xor_range`

English:
theorem xor_range
  given: (n : Nat)
  statement: (List.range (n + 1)).foldl (· ^^^ ·) 0 =
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 3 [← show Fin.ofNat 4 1 = (1 : Nat) from Fin.val_ofNat ..]
    rw [List.range_succ]; rw [List.foldl_append]; rw [ih]; rw [← Fin.ofNat_add]; rw [List.foldl_cons]; rw [List.foldl_nil]
    match h : Fin.ofNat 4 n with
    | 0 =>
      r

中文:
定理 xor_range
  条件: (n : 自然数)
  结论: (列表.range (n + 1)).foldl (· ^^^ ·) 0 =
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 3 [← show Fin.ofNat 4 1 = (1 : Nat) from Fin.val_ofNat ..]
    rw [List.range_succ]; rw [List.foldl_append]; rw [ih]; rw [← Fin.ofNat_add]; rw [List.foldl_cons]; rw [List.foldl_nil]
    match h : Fin.ofNat 4 n with
    | 0 =>
      r

Depends on / 依赖: Fin.ofNat, Fin.ofNat_add, Fin.val_ofNat, Fin.zero_add, List.foldl_append, List.foldl_cons, List.foldl_nil, List.range_succ, Nat.xor_comm, even_iff, even_iff.mpr, foldl_append, foldl_cons, foldl_nil, mod_mod_of_dvd, nth_rw, ofNat_add, range_succ, val_ofNat, xor_comm
-/
theorem xor_range (n : Nat) : (List.range (n + 1)).foldl (· ^^^ ·) 0 =
    match Fin.ofNat 4 n with | 0 => n | 1 => 1 | 2 => n + 1 | 3 => 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 3 [← show Fin.ofNat 4 1 = (1 : Nat) from Fin.val_ofNat ..]
    rw [List.range_succ]; rw [List.foldl_append]; rw [ih]; rw [← Fin.ofNat_add]; rw [List.foldl_cons]; rw [List.foldl_nil]
    match h : Fin.ofNat 4 n with
    | 0 =>
      rw [Fin.zero_add]; rw [← xor_one_of_even <| even_iff.mpr ?_]; rw [xor_xor_cancel_left]
      rw [← @mod_mod_of_dvd _ 4 _ <| by simp]; rw [← Fin.val_ofNat 4]; rw [h]
      rfl
    | 1 =>
      rw [Nat.xor_comm]
refine xor_one_of_even even_iff.mpr ?_
      rw [add_mod]; rw [← @mod_mod_of_dvd _ 4 n <| by simp]; rw [← Fin.val_ofNat 4]; rw [h]
      rfl
    | 2 =>
      apply Nat.xor_self
    | 3 =>
      apply zero_xor

/--
lemma `shiftLeft_lt` / 引理 `shiftLeft_lt`

English:
lemma shiftLeft_lt
  given: {x n m : Nat} (h : x < 2 ^ n)
  statement: x <<< m < 2 ^ (n + m)
  proof: by
  simp only [Nat.pow_add, shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]

中文:
引理 shiftLeft_lt
  条件: {x n m : 自然数} (h : x < 2 ^ n)
  结论: x <<< m < 2 ^ (n + m)
  证明: by
  simp only [Nat.pow_add, shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]

Depends on / 依赖: Nat.mul_lt_mul_right, Nat.pow_add, Nat.two_pow_pos, mul_lt_mul_right, pow_add, shiftLeft_eq, two_pow_pos
-/
lemma shiftLeft_lt {x n m : Nat} (h : x < 2 ^ n) : x <<< m < 2 ^ (n + m) := by
  simp only [Nat.pow_add, shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]

/--
lemma `append_lt` / 引理 `append_lt`

English:
lemma append_lt
  given: {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m)
  statement: y <<< n ||| x < 2 ^ (n + m)
  proof: by
  apply bitwise_lt_two_pow
  · rw [add_comm]; apply shiftLeft_lt hy
· apply lt_of_lt_of_le hx Nat.pow_le_pow_right (le_succ _) (le_add_right _ _)

中文:
引理 append_lt
  条件: {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m)
  结论: y <<< n ||| x < 2 ^ (n + m)
  证明: by
  apply bitwise_lt_two_pow
  · rw [add_comm]; apply shiftLeft_lt hy
· apply lt_of_lt_of_le hx Nat.pow_le_pow_right (le_succ _) (le_add_right _ _)

Depends on / 依赖: Nat.pow_le_pow_right, add_comm, bitwise_lt_two_pow, le_add_right, le_succ, lt_of_lt_of_le, pow_le_pow_right, shiftLeft_lt
-/
lemma append_lt {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m) : y <<< n ||| x < 2 ^ (n + m) := by
  apply bitwise_lt_two_pow
  · rw [add_comm]; apply shiftLeft_lt hy
· apply lt_of_lt_of_le hx Nat.pow_le_pow_right (le_succ _) (le_add_right _ _)

end Nat
