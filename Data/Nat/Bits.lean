/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Data.List.Defs

/-!
# Additional properties of binary recursion on `Nat`

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `Nat.bits` and `Nat.size`.

See also: `Nat.bitwise`, `Nat.pow` (for various lemmas about `size` and `shiftLeft`/`shiftRight`),
and `Nat.digits`.
-/

@[expose] public section

assert_not_exists Monoid

-- Once we're in the `Nat` namespace, `xor` will inconveniently resolve to `Nat.xor`.
/-- `bxor` denotes the `xor` function i.e. the exclusive-or function on type `Bool`. -/
local notation "bxor" => xor

namespace Nat
universe u
variable {m n : Nat}

/-- `boddDiv2 n` returns a 2-tuple of type `(Bool, Nat)` where the `Bool` value indicates whether
`n` is odd or not and the `Nat` value returns `⌊n/2⌋` -/
@[deprecated "use `Nat.bodd` and `Nat.div2` instead" (since := "2026-03-22")]
/--
Definition of `boddDiv2` / `boddDiv2` 的定义

English:
definition boddDiv2
  signature: : Nat -> Bool × Nat

中文:
定义 boddDiv2
  签名: : 自然数 -> 布尔值 × 自然数
-/
def boddDiv2 : Nat -> Bool × Nat
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)

/--
Definition of `div2` / `div2` 的定义

English:
definition div2
  signature: (n : Nat)
  body: n / 2

中文:
定义 div2
  签名: (n : 自然数)
  定义体: n / 2
-/
@[inline, grind =] def div2 (n : Nat) : Nat := n / 2

/--
theorem `div2_val` / 定理 `div2_val`

English:
theorem div2_val
  given: (n : Nat)
  statement: div2 n = n / 2
  proof: rfl

中文:
定理 div2_val
  条件: (n : 自然数)
  结论: div2 n = n / 2
  证明: rfl
-/
theorem div2_val (n : Nat) : div2 n = n / 2 := rfl

/--
Definition of `bodd` / `bodd` 的定义

English:
definition bodd
  signature: (n : Nat)
  body: n.testBit 0

中文:
定义 bodd
  签名: (n : 自然数)
  定义体: n.testBit 0
-/
@[inline] def bodd (n : Nat) : Bool := n.testBit 0

/--
lemma `bodd_zero` / 引理 `bodd_zero`

English:
lemma bodd_zero
  statement: bodd 0 = false
  proof: rfl

中文:
引理 bodd_zero
  结论: bodd 0 = false
  证明: rfl
-/
@[simp] lemma bodd_zero : bodd 0 = false := rfl

/--
lemma `bodd_one` / 引理 `bodd_one`

English:
lemma bodd_one
  statement: bodd 1 = true
  proof: rfl

中文:
引理 bodd_one
  结论: bodd 1 = true
  证明: rfl
-/
@[simp] lemma bodd_one : bodd 1 = true := rfl

/--
lemma `bodd_two` / 引理 `bodd_two`

English:
lemma bodd_two
  statement: bodd 2 = false
  proof: rfl

@[simp]

中文:
引理 bodd_two
  结论: bodd 2 = false
  证明: rfl

@[simp]
-/
lemma bodd_two : bodd 2 = false := rfl

@[simp]
/--
lemma `bodd_succ` / 引理 `bodd_succ`

English:
lemma bodd_succ
  given: (n : Nat)
  statement: bodd (succ n) = not (bodd n)
  proof: by
  simp only [bodd]
  cases mod_two_eq_zero_or_one n with | _ h => simp [h, add_mod]

@[simp]

中文:
引理 bodd_succ
  条件: (n : 自然数)
  结论: bodd (succ n) = not (bodd n)
  证明: by
  simp only [bodd]
  cases mod_two_eq_zero_or_one n with | _ h => simp [h, add_mod]

@[simp]

Depends on / 依赖: add_mod, mod_two_eq_zero_or_one
-/
lemma bodd_succ (n : Nat) : bodd (succ n) = not (bodd n) := by
  simp only [bodd]
  cases mod_two_eq_zero_or_one n with | _ h => simp [h, add_mod]

@[simp]
/--
lemma `bodd_add` / 引理 `bodd_add`

English:
lemma bodd_add
  given: (m n : Nat)
  statement: bodd (m + n) = bxor (bodd m) (bodd n)
  proof: by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, ih]

@[simp]

中文:
引理 bodd_add
  条件: (m n : 自然数)
  结论: bodd (m + n) = bxor (bodd m) (bodd n)
  证明: by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, ih]

@[simp]

Depends on / 依赖: Nat.add_assoc, add_assoc
-/
lemma bodd_add (m n : Nat) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, ih]

@[simp]
/--
lemma `bodd_mul` / 引理 `bodd_mul`

English:
lemma bodd_mul
  given: (m n : Nat)
  statement: bodd (m * n) = (bodd m && bodd n)
  proof: by
  induction n with
  | zero => simp
  | succ n IH =>
    simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl

@[simp, grind =]

中文:
引理 bodd_mul
  条件: (m n : 自然数)
  结论: bodd (m * n) = (bodd m && bodd n)
  证明: by
  induction n with
  | zero => simp
  | succ n IH =>
    simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl

@[simp, grind =]

Depends on / 依赖: bodd_add, bodd_succ, mul_succ
-/
lemma bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n) := by
  induction n with
  | zero => simp
  | succ n IH =>
    simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl

@[simp, grind =]
/--
lemma `bodd_bit` / 引理 `bodd_bit`

English:
lemma bodd_bit
  given: (b n)
  statement: bodd (bit b n) = b
  proof: by
  cases b <;> simp [bodd]

中文:
引理 bodd_bit
  条件: (b n)
  结论: bodd (bit b n) = b
  证明: by
  cases b <;> simp [bodd]
-/
lemma bodd_bit (b n) : bodd (bit b n) = b := by
  cases b <;> simp [bodd]

/--
lemma `mod_two_of_bodd` / 引理 `mod_two_of_bodd`

English:
lemma mod_two_of_bodd
  given: (n : Nat)
  statement: n % 2 = (bodd n).toNat
  proof: by
  cases n using bitCasesOn with
  | bit b n => cases b <;> simp

中文:
引理 mod_two_of_bodd
  条件: (n : 自然数)
  结论: n % 2 = (bodd n).to自然数
  证明: by
  cases n using bitCasesOn with
  | bit b n => cases b <;> simp

Depends on / 依赖: bitCasesOn
-/
lemma mod_two_of_bodd (n : Nat) : n % 2 = (bodd n).toNat := by
  cases n using bitCasesOn with
  | bit b n => cases b <;> simp

/--
lemma `div2_zero` / 引理 `div2_zero`

English:
lemma div2_zero
  statement: div2 0 = 0
  proof: rfl

中文:
引理 div2_zero
  结论: div2 0 = 0
  证明: rfl
-/
@[simp] lemma div2_zero : div2 0 = 0 := rfl

/--
lemma `div2_one` / 引理 `div2_one`

English:
lemma div2_one
  statement: div2 1 = 0
  proof: rfl

中文:
引理 div2_one
  结论: div2 1 = 0
  证明: rfl
-/
@[simp] lemma div2_one : div2 1 = 0 := rfl

/--
lemma `div2_two` / 引理 `div2_two`

English:
lemma div2_two
  statement: div2 2 = 1
  proof: rfl

@[simp]

中文:
引理 div2_two
  结论: div2 2 = 1
  证明: rfl

@[simp]
-/
lemma div2_two : div2 2 = 1 := rfl

@[simp]
/--
lemma `div2_succ` / 引理 `div2_succ`

English:
lemma div2_succ
  given: (n : Nat)
  statement: div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n)
  proof: by
  cases n using bitCasesOn with
  | bit b n => cases b <;>
    simp [bit_val, div2_val, Nat.succ_div, Nat.add_assoc, Nat.dvd_add_right (Nat.dvd_mul_right _ _)]

@[simp, grind =]

中文:
引理 div2_succ
  条件: (n : 自然数)
  结论: div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n)
  证明: by
  cases n using bitCasesOn with
  | bit b n => cases b <;>
    simp [bit_val, div2_val, Nat.succ_div, Nat.add_assoc, Nat.dvd_add_right (Nat.dvd_mul_right _ _)]

@[simp, grind =]

Depends on / 依赖: Nat.add_assoc, Nat.dvd_add_right, Nat.dvd_mul_right, Nat.succ_div, add_assoc, bitCasesOn, bit_val, div2_val, dvd_add_right, dvd_mul_right, succ_div
-/
lemma div2_succ (n : Nat) : div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  cases n using bitCasesOn with
  | bit b n => cases b <;>
    simp [bit_val, div2_val, Nat.succ_div, Nat.add_assoc, Nat.dvd_add_right (Nat.dvd_mul_right _ _)]

@[simp, grind =]
/--
lemma `div2_bit` / 引理 `div2_bit`

English:
lemma div2_bit
  given: (b n)
  statement: div2 (bit b n) = n
  proof: by
  rw [div2_val]; rw [bit_div_two]

中文:
引理 div2_bit
  条件: (b n)
  结论: div2 (bit b n) = n
  证明: by
  rw [div2_val]; rw [bit_div_two]

Depends on / 依赖: bit_div_two, div2_val
-/
lemma div2_bit (b n) : div2 (bit b n) = n := by
  rw [div2_val]; rw [bit_div_two]

attribute [local simp] Nat.add_comm Nat.mul_comm

/--
lemma `bodd_add_div2` / 引理 `bodd_add_div2`

English:
lemma bodd_add_div2
  given: (n : Nat)
  statement: (bodd n).toNat + 2 * div2 n = n
  proof: by
  cases n using bitCasesOn with
  | bit b n => simpa using (bit_val b n).symm

@[simp, grind =]

中文:
引理 bodd_add_div2
  条件: (n : 自然数)
  结论: (bodd n).to自然数 + 2 * div2 n = n
  证明: by
  cases n using bitCasesOn with
  | bit b n => simpa using (bit_val b n).symm

@[simp, grind =]

Depends on / 依赖: bitCasesOn, bit_val
-/
lemma bodd_add_div2 (n : Nat) : (bodd n).toNat + 2 * div2 n = n := by
  cases n using bitCasesOn with
  | bit b n => simpa using (bit_val b n).symm

@[simp, grind =]
/--
lemma `bit_bodd_div2` / 引理 `bit_bodd_div2`

English:
lemma bit_bodd_div2
  given: (n : Nat)
  statement: bit (bodd n) (div2 n) = n
  proof: (bit_val _ _).trans (Nat.add_comm _ _).trans bodd_add_div2 _

中文:
引理 bit_bodd_div2
  条件: (n : 自然数)
  结论: bit (bodd n) (div2 n) = n
  证明: (bit_val _ _).trans (Nat.add_comm _ _).trans bodd_add_div2 _

Depends on / 依赖: Nat.add_comm, add_comm, bit_val, bodd_add_div2
-/
lemma bit_bodd_div2 (n : Nat) : bit (bodd n) (div2 n) = n :=
(bit_val _ _).trans (Nat.add_comm _ _).trans bodd_add_div2 _

/--
lemma `bit_false_zero` / 引理 `bit_false_zero`

English:
lemma bit_false_zero
  statement: bit false 0 = 0
  proof: rfl

中文:
引理 bit_false_zero
  结论: bit false 0 = 0
  证明: rfl
-/
lemma bit_false_zero : bit false 0 = 0 :=
  rfl

/--
Definition of `shiftLeft'` / `shiftLeft'` 的定义

English:
definition shiftLeft'
  signature: (b : Bool) (m : Nat)

中文:
定义 shiftLeft'
  签名: (b : 布尔值) (m : 自然数)
-/
def shiftLeft' (b : Bool) (m : Nat) : Nat -> Nat
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)

@[simp]
/--
lemma `shiftLeft'_false` / 引理 `shiftLeft'_false`

English:
lemma shiftLeft'_false
  statement: forall n, shiftLeft' false m n = m <<< n
  proof: by
      rw [Nat.mul_comm]; rw [Nat.mul_assoc]; rw [← Nat.pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]

中文:
引理 shiftLeft'_false
  结论: 对任意 n, shiftLeft' false m n = m <<< n
  证明: by
      rw [Nat.mul_comm]; rw [Nat.mul_assoc]; rw [← Nat.pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]

Depends on / 依赖: Nat.mul_assoc, Nat.mul_comm, Nat.pow_succ, _false, bit_val, mul_assoc, mul_comm, pow_succ, shiftLeft, shiftLeft_eq
-/
lemma shiftLeft'_false : forall n, shiftLeft' false m n = m <<< n
  | 0 => rfl
  | n + 1 => by
    have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m := by
      rw [Nat.mul_comm]; rw [Nat.mul_assoc]; rw [← Nat.pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]

/--
lemma `shiftRight_eq` / 引理 `shiftRight_eq`

English:
lemma shiftRight_eq
  given: (m n : Nat)
  statement: shiftRight m n = m >>> n
  proof: rfl

中文:
引理 shiftRight_eq
  条件: (m n : 自然数)
  结论: shiftRight m n = m >>> n
  证明: rfl
-/
@[simp] lemma shiftRight_eq (m n : Nat) : shiftRight m n = m >>> n := rfl

/--
lemma `binaryRec_decreasing` / 引理 `binaryRec_decreasing`

English:
lemma binaryRec_decreasing
  given: (h : n != 0)
  statement: div2 n < n
  proof: by grind

中文:
引理 binaryRec_decreasing
  条件: (h : n != 0)
  结论: div2 n < n
  证明: by grind
-/
lemma binaryRec_decreasing (h : n != 0) : div2 n < n := by grind

/--
Definition of `size` / `size` 的定义

English:
definition size
  signature: : Nat -> Nat
  body: binaryRec 0 fun _ _ => succ

中文:
定义 size
  签名: : 自然数 -> 自然数
  定义体: binaryRec 0 fun _ _ => succ

Depends on / 依赖: binaryRec
-/
def size : Nat -> Nat :=
  binaryRec 0 fun _ _ => succ

/--
Definition of `bits` / `bits` 的定义

English:
definition bits
  signature: : Nat -> List Bool
  body: binaryRec [] fun b _ IH => b :: IH

中文:
定义 bits
  签名: : 自然数 -> 列表 布尔值
  定义体: binaryRec [] fun b _ IH => b :: IH

Depends on / 依赖: binaryRec
-/
def bits : Nat -> List Bool :=
  binaryRec [] fun b _ IH => b :: IH

/--
Definition of `ldiff` / `ldiff` 的定义

English:
definition ldiff
  signature: : Nat -> Nat -> Nat
  body: bitwise fun a b => a && not b

中文:
定义 ldiff
  签名: : 自然数 -> 自然数 -> 自然数
  定义体: bitwise fun a b => a && not b

Depends on / 依赖: bitwise
-/
def ldiff : Nat -> Nat -> Nat :=
  bitwise fun a b => a && not b


/--
lemma `shiftLeft'_add` / 引理 `shiftLeft'_add`

English:
lemma shiftLeft'_add
  given: (b m n)
  statement: forall k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k

中文:
引理 shiftLeft'_add
  条件: (b m n)
  结论: 对任意 k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
-/
lemma shiftLeft'_add (b m n) : forall k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftLeft'_add b m n k)

/--
lemma `shiftLeft'_sub` / 引理 `shiftLeft'_sub`

English:
lemma shiftLeft'_sub
  given: (b m)
  statement: forall {n k}, k <= n -> shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k

中文:
引理 shiftLeft'_sub
  条件: (b m)
  结论: 对任意 {n k}, k <= n -> shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
-/
lemma shiftLeft'_sub (b m) : forall {n k}, k <= n -> shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
  | _, 0, _ => rfl
  | n + 1, k + 1, h => by
    rw [succ_sub_succ_eq_sub]; rw [shiftLeft']; rw [Nat.add_comm]; rw [shiftRight_add]
    simp only [shiftLeft'_sub, Nat.le_of_succ_le_succ h, shiftRight_succ, shiftRight_zero]
    simp [← div2_val, div2_bit]

/--
lemma `shiftLeft_sub` / 引理 `shiftLeft_sub`

English:
lemma shiftLeft_sub
  statement: forall (m : Nat) {n k}, k <= n -> m <<< (n - k) = (m <<< n) >>> k
  proof: fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

中文:
引理 shiftLeft_sub
  结论: 对任意 (m : 自然数) {n k}, k <= n -> m <<< (n - k) = (m <<< n) >>> k
  证明: fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

Depends on / 依赖: _false, _sub, shiftLeft
-/
lemma shiftLeft_sub : forall (m : Nat) {n k}, k <= n -> m <<< (n - k) = (m <<< n) >>> k :=
  fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

/--
lemma `bodd_eq_one_and_ne_zero` / 引理 `bodd_eq_one_and_ne_zero`

English:
lemma bodd_eq_one_and_ne_zero
  statement: forall n, bodd n = (1 &&& n != 0)

中文:
引理 bodd_eq_one_and_ne_zero
  结论: 对任意 n, bodd n = (1 &&& n != 0)
-/
lemma bodd_eq_one_and_ne_zero : forall n, bodd n = (1 &&& n != 0)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simpa using bodd_eq_one_and_ne_zero n

/--
lemma `testBit_bit_succ` / 引理 `testBit_bit_succ`

English:
lemma testBit_bit_succ
  given: (m b n)
  statement: testBit (bit b n) (succ m) = testBit n m
  proof: by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add]; rw [Nat.add_comm] at this
  simp only [bodd_eq_one_and_ne_zero] at this
  exact this

中文:
引理 testBit_bit_succ
  条件: (m b n)
  结论: testBit (bit b n) (succ m) = testBit n m
  证明: by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add]; rw [Nat.add_comm] at this
  simp only [bodd_eq_one_and_ne_zero] at this
  exact this

Depends on / 依赖: Nat.add_comm, add_comm, bodd_eq_one_and_ne_zero, div2_bit, div2_val, shiftRight_add, shiftRight_eq_div_pow
-/
lemma testBit_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add]; rw [Nat.add_comm] at this
  simp only [bodd_eq_one_and_ne_zero] at this
  exact this

/-! ### `boddDiv2_eq` and `bodd` -/

@[deprecated "`Nat.boddDiv2` has been deprecated" (since := "2026-03-22")]
/--
theorem `boddDiv2_eq` / 定理 `boddDiv2_eq`

English:
theorem boddDiv2_eq
  given: (n : Nat)
  statement: boddDiv2 n = (bodd n, div2 n)
  proof: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boddDiv2]; rw [ih]
    cases hn : n.bodd <;> simp [hn]

@[simp]

中文:
定理 boddDiv2_eq
  条件: (n : 自然数)
  结论: boddDiv2 n = (bodd n, div2 n)
  证明: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boddDiv2]; rw [ih]
    cases hn : n.bodd <;> simp [hn]

@[simp]

Depends on / 依赖: boddDiv2, n.bodd
-/
theorem boddDiv2_eq (n : Nat) : boddDiv2 n = (bodd n, div2 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boddDiv2]; rw [ih]
    cases hn : n.bodd <;> simp [hn]

@[simp]
/--
theorem `div2_bit0` / 定理 `div2_bit0`

English:
theorem div2_bit0
  given: (n)
  statement: div2 (2 * n) = n
  proof: div2_bit false n

中文:
定理 div2_bit0
  条件: (n)
  结论: div2 (2 * n) = n
  证明: div2_bit false n

Depends on / 依赖: div2_bit
-/
theorem div2_bit0 (n) : div2 (2 * n) = n :=
  div2_bit false n

-- simp can prove this
/--
theorem `div2_bit1` / 定理 `div2_bit1`

English:
theorem div2_bit1
  given: (n)
  statement: div2 (2 * n + 1) = n
  proof: div2_bit true n

中文:
定理 div2_bit1
  条件: (n)
  结论: div2 (2 * n + 1) = n
  证明: div2_bit true n

Depends on / 依赖: div2_bit
-/
theorem div2_bit1 (n) : div2 (2 * n + 1) = n :=
  div2_bit true n


/--
theorem `bit_add` / 定理 `bit_add`

English:
theorem bit_add
  statement: forall (b : Bool) (n m : Nat), bit b (n + m) = bit false n + bit b m

中文:
定理 bit_add
  结论: 对任意 (b : 布尔值) (n m : 自然数), bit b (n + m) = bit false n + bit b m
-/
theorem bit_add : forall (b : Bool) (n m : Nat), bit b (n + m) = bit false n + bit b m
  | true, _, _ => by dsimp [bit]; lia
  | false, _, _ => by dsimp [bit]; lia

/--
theorem `bit_add'` / 定理 `bit_add'`

English:
theorem bit_add'
  statement: forall (b : Bool) (n m : Nat), bit b (n + m) = bit b n + bit false m

中文:
定理 bit_add'
  结论: 对任意 (b : 布尔值) (n m : 自然数), bit b (n + m) = bit b n + bit false m
-/
theorem bit_add' : forall (b : Bool) (n m : Nat), bit b (n + m) = bit b n + bit false m
  | true, _, _ => by dsimp [bit]; lia
  | false, _, _ => by dsimp [bit]; lia

/--
theorem `bit_ne_zero` / 定理 `bit_ne_zero`

English:
theorem bit_ne_zero
  given: (b) {n} (h : n != 0)
  statement: bit b n != 0
  proof: by
  cases b <;> dsimp [bit] <;> lia

@[simp]

中文:
定理 bit_ne_zero
  条件: (b) {n} (h : n != 0)
  结论: bit b n != 0
  证明: by
  cases b <;> dsimp [bit] <;> lia

@[simp]
-/
theorem bit_ne_zero (b) {n} (h : n != 0) : bit b n != 0 := by
  cases b <;> dsimp [bit] <;> lia

@[simp]
/--
theorem `bitCasesOn_bit0` / 定理 `bitCasesOn_bit0`

English:
theorem bitCasesOn_bit0
  given: {motive : Nat -> Sort u} (H : forall b n, motive (bit b n)) (n : Nat)
  proof: bitCasesOn_bit H false n

@[simp]

中文:
定理 bitCasesOn_bit0
  条件: {motive : 自然数 -> 类型层 u} (H : 对任意 b n, motive (bit b n)) (n : 自然数)
  证明: bitCasesOn_bit H false n

@[simp]

Depends on / 依赖: Finite, Finite.of_equiv, bitCasesOn_bit, n.quotientSpanEquivZMod.symm.toEquiv, of_equiv, quotientSpanEquivZMod, toEquiv
-/
theorem bitCasesOn_bit0 {motive : Nat -> Sort u} (H : forall b n, motive (bit b n)) (n : Nat) :
    bitCasesOn (2 * n) H = H false n :=
  bitCasesOn_bit H false n

@[simp]
/--
theorem `bitCasesOn_bit1` / 定理 `bitCasesOn_bit1`

English:
theorem bitCasesOn_bit1
  given: {motive : Nat -> Sort u} (H : forall b n, motive (bit b n)) (n : Nat)
  proof: bitCasesOn_bit H true n

中文:
定理 bitCasesOn_bit1
  条件: {motive : 自然数 -> 类型层 u} (H : 对任意 b n, motive (bit b n)) (n : 自然数)
  证明: bitCasesOn_bit H true n

Depends on / 依赖: bitCasesOn_bit
-/
theorem bitCasesOn_bit1 {motive : Nat -> Sort u} (H : forall b n, motive (bit b n)) (n : Nat) :
    bitCasesOn (2 * n + 1) H = H true n :=
  bitCasesOn_bit H true n

/--
theorem `bit_cases_on_injective` / 定理 `bit_cases_on_injective`

English:
theorem bit_cases_on_injective
  given: {motive : Nat -> Sort u}
  proof: by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)

@[simp]

中文:
定理 bit_cases_on_injective
  条件: {motive : 自然数 -> 类型层 u}
  证明: by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)

@[simp]

Depends on / 依赖: bitCasesOn_bit, congr_fun
-/
theorem bit_cases_on_injective {motive : Nat -> Sort u} :
    Function.Injective fun H : forall b n, motive (bit b n) => fun n => bitCasesOn n H := by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)

@[simp]
/--
theorem `bit_cases_on_inj` / 定理 `bit_cases_on_inj`

English:
theorem bit_cases_on_inj
  given: {motive : Nat -> Sort u} (H₁ H₂ : forall b n, motive (bit b n))
  proof: bit_cases_on_injective.eq_iff

中文:
定理 bit_cases_on_inj
  条件: {motive : 自然数 -> 类型层 u} (H₁ H₂ : 对任意 b n, motive (bit b n))
  证明: bit_cases_on_injective.eq_iff

Depends on / 依赖: bit_cases_on_injective, bit_cases_on_injective.eq_iff, eq_iff
-/
theorem bit_cases_on_inj {motive : Nat -> Sort u} (H₁ H₂ : forall b n, motive (bit b n)) :
    ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂ :=
  bit_cases_on_injective.eq_iff

/--
lemma `bit_le` / 引理 `bit_le`

English:
lemma bit_le
  statement: forall (b : Bool) {m n : Nat}, m <= n -> bit b m <= bit b n

中文:
引理 bit_le
  结论: 对任意 (b : 布尔值) {m n : 自然数}, m <= n -> bit b m <= bit b n
-/
lemma bit_le : forall (b : Bool) {m n : Nat}, m <= n -> bit b m <= bit b n
  | true, _, _, h => by dsimp [bit]; lia
  | false, _, _, h => by dsimp [bit]; lia

/--
lemma `bit_lt_bit` / 引理 `bit_lt_bit`

English:
lemma bit_lt_bit
  given: (a b) (h : m < n)
  statement: bit a m < bit b n
  proof: calc
  bit a m < 2 * n := by cases a <;> dsimp [bit] <;> lia
        _ <= bit b n := by cases b <;> dsimp [bit] <;> lia

@[simp]

中文:
引理 bit_lt_bit
  条件: (a b) (h : m < n)
  结论: bit a m < bit b n
  证明: calc
  bit a m < 2 * n := by cases a <;> dsimp [bit] <;> lia
        _ <= bit b n := by cases b <;> dsimp [bit] <;> lia

@[simp]
-/
lemma bit_lt_bit (a b) (h : m < n) : bit a m < bit b n := calc
  bit a m < 2 * n := by cases a <;> dsimp [bit] <;> lia
        _ <= bit b n := by cases b <;> dsimp [bit] <;> lia

@[simp]
/--
theorem `zero_bits` / 定理 `zero_bits`

English:
theorem zero_bits
  statement: bits 0 = []
  proof: by simp [Nat.bits]

@[simp]

中文:
定理 zero_bits
  结论: bits 0 = []
  证明: by simp [Nat.bits]

@[simp]

Depends on / 依赖: Nat.bits
-/
theorem zero_bits : bits 0 = [] := by simp [Nat.bits]

@[simp]
/--
theorem `bits_append_bit` / 定理 `bits_append_bit`

English:
theorem bits_append_bit
  given: (n : Nat) (b : Bool) (hn : n = 0 -> b = true)
  proof: by
  rw [Nat.bits]; rw [Nat.bits]; rw [binaryRec_eq]
  simpa

@[simp]

中文:
定理 bits_append_bit
  条件: (n : 自然数) (b : 布尔值) (hn : n = 0 -> b = true)
  证明: by
  rw [Nat.bits]; rw [Nat.bits]; rw [binaryRec_eq]
  simpa

@[simp]

Depends on / 依赖: Nat.bits, binaryRec_eq
-/
theorem bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 -> b = true) :
    (bit b n).bits = b :: n.bits := by
  rw [Nat.bits]; rw [Nat.bits]; rw [binaryRec_eq]
  simpa

@[simp]
/--
theorem `bit0_bits` / 定理 `bit0_bits`

English:
theorem bit0_bits
  given: (n : Nat) (hn : n != 0)
  statement: (2 * n).bits = false :: n.bits
  proof: bits_append_bit n false fun hn' => absurd hn' hn

@[simp]

中文:
定理 bit0_bits
  条件: (n : 自然数) (hn : n != 0)
  结论: (2 * n).bits = false :: n.bits
  证明: bits_append_bit n false fun hn' => absurd hn' hn

@[simp]

Depends on / 依赖: absurd, bits_append_bit
-/
theorem bit0_bits (n : Nat) (hn : n != 0) : (2 * n).bits = false :: n.bits :=
  bits_append_bit n false fun hn' => absurd hn' hn

@[simp]
/--
theorem `bit1_bits` / 定理 `bit1_bits`

English:
theorem bit1_bits
  given: (n : Nat)
  statement: (2 * n + 1).bits = true :: n.bits
  proof: bits_append_bit n true fun _ => rfl

@[simp]

中文:
定理 bit1_bits
  条件: (n : 自然数)
  结论: (2 * n + 1).bits = true :: n.bits
  证明: bits_append_bit n true fun _ => rfl

@[simp]

Depends on / 依赖: bits_append_bit
-/
theorem bit1_bits (n : Nat) : (2 * n + 1).bits = true :: n.bits :=
  bits_append_bit n true fun _ => rfl

@[simp]
/--
theorem `one_bits` / 定理 `one_bits`

English:
theorem one_bits
  statement: Nat.bits 1 = [true]
  proof: bit1_bits 0

中文:
定理 one_bits
  结论: 自然数.bits 1 = [true]
  证明: bit1_bits 0

Depends on / 依赖: bit1_bits
-/
theorem one_bits : Nat.bits 1 = [true] := bit1_bits 0

-- TODO Find somewhere this can live.
-- example : bits 3423 = [true, true, true, true, true, false, true, false, true, false, true, true]
-- := by norm_num

/--
theorem `bodd_eq_bits_head` / 定理 `bodd_eq_bits_head`

English:
theorem bodd_eq_bits_head
  given: (n : Nat)
  statement: n.bodd = n.bits.headI
  proof: by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [bodd_bit, bits_append_bit _ _ h]

中文:
定理 bodd_eq_bits_head
  条件: (n : 自然数)
  结论: n.bodd = n.bits.headI
  证明: by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [bodd_bit, bits_append_bit _ _ h]

Depends on / 依赖: Nat.binaryRec, binaryRec, bits_append_bit, bodd_bit
-/
theorem bodd_eq_bits_head (n : Nat) : n.bodd = n.bits.headI := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [bodd_bit, bits_append_bit _ _ h]

/--
theorem `div2_bits_eq_tail` / 定理 `div2_bits_eq_tail`

English:
theorem div2_bits_eq_tail
  given: (n : Nat)
  statement: n.div2.bits = n.bits.tail
  proof: by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [div2_bit, bits_append_bit _ _ h]

中文:
定理 div2_bits_eq_tail
  条件: (n : 自然数)
  结论: n.div2.bits = n.bits.tail
  证明: by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [div2_bit, bits_append_bit _ _ h]

Depends on / 依赖: Nat.binaryRec, binaryRec, bits_append_bit, div2_bit
-/
theorem div2_bits_eq_tail (n : Nat) : n.div2.bits = n.bits.tail := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [div2_bit, bits_append_bit _ _ h]

end Nat
