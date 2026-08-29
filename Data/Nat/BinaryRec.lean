/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Praneeth Kolichala, Yuyang Zhao
-/
module

public import Mathlib.Init

/-!
# Binary recursion on `Nat`

This file defines binary recursion on `Nat`.

## Main results
* `Nat.binaryRec`: A recursion principle for `bit` representations of natural numbers.
* `Nat.binaryRec'`: The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`.
* `Nat.binaryRecFromOne`: The same as `binaryRec`, but special casing both 0 and 1 as base cases.
-/

@[expose] public section

universe u

namespace Nat

/--
Definition of `bit` / `bit` 的定义

English:
definition bit
  signature: (b : Bool) (n : Nat)
  body: cond b (2 * n + 1) (2 * n)

中文:
定义 bit
  签名: (b : 布尔) (n : 自然数)
  定义体: cond b (2 * n + 1) (2 * n)
-/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (2 * n + 1) (2 * n)

/--
theorem `shiftRight_one` / 定理 `shiftRight_one`

English:
theorem shiftRight_one
  given: (n)
  statement: n >>> 1 = n / 2
  proof: rfl

@[simp]

中文:
定理 shiftRight_one
  条件: (n)
  结论: n >>> 1 = n / 2
  证明: rfl

@[simp]
-/
theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

@[simp]
/--
theorem `bit_decide_mod_two_eq_one_shiftRight_one` / 定理 `bit_decide_mod_two_eq_one_shiftRight_one`

English:
theorem bit_decide_mod_two_eq_one_shiftRight_one
  given: (n : Nat)
  statement: bit (n % 2 = 1) (n >>> 1) = n
  proof: by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2

中文:
定理 bit_decide_mod_two_eq_one_shiftRight_one
  条件: (n : 自然数)
  结论: bit (n % 2 = 1) (n >>> 1) = n
  证明: by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2

Depends on / 依赖: Nat.div_add_mod, div_add_mod, mod_two_eq_zero_or_one, shiftRight_one
-/
theorem bit_decide_mod_two_eq_one_shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>> 1) = n := by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2

/--
theorem `bit_testBit_zero_shiftRight_one` / 定理 `bit_testBit_zero_shiftRight_one`

English:
theorem bit_testBit_zero_shiftRight_one
  given: (n : Nat)
  statement: bit (n.testBit 0) (n >>> 1) = n
  proof: by
  simp

@[simp]

中文:
定理 bit_testBit_zero_shiftRight_one
  条件: (n : 自然数)
  结论: bit (n.testBit 0) (n >>> 1) = n
  证明: by
  simp

@[simp]
-/
theorem bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp

@[simp]
/--
theorem `bit_false` / 定理 `bit_false`

English:
theorem bit_false
  statement: bit false = (2 * ·)
  proof: rfl

@[simp]

中文:
定理 bit_false
  结论: bit false = (2 * ·)
  证明: rfl

@[simp]
-/
theorem bit_false : bit false = (2 * ·) :=
  rfl

@[simp]
/--
theorem `bit_true` / 定理 `bit_true`

English:
theorem bit_true
  statement: bit true = (2 * · + 1)
  proof: rfl

@[simp]

中文:
定理 bit_true
  结论: bit true = (2 * · + 1)
  证明: rfl

@[simp]
-/
theorem bit_true : bit true = (2 * · + 1) :=
  rfl

@[simp]
/--
theorem `bit_false_apply` / 定理 `bit_false_apply`

English:
theorem bit_false_apply
  given: (n)
  statement: bit false n = (2 * n)
  proof: rfl

@[simp]

中文:
定理 bit_false_apply
  条件: (n)
  结论: bit false n = (2 * n)
  证明: rfl

@[simp]
-/
theorem bit_false_apply (n) : bit false n = (2 * n) :=
  rfl

@[simp]
/--
theorem `bit_true_apply` / 定理 `bit_true_apply`

English:
theorem bit_true_apply
  given: (n)
  statement: bit true n = (2 * n + 1)
  proof: rfl

@[simp]

中文:
定理 bit_true_apply
  条件: (n)
  结论: bit true n = (2 * n + 1)
  证明: rfl

@[simp]
-/
theorem bit_true_apply (n) : bit true n = (2 * n + 1) :=
  rfl

@[simp]
/--
theorem `bit_eq_zero_iff` / 定理 `bit_eq_zero_iff`

English:
theorem bit_eq_zero_iff
  given: {n : Nat} {b : Bool}
  statement: bit b n = 0 ↔ n = 0 ∧ b = false
  proof: by
  cases n <;> cases b <;> simp [bit, Nat.two_mul, ← Nat.add_assoc]

中文:
定理 bit_eq_zero_iff
  条件: {n : 自然数} {b : 布尔}
  结论: bit b n = 0 ↔ n = 0 ∧ b = false
  证明: by
  cases n <;> cases b <;> simp [bit, Nat.two_mul, ← Nat.add_assoc]

Depends on / 依赖: Nat.add_assoc, Nat.two_mul, add_assoc, two_mul
-/
theorem bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  cases n <;> cases b <;> simp [bit, Nat.two_mul, ← Nat.add_assoc]

/--
theorem `bit_ne_zero_iff` / 定理 `bit_ne_zero_iff`

English:
theorem bit_ne_zero_iff
  given: {n : Nat} {b : Bool}
  statement: n.bit b != 0 ↔ n = 0 -> b = true
  proof: by
  simp

中文:
定理 bit_ne_zero_iff
  条件: {n : 自然数} {b : 布尔}
  结论: n.bit b != 0 ↔ n = 0 -> b = true
  证明: by
  simp
-/
theorem bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0 ↔ n = 0 -> b = true := by
  simp

/-- For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
/--
Definition of `bitCasesOn` / `bitCasesOn` 的定义

English:
definition bitCasesOn
  signature: {motive : Nat -> Sort u} (n) (bit : forall b n, motive (bit b n))
  body: -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := bit (1 &&& n != 0) (n >>> 1)
  -- `congrArg motive _ ▸ x` is defeq to `x` in non-dependent case
  congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x

中文:
定义 bitCasesOn
  签名: {motive : 自然数 -> Sort u} (n) (bit : 对任意 b n, motive (bit b n))
  定义体: -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := bit (1 &&& n != 0) (n >>> 1)
  -- `congrArg motive _ ▸ x` is defeq to `x` in non-dependent case
  congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
-/
def bitCasesOn {motive : Nat -> Sort u} (n) (bit : forall b n, motive (bit b n)) : motive n :=
  -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := bit (1 &&& n != 0) (n >>> 1)
  -- `congrArg motive _ ▸ x` is defeq to `x` in non-dependent case
  congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x

/--
theorem `bit_lt_two_pow_succ_iff` / 定理 `bit_lt_two_pow_succ_iff`

English:
theorem bit_lt_two_pow_succ_iff
  given: {b x n}
  statement: bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n
  proof: by
  cases b <;> simp <;> lia

中文:
定理 bit_lt_two_pow_succ_iff
  条件: {b x n}
  结论: bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n
  证明: by
  cases b <;> simp <;> lia
-/
@[simp] theorem bit_lt_two_pow_succ_iff {b x n} : bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n := by
  cases b <;> simp <;> lia

/--
theorem `log2_eq_succ_log2_shiftRight` / 定理 `log2_eq_succ_log2_shiftRight`

English:
theorem log2_eq_succ_log2_shiftRight
  given: {n : Nat} (hn : n >>> 1 != 0)
  statement: n.log2 = (n >>> 1).log2.succ
  proof: (log2_eq_iff (by rintro rfl; exact hn rfl)).mpr
    ⟨Nat.mul_le_of_le_div _ _ _ (log2_self_le hn), (div_lt_iff_lt_mul <| by decide).mp lt_log2_self⟩

中文:
定理 log2_eq_succ_log2_shiftRight
  条件: {n : 自然数} (hn : n >>> 1 != 0)
  结论: n.log2 = (n >>> 1).log2.succ
  证明: (log2_eq_iff (by rintro rfl; exact hn rfl)).mpr
    ⟨Nat.mul_le_of_le_div _ _ _ (log2_self_le hn), (div_lt_iff_lt_mul <| by decide).mp lt_log2_self⟩

Depends on / 依赖: Nat.mul_le_of_le_div, div_lt_iff_lt_mul, log2_eq_iff, log2_self_le, lt_log2_self, mul_le_of_le_div
-/
theorem log2_eq_succ_log2_shiftRight {n : Nat} (hn : n >>> 1 != 0) : n.log2 = (n >>> 1).log2.succ :=
  (log2_eq_iff (by rintro rfl; exact hn rfl)).mpr
    ⟨Nat.mul_le_of_le_div _ _ _ (log2_self_le hn), (div_lt_iff_lt_mul <| by decide).mp lt_log2_self⟩

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize, semireducible]
/--
Definition of `binaryRec` / `binaryRec` 的定义

English:
definition binaryRec
  signature: {motive : Nat -> Sort u} (zero : motive 0) (bit : forall b n, motive n -> motive (bit b n))
  body: if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let x := bit (1 &&& n != 0) (n >>> 1) (binaryRec zero bit (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
termination_by if n = 0 then 0 else n.log2.succ -- redundant, but removing causes slowdown
decreasing_by
  obtain _ |

中文:
定义 binaryRec
  签名: {motive : 自然数 -> Sort u} (zero : motive 0) (bit : 对任意 b n, motive n -> motive (bit b n))
  定义体: if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let x := bit (1 &&& n != 0) (n >>> 1) (binaryRec zero bit (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
termination_by if n = 0 then 0 else n.log2.succ -- redundant, but removing causes slowdown
decreasing_by
  obtain _ |

Depends on / 依赖: Nat.div_ne_zero_iff.mpr, binaryRec, bit_testBit_zero_shiftRight_one, causes, decreasing_by, div_ne_zero_iff, if_neg, le_add_left, log2_eq_succ_log2_shiftRight, motive, n.bit_testBit_zero_shiftRight_one, n.log2.succ, redundant, removing, slowdown, termination_by
-/
def binaryRec {motive : Nat -> Sort u} (zero : motive 0) (bit : forall b n, motive n -> motive (bit b n))
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let x := bit (1 &&& n != 0) (n >>> 1) (binaryRec zero bit (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
termination_by if n = 0 then 0 else n.log2.succ -- redundant, but removing causes slowdown
decreasing_by
  obtain _ | n := n; · exact (n0 rfl).elim
  obtain _ | n := n; · simp
  have : (n + 1 + 1) >>> 1 != 0 := Nat.div_ne_zero_iff.mpr ⟨by decide, le_add_left ..⟩
  simpa only [if_neg n0, if_neg this, log2_eq_succ_log2_shiftRight this] using lt_succ_self _

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true` -/
@[elab_as_elim, specialize]
/--
Definition of `binaryRec'` / `binaryRec'` 的定义

English:
definition binaryRec'
  signature: {motive : Nat -> Sort u} (zero : motive 0)
  body: binaryRec zero fun b n ih =>
    if h : n = 0 -> b = true then bit b n h ih
    else
      have : n.bit b = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h ⊢
      congrArg motive this ▸ zero

中文:
定义 binaryRec'
  签名: {motive : 自然数 -> Sort u} (zero : motive 0)
  定义体: binaryRec zero fun b n ih =>
    if h : n = 0 -> b = true then bit b n h ih
    else
      have : n.bit b = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h ⊢
      congrArg motive this ▸ zero

Depends on / 依赖: binaryRec, bit_eq_zero_iff, motive, n.bit
-/
def binaryRec' {motive : Nat -> Sort u} (zero : motive 0)
    (bit : forall b n, (n = 0 -> b = true) -> motive n -> motive (bit b n)) :
    forall n, motive n :=
  binaryRec zero fun b n ih =>
    if h : n = 0 -> b = true then bit b n h ih
    else
      have : n.bit b = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h ⊢
      congrArg motive this ▸ zero

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
/--
Definition of `binaryRecFromOne` / `binaryRecFromOne` 的定义

English:
definition binaryRecFromOne
  signature: {motive : Nat -> Sort u} (zero : motive 0) (one : motive 1)
  body: binaryRec' zero fun b n h ih =>
    if h' : n = 0 then
      have : n.bit b = Nat.bit true 0 := by
        rw [h']; rw [h h']
      congrArg motive this ▸ one
    else bit b n h' ih

中文:
定义 binaryRecFromOne
  签名: {motive : 自然数 -> Sort u} (zero : motive 0) (one : motive 1)
  定义体: binaryRec' zero fun b n h ih =>
    if h' : n = 0 then
      have : n.bit b = Nat.bit true 0 := by
        rw [h']; rw [h h']
      congrArg motive this ▸ one
    else bit b n h' ih

Depends on / 依赖: Nat.bit, binaryRec, motive, n.bit
-/
def binaryRecFromOne {motive : Nat -> Sort u} (zero : motive 0) (one : motive 1)
    (bit : forall b n, n != 0 -> motive n -> motive (bit b n)) :
    forall n, motive n :=
  binaryRec' zero fun b n h ih =>
    if h' : n = 0 then
      have : n.bit b = Nat.bit true 0 := by
        rw [h']; rw [h h']
      congrArg motive this ▸ one
    else bit b n h' ih

/--
theorem `bit_val` / 定理 `bit_val`

English:
theorem bit_val
  given: (b n)
  statement: bit b n = 2 * n + b.toNat
  proof: by
  cases b <;> rfl

@[simp]

中文:
定理 bit_val
  条件: (b n)
  结论: bit b n = 2 * n + b.to自然数
  证明: by
  cases b <;> rfl

@[simp]
-/
theorem bit_val (b n) : bit b n = 2 * n + b.toNat := by
  cases b <;> rfl

@[simp]
/--
theorem `bit_div_two` / 定理 `bit_div_two`

English:
theorem bit_div_two
  given: (b n)
  statement: bit b n / 2 = n
  proof: by
  rw [bit_val]; rw [Nat.add_comm]; rw [add_mul_div_left]; rw [div_eq_of_lt]; rw [Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]

中文:
定理 bit_div_two
  条件: (b n)
  结论: bit b n / 2 = n
  证明: by
  rw [bit_val]; rw [Nat.add_comm]; rw [add_mul_div_left]; rw [div_eq_of_lt]; rw [Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]

Depends on / 依赖: Nat.add_comm, Nat.zero_add, add_comm, add_mul_div_left, bit_val, div_eq_of_lt, zero_add
-/
theorem bit_div_two (b n) : bit b n / 2 = n := by
  rw [bit_val]; rw [Nat.add_comm]; rw [add_mul_div_left]; rw [div_eq_of_lt]; rw [Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]
/--
theorem `bit_mod_two` / 定理 `bit_mod_two`

English:
theorem bit_mod_two
  given: (b n)
  statement: bit b n % 2 = b.toNat
  proof: by
  cases b <;> simp [bit_val]

@[simp]

中文:
定理 bit_mod_two
  条件: (b n)
  结论: bit b n % 2 = b.to自然数
  证明: by
  cases b <;> simp [bit_val]

@[simp]

Depends on / 依赖: bit_val
-/
theorem bit_mod_two (b n) : bit b n % 2 = b.toNat := by
  cases b <;> simp [bit_val]

@[simp]
/--
theorem `bit_shiftRight_one` / 定理 `bit_shiftRight_one`

English:
theorem bit_shiftRight_one
  given: (b n)
  statement: bit b n >>> 1 = n
  proof: bit_div_two b n

中文:
定理 bit_shiftRight_one
  条件: (b n)
  结论: bit b n >>> 1 = n
  证明: bit_div_two b n

Depends on / 依赖: bit_div_two
-/
theorem bit_shiftRight_one (b n) : bit b n >>> 1 = n :=
  bit_div_two b n

/--
theorem `testBit_bit_zero` / 定理 `testBit_bit_zero`

English:
theorem testBit_bit_zero
  given: (b n)
  statement: (bit b n).testBit 0 = b
  proof: by
  simp

中文:
定理 testBit_bit_zero
  条件: (b n)
  结论: (bit b n).testBit 0 = b
  证明: by
  simp
-/
theorem testBit_bit_zero (b n) : (bit b n).testBit 0 = b := by
  simp

variable {motive : Nat -> Sort u}

@[simp]
/--
theorem `bitCasesOn_bit` / 定理 `bitCasesOn_bit`

English:
theorem bitCasesOn_bit
  given: (h : forall b n, motive (bit b n)) (b : Bool) (n : Nat)
  proof: by
  change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [testBit_bit_zero]; rw [bit_shiftRight_one]
  intros; rfl

@[simp]

中文:
定理 bitCasesOn_bit
  条件: (h : 对任意 b n, motive (bit b n)) (b : 布尔) (n : 自然数)
  证明: by
  change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [testBit_bit_zero]; rw [bit_shiftRight_one]
  intros; rfl

@[simp]

Depends on / 依赖: bit_shiftRight_one, bit_testBit_zero_shiftRight_one, generalize, intros, motive, revert, testBit_bit_zero
-/
theorem bitCasesOn_bit (h : forall b n, motive (bit b n)) (b : Bool) (n : Nat) :
    bitCasesOn (bit b n) h = h b n := by
  change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [testBit_bit_zero]; rw [bit_shiftRight_one]
  intros; rfl

@[simp]
/--
theorem `binaryRec_zero` / 定理 `binaryRec_zero`

English:
theorem binaryRec_zero
  given: (zero : motive 0) (bit : forall b n, motive n -> motive (bit b n))
  proof: rfl

@[simp]

中文:
定理 binaryRec_zero
  条件: (zero : motive 0) (bit : 对任意 b n, motive n -> motive (bit b n))
  证明: rfl

@[simp]
-/
theorem binaryRec_zero (zero : motive 0) (bit : forall b n, motive n -> motive (bit b n)) :
    binaryRec zero bit 0 = zero := rfl

@[simp]
/--
theorem `binaryRec_one` / 定理 `binaryRec_one`

English:
theorem binaryRec_one
  given: (zero : motive 0) (bit : forall b n, motive n -> motive (bit b n))
  proof: rfl

中文:
定理 binaryRec_one
  条件: (zero : motive 0) (bit : 对任意 b n, motive n -> motive (bit b n))
  证明: rfl

Depends on / 依赖: motive
-/
theorem binaryRec_one (zero : motive 0) (bit : forall b n, motive n -> motive (bit b n)) :
    binaryRec (motive := motive) zero bit 1 = bit true 0 zero := rfl

/--
theorem `binaryRec_eq` / 定理 `binaryRec_eq`

English:
theorem binaryRec_eq
  statement: {zero : motive 0} {bit : forall b n, motive n -> motive (bit b n)}
  proof: by
  by_cases h' : n.bit b = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [Bool.false_eq_true, imp_false, not_true_eq_false, or_false] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec]; rw [dif_neg h']
    change congrArg motive (n.bit b).bit

中文:
定理 binaryRec_eq
  结论: {zero : motive 0} {bit : 对任意 b n, motive n -> motive (bit b n)}
  证明: by
  by_cases h' : n.bit b = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [Bool.false_eq_true, imp_false, not_true_eq_false, or_false] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec]; rw [dif_neg h']
    change congrArg motive (n.bit b).bit

Depends on / 依赖: Bool.false_eq_true, binaryRec, bit_eq_zero_iff, bit_eq_zero_iff.mp, bit_shiftRight_one, bit_testBit_zero_shiftRight_one, dif_neg, false_eq_true, generalize, h.symm, imp_false, intros, motive, n.bit, not_true_eq_false, or_false, revert, testBit_bit_zero
-/
theorem binaryRec_eq {zero : motive 0} {bit : forall b n, motive n -> motive (bit b n)}
    (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = true)) :
    binaryRec zero bit (n.bit b) = bit b n (binaryRec zero bit n) := by
  by_cases h' : n.bit b = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [Bool.false_eq_true, imp_false, not_true_eq_false, or_false] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec]; rw [dif_neg h']
    change congrArg motive (n.bit b).bit_testBit_zero_shiftRight_one ▸ bit _ _ _ = _
    generalize congrArg motive (n.bit b).bit_testBit_zero_shiftRight_one = e; revert e
    rw [testBit_bit_zero]; rw [bit_shiftRight_one]
    intros; rfl

/--
theorem `binaryRec'_zero` / 定理 `binaryRec'_zero`

English:
theorem binaryRec'_zero
  statement: (zero : motive 0)
  proof: by
  rw [binaryRec']; rw [binaryRec_zero]

中文:
定理 binaryRec'_zero
  结论: (zero : motive 0)
  证明: by
  rw [binaryRec']; rw [binaryRec_zero]
-/
@[simp] theorem binaryRec'_zero (zero : motive 0)
    (bit : (b : Bool) -> (n : Nat) -> (n = 0 -> b = true) -> motive n -> motive (n.bit b)) :
    binaryRec' zero bit 0 = zero := by
  rw [binaryRec']; rw [binaryRec_zero]

/--
theorem `binaryRec'_one` / 定理 `binaryRec'_one`

English:
theorem binaryRec'_one
  statement: (zero : motive 0)
  proof: by
  rw [binaryRec']; rw [binaryRec_one]; rw [dif_pos]

中文:
定理 binaryRec'_one
  结论: (zero : motive 0)
  证明: by
  rw [binaryRec']; rw [binaryRec_one]; rw [dif_pos]
-/
@[simp] theorem binaryRec'_one (zero : motive 0)
    (bit : (b : Bool) -> (n : Nat) -> (n = 0 -> b = true) -> motive n -> motive (n.bit b)) :
    binaryRec' (motive := motive) zero bit 1 = bit true 0 (by simp) zero := by
  rw [binaryRec']; rw [binaryRec_one]; rw [dif_pos]

/--
theorem `binaryRec'_eq` / 定理 `binaryRec'_eq`

English:
theorem binaryRec'_eq
  statement: {zero : motive 0}
  proof: by
  rw [binaryRec']; rw [binaryRec_eq _ _ (by simp)]; rw [dif_pos h]; rw [binaryRec']

中文:
定理 binaryRec'_eq
  结论: {zero : motive 0}
  证明: by
  rw [binaryRec']; rw [binaryRec_eq _ _ (by simp)]; rw [dif_pos h]; rw [binaryRec']
-/
theorem binaryRec'_eq {zero : motive 0}
    {bit : (b : Bool) -> (n : Nat) -> (n = 0 -> b = true) -> motive n -> motive (n.bit b)}
    (b n) (h : n = 0 -> b = true) :
    binaryRec' zero bit (n.bit b) = bit b n h (binaryRec' zero bit n) := by
  rw [binaryRec']; rw [binaryRec_eq _ _ (by simp)]; rw [dif_pos h]; rw [binaryRec']

/--
theorem `binaryRecFromOne_zero` / 定理 `binaryRecFromOne_zero`

English:
theorem binaryRecFromOne_zero
  statement: (zero : motive 0) (one : motive 1)
  proof: binaryRec'_zero _ _

中文:
定理 binaryRecFromOne_zero
  结论: (zero : motive 0) (one : motive 1)
  证明: binaryRec'_zero _ _
-/
@[simp] theorem binaryRecFromOne_zero (zero : motive 0) (one : motive 1)
    (bit : (b : Bool) -> (n : Nat) -> n != 0 -> motive n -> motive (n.bit b)) :
    binaryRecFromOne zero one bit 0 = zero :=
  binaryRec'_zero _ _

/--
theorem `binaryRecFromOne_one` / 定理 `binaryRecFromOne_one`

English:
theorem binaryRecFromOne_one
  statement: {zero : motive 0} {one : motive 1}
  proof: by
  rw [binaryRecFromOne]; rw [binaryRec'_one]; rw [dif_pos rfl]

中文:
定理 binaryRecFromOne_one
  结论: {zero : motive 0} {one : motive 1}
  证明: by
  rw [binaryRecFromOne]; rw [binaryRec'_one]; rw [dif_pos rfl]
-/
@[simp] theorem binaryRecFromOne_one {zero : motive 0} {one : motive 1}
    (bit : (b : Bool) -> (n : Nat) -> n != 0 -> motive n -> motive (n.bit b)) :
    binaryRecFromOne zero one bit 1 = one := by
  rw [binaryRecFromOne]; rw [binaryRec'_one]; rw [dif_pos rfl]

/--
theorem `binaryRecFromOne_eq` / 定理 `binaryRecFromOne_eq`

English:
theorem binaryRecFromOne_eq
  statement: {zero : motive 0} {one : motive 1}
  proof: by
  rw [binaryRecFromOne]; rw [binaryRec'_eq _ _ (by simp [h]), dif_neg h, binaryRecFromOne]

中文:
定理 binaryRecFromOne_eq
  结论: {zero : motive 0} {one : motive 1}
  证明: by
  rw [binaryRecFromOne]; rw [binaryRec'_eq _ _ (by simp [h]), dif_neg h, binaryRecFromOne]

Depends on / 依赖: binaryRec, binaryRecFromOne, dif_neg
-/
theorem binaryRecFromOne_eq {zero : motive 0} {one : motive 1}
    {bit : (b : Bool) -> (n : Nat) -> n != 0 -> motive n -> motive (n.bit b)}
    (b n) (h) :
    binaryRecFromOne zero one bit (Nat.bit b n) =
      bit b n h (binaryRecFromOne zero one bit n) := by
  rw [binaryRecFromOne]; rw [binaryRec'_eq _ _ (by simp [h]), dif_neg h, binaryRecFromOne]

end Nat
