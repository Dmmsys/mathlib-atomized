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

/-- `bit b` appends the digit `b` to the little end of the binary representation of
its natural number input. -/
/-
**Nat.bit** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：bit (b : Bool) (n : Nat) : Nat
参数：b : Bool；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit b` appends the digit `b` to the little end of the binary representation of
its natural number input.
-/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (2 * n + 1) (2 * n)
/-
**Nat.shiftRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：shiftRight_one (n) : n >>> 1 = n / 2
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

@[simp]
/-
**Nat.bit_decide_mod_two_eq_one_shiftRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_decide_mod_two_eq_one_shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>
> 1) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_two_eq_zero_or_one`：∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
-/
theorem bit_decide_mod_two_eq_one_shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>> 1) = n := by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2
/-
**Nat.bit_testBit_zero_shiftRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = 
n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.testBit_zero`：∀ (x : ℕ), x.testBit 0 = decide (x % 2 = 1)
· 使用定理 `Nat.bit_decide_mod_two_eq_one_shiftRight_one`：bit_decide_mod_two_eq_one_
shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>> 1) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp

@[simp]
/-
**Nat.bit_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_false : bit false = (2 * ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit_false : bit false = (2 * ·) :=
  rfl

@[simp]
/-
**Nat.bit_true** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_true : bit true = (2 * · + 1)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit_true : bit true = (2 * · + 1) :=
  rfl

@[simp]
/-
**Nat.bit_false_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_false_apply (n) : bit false n = (2 * n)
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit_false_apply (n) : bit false n = (2 * n) :=
  rfl

@[simp]
/-
**Nat.bit_true_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_true_apply (n) : bit true n = (2 * n + 1)
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit_true_apply (n) : bit true n = (2 * n + 1) :=
  rfl

@[simp]
/-
**Nat.bit_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  cases n <;> cases b <;> simp [bit, Nat.two_mul, ← Nat.add_assoc]
/-
**Nat.bit_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0 ↔ n = 0 -> b = true
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b ≠ 0 ↔ n = 0 → b = true := by
  simp

/-- For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
/-
**Nat.bitCasesOn** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：bitCasesOn {motive : Nat -> Sort u} (n) (bit : forall b n, motive (bit b n
)) : motive n
参数：n；bit : forall b n, motive (bit b n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number.
-/
def bitCasesOn {motive : Nat → Sort u} (n) (bit : ∀ b n, motive (bit b n)) : motive n :=
  -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := bit (1 &&& n != 0) (n >>> 1)
  -- `congrArg motive _ ▸ x` is defeq to `x` in non-dependent case
  congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
/-
**Nat.bit_lt_two_pow_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {b : Bool} {x n : ℕ}, Nat.bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n
参数：n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem bit_lt_two_pow_succ_iff {b x n} : bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n := by
  cases b <;> simp <;> lia
/-
**Nat.log2_eq_succ_log2_shiftRight** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log2_eq_succ_log2_shiftRight {n : Nat} (hn : n >>> 1 != 0) : n.log2 = (n >
>> 1).log2.succ
参数：hn : n >>> 1 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.log2_eq_iff`：∀ {n k : ℕ}, n ≠ 0 → (n.log2 = k ↔ 2 ^ k ≤ n ∧ n < 2 ^ 
(k + 1))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_le_of_le_div`：∀ (k x y : ℕ), x ≤ y / k → x * k ≤ y
· 使用定理 `Nat.log2_self_le`：∀ {n : ℕ}, n ≠ 0 → 2 ^ n.log2 ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.lt_log2_self`：∀ {n : ℕ}, n < 2 ^ (n.log2 + 1)
-/
theorem log2_eq_succ_log2_shiftRight {n : Nat} (hn : n >>> 1 ≠ 0) : n.log2 = (n >>> 1).log2.succ :=
  (log2_eq_iff (by rintro rfl; exact hn rfl)).mpr
    ⟨Nat.mul_le_of_le_div _ _ _ (log2_self_le hn), (div_lt_iff_lt_mul <| by decide).mp lt_log2_self⟩

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize, semireducible]
/-
**Nat.binaryRec** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：binaryRec {motive : Nat -> Sort u} (zero : motive 0) (bit : forall b n, mo
tive n -> motive (bit b n)) (n : Nat) : motive n
参数：zero : motive 0；bit : forall b n, motive n -> motive (bit b n)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursion principle for `bit` representations of natural numbers.
  For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers.
-/
def binaryRec {motive : Nat → Sort u} (zero : motive 0) (bit : ∀ b n, motive n → motive (bit b n))
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let x := bit (1 &&& n != 0) (n >>> 1) (binaryRec zero bit (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
termination_by if n = 0 then 0 else n.log2.succ -- redundant, but removing causes slowdown
decreasing_by
  obtain _ | n := n; · exact (n0 rfl).elim
  obtain _ | n := n; · simp
  have : (n + 1 + 1) >>> 1 ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨by decide, le_add_left ..⟩
  simpa only [if_neg n0, if_neg this, log2_eq_succ_log2_shiftRight this] using lt_succ_self _

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true` -/
@[elab_as_elim, specialize]
/-
**Nat.binaryRec'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：binaryRec' {motive : Nat -> Sort u} (zero : motive 0) (bit : forall b n, (
n = 0 -> b = true) -> motive n -> motive (bit b n)) : forall n, motive n
参数：zero : motive 0；bit : forall b n, (n = 0 -> b = true) -> motive n -> motive (
bit b n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`
-/
def binaryRec' {motive : Nat → Sort u} (zero : motive 0)
    (bit : ∀ b n, (n = 0 → b = true) → motive n → motive (bit b n)) :
    ∀ n, motive n :=
  binaryRec zero fun b n ih =>
    if h : n = 0 → b = true then bit b n h ih
    else
      have : n.bit b = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h ⊢
      congrArg motive this ▸ zero

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
/-
**Nat.binaryRecFromOne** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：binaryRecFromOne {motive : Nat -> Sort u} (zero : motive 0) (one : motive 
1) (bit : forall b n, n != 0 -> motive n -> motive (bit b n)) : forall n, motive
 n
参数：zero : motive 0；one : motive 1；bit : forall b n, n != 0 -> motive n -> motive
 (bit b n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The same as `binaryRec`, but special casing both 0 and 1 as base cases
-/
def binaryRecFromOne {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
    (bit : ∀ b n, n ≠ 0 → motive n → motive (bit b n)) :
    ∀ n, motive n :=
  binaryRec' zero fun b n h ih =>
    if h' : n = 0 then
      have : n.bit b = Nat.bit true 0 := by
        rw [h', h h']
      congrArg motive this ▸ one
    else bit b n h' ih
/-
**Nat.bit_val** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_val (b n) : bit b n = 2 * n + b.toNat
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bit_val (b n) : bit b n = 2 * n + b.toNat := by
  cases b <;> rfl

@[simp]
/-
**Nat.bit_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_div_two (b n) : bit b n / 2 = n
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_mul_div_left`：∀ (x z : ℕ) {y : ℕ}, 0 < y → (x + y * z) / y = x /
 y + z
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
-/
theorem bit_div_two (b n) : bit b n / 2 = n := by
  rw [bit_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]
/-
**Nat.bit_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_mod_two (b n) : bit b n % 2 = b.toNat
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_add_mod_self_left`：∀ (a b c : ℕ), (a * b + c) % a = c % a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
-/
theorem bit_mod_two (b n) : bit b n % 2 = b.toNat := by
  cases b <;> simp [bit_val]

@[simp]
/-
**Nat.bit_shiftRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_shiftRight_one (b n) : bit b n >>> 1 = n
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bit_div_two`：bit_div_two (b n) : bit b n / 2 = n
-/
theorem bit_shiftRight_one (b n) : bit b n >>> 1 = n :=
  bit_div_two b n
/-
**Nat.testBit_bit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.testBit_zero`：∀ (x : ℕ), x.testBit 0 = decide (x % 2 = 1)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Nat.bit_mod_two`：bit_mod_two (b n) : bit b n % 2 = b.toNat
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem testBit_bit_zero (b n) : (bit b n).testBit 0 = b := by
  simp

variable {motive : Nat → Sort u}

@[simp]
/-
**Nat.bitCasesOn_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitCasesOn_bit (h : forall b n, motive (bit b n)) (b : Bool) (n : Nat) : b
itCasesOn (bit b n) h = h b n
参数：h : forall b n, motive (bit b n)；b : Bool；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.testBit_bit_zero`：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
· 使用定理 `Nat.bit_shiftRight_one`：bit_shiftRight_one (b n) : bit b n >>> 1 = n
· 使用定理 `Nat.bit_testBit_zero_shiftRight_one`：bit_testBit_zero_shiftRight_one (n 
: Nat) : bit (n.testBit 0) (n >>> 1) = n
-/
theorem bitCasesOn_bit (h : ∀ b n, motive (bit b n)) (b : Bool) (n : Nat) :
    bitCasesOn (bit b n) h = h b n := by
  change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [testBit_bit_zero, bit_shiftRight_one]
  intros; rfl

@[simp]
/-
**Nat.binaryRec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binaryRec_zero (zero : motive 0) (bit : forall b n, motive n -> motive (bi
t b n)) : binaryRec zero bit 0 = zero
参数：zero : motive 0；bit : forall b n, motive n -> motive (bit b n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binaryRec_zero (zero : motive 0) (bit : ∀ b n, motive n → motive (bit b n)) :
    binaryRec zero bit 0 = zero := rfl

@[simp]
/-
**Nat.binaryRec_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binaryRec_one (zero : motive 0) (bit : forall b n, motive n -> motive (bit
 b n)) : binaryRec (motive
参数：zero : motive 0；bit : forall b n, motive n -> motive (bit b n)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binaryRec_one (zero : motive 0) (bit : ∀ b n, motive n → motive (bit b n)) :
    binaryRec (motive := motive) zero bit 1 = bit true 0 zero := rfl
/-
**Nat.binaryRec_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binaryRec_eq {zero : motive 0} {bit : forall b n, motive n -> motive (bit 
b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = true)) : binaryRec zero
 bit (n.bit b) = bit b n (binaryRec zero bit n)
参数：bit b n；b n；h : bit false 0 zero = zero ∨ (n = 0 -> b = true)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.bit_eq_zero_iff`：bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 
↔ n = 0 ∧ b = false
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRec.eq_def`：∀ {motive : ℕ → Sort u} (zero : motive 0) (bit : (
b : Bool) → (n : ℕ) → motive n → motive (Nat.bit b n)) (n : ℕ),   Nat.binaryRec 
zero bit n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.binaryRec.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0) (bit : (b 
: Bool) → (n : ℕ) → motive n → motive (Nat.bit b n)) (n : ℕ),   Nat.binaryRec ze
ro bit n…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.testBit_bit_zero`：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
· 使用定理 `Nat.bit_shiftRight_one`：bit_shiftRight_one (b n) : bit b n >>> 1 = n
· 使用定理 `Nat.bit_testBit_zero_shiftRight_one`：bit_testBit_zero_shiftRight_one (n 
: Nat) : bit (n.testBit 0) (n >>> 1) = n
-/
theorem binaryRec_eq {zero : motive 0} {bit : ∀ b n, motive n → motive (bit b n)}
    (b n) (h : bit false 0 zero = zero ∨ (n = 0 → b = true)) :
    binaryRec zero bit (n.bit b) = bit b n (binaryRec zero bit n) := by
  by_cases h' : n.bit b = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [Bool.false_eq_true, imp_false, not_true_eq_false, or_false] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec, dif_neg h']
    change congrArg motive (n.bit b).bit_testBit_zero_shiftRight_one ▸ bit _ _ _ = _
    generalize congrArg motive (n.bit b).bit_testBit_zero_shiftRight_one = e; revert e
    rw [testBit_bit_zero, bit_shiftRight_one]
    intros; rfl
/-
**Nat.binaryRec'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : (b : Bool) → (n : ℕ) → 
(n = 0 → b = true) → motive n → motive (Nat.bit b n)), Nat.binaryRec' zero bit 0
 = zero
参数：zero : motive 0；bit : (b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → 
motive (Nat.bit b n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRec'.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : 
(b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → motive (Nat.bit b n)) (n 
: ℕ),   N…
· 使用定理 `Nat.binaryRec_zero`：binaryRec_zero (zero : motive 0) (bit : forall b n, 
motive n -> motive (bit b n)) : binaryRec zero bit 0 = zero
-/
@[simp] theorem binaryRec'_zero (zero : motive 0)
    (bit : (b : Bool) → (n : Nat) → (n = 0 → b = true) → motive n → motive (n.bit b)) :
    binaryRec' zero bit 0 = zero := by
  rw [binaryRec', binaryRec_zero]
/-
**Nat.binaryRec'_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : (b : Bool) → (n : ℕ) → 
(n = 0 → b = true) → motive n → motive (Nat.bit b n)),   Nat.binaryRec' zero bit
 1 = bit true 0 Nat.binaryRec'_one._proof_1 zero
参数：zero : motive 0；bit : (b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → 
motive (Nat.bit b n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRec'.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : 
(b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → motive (Nat.bit b n)) (n 
: ℕ),   N…
· 使用定理 `Nat.binaryRec_one`：binaryRec_one (zero : motive 0) (bit : forall b n, mo
tive n -> motive (bit b n)) : binaryRec (motive
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] theorem binaryRec'_one (zero : motive 0)
    (bit : (b : Bool) → (n : Nat) → (n = 0 → b = true) → motive n → motive (n.bit b)) :
    binaryRec' (motive := motive) zero bit 1 = bit true 0 (by simp) zero := by
  rw [binaryRec', binaryRec_one, dif_pos]
/-
**Nat.binaryRec'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {motive : ℕ → Sort u} {zero : motive 0}   {bit : (b : Bool) → (n : ℕ) → 
(n = 0 → b = true) → motive n → motive (Nat.bit b n)} (b : Bool) (n : ℕ)   (h : 
n = 0 → b = true), Nat.binaryRec' zero bit (Nat.bit b n) = bit b n h (Nat.binary
Rec' zero bit n)
参数：b : Bool；n : ℕ；n = 0 → b = true；Nat.bit b n；b : Bool；n : ℕ；h : n = 0 → b = tr
ue；Nat.bit b n；Nat.binaryRec' zero bit n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRec'.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : 
(b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → motive (Nat.bit b n)) (n 
: ℕ),   N…
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem binaryRec'_eq {zero : motive 0}
    {bit : (b : Bool) → (n : Nat) → (n = 0 → b = true) → motive n → motive (n.bit b)}
    (b n) (h : n = 0 → b = true) :
    binaryRec' zero bit (n.bit b) = bit b n h (binaryRec' zero bit n) := by
  rw [binaryRec', binaryRec_eq _ _ (by simp), dif_pos h, binaryRec']
/-
**Nat.binaryRecFromOne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {motive : ℕ → Sort u} (zero : motive 0) (one : motive 1)   (bit : (b : B
ool) → (n : ℕ) → n ≠ 0 → motive n → motive (Nat.bit b n)), Nat.binaryRecFromOne 
zero one bit 0 = zero
参数：zero : motive 0；one : motive 1；bit : (b : Bool) → (n : ℕ) → n ≠ 0 → motive n 
→ motive (Nat.bit b n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec'_zero`：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : 
(b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → motive (Nat.bit b n)), Na
t.binaryR…
-/
@[simp] theorem binaryRecFromOne_zero (zero : motive 0) (one : motive 1)
    (bit : (b : Bool) → (n : Nat) → n ≠ 0 → motive n → motive (n.bit b)) :
    binaryRecFromOne zero one bit 0 = zero :=
  binaryRec'_zero _ _
/-
**Nat.binaryRecFromOne_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {motive : ℕ → Sort u} {zero : motive 0} {one : motive 1}   (bit : (b : B
ool) → (n : ℕ) → n ≠ 0 → motive n → motive (Nat.bit b n)), Nat.binaryRecFromOne 
zero one bit 1 = one
参数：bit : (b : Bool) → (n : ℕ) → n ≠ 0 → motive n → motive (Nat.bit b n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRecFromOne.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0) (on
e : motive 1)   (bit : (b : Bool) → (n : ℕ) → n ≠ 0 → motive n → motive (Nat.bit
 b n)) (n : ℕ),…
· 使用定理 `Nat.binaryRec'_one`：∀ {motive : ℕ → Sort u} (zero : motive 0)   (bit : (
b : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → motive (Nat.bit b n)),   N
at.binar…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] theorem binaryRecFromOne_one {zero : motive 0} {one : motive 1}
    (bit : (b : Bool) → (n : Nat) → n ≠ 0 → motive n → motive (n.bit b)) :
    binaryRecFromOne zero one bit 1 = one := by
  rw [binaryRecFromOne, binaryRec'_one, dif_pos rfl]
/-
**Nat.binaryRecFromOne_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binaryRecFromOne_eq {zero : motive 0} {one : motive 1} {bit : (b : Bool) -
> (n : Nat) -> n != 0 -> motive n -> motive (n.bit b)} (b n) (h) : binaryRecFrom
One zero one bit (Nat.bit b n) = bit b n h (binaryRecFromOne zero one bit n)
参数：b : Bool；n : Nat；n.bit b；b n；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRecFromOne.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0) (on
e : motive 1)   (bit : (b : Bool) → (n : ℕ) → n ≠ 0 → motive n → motive (Nat.bit
 b n)) (n : ℕ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `Nat.binaryRec'_eq`：∀ {motive : ℕ → Sort u} {zero : motive 0}   {bit : (b
 : Bool) → (n : ℕ) → (n = 0 → b = true) → motive n → motive (Nat.bit b n)} (b : 
Bool) (…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem binaryRecFromOne_eq {zero : motive 0} {one : motive 1}
    {bit : (b : Bool) → (n : Nat) → n ≠ 0 → motive n → motive (n.bit b)}
    (b n) (h) :
    binaryRecFromOne zero one bit (Nat.bit b n) =
      bit b n h (binaryRecFromOne zero one bit n) := by
  rw [binaryRecFromOne, binaryRec'_eq _ _ (by simp [h]), dif_neg h, binaryRecFromOne]

end Nat

