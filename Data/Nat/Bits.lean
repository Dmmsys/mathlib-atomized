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
variable {m n : ℕ}

/-- `boddDiv2 n` returns a 2-tuple of type `(Bool, Nat)` where the `Bool` value indicates whether
`n` is odd or not and the `Nat` value returns `⌊n/2⌋` -/
@[deprecated "use `Nat.bodd` and `Nat.div2` instead" (since := "2026-03-22")]
/-
**Nat.boddDiv2** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → Bool × ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`boddDiv2 n` returns a 2-tuple of type `(Bool, Nat)` where the `Bool` value indi
cates whether
`n` is odd or not and the `Nat` value returns `⌊n/2⌋`
-/
def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)

/-- `div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2` -/
/-
**Nat.div2** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`
-/
@[inline, grind =] def div2 (n : ℕ) : ℕ := n / 2
/-
**Nat.div2_val** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：div2_val (n : Nat) : div2 n = n / 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`
-/
theorem div2_val (n : ℕ) : div2 n = n / 2 := rfl

/-- `bodd n` returns `true` if `n` is odd -/
/-
**Nat.bodd** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bodd n` returns `true` if `n` is odd
-/
@[inline] def bodd (n : ℕ) : Bool := n.testBit 0
/-
**Nat.bodd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.bodd 0 = false
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bodd n` returns `true` if `n` is odd
-/
@[simp] lemma bodd_zero : bodd 0 = false := rfl
/-
**Nat.bodd_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.bodd 1 = true
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bodd n` returns `true` if `n` is odd
-/
@[simp] lemma bodd_one : bodd 1 = true := rfl
/-
**Nat.bodd_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bodd_two : bodd 2 = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bodd n` returns `true` if `n` is odd
-/
lemma bodd_two : bodd 2 = false := rfl

@[simp]
/-
**Nat.bodd_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_two_eq_zero_or_one`：∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.testBit_zero`：∀ (x : ℕ), x.testBit 0 = decide (x % 2 = 1)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Bool.not_true`：(!true) = false
-/
lemma bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  simp only [bodd]
  cases mod_two_eq_zero_or_one n with | _ h => simp [h, add_mod]

@[simp]
/-
**Nat.bodd_add** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bodd_add (m n : Nat) : bodd (m + n) = bxor (bodd m) (bodd n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.bne_false`：∀ (b : Bool), (b != false) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.bne_not`：∀ (a b : Bool), (a != !b) = !a != b
-/
lemma bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, ih]

@[simp]
/-
**Nat.bodd_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.and_false`：∀ (b : Bool), (b && false) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_add`：bodd_add (m n : Nat) : bodd (m + n) = bxor (bodd m) (bodd 
n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction n with
  | zero => simp
  | succ n IH =>
    simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl

@[simp, grind =]
/-
**Nat.bodd_bit** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bodd_bit (b n) : bodd (bit b n) = b
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
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_add_mod_self_left`：∀ (a b c : ℕ), (a * b + c) % a = c % a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
-/
lemma bodd_bit (b n) : bodd (bit b n) = b := by
  cases b <;> simp [bodd]
/-
**Nat.mod_two_of_bodd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mod_two_of_bodd (n : Nat) : n % 2 = (bodd n).toNat
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用引理 `Nat.bodd_mul`：bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.false_and`：∀ (b : Bool), (false && b) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_add_mod_self_left`：∀ (a b c : ℕ), (a * b + c) % a = c % a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
-/
lemma mod_two_of_bodd (n : ℕ) : n % 2 = (bodd n).toNat := by
  cases n using bitCasesOn with
  | bit b n => cases b <;> simp
/-
**Nat.div2_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.div2 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma div2_zero : div2 0 = 0 := rfl
/-
**Nat.div2_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.div2 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma div2_one : div2 1 = 0 := rfl
/-
**Nat.div2_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div2_two : div2 2 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div2_two : div2 2 = 1 := rfl

@[simp]
/-
**Nat.div2_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div2_succ (n : Nat) : div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n
)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
· 使用定理 `Nat.succ_div`：∀ {a b : ℕ}, (a + 1) / b = a / b + if b ∣ a + 1 then 1 els
e 0
· 使用定理 `Nat.mul_div_right`：∀ (n : ℕ) {m : ℕ}, 0 < m → m * n / m = n
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.dvd_add_right`：∀ {a b c : ℕ}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用引理 `Nat.bodd_mul`：bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n)
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.false_and`：∀ (b : Bool), (false && b) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
lemma div2_succ (n : ℕ) : div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  cases n using bitCasesOn with
  | bit b n => cases b <;>
    simp [bit_val, div2_val, Nat.succ_div, Nat.add_assoc, Nat.dvd_add_right (Nat.dvd_mul_right _ _)]

@[simp, grind =]
/-
**Nat.div2_bit** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div2_bit (b n) : div2 (bit b n) = n
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div2_val`：div2_val (n : Nat) : div2 n = n / 2
· 使用定理 `Nat.bit_div_two`：bit_div_two (b n) : bit b n / 2 = n
-/
lemma div2_bit (b n) : div2 (bit b n) = n := by
  rw [div2_val, bit_div_two]

attribute [local simp] Nat.add_comm Nat.mul_comm
/-
**Nat.bodd_add_div2** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bodd_add_div2 (n : Nat) : (bodd n).toNat + 2 * div2 n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_bit`：bodd_bit (b n) : bodd (bit b n) = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
-/
lemma bodd_add_div2 (n : ℕ) : (bodd n).toNat + 2 * div2 n = n := by
  cases n using bitCasesOn with
  | bit b n => simpa using (bit_val b n).symm

@[simp, grind =]
/-
**Nat.bit_bodd_div2** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bit_bodd_div2 (n : Nat) : bit (bodd n) (div2 n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.bit_val`：bit_val (b n) : bit b n = 2 * n + b.toNat
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用引理 `Nat.bodd_add_div2`：bodd_add_div2 (n : Nat) : (bodd n).toNat + 2 * div2 n
 = n
-/
lemma bit_bodd_div2 (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _
/-
**Nat.bit_false_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bit_false_zero : bit false 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bit_false_zero : bit false 0 = 0 :=
  rfl

/-- `shiftLeft' b m n` performs a left shift of `m` `n` times
and adds the bit `b` as the least significant bit each time.
Returns the corresponding natural number -/
/-
**Nat.shiftLeft'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：shiftLeft'_false : forall n, shiftLeft' false m n = m <<< n | 0 => rfl | n
 + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`shiftLeft' b m n` performs a left shift of `m` `n` times
and adds the bit `b` as the least significant bit each time.
Returns the corresponding natural number
-/
def shiftLeft' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)

@[simp]
/-
**Nat.shiftLeft'_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m : ℕ} (n : ℕ), Nat.shiftLeft' false m n = m <<< n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
-/
lemma shiftLeft'_false : ∀ n, shiftLeft' false m n = m <<< n
  | 0 => rfl
  | n + 1 => by
    have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m := by
      rw [Nat.mul_comm, Nat.mul_assoc, ← Nat.pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]
/-
**Nat.shiftRight_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m n : ℕ), m.shiftRight n = m >>> n
参数：m n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma shiftRight_eq (m n : Nat) : shiftRight m n = m >>> n := rfl
/-
**Nat.binaryRec_decreasing** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：binaryRec_decreasing (h : n != 0) : div2 n < n
参数：h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma binaryRec_decreasing (h : n ≠ 0) : div2 n < n := by grind

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
/-
**Nat.size** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：size : Nat -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation
-/
def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ

/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
the head of the list represents the least significant bit -/
/-
**Nat.bits** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：bits : Nat -> List Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bits n` returns a list of Bools which correspond to the binary representation o
f n, where
the head of the list represents the least significant bit
-/
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as Booleans, say `aᵢ` and `bᵢ`, it applies the
  Boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
/-
**Nat.ldiff** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ldiff : Nat -> Nat -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as Booleans, say `aᵢ` and `bᵢ`, it applies the
  Boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result.
-/
def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b

/-! bitwise ops -/

/-
**Nat.shiftLeft'_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : Bool) (m n k : ℕ), Nat.shiftLeft' b m (n + k) = Nat.shiftLeft' b (N
at.shiftLeft' b m n) k
参数：b : Bool；m n k : ℕ；n + k；Nat.shiftLeft' b m n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m

--- 原说明 ---
bitwise ops
-/
lemma shiftLeft'_add (b m n) : ∀ k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftLeft'_add b m n k)
/-
**Nat.shiftLeft'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : Bool) (m : ℕ) {n k : ℕ}, k ≤ n → Nat.shiftLeft' b m (n - k) = Nat.s
hiftLeft' b m n >>> k
参数：b : Bool；m : ℕ；n - k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
-/
lemma shiftLeft'_sub (b m) : ∀ {n k}, k ≤ n → shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
  | _, 0, _ => rfl
  | n + 1, k + 1, h => by
    rw [succ_sub_succ_eq_sub, shiftLeft', Nat.add_comm, shiftRight_add]
    simp only [shiftLeft'_sub, Nat.le_of_succ_le_succ h, shiftRight_succ, shiftRight_zero]
    simp [← div2_val, div2_bit]
/-
**Nat.shiftLeft_sub** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：shiftLeft_sub : forall (m : Nat) {n k}, k <= n -> m <<< (n - k) = (m <<< n
) >>> k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft'_sub`：∀ (b : Bool) (m : ℕ) {n k : ℕ}, k ≤ n → Nat.shiftLef
t' b m (n - k) = Nat.shiftLeft' b m n >>> k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftLeft_sub : ∀ (m : Nat) {n k}, k ≤ n → m <<< (n - k) = (m <<< n) >>> k :=
  fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]
/-
**Nat.bodd_eq_one_and_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.bodd = (1 &&& n != 0)
参数：n : ℕ；1 &&& n != 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bodd_eq_one_and_ne_zero : ∀ n, bodd n = (1 &&& n != 0)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simpa using bodd_eq_one_and_ne_zero n
/-
**Nat.testBit_bit_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：testBit_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m
参数：m b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.shiftRight_eq_div_pow`：∀ (m n : ℕ), m >>> n = m / 2 ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.bodd_eq_one_and_ne_zero`：∀ (n : ℕ), n.bodd = (1 &&& n != 0)
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.shiftRight_add`：∀ (m n k : ℕ), m >>> (n + k) = m >>> n >>> k
-/
lemma testBit_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add, Nat.add_comm] at this
  simp only [bodd_eq_one_and_ne_zero] at this
  exact this

/-! ### `boddDiv2_eq` and `bodd` -/

@[deprecated "`Nat.boddDiv2` has been deprecated" (since := "2026-03-22")]
/-
**Nat.boddDiv2_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：boddDiv2_eq (n : Nat) : boddDiv2 n = (bodd n, div2 n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.boddDiv2.eq_2`：∀ (n : ℕ),   n.succ.boddDiv2 =     match n.boddDiv2 w
ith     | (false, m) => (true, m)     | (true, m) => (false, m.succ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.not_false`：(!false) = true
· 使用引理 `Nat.div2_succ`：div2_succ (n : Nat) : div2 (n + 1) = cond (bodd n) (succ 
(div2 n)) (div2 n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.not_true`：(!true) = false

--- 原说明 ---
### `boddDiv2_eq` and `bodd`
-/
theorem boddDiv2_eq (n : ℕ) : boddDiv2 n = (bodd n, div2 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boddDiv2, ih]
    cases hn : n.bodd <;> simp [hn]

@[simp]
/-
**Nat.div2_bit0** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：div2_bit0 (n) : div2 (2 * n) = n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
-/
theorem div2_bit0 (n) : div2 (2 * n) = n :=
  div2_bit false n

-- simp can prove this
/-
**Nat.div2_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：div2_bit1 (n) : div2 (2 * n + 1) = n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
-/
theorem div2_bit1 (n) : div2 (2 * n + 1) = n :=
  div2_bit true n

/-! ### `bit0` and `bit1` -/

/-
**Nat.bit_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : Bool) (n m : ℕ), Nat.bit b (n + m) = Nat.bit false n + Nat.bit b m
参数：b : Bool；n m : ℕ；n + m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `bit0` and `bit1`
-/
theorem bit_add : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit false n + bit b m
  | true, _, _ => by dsimp [bit]; lia
  | false, _, _ => by dsimp [bit]; lia
/-
**Nat.bit_add'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : Bool) (n m : ℕ), Nat.bit b (n + m) = Nat.bit b n + Nat.bit false m
参数：b : Bool；n m : ℕ；n + m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit_add' : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit b n + bit false m
  | true, _, _ => by dsimp [bit]; lia
  | false, _, _ => by dsimp [bit]; lia
/-
**Nat.bit_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_ne_zero (b) {n} (h : n != 0) : bit b n != 0
参数：b；h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 := by
  cases b <;> dsimp [bit] <;> lia

@[simp]
/-
**Nat.bitCasesOn_bit0** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitCasesOn_bit0 {motive : Nat -> Sort u} (H : forall b n, motive (bit b n)
) (n : Nat) : bitCasesOn (2 * n) H = H false n
参数：H : forall b n, motive (bit b n)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bitCasesOn_bit`：bitCasesOn_bit (h : forall b n, motive (bit b n)) (b
 : Bool) (n : Nat) : bitCasesOn (bit b n) h = h b n
-/
theorem bitCasesOn_bit0 {motive : ℕ → Sort u} (H : ∀ b n, motive (bit b n)) (n : ℕ) :
    bitCasesOn (2 * n) H = H false n :=
  bitCasesOn_bit H false n

@[simp]
/-
**Nat.bitCasesOn_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitCasesOn_bit1 {motive : Nat -> Sort u} (H : forall b n, motive (bit b n)
) (n : Nat) : bitCasesOn (2 * n + 1) H = H true n
参数：H : forall b n, motive (bit b n)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bitCasesOn_bit`：bitCasesOn_bit (h : forall b n, motive (bit b n)) (b
 : Bool) (n : Nat) : bitCasesOn (bit b n) h = h b n
-/
theorem bitCasesOn_bit1 {motive : ℕ → Sort u} (H : ∀ b n, motive (bit b n)) (n : ℕ) :
    bitCasesOn (2 * n + 1) H = H true n :=
  bitCasesOn_bit H true n
/-
**Nat.bit_cases_on_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_cases_on_injective {motive : Nat -> Sort u} : Function.Injective fun H
 : forall b n, motive (bit b n) => fun n => bitCasesOn n H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bitCasesOn_bit`：bitCasesOn_bit (h : forall b n, motive (bit b n)) (b
 : Bool) (n : Nat) : bitCasesOn (bit b n) h = h b n
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem bit_cases_on_injective {motive : ℕ → Sort u} :
    Function.Injective fun H : ∀ b n, motive (bit b n) => fun n => bitCasesOn n H := by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)

@[simp]
/-
**Nat.bit_cases_on_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit_cases_on_inj {motive : Nat -> Sort u} (H₁ H₂ : forall b n, motive (bit
 b n)) : ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂
参数：H₁ H₂ : forall b n, motive (bit b n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Nat.bit_cases_on_injective`：bit_cases_on_injective {motive : Nat -> Sort
 u} : Function.Injective fun H : forall b n, motive (bit b n) => fun n => bitCas
esOn n H
-/
theorem bit_cases_on_inj {motive : ℕ → Sort u} (H₁ H₂ : ∀ b n, motive (bit b n)) :
    ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂ :=
  bit_cases_on_injective.eq_iff
/-
**Nat.bit_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : Bool) {m n : ℕ}, m ≤ n → Nat.bit b m ≤ Nat.bit b n
参数：b : Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bit_le : ∀ (b : Bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
  | true, _, _, h => by dsimp [bit]; lia
  | false, _, _, h => by dsimp [bit]; lia
/-
**Nat.bit_lt_bit** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bit_lt_bit (a b) (h : m < n) : bit a m < bit b n
参数：a b；h : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma bit_lt_bit (a b) (h : m < n) : bit a m < bit b n := calc
  bit a m < 2 * n := by cases a <;> dsimp [bit] <;> lia
        _ ≤ bit b n := by cases b <;> dsimp [bit] <;> lia

@[simp]
/-
**Nat.zero_bits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：zero_bits : bits 0 = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_bits : bits 0 = [] := by simp [Nat.bits]

@[simp]
/-
**Nat.bits_append_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 -> b = true) : (bit b n).
bits = b :: n.bits
参数：n : Nat；b : Bool；hn : n = 0 -> b = true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bits.eq_1`：∀ (n : ℕ), n.bits = Nat.binaryRec [] (fun b x IH => b :: 
IH) n
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem bits_append_bit (n : ℕ) (b : Bool) (hn : n = 0 → b = true) :
    (bit b n).bits = b :: n.bits := by
  rw [Nat.bits, Nat.bits, binaryRec_eq]
  simpa

@[simp]
/-
**Nat.bit0_bits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit0_bits (n : Nat) (hn : n != 0) : (2 * n).bits = false :: n.bits
参数：n : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bits_append_bit`：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 ->
 b = true) : (bit b n).bits = b :: n.bits
-/
theorem bit0_bits (n : ℕ) (hn : n ≠ 0) : (2 * n).bits = false :: n.bits :=
  bits_append_bit n false fun hn' => absurd hn' hn

@[simp]
/-
**Nat.bit1_bits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bit1_bits (n : Nat) : (2 * n + 1).bits = true :: n.bits
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bits_append_bit`：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 ->
 b = true) : (bit b n).bits = b :: n.bits
-/
theorem bit1_bits (n : ℕ) : (2 * n + 1).bits = true :: n.bits :=
  bits_append_bit n true fun _ => rfl

@[simp]
/-
**Nat.one_bits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_bits : Nat.bits 1 = [true]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bit1_bits`：bit1_bits (n : Nat) : (2 * n + 1).bits = true :: n.bits
-/
theorem one_bits : Nat.bits 1 = [true] := bit1_bits 0

-- TODO Find somewhere this can live.
-- example : bits 3423 = [true, true, true, true, true, false, true, false, true, false, true, true]
-- := by norm_num
/-
**Nat.bodd_eq_bits_head** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bodd_eq_bits_head (n : Nat) : n.bodd = n.bits.headI
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_bits`：zero_bits : bits 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_bit`：bodd_bit (b n) : bodd (bit b n) = b
· 使用定理 `Nat.bits_append_bit`：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 ->
 b = true) : (bit b n).bits = b :: n.bits
-/
theorem bodd_eq_bits_head (n : ℕ) : n.bodd = n.bits.headI := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [bodd_bit, bits_append_bit _ _ h]
/-
**Nat.div2_bits_eq_tail** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：div2_bits_eq_tail (n : Nat) : n.div2.bits = n.bits.tail
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_bits`：zero_bits : bits 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
· 使用定理 `Nat.bits_append_bit`：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 ->
 b = true) : (bit b n).bits = b :: n.bits
-/
theorem div2_bits_eq_tail (n : ℕ) : n.div2.bits = n.bits.tail := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h => simp [div2_bit, bits_append_bit _ _ h]

end Nat

