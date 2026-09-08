/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `Nat.log b` and `Nat.clog b` are respectively right and
left adjoints of `(b ^ ·)`. See `le_log_iff_pow_le` and `clog_le_iff_le_pow`.

## Implementation notes

We define both functions using recursion on `b`.
In order to compute, e.g., `Nat.log b n`, we compute `e = Nat.log (b * b) n` first,
then figure out whether the answer is `2 * e` or `2 * e + 1`.
The actual implementations use fuel recursion so that `(by decide : Nat.log 2 20 = 4)` works.

Adapted from https://downloads.haskell.org/~ghc/9.0.1/docs/html/libraries/ghc-bignum-1.0/GHC-Num-BigNat.html#v:bigNatLogBase-35-

Note a tail-recursive version of `Nat.log` is also possible:
```
def logTR (b n : ℕ) : ℕ :=
  let rec go : ℕ → ℕ → ℕ | n, acc => if h : b ≤ n ∧ 1 < b then go (n / b) (acc + 1) else acc
  decreasing_by
    have : n / b < n := Nat.div_lt_self (by lia) h.2
    decreasing_trivial
  go n 0
```
but performs worse for large numbers than `Nat.log`:
```
#eval Nat.logTR 2 (2 ^ 1000000)
#eval Nat.log 2 (2 ^ 1000000)
```
-/

@[expose] public section

assert_not_exists OrderTop

namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
/-
**Nat.log** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：log (b n : Nat) : Nat
参数：b n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`log b n`, is the logarithm of natural number `n` in base `b`. It returns the la
rgest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`.
-/
def log (b n : ℕ) : ℕ :=
  if b ≤ 1 then 0 else (go b n).2 where
  /-- An auxiliary definition for `Nat.log`.

  For `b > 1`, `n ≠ 0`, `n < b ^ fuel`, `Nat.log.go n b fuel = (n / b ^ b.log n, b.log n)`. -/
  go : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)
/-
**Nat.log_of_left_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) : log b n = 0
参数：hb : b <= 1；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log.eq_1`：∀ (b n : ℕ), Nat.log b n = if b ≤ 1 then 0 else (Nat.log.g
o n b n).2
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 := by
  rw [log, if_pos hb]
/-
**Nat.log_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_of_lt {b n : Nat} (hb : n < b) : log b n = 0
参数：hb : n < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log.fun_cases_unfolding`：∀ (b n : ℕ) (motive : ℕ → Prop), (b ≤ 1 → m
otive 0) → (¬b ≤ 1 → motive (Nat.log.go n b n).2) → motive (Nat.log b n)
· 使用定理 `Nat.log.go.fun_cases_unfolding`：∀ (n : ℕ) (motive : ℕ → ℕ → ℕ × ℕ → Prop
),   (∀ (x : ℕ), motive x 0 (n, 0)) →     (∀ (b fuel : ℕ), n < b → motive b fuel
.succ (n, 0)) →     …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 := by
  fun_cases log with
  | case1 => rfl
  | case2 => fun_cases log.go with grind
/-
**Nat.log.go_aux** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem log.go_aux {n b fuel : ℕ} (hb : 1 < b) (hfuel : n < b ^ (fuel + 1)) (hbn : b ≤ n) :
    n < (b * b) ^ fuel := by
  obtain hfuel₀ : fuel ≠ 0 := by rintro rfl; simp [Nat.not_lt_of_le hbn] at hfuel
  rw [← Nat.pow_two, ← Nat.pow_mul]
  exact Nat.lt_of_lt_of_le hfuel <| Nat.pow_le_pow_right (by grind) (by grind)
/-
**Nat.log.go_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.log`。
形式化陈述：∀ {b n fuel : ℕ},   1 < b →     n ≠ 0 →       n < b ^ fuel →         (Nat.
log.go n b fuel).1 = n / b ^ (Nat.log.go n b fuel).2 ∧           b ^ (Nat.log.go
 n b fuel).2 ≤ n ∧ n < b ^ ((Nat.log.go n b fuel).2 + 1)
参数：Nat.log.go n b fuel；Nat.log.go n b fuel；Nat.log.go n b fuel；(Nat.log.go n b f
uel).2 + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.mul_lt_mul_of_lt_of_lt`：∀ {a b c d : ℕ}, a < c → b < d → a * b < c *
 d
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `_private.Mathlib.Data.Nat.Log.0.Nat.log.go_aux`：∀ {n b fuel : ℕ}, 1 < b 
→ n < b ^ (fuel + 1) → b ≤ n → n < (b * b) ^ fuel
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.not_lt_of_le`：∀ {a b : ℕ}, a ≤ b → ¬b < a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma log.go_spec {b n fuel : ℕ} (hb : 1 < b) (hn : n ≠ 0) (hfuel : n < b ^ fuel) :
    (log.go n b fuel).1 = n / b ^ (log.go n b fuel).2 ∧
      b ^ (log.go n b fuel).2 ≤ n ∧ n < b ^ ((log.go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge n b with
    | inl hnb =>
      simp [go, hnb, one_le_iff_ne_zero, hn]
    | inr hnb =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb) (go_aux hb hfuel hnb)
        with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_lt_of_le hnb), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul, Nat.pow_pos (Nat.zero_lt_of_lt hb), Nat.div_div_eq_div_mul,
        ← Nat.pow_add_one, ← Nat.pow_add_one', Nat.mul_add_one]
      split <;> simp_all
/-
**Nat.log_lt_iff_lt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : Nat} (hy : y != 0) : log b
 y < x ↔ y < b ^ x
参数：hb : 1 < b；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log.go_spec`：∀ {b n fuel : ℕ},   1 < b →     n ≠ 0 →       n < b ^ f
uel →         (Nat.log.go n b fuel).1 = n / b ^ (Nat.log.go n b fuel).2 ∧       
    b…
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log.eq_1`：∀ (b n : ℕ), Nat.log b n = if b ≤ 1 then 0 else (Nat.log.g
o n b n).2
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.not_le_of_lt`：∀ {a b : ℕ}, a < b → ¬b ≤ a
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Nat.not_lt_of_ge`：∀ {a b : ℕ}, b ≥ a → ¬b < a
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
-/
theorem log_lt_iff_lt_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    log b y < x ↔ y < b ^ x := by
  rcases log.go_spec hb hy (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
  rw [log, if_neg (Nat.not_le_of_lt hb)]
  cases Nat.lt_or_ge (log.go y b y).snd x with
  | inl h =>
    exact iff_of_true h <| Nat.lt_of_lt_of_le H₂ <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h
  | inr h =>
    refine iff_of_false (Nat.not_lt_of_ge h) <| Nat.not_lt_of_ge <| Nat.le_trans ?_ H₁
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h

@[simp]
/-
**Nat.log_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_eq_zero_iff {b n : Nat} : log b n = 0 ↔ n < b ∨ b <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.log_lt_iff_lt_pow`：log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : log b y < x ↔ y < b ^ x
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Nat.not_le_of_lt`：∀ {a b : ℕ}, a < b → ¬b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rcases eq_or_ne n 0 with rfl | hn
    · grind [log_of_lt]
    · rw [← Nat.lt_one_iff, log_lt_iff_lt_pow hb hn, Nat.pow_one, or_iff_left (Nat.not_le_of_lt hb)]
  · simp [hb, log_of_left_le_one]

@[simp]
/-
**Nat.log_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_pos_iff {b n : Nat} : 0 < log b n ↔ b <= n ∧ 1 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.log_eq_zero_iff`：log_eq_zero_iff {b n : Nat} : log b n = 0 ↔ n < b ∨
 b <= 1
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_pos_iff {b n : ℕ} : 0 < log b n ↔ b ≤ n ∧ 1 < b := by
  rw [Nat.pos_iff_ne_zero, Ne, log_eq_zero_iff, not_or, not_lt, not_le]

@[bound]
/-
**Nat.log_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_pos {b n : Nat} (hb : 1 < b) (hbn : b <= n) : 0 < log b n
参数：hb : 1 < b；hbn : b <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.log_pos_iff`：log_pos_iff {b n : Nat} : 0 < log b n ↔ b <= n ∧ 1 < b
-/
theorem log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n :=
  log_pos_iff.2 ⟨hbn, hb⟩
/-
**Nat.log_of_one_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_of_one_lt_of_le {b n : Nat} (h : 1 < b) (hn : b <= n) : log b n = log 
b (n / b) + 1
参数：h : 1 < b；hn : b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_gt_iff`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, 
(∀ (c : α), a < c ↔ b < c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.log_lt_iff_lt_pow`：log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : log b y < x ↔ y < b ^ x
· 使用定理 `Nat.add_lt_add_iff_right`：∀ {k n m : ℕ}, n + k < m + k ↔ n < m
· 使用定理 `Nat.pow_add_one`：∀ (n m : ℕ), n ^ (m + 1) = n ^ m * n
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 := by
  apply eq_of_forall_gt_iff
  rintro (_ | c)
  · simp
  · have : n / b ≠ 0 := by simp [*, Nat.ne_zero_of_lt h]
    rw [log_lt_iff_lt_pow, Nat.add_lt_add_iff_right, log_lt_iff_lt_pow,
      Nat.pow_add_one, Nat.div_lt_iff_lt_mul] <;> grind
/-
**Nat.log_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), Nat.log 0 n = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
@[simp] lemma log_zero_left : ∀ n, log 0 n = 0 := log_of_left_le_one <| Nat.zero_le _

@[simp]
/-
**Nat.log_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_zero_right (b : Nat) : log b 0 = 0
参数：b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.log_eq_zero_iff`：log_eq_zero_iff {b n : Nat} : log b n = 0 ↔ n < b ∨
 b <= 1
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
theorem log_zero_right (b : ℕ) : log b 0 = 0 :=
  log_eq_zero_iff.2 (le_total 1 b)

@[simp]
/-
**Nat.log_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_one_left : forall n, log 1 n = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem log_one_left : ∀ n, log 1 n = 0 :=
  log_of_left_le_one le_rfl

@[simp]
/-
**Nat.log_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_one_right (b : Nat) : log b 1 = 0
参数：b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.log_eq_zero_iff`：log_eq_zero_iff {b n : Nat} : log b n = 0 ↔ n < b ∨
 b <= 1
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
theorem log_one_right (b : ℕ) : log b 1 = 0 :=
  log_eq_zero_iff.2 (lt_or_ge _ _)

/-- `(b ^ ·)` and `log b` (almost) form a Galois connection. See also `Nat.pow_le_of_le_log` and
`Nat.le_log_of_pow_le` for individual implications under weaker assumptions. -/
/-
**Nat.le_log_iff_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : Nat} (hy : y != 0) : x <= 
log b y ↔ b ^ x <= y
参数：hb : 1 < b；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Nat.log_lt_iff_lt_pow`：log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : log b y < x ↔ y < b ^ x

--- 原说明 ---
`(b ^ ·)` and `log b` (almost) form a Galois connection. See also `Nat.pow_le_of
_le_log` and
`Nat.le_log_of_pow_le` for individual implications under weaker assumptions.
-/
theorem le_log_iff_pow_le {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    x ≤ log b y ↔ b ^ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.mpr <| log_lt_iff_lt_pow hb hy
/-
**Nat.pow_le_of_le_log** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_le_of_le_log {b x y : Nat} (hy : y != 0) (h : x <= log b y) : b ^ x <=
 y
参数：hy : y != 0；h : x <= log b y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.pow_zero`：∀ (n : ℕ), n ^ 0 = 1
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_log_iff_pow_le`：le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : x <= log b y ↔ b ^ x <= y
-/
theorem pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y := by
  refine (le_or_gt b 1).elim (fun hb => ?_) fun hb => (le_log_iff_pow_le hb hy).1 h
  rw [log_of_left_le_one hb, Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]
/-
**Nat.le_log_of_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b ^ x <= y) : x <= log b 
y
参数：hb : 1 < b；h : b ^ x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_log_iff_pow_le`：le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : x <= log b y ↔ b ^ x <= y
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y := by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(le_log_iff_pow_le hb hy).2 h, (h.not_gt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]
/-
**Nat.pow_log_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) : b ^ log b x <= x
参数：b : Nat；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_le_of_le_log`：pow_le_of_le_log {b x y : Nat} (hy : y != 0) (h : 
x <= log b y) : b ^ x <= y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x :=
  pow_le_of_le_log hx le_rfl

/-- See also `log_lt_of_lt_pow'` for a version that assumes `x ≠ 0` instead of `y ≠ 0`. -/
/-
**Nat.log_lt_of_lt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_lt_of_lt_pow {b x y : Nat} (hy : y != 0) : y < b ^ x -> log b y < x
参数：hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Nat.pow_le_of_le_log`：pow_le_of_le_log {b x y : Nat} (hy : y != 0) (h : 
x <= log b y) : b ^ x <= y

--- 原说明 ---
See also `log_lt_of_lt_pow'` for a version that assumes `x ≠ 0` instead of `y ≠ 
0`.
-/
theorem log_lt_of_lt_pow {b x y : ℕ} (hy : y ≠ 0) : y < b ^ x → log b y < x :=
  lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

/-- A version of `log_lt_of_lt_pow` that assumes `x ≠ 0` instead of `y ≠ 0`. -/
/-
**Nat.log_lt_of_lt_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_lt_of_lt_pow' {b x y : Nat} (hx : x != 0) (hlt : y < b ^ x) : log b y 
< x
参数：hx : x != 0；hlt : y < b ^ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.log_lt_of_lt_pow`：log_lt_of_lt_pow {b x y : Nat} (hy : y != 0) : y <
 b ^ x -> log b y < x

--- 原说明 ---
A version of `log_lt_of_lt_pow` that assumes `x ≠ 0` instead of `y ≠ 0`.
-/
theorem log_lt_of_lt_pow' {b x y : ℕ} (hx : x ≠ 0) (hlt : y < b ^ x) : log b y < x := by
  rcases eq_or_ne y 0 with rfl | hy
  · grind [log_zero_right]
  · exact log_lt_of_lt_pow hy hlt
/-
**Nat.lt_pow_of_log_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_pow_of_log_lt {b x y : Nat} (hb : 1 < b) : log b y < x -> y < b ^ x
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
-/
theorem lt_pow_of_log_lt {b x y : ℕ} (hb : 1 < b) : log b y < x → y < b ^ x :=
  lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)
/-
**Nat.log_lt_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log_lt_self (b : Nat) {x : Nat} (hx : x != 0) : log b x < x
参数：b : Nat；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.log_lt_of_lt_pow`：log_lt_of_lt_pow {b x y : Nat} (hy : y != 0) : y <
 b ^ x -> log b y < x
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
-/
lemma log_lt_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : log b x < x :=
  match le_or_gt b 1 with
  | .inl h => log_of_left_le_one h x ▸ Nat.pos_iff_ne_zero.2 hx
  | .inr h => log_lt_of_lt_pow hx <| Nat.lt_pow_self h
/-
**Nat.log_le_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log_le_self (b x : Nat) : log b x <= x
参数：b x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Nat.log_lt_self`：log_lt_self (b : Nat) {x : Nat} (hx : x != 0) : log b x
 < x
-/
lemma log_le_self (b x : ℕ) : log b x ≤ x :=
  if hx : x = 0 then by simp [hx]
  else (log_lt_self b hx).le
/-
**Nat.lt_pow_succ_log_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_pow_succ_log_self {b : Nat} (hb : 1 < b) (x : Nat) : x < b ^ (log b x).
succ
参数：hb : 1 < b；x : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_pow_of_log_lt`：lt_pow_of_log_lt {b x y : Nat} (hb : 1 < b) : log 
b y < x -> y < b ^ x
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ :=
  lt_pow_of_log_lt hb (lt_succ_self _)
/-
**Nat.log_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) : log b n = m ↔ b ^
 m <= n ∧ n < b ^ (m + 1)
参数：h : m != 0 ∨ 1 < b ∧ n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.le_log_iff_pow_le`：le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : x <= log b y ↔ b ^ x <= y
· 使用定理 `Nat.log_lt_iff_lt_pow`：log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : log b y < x ↔ y < b ^ x
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.log_zero_left`：∀ (n : ℕ), Nat.log 0 n = 0
· 使用定理 `Nat.log_one_left`：log_one_left : forall n, log 1 n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 31 条，此处仅展示前 30 条）
-/
theorem log_eq_iff {b m n : ℕ} (h : m ≠ 0 ∨ 1 < b ∧ n ≠ 0) :
    log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1) := by
  rcases em (1 < b ∧ n ≠ 0) with (⟨hb, hn⟩ | hbn)
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, le_log_iff_pow_le, log_lt_iff_lt_pow,
      and_comm] <;> assumption
  have hm : m ≠ 0 := h.resolve_right hbn
  rw [not_and_or, not_lt, Ne, not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb <;>
      simp only [log_zero_left, log_one_left] <;> lia
  · simp [@eq_comm _ 0, hm]
/-
**Nat.log_eq_of_pow_le_of_lt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_eq_of_pow_le_of_lt_pow {b m n : Nat} (h₁ : b ^ m <= n) (h₂ : n < b ^ (
m + 1)) : log b n = m
参数：h₁ : b ^ m <= n；h₂ : n < b ^ (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.log_of_lt`：log_of_lt {b n : Nat} (hb : n < b) : log b n = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.log_eq_iff`：log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) :
 log b n = m ↔ b ^ m <= n ∧ n < b ^ (m + 1)
-/
theorem log_eq_of_pow_le_of_lt_pow {b m n : ℕ} (h₁ : b ^ m ≤ n) (h₂ : n < b ^ (m + 1)) :
    log b n = m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · rw [Nat.pow_one] at h₂
    exact log_of_lt h₂
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩

@[simp]
/-
**Nat.log_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_pow {b : Nat} (hb : 1 < b) (x : Nat) : log b (b ^ x) = x
参数：hb : 1 < b；x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_eq_of_pow_le_of_lt_pow`：log_eq_of_pow_le_of_lt_pow {b m n : Nat}
 (h₁ : b ^ m <= n) (h₂ : n < b ^ (m + 1)) : log b n = m
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.pow_lt_pow_right`：∀ {a m n : ℕ}, 1 < a → m < n → a ^ m < a ^ n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
  log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)
/-
**Nat.log_eq_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_eq_one_iff' {b n : Nat} : log b n = 1 ↔ b <= n ∧ n < b * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_eq_iff`：log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) :
 log b n = m ↔ b ^ m <= n ∧ n < b ^ (m + 1)
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
· 使用定理 `Nat.pow_add`：∀ (a m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_eq_one_iff' {b n : ℕ} : log b n = 1 ↔ b ≤ n ∧ n < b * b := by
  rw [log_eq_iff (Or.inl Nat.one_ne_zero), Nat.pow_add, Nat.pow_one]
/-
**Nat.log_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_eq_one_iff {b n : Nat} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.log_eq_one_iff'`：log_eq_one_iff' {b n : Nat} : log b n = 1 ↔ b <= n 
∧ n < b * b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_mul_self_iff`：∀ {n : ℕ}, n < n * n ↔ 1 < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n :=
  log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩

@[simp]
/-
**Nat.log_mul_base** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_mul_base {b n : Nat} (hb : 1 < b) (hn : n != 0) : log b (n * b) = log 
b n + 1
参数：hb : 1 < b；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_eq_of_pow_le_of_lt_pow`：log_eq_of_pow_le_of_lt_pow {b m n : Nat}
 (h₁ : b ^ m <= n) (h₂ : n < b ^ (m + 1)) : log b n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Nat.pow_log_le_self`：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) :
 b ^ log b x <= x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mul_lt_mul_right`：∀ {a b c : ℕ}, 0 < a → (b * a < c * a ↔ b < c)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `Nat.lt_pow_succ_log_self`：lt_pow_succ_log_self {b : Nat} (hb : 1 < b) (x
 : Nat) : x < b ^ (log b x).succ
-/
theorem log_mul_base {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b (n * b) = log b n + 1 := by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self _ hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]
/-
**Nat.pow_log_le_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b x : ℕ), b ^ Nat.log b x ≤ x + 1
参数：b x : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Nat.pow_zero`：∀ (n : ℕ), n ^ 0 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.pow_log_le_self`：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) :
 b ^ log b x <= x
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem pow_log_le_add_one (b : ℕ) : ∀ x, b ^ log b x ≤ x + 1
  | 0 => by rw [log_zero_right, Nat.pow_zero]
  | x + 1 => (pow_log_le_self b x.succ_ne_zero).trans (x + 1).le_succ
/-
**Nat.log_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_monotone {b : Nat} : Monotone (log b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
· 使用定理 `Nat.pow_log_le_add_one`：∀ (b x : ℕ), b ^ Nat.log b x ≤ x + 1
-/
theorem log_monotone {b : ℕ} : Monotone (log b) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)

@[mono, gcongr]
/-
**Nat.log_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_mono_right {b n m : Nat} (h : n <= m) : log b n <= log b m
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_monotone`：log_monotone {b : Nat} : Monotone (log b)
-/
theorem log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
  log_monotone h
/-
**Nat.log_lt_log_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_lt_log_succ_iff {b n : Nat} (hb : 1 < b) (hn : n != 0) : log b n < log
 b (n + 1) ↔ b ^ log b (n + 1) = n + 1
参数：hb : 1 < b；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.pow_log_le_self`：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) :
 b ^ log b x <= x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.zero_ne_add_one`：∀ (n : ℕ), 0 ≠ n + 1
· 使用定理 `Nat.lt_pow_of_log_lt`：lt_pow_of_log_lt {b x y : Nat} (hb : 1 < b) : log 
b y < x -> y < b ^ x
· 使用定理 `Nat.log_lt_of_lt_pow`：log_lt_of_lt_pow {b x y : Nat} (hy : y != 0) : y <
 b ^ x -> log b y < x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem log_lt_log_succ_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n < log b (n + 1) ↔ b ^ log b (n + 1) = n + 1 := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm _ (Nat.lt_pow_of_log_lt hb H)
    exact Nat.pow_log_le_self b (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow hn
    simp [H]
/-
**Nat.log_eq_log_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_eq_log_succ_iff {b n : Nat} (hb : 1 < b) (hn : n != 0) : log b n = log
 b (n + 1) ↔ b ^ log b (n + 1) != n + 1
参数：hb : 1 < b；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.log_lt_log_succ_iff`：log_lt_log_succ_iff {b n : Nat} (hb : 1 < b) (h
n : n != 0) : log b n < log b (n + 1) ↔ b ^ log b (n + 1) = n + 1
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.log_monotone`：log_monotone {b : Nat} : Monotone (log b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem log_eq_log_succ_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n = log b (n + 1) ↔ b ^ log b (n + 1) ≠ n + 1 := by
  rw [ne_eq, ← log_lt_log_succ_iff hb hn, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ log_monotone (le_add_right n 1)
/-
**Nat.log_anti_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <= b) : log b n <= log c 
n
参数：hc : 1 < c；hb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Nat.pow_log_le_self`：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) :
 b ^ log b x <= x
-/
theorem log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n := by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  apply le_log_of_pow_le hc
  calc
    c ^ log b n ≤ b ^ log b n := Nat.pow_le_pow_left hb _
    _ ≤ n := pow_log_le_self _ hn
/-
**Nat.log_antitone_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_antitone_left {n : Nat} : AntitoneOn (fun b => log b n) (Set.Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.log_anti_left`：log_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <= b
) : log b n <= log c n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
-/
theorem log_antitone_left {n : ℕ} : AntitoneOn (fun b => log b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb

@[gcongr, mono]
/-
**Nat.log_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_mono {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn : m <= n) : log b
 m <= log c n
参数：hc : 1 < c；hb : c <= b；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.log_anti_left`：log_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <= b
) : log b n <= log c n
· 使用定理 `Nat.log_mono_right`：log_mono_right {b n m : Nat} (h : n <= m) : log b n 
<= log b m
-/
theorem log_mono {b c m n : ℕ} (hc : 1 < c) (hb : c ≤ b) (hmn : m ≤ n) :
    log b m ≤ log c n :=
  (log_anti_left hc hb).trans <| by gcongr

@[simp]
/-
**Nat.log_div_base** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_div_base (b n : Nat) : log b (n / b) = log b n - 1
参数：b n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.zero_sub`：∀ (n : ℕ), 0 - n = 0
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Nat.log_of_lt`：log_of_lt {b n : Nat} (hb : n < b) : log b n = 0
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Nat.log_of_one_lt_of_le`：log_of_one_lt_of_le {b n : Nat} (h : 1 < b) (hn
 : b <= n) : log b n = log b (n / b) + 1
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h, Nat.add_sub_cancel_right]
/-
**Nat.log_div_base_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log_div_base_pow (b n k : Nat) : log b (n / b ^ k) = log b n - k
参数：b n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用定理 `Nat.log_div_base`：log_div_base (b n : Nat) : log b (n / b) = log b n - 1
· 使用定理 `Nat.sub_add_eq`：∀ (a b c : ℕ), a - (b + c) = a - b - c
-/
lemma log_div_base_pow (b n k : ℕ) : log b (n / b ^ k) = log b n - k := by
  induction k with
  | zero => grind
  | succ k hk => rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, log_div_base, hk, sub_add_eq]

@[simp]
/-
**Nat.log_div_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_div_mul_self (b n : Nat) : log b (n / b * b) = log b n
参数：b n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Nat.log_of_lt`：log_of_lt {b n : Nat} (hb : n < b) : log b n = 0
· 使用定理 `Nat.log_mul_base`：log_mul_base {b n : Nat} (hb : 1 < b) (hn : n != 0) : 
log b (n * b) = log b n + 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.log_div_base`：log_div_base (b n : Nat) : log b (n / b) = log b n - 1
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Nat.log_pos`：log_pos {b n : Nat} (hb : 1 < b) (hbn : b <= n) : 0 < log b
 n
-/
theorem log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by lia)).ne', log_div_base,
    Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]
/-
**Nat.add_pred_div_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_pred_div_lt {b n : Nat} (hb : 1 < b) (hn : 2 <= n) : (n + b - 1) / b <
 n
参数：hb : 1 < b；hn : 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Nat.pred_eq_sub_one`：∀ {n : ℕ}, n.pred = n - 1
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.add_le_mul`：∀ {a : ℕ}, 2 ≤ a → ∀ {b : ℕ}, 2 ≤ b → a + b ≤ a * b
-/
theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (by lia), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (by lia)]
  exact Nat.add_le_mul hn hb
/-
**Nat.log_two_bit** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log_two_bit {b n} (hn : n != 0) : Nat.log 2 (n.bit b) = Nat.log 2 n + 1
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.log_div_mul_self`：log_div_mul_self (b n : Nat) : log b (n / b * b) =
 log b n
· 使用定理 `Nat.bit_div_two`：bit_div_two (b n) : bit b n / 2 = n
· 使用定理 `Nat.log_mul_base`：log_mul_base {b n : Nat} (hb : 1 < b) (hn : n != 0) : 
log b (n * b) = log b n + 1
· 使用定理 `Nat.one_lt_two`：1 < 2
-/
lemma log_two_bit {b n} (hn : n ≠ 0) : Nat.log 2 (n.bit b) = Nat.log 2 n + 1 := by
  rw [← log_div_mul_self, bit_div_two, log_mul_base Nat.one_lt_two hn]
/-
**Nat.log2_eq_log_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log2_eq_log_two {n : Nat} : Nat.log2 n = Nat.log 2 n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log2_zero`：Nat.log2 0 = 0
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Nat.le_log2`：∀ {n k : ℕ}, n ≠ 0 → (k ≤ n.log2 ↔ 2 ^ k ≤ n)
· 使用定理 `Nat.le_log_iff_pow_le`：le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : x <= log b y ↔ b ^ x <= y
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma log2_eq_log_two {n : ℕ} : Nat.log2 n = Nat.log 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn, Nat.le_log_iff_pow_le Nat.one_lt_two hn]

@[simp]
/-
**Nat.log_pow_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log_pow_left (b k n : Nat) : log (b ^ k) n = log b n / k
参数：b k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Nat.log_one_left`：log_one_left : forall n, log 1 n = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Nat.le_log_iff_pow_le`：le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : N
at} (hy : y != 0) : x <= log b y ↔ b ^ x <= y
· 使用定理 `Nat.one_lt_pow`：∀ {n a : ℕ}, n ≠ 0 → 1 < a → 1 < a ^ n
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `Nat.pow_mul'`：∀ (a m n : ℕ), a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.pow_le_one_iff`：∀ {n a : ℕ}, n ≠ 0 → (a ^ n ≤ 1 ↔ a ≤ 1)
-/
lemma log_pow_left (b k n : ℕ) : log (b ^ k) n = log b n / k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rcases Nat.lt_or_ge 1 b with hb | hb
      · refine eq_of_forall_le_iff fun c ↦ ?_
        rw [le_log_iff_pow_le (Nat.one_lt_pow (Nat.ne_of_gt hk) hb) hn, Nat.le_div_iff_mul_le hk,
          le_log_iff_pow_le hb hn, Nat.pow_mul']
      · rw [log_of_left_le_one hb, Nat.zero_div, log_of_left_le_one]
        rwa [Nat.pow_le_one_iff (Nat.ne_of_gt hk)]

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
/-
**Nat.clog** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：clog (b n : Nat) : Nat
参数：b n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns
 the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`.
-/
def clog (b n : ℕ) : ℕ :=
  if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  /-- An auxiliary definition for `Nat.clog`.

  For `n > 1`, `b > 1`, `n ≤ b ^ fuel`, returns `(b ^ clog b n / n, clog b n - 1)`.
  -/
  go : ℕ → ℕ → ℕ × ℕ
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n ≤ b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)
/-
**Nat.clog_of_left_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_of_left_le_one {b : Nat} (hb : b <= 1) (n : Nat) : clog b n = 0
参数：hb : b <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 := by
  grind [clog]
/-
**Nat.clog_of_right_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_of_right_le_one {n : Nat} (hn : n <= 1) (b : Nat) : clog b n = 0
参数：hn : n <= 1；b : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  grind [clog]
/-
**Nat.clog_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), Nat.clog 0 n = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_left_le_one`：clog_of_left_le_one {b : Nat} (hb : b <= 1) (n 
: Nat) : clog b n = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
@[simp] lemma clog_zero_left (n : ℕ) : clog 0 n = 0 := clog_of_left_le_one (Nat.zero_le _) _
/-
**Nat.clog_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : ℕ), Nat.clog b 0 = 0
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_right_le_one`：clog_of_right_le_one {n : Nat} (hn : n <= 1) (
b : Nat) : clog b n = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 := clog_of_right_le_one (Nat.zero_le _) _

@[simp]
/-
**Nat.clog_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_one_left (n : Nat) : clog 1 n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_left_le_one`：clog_of_left_le_one {b : Nat} (hb : b <= 1) (n 
: Nat) : clog b n = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem clog_one_left (n : ℕ) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _

@[simp]
/-
**Nat.clog_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_one_right (b : Nat) : clog b 1 = 0
参数：b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_right_le_one`：clog_of_right_le_one {n : Nat} (hn : n <= 1) (
b : Nat) : clog b n = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _
/-
**Nat.clog.go_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.clog`。
形式化陈述：∀ {n b fuel : ℕ},   1 < n →     1 < b →       n < b ^ fuel →         (Nat.
clog.go n b fuel).1 = b ^ ((Nat.clog.go n b fuel).2 + 1) / n ∧           b ^ (Na
t.clog.go n b fuel).2 < n ∧ n ≤ b ^ ((Nat.clog.go n b fuel).2 + 1)
参数：Nat.clog.go n b fuel；(Nat.clog.go n b fuel).2 + 1；Nat.clog.go n b fuel；(Nat.c
log.go n b fuel).2 + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `Nat.mul_lt_mul_of_lt_of_lt`：∀ {a b c d : ℕ}, a < c → b < d → a * b < c *
 d
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `_private.Mathlib.Data.Nat.Log.0.Nat.log.go_aux`：∀ {n b fuel : ℕ}, 1 < b 
→ n < b ^ (fuel + 1) → b ≤ n → n < (b * b) ^ fuel
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.pow_add_one'`：∀ {m n : ℕ}, m ^ (n + 1) = m * m ^ n
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_div_mul_left`：∀ {m : ℕ} (n k : ℕ), 0 < m → m * n / (m * k) = n /
 k
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.not_le_of_gt`：∀ {n m : ℕ}, n > m → ¬n ≤ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
-/
theorem clog.go_spec {n b fuel} (hn : 1 < n) (hb : 1 < b) (hfuel : n < b ^ fuel) :
    (go n b fuel).1 = b ^ ((go n b fuel).2 + 1) / n ∧
      b ^ (go n b fuel).2 < n ∧ n ≤ b ^ ((go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge b n with
    | inr hbn => simp_all [go]
    | inl hbn =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb)
        (log.go_aux hb hfuel (Nat.le_of_lt hbn)) with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_le_of_gt hbn), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hbn), Nat.div_div_eq_div_mul,
        Nat.mul_comm n b, Nat.mul_add_one, @Nat.pow_add_one' _ (2 * _ + 1),
        Nat.mul_lt_mul_left, Nat.mul_div_mul_left, Nat.zero_lt_of_lt hb]
      split <;> simp_all [Nat.mul_add_one, Nat.pow_add_one']

/-- For `b > 1`, `clog b` and `(b ^ ·)` form a Galois connection.

See also `clog_le_of_le_pow` for the implication that does not require `1 < b`. -/
/-
**Nat.clog_le_iff_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y : Nat} : clog b x <= y ↔ x 
<= b ^ y
参数：hb : 1 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog.fun_cases_unfolding`：∀ (b n : ℕ) (motive : ℕ → Prop),   (1 < b 
∧ 1 < n → motive ((Nat.clog.go n b n).2 + 1)) → (¬(1 < b ∧ 1 < n) → motive 0) → 
motive (Nat.clog b…
· 使用定理 `Nat.clog.go_spec`：∀ {n b fuel : ℕ},   1 < n →     1 < b →       n < b ^ 
fuel →         (Nat.clog.go n b fuel).1 = b ^ ((Nat.clog.go n b fuel).2 + 1) / n
 ∧    …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Nat.not_le_of_gt`：∀ {n m : ℕ}, n > m → ¬n ≤ m
· 使用定理 `Nat.lt_add_one_of_le`：∀ {n m : ℕ}, n ≤ m → n < m + 1
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k

--- 原说明 ---
For `b > 1`, `clog b` and `(b ^ ·)` form a Galois connection.

See also `clog_le_of_le_pow` for the implication that does not require `1 < b`.
-/
theorem clog_le_iff_le_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} : clog b x ≤ y ↔ x ≤ b ^ y := by
  fun_cases clog with
  | case1 h =>
    rcases clog.go_spec h.2 hb (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
    cases Nat.lt_or_ge (clog.go x b x).2 y with
    | inl hy =>
      rw [← Nat.add_one_le_iff] at hy
      exact iff_of_true hy <| Nat.le_trans H₂ <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy
    | inr hy =>
      apply_rules [iff_of_false, Nat.not_le_of_gt, Nat.lt_add_one_of_le]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy) H₁
  | case2 h => grind [Nat.one_le_pow]
/-
**Nat.clog_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_pos {b n : Nat} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n
参数：hb : 1 < b；hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog.eq_1`：∀ (b n : ℕ), Nat.clog b n = if 1 < b ∧ 1 < n then (Nat.cl
og.go n b n).2 + 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n := by
  rw [clog, if_pos]
  exacts [Nat.succ_pos _, ⟨hb, hn⟩]
/-
**Nat.clog_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_of_one_lt {b n : Nat} (hb : 1 < b) (hn : 1 < n) : clog b n = clog b (
(n + b - 1) / b) + 1
参数：hb : 1 < b；hn : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.clog_pos`：clog_pos {b n : Nat} (hb : 1 < b) (hn : 1 < n) : 0 < clog 
b n
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
-/
theorem clog_of_one_lt {b n : ℕ} (hb : 1 < b) (hn : 1 < n) :
    clog b n = clog b ((n + b - 1) / b) + 1 := by
  apply eq_of_forall_ge_iff
  rintro (_ | c)
  · simp [Nat.ne_of_gt <| clog_pos hb hn]
  · simp only [clog_le_iff_le_pow, Nat.pow_add_one, Nat.add_le_add_iff_right, Nat.zero_lt_of_lt hb,
      div_le_iff_le_mul, hb]
    grind
/-
**Nat.clog_of_two_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_of_two_le {b n : Nat} (hb : 1 < b) (hn : 2 <= n) : clog b n = clog b 
((n + b - 1) / b) + 1
参数：hb : 1 < b；hn : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_of_one_lt`：clog_of_one_lt {b n : Nat} (hb : 1 < b) (hn : 1 < n)
 : clog b n = clog b ((n + b - 1) / b) + 1
-/
theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog b n = clog b ((n + b - 1) / b) + 1 :=
  clog_of_one_lt hb hn
/-
**Nat.clog_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_eq_one {b n : Nat} (hn : 2 <= n) (h : n <= b) : clog b n = 1
参数：hn : 2 <= n；h : n <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog_of_two_le`：clog_of_two_le {b n : Nat} (hb : 1 < b) (hn : 2 <= n
) : clog b n = clog b ((n + b - 1) / b) + 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.clog_of_right_le_one`：clog_of_right_le_one {n : Nat} (hn : n <= 1) (
b : Nat) : clog b n = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
-/
theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> lia
/-
**Nat.clog_le_of_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_le_of_le_pow {b x y : Nat} (h : x <= b ^ y) : clog b x <= y
参数：h : x <= b ^ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
-/
theorem clog_le_of_le_pow {b x y : ℕ} (h : x ≤ b ^ y) : clog b x ≤ y := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rwa [clog_le_iff_le_pow hb]
  · grind [clog_of_left_le_one]
/-
**Nat.lt_clog_iff_pow_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_clog_iff_pow_lt {b : Nat} (hb : 1 < b) {x y : Nat} : y < clog b x ↔ b ^
 y < x
参数：hb : 1 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
-/
theorem lt_clog_iff_pow_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} : y < clog b x ↔ b ^ y < x :=
  lt_iff_lt_of_le_iff_le (clog_le_iff_le_pow hb)
/-
**Nat.pow_lt_of_lt_clog** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_lt_of_lt_clog {b x y : Nat} (h : y < clog b x) : b ^ y < x
参数：h : y < clog b x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Nat.clog_le_of_le_pow`：clog_le_of_le_pow {b x y : Nat} (h : x <= b ^ y) 
: clog b x <= y
-/
theorem pow_lt_of_lt_clog {b x y : ℕ} (h : y < clog b x) : b ^ y < x :=
  lt_imp_lt_of_le_imp_le clog_le_of_le_pow h

@[simp]
/-
**Nat.clog_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_pow (b x : Nat) (hb : 1 < b) : clog b (b ^ x) = x
参数：b x : Nat；hb : 1 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
· 使用定理 `Nat.pow_le_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n ≤ a ^ m ↔ n ≤ m)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z ↦ by rw [clog_le_iff_le_pow hb, Nat.pow_le_pow_iff_right hb]
/-
**Nat.pow_pred_clog_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_pred_clog_lt_self {b : Nat} (hb : 1 < b) {x : Nat} (hx : 1 < x) : b ^ 
(clog b x).pred < x
参数：hb : 1 < b；hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_clog_iff_pow_lt`：lt_clog_iff_pow_lt {b : Nat} (hb : 1 < b) {x y :
 Nat} : y < clog b x ↔ b ^ y < x
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.clog_pos`：clog_pos {b n : Nat} (hb : 1 < b) (hn : 1 < n) : 0 < clog 
b n
-/
theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
    b ^ (clog b x).pred < x := by
  rw [← lt_clog_iff_pow_lt hb]
  exact pred_lt (clog_pos hb hx).ne'
/-
**Nat.le_pow_clog** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_pow_clog {b : Nat} (hb : 1 < b) (x : Nat) : x <= b ^ clog b x
参数：hb : 1 < b；x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (clog_le_iff_le_pow hb).1 le_rfl

@[mono, gcongr]
/-
**Nat.clog_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_mono_right (b : Nat) {n m : Nat} (h : n <= m) : clog b n <= clog b m
参数：b : Nat；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog_of_left_le_one`：clog_of_left_le_one {b : Nat} (hb : b <= 1) (n 
: Nat) : clog b n = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_pow_clog`：le_pow_clog {b : Nat} (hb : 1 < b) (x : Nat) : x <= b ^
 clog b x
-/
theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m := by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [clog_le_iff_le_pow hb]
    exact h.trans (le_pow_clog hb _)
/-
**Nat.clog_anti_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <= b) : clog b n <= clog
 c n
参数：hc : 1 < c；hb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog_le_iff_le_pow`：clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y :
 Nat} : clog b x <= y ↔ x <= b ^ y
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.le_pow_clog`：le_pow_clog {b : Nat} (hb : 1 < b) (x : Nat) : x <= b ^
 clog b x
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
-/
theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [clog_le_iff_le_pow (lt_of_lt_of_le hc hb)]
  calc
    n ≤ c ^ clog c n := le_pow_clog hc _
    _ ≤ b ^ clog c n := Nat.pow_le_pow_left hb _
/-
**Nat.clog_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_monotone (b : Nat) : Monotone (clog b)
参数：b : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_mono_right`：clog_mono_right (b : Nat) {n m : Nat} (h : n <= m) 
: clog b n <= clog b m
-/
theorem clog_monotone (b : ℕ) : Monotone (clog b) := fun _ _ => clog_mono_right _
/-
**Nat.clog_antitone_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_antitone_left {n : Nat} : AntitoneOn (fun b : Nat => clog b n) (Set.I
oi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.clog_anti_left`：clog_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <=
 b) : clog b n <= clog c n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
-/
theorem clog_antitone_left {n : ℕ} : AntitoneOn (fun b : ℕ => clog b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb

@[mono, gcongr]
/-
**Nat.clog_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_mono {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn : m <= n) : clog
 b m <= clog c n
参数：hc : 1 < c；hb : c <= b；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.clog_anti_left`：clog_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <=
 b) : clog b n <= clog c n
· 使用定理 `Nat.clog_mono_right`：clog_mono_right (b : Nat) {n m : Nat} (h : n <= m) 
: clog b n <= clog b m
-/
theorem clog_mono {b c m n : ℕ} (hc : 1 < c) (hb : c ≤ b) (hmn : m ≤ n) :
    clog b m ≤ clog c n :=
  (clog_anti_left hc hb).trans <| by gcongr

@[simp]
/-
**Nat.log_le_clog** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：log_le_clog (b n : Nat) : log b n <= clog b n
参数：b n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_le_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n ≤ a ^ m ↔ n ≤ m)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.pow_log_le_self`：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) :
 b ^ log b x <= x
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.le_pow_clog`：le_pow_clog {b : Nat} (hb : 1 < b) (x : Nat) : x <= b ^
 clog b x
-/
theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n := by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (Nat.pow_le_pow_iff_right hb).1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)
/-
**Nat.clog_lt_clog_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_lt_clog_succ_iff {b n : Nat} (hb : 1 < b) : clog b n < clog b (n + 1)
 ↔ b ^ clog b n = n
参数：hb : 1 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_clog_iff_pow_lt`：lt_clog_iff_pow_lt {b : Nat} (hb : 1 < b) {x y :
 Nat} : y < clog b x ↔ b ^ y < x
· 使用定理 `Nat.le_pow_clog`：le_pow_clog {b : Nat} (hb : 1 < b) (x : Nat) : x <= b ^
 clog b x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
-/
theorem clog_lt_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n < clog b (n + 1) ↔ b ^ clog b n = n := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm _ (le_pow_clog hb n)
    apply le_of_lt_succ
    exact (lt_clog_iff_pow_lt hb).mp H
  · rw [lt_clog_iff_pow_lt hb, H]
    exact n.lt_add_one
/-
**Nat.clog_eq_clog_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_eq_clog_succ_iff {b n : Nat} (hb : 1 < b) : clog b n = clog b (n + 1)
 ↔ b ^ clog b n != n
参数：hb : 1 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.clog_lt_clog_succ_iff`：clog_lt_clog_succ_iff {b n : Nat} (hb : 1 < b
) : clog b n < clog b (n + 1) ↔ b ^ clog b n = n
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.clog_monotone`：clog_monotone (b : Nat) : Monotone (clog b)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem clog_eq_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n = clog b (n + 1) ↔ b ^ clog b n ≠ n := by
  rw [ne_eq, ← clog_lt_clog_succ_iff hb, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ clog_monotone b (le_add_right n 1)

/-- This lemma says that `⌈log (b ^ k) n⌉ = ⌈(⌈log b n⌉ / k)⌉`, using operations on natural numbers
to express this equality.

Since Lean has no dedicated function for the ceiling division,
we use `(a + (b - 1)) / b` for `⌈a / b⌉`. -/
/-
**Nat.clog_pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：clog_pow_left (b k n : Nat) : clog (b ^ k) n = (clog b n + (k - 1)) / k
参数：b k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.clog_one_left`：clog_one_left (n : Nat) : clog 1 n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `eq_of_forall_lt_iff`：eq_of_forall_lt_iff (h : forall c, c < a ↔ c < b) :
 a = b
· 使用定理 `Nat.lt_clog_iff_pow_lt`：lt_clog_iff_pow_lt {b : Nat} (hb : 1 < b) {x y :
 Nat} : y < clog b x ↔ b ^ y < x
· 使用定理 `Nat.one_lt_pow`：∀ {n a : ℕ}, n ≠ 0 → 1 < a → 1 < a ^ n
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.lt_div_iff_mul_lt`：∀ {k x y : ℕ}, 0 < k → (x < y / k ↔ x * k < y - (
k - 1))
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Nat.pow_mul'`：∀ (a m n : ℕ), a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0

--- 原说明 ---
This lemma says that `⌈log (b ^ k) n⌉ = ⌈(⌈log b n⌉ / k)⌉`, using operations on 
natural numbers
to express this equality.

Since Lean has no dedicated function for the ceiling division,
we use `(a + (b - 1)) / b` for `⌈a / b⌉`.
-/
theorem clog_pow_left (b k n : ℕ) : clog (b ^ k) n = (clog b n + (k - 1)) / k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · rcases Nat.lt_or_ge 1 b with hb | hb
    · refine eq_of_forall_lt_iff fun c ↦ ?_
      rw [lt_clog_iff_pow_lt (Nat.one_lt_pow (Nat.ne_of_gt hk) hb), Nat.lt_div_iff_mul_lt hk,
        Nat.add_sub_cancel, lt_clog_iff_pow_lt hb, Nat.pow_mul']
    · suffices (k - 1) / k = 0 by grind [clog_of_left_le_one, Nat.pow_le_one_iff]
      apply Nat.div_eq_of_lt
      grind

end Nat

