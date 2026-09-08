/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Batteries.Logic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.DepRewrite

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries easily.
-/

@[expose] public section

open Nat

namespace Int

variable {a b c d m n : ℤ}

/-
**Int.neg_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {a b : ℤ}, -a = -b → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.neg_inj`：∀ {a b : ℤ}, -a = -b ↔ a = b
-/
protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
/-
**Int.succ** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：succ (a : Int)
参数：a : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Immediate successor of an integer: `succ n = n + 1`
-/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
/-
**Int.pred** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：pred (a : Int)
参数：a : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Immediate predecessor of an integer: `pred n = n - 1`
-/
def pred (a : ℤ) := a - 1
/-
**Int.pred_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：pred_succ (a : Int) : pred (succ a) = a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_sub_cancel`：∀ (a b : ℤ), a + b - b = a
-/
lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _
/-
**Int.succ_pred** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：succ_pred (a : Int) : succ (pred a) = a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.sub_add_cancel`：∀ (a b : ℤ), a - b + b = a
-/
lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _
/-
**Int.neg_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：neg_succ (a : Int) : -succ a = pred (-a)
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.neg_add`：∀ {a b : ℤ}, -(a + b) = -a + -b
-/
lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add
/-
**Int.succ_neg_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：succ_neg_succ (a : Int) : succ (-succ a) = -a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.neg_succ`：neg_succ (a : Int) : -succ a = pred (-a)
· 使用引理 `Int.succ_pred`：succ_pred (a : Int) : succ (pred a) = a
-/
lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]
/-
**Int.neg_pred** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：neg_pred (a : Int) : -pred a = succ (-a)
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.neg_eq_comm`：∀ {a b : ℤ}, -a = b ↔ -b = a
· 使用引理 `Int.neg_succ`：neg_succ (a : Int) : -succ a = pred (-a)
· 使用定理 `Int.neg_neg`：∀ (a : ℤ), - -a = a
-/
lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]
/-
**Int.pred_neg_pred** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：pred_neg_pred (a : Int) : pred (-pred a) = -a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.neg_pred`：neg_pred (a : Int) : -pred a = succ (-a)
· 使用引理 `Int.pred_succ`：pred_succ (a : Int) : pred (succ a) = a
-/
lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]
/-
**Int.pred_nat_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：pred_nat_succ (n : Nat) : pred (Nat.succ n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.pred_succ`：pred_succ (a : Int) : pred (succ a) = a
-/
lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n
/-
**Int.neg_nat_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：neg_nat_succ (n : Nat) : -(Nat.succ n : Int) = pred (-n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.neg_succ`：neg_succ (a : Int) : -succ a = pred (-a)
-/
lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n
/-
**Int.succ_neg_natCast_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：succ_neg_natCast_succ (n : Nat) : succ (-Nat.succ n) = -n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.succ_neg_succ`：succ_neg_succ (a : Int) : succ (-succ a) = -a
-/
lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n
/-
**Int.natCast_pred_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℕ}, 0 < n → ↑(n - 1) = ↑n - 1
参数：n - 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  grind
/-
**Int.lt_succ_self** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：lt_succ_self (a : Int) : a < succ a
参数：a : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_succ_self (a : ℤ) : a < succ a := by unfold succ; lia
/-
**Int.pred_self_lt** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：pred_self_lt (a : Int) : pred a < a
参数：a : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pred_self_lt (a : ℤ) : pred a < a := by unfold pred; lia

/--
Induction on integers: prove a proposition `p i` by proving the base case `p 0`,
the upwards induction step `p i → p (i + 1)` and the downwards induction step `p (-i) → p (-i - 1)`.

It is used as the default induction principle for the `induction` tactic.
-/
/-
**Int.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ), motive ↑i → motive
 (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → motive i
参数：i : ℤ；∀ (i : ℕ), motive ↑i → motive (↑i + 1)；∀ (i : ℕ), motive (-↑i) → motive
 (-↑i - 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.neg_add`：∀ {a b : ℤ}, -(a + b) = -a + -b

--- 原说明 ---
Induction on integers: prove a proposition `p i` by proving the base case `p 0`,
the upwards induction step `p i → p (i + 1)` and the downwards induction step `p
 (-i) → p (-i - 1)`.

It is used as the default induction principle for the `induction` tactic.
-/
@[elab_as_elim, induction_eliminator] protected lemma induction_on {motive : ℤ → Prop} (i : ℤ)
    (zero : motive 0) (succ : ∀ i : ℕ, motive i → motive (i + 1))
    (pred : ∀ i : ℕ, motive (-i) → motive (-i - 1)) : motive i := by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact zero
    | succ i ih => exact succ _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, motive (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [zero]
    | succ n ih => simpa [natCast_succ, Int.neg_add, Int.sub_eq_add_neg] using pred _ ih

section inductionOn'

variable {motive : ℤ → Sort*} (z b : ℤ) (zero : motive b)
  (succ : ∀ k, b ≤ k → motive k → motive (k + 1)) (pred : ∀ k ≤ b, motive k → motive (k - 1))

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
/-
**Int.inductionOn'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：inductionOn'_self : b.inductionOn' b zero succ pred = zero
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a 
number greater
than `b`, and the `pred` of a number less than `b`.
-/
@[elab_as_elim] protected def inductionOn' : motive z :=
  cast (congrArg motive <| show b + (z - b) = z by lia) <|
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, motive (b + n)
  | 0 => cast (by simp) zero
  | n + 1 => cast (by lia) <| succ _ (Int.le_add_of_nonneg_right (natCast_nonneg _)) (pos n)
  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, motive (b + -[n+1])
  | 0 => pred _ Int.le_rfl zero
  | n + 1 => cast (by lia) <| pred _ (by lia) (neg n)

variable {z b zero succ pred}
/-
**Int.inductionOn'_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {motive : ℤ → Sort u_1} {b : ℤ} {zero : motive b} {succ : (k : ℤ) → b ≤ 
k → motive k → motive (k + 1)}   {pred : (k : ℤ) → k ≤ b → motive k → motive (k 
- 1)}, Int.inductionOn' b b zero succ pred = zero
参数：k : ℤ；k + 1；k : ℤ；k - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.sub_self`：∀ (a : ℤ), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma inductionOn'_self : b.inductionOn' b zero succ pred = zero :=
  cast_eq_iff_heq.mpr <| .symm <| by rw [b.sub_self, ← cast_eq_iff_heq]; rfl
/-
**Int.inductionOn'_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {motive : ℤ → Sort u_1} {z b : ℤ} {zero : motive b} {succ : (k : ℤ) → b 
≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) → k ≤ b → motive k → motive (
k - 1)} (hz : b ≤ z),   Int.inductionOn' (z + 1) b zero succ pred = succ z hz (I
nt.inductionOn' z b zero succ pred)
参数：k : ℤ；k + 1；k : ℤ；k - 1；hz : b ≤ z；z + 1；Int.inductionOn' z b zero succ pred。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
-/
theorem inductionOn'_add_one (hz : b ≤ z) :
    (z + 1).inductionOn' b zero succ pred = succ z hz (z.inductionOn' b zero succ pred) := by
  unfold Int.inductionOn'
  rw! [show z - b = (z - b).toNat by lia, show z + 1 - b = ((z - b).toNat + 1 : ℕ) by lia]
  grind [inductionOn'.pos, show b + (z - b).toNat = z by lia]
/-
**Int.inductionOn'_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {motive : ℤ → Sort u_1} {z b : ℤ} {zero : motive b} {succ : (k : ℤ) → b 
≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) → k ≤ b → motive k → motive (
k - 1)} (hz : z ≤ b),   Int.inductionOn' (z - 1) b zero succ pred = pred z hz (I
nt.inductionOn' z b zero succ pred)
参数：k : ℤ；k + 1；k : ℤ；k - 1；hz : z ≤ b；z - 1；Int.inductionOn' z b zero succ pred。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `Int.le_rfl`：∀ {a : ℤ}, a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `cast.congr_simp`：∀ {α β : Sort u} (h : α = β) (a a_1 : α), a = a_1 → cas
t h a = cast h a_1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.inductionOn'.neg.eq_def`：∀ {motive : ℤ → Sort u_1} (b : ℤ) (zero : m
otive b) (pred : (k : ℤ) → k ≤ b → motive k → motive (k - 1)) (n : ℕ),   Int.ind
uctionOn'.neg b z…
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
-/
theorem inductionOn'_sub_one (hz : z ≤ b) :
    (z - 1).inductionOn' b zero succ pred = pred z hz (z.inductionOn' b zero succ pred) := by
  unfold Int.inductionOn'
  conv => lhs; unfold inductionOn'.neg
  by_cases z = b
  · rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = 0 by lia]
    grind [inductionOn'.pos]
  rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = -[(b - z - 1).toNat+1] by lia]
  grind

end inductionOn'

/-- Inductively define a function on `ℤ` by defining it on `ℕ` and extending it from `n` to `-n`. -/
/-
**Int.negInduction** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：{motive : ℤ → Sort u_1} → ((n : ℕ) → motive ↑n) → (((n : ℕ) → motive ↑n) →
 (n : ℕ) → motive (-↑n)) → (n : ℤ) → motive n
参数：(n : ℕ) → motive ↑n；((n : ℕ) → motive ↑n) → (n : ℕ) → motive (-↑n)；n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductively define a function on `ℤ` by defining it on `ℕ` and extending it from
 `n` to `-n`.
-/
@[elab_as_elim] protected def negInduction {motive : ℤ → Sort*} (nat : ∀ n : ℕ, motive n)
    (neg : (∀ n : ℕ, motive n) → ∀ n : ℕ, motive (-n)) : ∀ n : ℤ, motive n
  | .ofNat n => nat n
  | .negSucc n => neg nat <| n + 1

/-- See `Int.inductionOn'` for an induction in both directions. -/
@[elab_as_elim]
/-
**Int.leInduction** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：{m : ℤ} →   {motive : (n : ℤ) → m ≤ n → Sort u_1} →     motive m ⋯ → ((n :
 ℤ) → (hmn : m ≤ n) → motive n hmn → motive (n + 1) ⋯) → (n : ℤ) → (hmn : m ≤ n)
 → motive n hmn
参数：n : ℤ；(n : ℤ) → (hmn : m ≤ n) → motive n hmn → motive (n + 1) ⋯；n : ℤ；hmn : m
 ≤ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用定理 `Int.le_add_one`：∀ {a b : ℤ}, a ≤ b → a ≤ b + 1
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero

--- 原说明 ---
See `Int.inductionOn'` for an induction in both directions.
-/
protected def leInduction {m : ℤ} {motive : ∀ n, m ≤ n → Sort*} (base : motive m m.le_refl)
    (succ : ∀ n hmn, motive n hmn → motive (n + 1) (le_add_one hmn)) : ∀ n hmn, motive n hmn :=
  fun n ↦ n.inductionOn' m
    (fun _ ↦ base) (fun k hle ih _ ↦ succ k hle <| ih hle) (fun _ _ _ _ ↦ False.elim <| by lia)

@[deprecated (since := "2026-03-25")] protected alias le_induction := Int.leInduction
/-
**Int.leInduction_base** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：leInduction_base {m : Int} {motive : forall n, m <= n -> Sort*} (base : mo
tive m m.le_refl) (succ : forall n hmn, motive n hmn -> motive (n + 1) (le_add_o
ne hmn)) : Int.leInduction (motive
参数：base : motive m m.le_refl；succ : forall n hmn, motive n hmn -> motive (n + 1)
 (le_add_one hmn)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用定理 `Int.le_add_one`：∀ {a b : ℤ}, a ≤ b → a ≤ b + 1
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.leInduction.eq_1`：∀ {m : ℤ} {motive : (n : ℤ) → m ≤ n → Sort u_1} (b
ase : motive m ⋯)   (succ : (n : ℤ) → (hmn : m ≤ n) → motive n hmn → motive (n +
 1) ⋯) (n …
· 使用定理 `Int.inductionOn'_self`：∀ {motive : ℤ → Sort u_1} {b : ℤ} {zero : motive 
b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) → k ≤ 
b → motive …
-/
theorem leInduction_base {m : ℤ} {motive : ∀ n, m ≤ n → Sort*} (base : motive m m.le_refl)
    (succ : ∀ n hmn, motive n hmn → motive (n + 1) (le_add_one hmn)) :
    Int.leInduction (motive := motive) base succ m m.le_refl = base := by
  rw [Int.leInduction, inductionOn'_self]
/-
**Int.leInduction_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：leInduction_add_one {m : Int} {motive : forall n, m <= n -> Sort*} (base :
 motive m m.le_refl) (succ : forall n hmn, motive n hmn -> motive (n + 1) (le_ad
d_one hmn)) (n : Int) (hmn : m <= n) : Int.leInduction (motive
参数：base : motive m m.le_refl；succ : forall n hmn, motive n hmn -> motive (n + 1)
 (le_add_one hmn)；n : Int；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用定理 `Int.le_add_one`：∀ {a b : ℤ}, a ≤ b → a ≤ b + 1
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.leInduction.eq_1`：∀ {m : ℤ} {motive : (n : ℤ) → m ≤ n → Sort u_1} (b
ase : motive m ⋯)   (succ : (n : ℤ) → (hmn : m ≤ n) → motive n hmn → motive (n +
 1) ⋯) (n …
· 使用定理 `Int.inductionOn'_add_one`：∀ {motive : ℤ → Sort u_1} {z b : ℤ} {zero : mo
tive b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) →
 k ≤ b → motiv…
-/
theorem leInduction_add_one {m : ℤ} {motive : ∀ n, m ≤ n → Sort*} (base : motive m m.le_refl)
    (succ : ∀ n hmn, motive n hmn → motive (n + 1) (le_add_one hmn)) (n : ℤ) (hmn : m ≤ n) :
    Int.leInduction (motive := motive) base succ (n + 1) (by lia) =
      succ n hmn (Int.leInduction (motive := motive) base succ n hmn) := by
  rw [Int.leInduction, inductionOn'_add_one hmn]
  rfl

/-- See `Int.inductionOn'` for an induction in both directions. -/
@[elab_as_elim]
/-
**Int.leInductionDown** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：{m : ℤ} →   {motive : (n : ℤ) → n ≤ m → Sort u_1} →     motive m ⋯ → ((n :
 ℤ) → (hnm : n ≤ m) → motive n hnm → motive (n - 1) ⋯) → (n : ℤ) → (hnm : n ≤ m)
 → motive n hnm
参数：n : ℤ；(n : ℤ) → (hnm : n ≤ m) → motive n hnm → motive (n - 1) ⋯；n : ℤ；hnm : n
 ≤ m。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero

--- 原说明 ---
See `Int.inductionOn'` for an induction in both directions.
-/
protected def leInductionDown {m : ℤ} {motive : ∀ n, n ≤ m → Sort*} (base : motive m m.le_refl)
    (pred : ∀ n hnm, motive n hnm → motive (n - 1) (by lia)) : ∀ n hnm, motive n hnm :=
  fun n ↦ n.inductionOn' m
    (fun _ ↦ base) (fun _ _ _ _ ↦ False.elim <| by lia) (fun k hle ih _ ↦ pred k hle <| ih hle)
/-
**Int.leInductionDown_base** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：leInductionDown_base {m : Int} {motive : forall n, n <= m -> Sort*} (base 
: motive m m.le_refl) (pred : forall n hnm, motive n hnm -> motive (n - 1) (by l
ia)) : Int.leInductionDown (motive
参数：base : motive m m.le_refl；pred : forall n hnm, motive n hnm -> motive (n - 1)
 (by lia)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.leInductionDown.eq_1`：∀ {m : ℤ} {motive : (n : ℤ) → n ≤ m → Sort u_1
} (base : motive m ⋯)   (pred : (n : ℤ) → (hnm : n ≤ m) → motive n hnm → motive 
(n - 1) ⋯) (n …
· 使用定理 `Int.inductionOn'_self`：∀ {motive : ℤ → Sort u_1} {b : ℤ} {zero : motive 
b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) → k ≤ 
b → motive …
-/
theorem leInductionDown_base {m : ℤ} {motive : ∀ n, n ≤ m → Sort*} (base : motive m m.le_refl)
    (pred : ∀ n hnm, motive n hnm → motive (n - 1) (by lia)) :
    Int.leInductionDown (motive := motive) base pred m m.le_refl = base := by
  rw [Int.leInductionDown, inductionOn'_self]
/-
**Int.leInductionDown_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：leInductionDown_sub_one {m : Int} {motive : forall n, n <= m -> Sort*} (ba
se : motive m m.le_refl) (pred : forall n hnm, motive n hnm -> motive (n - 1) (b
y lia)) (n : Int) (hnm : n <= m) : Int.leInductionDown (motive
参数：base : motive m m.le_refl；pred : forall n hnm, motive n hnm -> motive (n - 1)
 (by lia)；n : Int；hnm : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.leInductionDown.eq_1`：∀ {m : ℤ} {motive : (n : ℤ) → n ≤ m → Sort u_1
} (base : motive m ⋯)   (pred : (n : ℤ) → (hnm : n ≤ m) → motive n hnm → motive 
(n - 1) ⋯) (n …
· 使用定理 `Int.inductionOn'_sub_one`：∀ {motive : ℤ → Sort u_1} {z b : ℤ} {zero : mo
tive b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) →
 k ≤ b → motiv…
-/
theorem leInductionDown_sub_one {m : ℤ} {motive : ∀ n, n ≤ m → Sort*} (base : motive m m.le_refl)
    (pred : ∀ n hnm, motive n hnm → motive (n - 1) (by lia)) (n : ℤ) (hnm : n ≤ m) :
    Int.leInductionDown (motive := motive) base pred (n - 1) (by lia) =
      pred n hnm (Int.leInductionDown (motive := motive) base pred n hnm) := by
  rw [Int.leInductionDown, inductionOn'_sub_one hnm]
  rfl

@[deprecated (since := "2026-03-25")] protected alias le_induction_down := Int.leInductionDown

section strongRec

variable {motive : ℤ → Sort*} (lt : ∀ n < m, motive n)
  (ge : ∀ n ≥ m, (∀ k < n, motive k) → motive n)

/-- A strong recursor for `Int` that specifies explicit values for integers below a threshold,
and is analogous to `Nat.strongRec` for integers on or above the threshold. -/
/-
**Int.strongRec** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：{m : ℤ} →   {motive : ℤ → Sort u_1} →     ((n : ℤ) → n < m → motive n) → (
(n : ℤ) → n ≥ m → ((k : ℤ) → k < n → motive k) → motive n) → (n : ℤ) → motive n
参数：(n : ℤ) → n < m → motive n；(n : ℤ) → n ≥ m → ((k : ℤ) → k < n → motive k) → m
otive n；n : ℤ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero

--- 原说明 ---
A strong recursor for `Int` that specifies explicit values for integers below a 
threshold,
and is analogous to `Nat.strongRec` for integers on or above the threshold.
-/
@[elab_as_elim] protected def strongRec (n : ℤ) : motive n := by
  refine if hnm : n < m then lt n hnm else ge n (by lia) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by lia) fun k _ ↦ ih k (by lia)
  · exact fun n _ hn l _ ↦ hn l (by lia)

variable {lt ge}
/-
**Int.strongRec_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：strongRec_of_lt (hn : n < m) : m.strongRec lt ge n = lt n hn
参数：hn : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
-/
lemma strongRec_of_lt (hn : n < m) : m.strongRec lt ge n = lt n hn := dif_pos _

end strongRec

/-! ### mul -/

/-! ### natAbs -/

alias natAbs_sq := natAbs_pow_two

/-
**Int.sign_mul_self_eq_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sign_mul_self_eq_natAbs (a : Int) : sign a * a = natAbs a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.sign_mul_self`：∀ (i : ℤ), i.sign * i = ↑i.natAbs
-/
theorem sign_mul_self_eq_natAbs (a : Int) : sign a * a = natAbs a :=
  sign_mul_self a

/-! ### `/` -/

/-
**Int.natCast_div** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natCast_div (m n : Nat) : ((m / n : Nat) : Int) = m / n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_ediv`：∀ (m n : ℕ), ↑(m / n) = ↑m / ↑n

--- 原说明 ---
### `/`
-/
lemma natCast_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := natCast_ediv m n
/-
**Int.ediv_of_neg_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：ediv_of_neg_of_pos {a b : Int} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-
a - 1) / b + 1)
参数：Ha : a < 0；Hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_negSucc_of_lt_zero`：∀ {a : ℤ}, a < 0 → ∃ n, a = Int.negSucc n
· 使用定理 `Int.eq_succ_of_zero_lt`：∀ {a : ℤ}, 0 < a → ∃ n, a = ↑n + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_sub_cancel`：∀ (a b : ℤ), a + b - b = a
-/
lemma ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [Int.add_sub_cancel]; rfl

/-! ### mod -/

/-
**Int.natCast_mod** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m n : ℕ), ↑(m % n) = ↑m % ↑n
参数：m n : ℕ；m % n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### mod
-/
@[simp, norm_cast] lemma natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl
/-
**Int.div_le_iff_of_dvd_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_le_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b <= c ↔ a <= b 
* c
参数：hb : 0 < b；hba : b ∣ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_le_iff_of_dvd_of_pos`：∀ {a b c : ℤ}, 0 < b → b ∣ a → (a / b ≤ c
 ↔ a ≤ b * c)

--- 原说明 ---
### mod
-/
lemma div_le_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b ≤ c ↔ a ≤ b * c :=
  ediv_le_iff_of_dvd_of_pos hb hba
/-
**Int.div_le_iff_of_dvd_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_le_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b <= c ↔ b * c <
= a
参数：hb : b < 0；hba : b ∣ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_le_iff_of_dvd_of_neg`：∀ {a b c : ℤ}, b < 0 → b ∣ a → (a / b ≤ c
 ↔ b * c ≤ a)
-/
lemma div_le_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b ≤ c ↔ b * c ≤ a :=
  ediv_le_iff_of_dvd_of_neg hb hba
/-
**Int.div_lt_iff_of_dvd_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_lt_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b < c ↔ a < b * 
c
参数：hb : 0 < b；hba : b ∣ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_lt_iff_of_dvd_of_pos`：∀ {a b c : ℤ}, 0 < b → b ∣ a → (a / b < c
 ↔ a < b * c)
-/
lemma div_lt_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b < c ↔ a < b * c :=
  ediv_lt_iff_of_dvd_of_pos hb hba
/-
**Int.div_lt_iff_of_dvd_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_lt_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b < c ↔ b * c < 
a
参数：hb : b < 0；hba : b ∣ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_lt_iff_of_dvd_of_neg`：∀ {a b c : ℤ}, b < 0 → b ∣ a → (a / b < c
 ↔ b * c < a)
-/
lemma div_lt_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b < c ↔ b * c < a :=
  ediv_lt_iff_of_dvd_of_neg hb hba
/-
**Int.le_div_iff_of_dvd_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：le_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a <= b / c ↔ c * a <
= b
参数：hc : 0 < c；hcb : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_ediv_iff_of_dvd_of_pos`：∀ {a b c : ℤ}, 0 < c → c ∣ b → (a ≤ b / c
 ↔ c * a ≤ b)
-/
lemma le_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a ≤ b / c ↔ c * a ≤ b :=
  le_ediv_iff_of_dvd_of_pos hc hcb
/-
**Int.le_div_iff_of_dvd_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：le_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a <= b / c ↔ b <= c 
* a
参数：hc : c < 0；hcb : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_ediv_iff_of_dvd_of_neg`：∀ {a b c : ℤ}, c < 0 → c ∣ b → (a ≤ b / c
 ↔ b ≤ c * a)
-/
lemma le_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a ≤ b / c ↔ b ≤ c * a :=
  le_ediv_iff_of_dvd_of_neg hc hcb
/-
**Int.lt_div_iff_of_dvd_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：lt_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a < b / c ↔ c * a < 
b
参数：hc : 0 < c；hcb : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.lt_ediv_iff_of_dvd_of_pos`：∀ {a b c : ℤ}, 0 < c → c ∣ b → (a < b / c
 ↔ c * a < b)
-/
lemma lt_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a < b / c ↔ c * a < b :=
  lt_ediv_iff_of_dvd_of_pos hc hcb
/-
**Int.lt_div_iff_of_dvd_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：lt_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a < b / c ↔ b < c * 
a
参数：hc : c < 0；hcb : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.lt_ediv_iff_of_dvd_of_neg`：∀ {a b c : ℤ}, c < 0 → c ∣ b → (a < b / c
 ↔ b < c * a)
-/
lemma lt_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a < b / c ↔ b < c * a :=
  lt_ediv_iff_of_dvd_of_neg hc hcb
/-
**Int.div_le_div_iff_of_dvd_of_pos_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_le_div_iff_of_dvd_of_pos_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a
) (hdc : d ∣ c) : a / b <= c / d ↔ d * a <= c * b
参数：hb : 0 < b；hd : 0 < d；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_le_ediv_iff_of_dvd_of_pos_of_pos`：∀ {a b c d : ℤ}, 0 < b → 0 < 
d → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b)
-/
lemma div_le_div_iff_of_dvd_of_pos_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤ c / d ↔ d * a ≤ c * b :=
  ediv_le_ediv_iff_of_dvd_of_pos_of_pos hb hd hba hdc
/-
**Int.div_le_div_iff_of_dvd_of_pos_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_le_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a
) (hdc : d ∣ c) : a / b <= c / d ↔ c * b <= d * a
参数：hb : 0 < b；hd : d < 0；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_le_ediv_iff_of_dvd_of_pos_of_neg`：∀ {a b c d : ℤ}, 0 < b → d < 
0 → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a)
-/
lemma div_le_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ c * b ≤ d * a :=
  ediv_le_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc
/-
**Int.div_le_div_iff_of_dvd_of_neg_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_le_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a
) (hdc : d ∣ c) : a / b <= c / d ↔ c * b <= d * a
参数：hb : b < 0；hd : 0 < d；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_le_ediv_iff_of_dvd_of_neg_of_pos`：∀ {a b c d : ℤ}, b < 0 → 0 < 
d → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a)
-/
lemma div_le_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ c * b ≤ d * a :=
  ediv_le_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc
/-
**Int.div_le_div_iff_of_dvd_of_neg_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_le_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a
) (hdc : d ∣ c) : a / b <= c / d ↔ d * a <= c * b
参数：hb : b < 0；hd : d < 0；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_le_ediv_iff_of_dvd_of_neg_of_neg`：∀ {a b c d : ℤ}, b < 0 → d < 
0 → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b)
-/
lemma div_le_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ d * a ≤ c * b :=
  ediv_le_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc
/-
**Int.div_lt_div_iff_of_dvd_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_lt_div_iff_of_dvd_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc 
: d ∣ c) : a / b < c / d ↔ d * a < c * b
参数：hb : 0 < b；hd : 0 < d；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_lt_ediv_iff_of_dvd_of_pos`：∀ {a b c d : ℤ}, 0 < b → 0 < d → b ∣
 a → d ∣ c → (a / b < c / d ↔ d * a < c * b)
-/
lemma div_lt_div_iff_of_dvd_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b :=
  ediv_lt_ediv_iff_of_dvd_of_pos hb hd hba hdc
/-
**Int.div_lt_div_iff_of_dvd_of_pos_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_lt_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a
) (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a
参数：hb : 0 < b；hd : d < 0；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg`：∀ {a b c d : ℤ}, 0 < b → d < 
0 → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a)
-/
lemma div_lt_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a :=
  ediv_lt_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc
/-
**Int.div_lt_div_iff_of_dvd_of_neg_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_lt_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a
) (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a
参数：hb : b < 0；hd : 0 < d；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_lt_ediv_iff_of_dvd_of_neg_of_pos`：∀ {a b c d : ℤ}, b < 0 → 0 < 
d → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a)
-/
lemma div_lt_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a :=
  ediv_lt_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc
/-
**Int.div_lt_div_iff_of_dvd_of_neg_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_lt_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a
) (hdc : d ∣ c) : a / b < c / d ↔ d * a < c * b
参数：hb : b < 0；hd : d < 0；hba : b ∣ a；hdc : d ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_lt_ediv_iff_of_dvd_of_neg_of_neg`：∀ {a b c d : ℤ}, b < 0 → d < 
0 → b ∣ a → d ∣ c → (a / b < c / d ↔ d * a < c * b)
-/
lemma div_lt_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b :=
  ediv_lt_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

/-! ### properties of `/` and `%` -/

/-
**Int.emod_two_eq_zero_or_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：emod_two_eq_zero_or_one (n : Int) : n % 2 = 0 ∨ n % 2 = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.emod_two_eq`：∀ (x : ℤ), x % 2 = 0 ∨ x % 2 = 1

--- 原说明 ---
### properties of `/` and `%`
-/
lemma emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
  emod_two_eq n

/-! ### dvd -/

/-
**Int.dvd_mul_of_div_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c
参数：h : b ∣ a；hdiv : a / b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.dvd_mul_of_ediv_dvd`：∀ {a b c : ℤ}, b ∣ a → a / b ∣ c → a ∣ b * c

--- 原说明 ---
### dvd
-/
lemma dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c :=
  dvd_mul_of_ediv_dvd h hdiv
/-
**Int.div_dvd_iff_dvd_mul** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b != 0) : a / b ∣ c ↔ a ∣ b * c
参数：h : b ∣ a；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ediv_dvd_iff_dvd_mul`：∀ {a b c : ℤ}, b ∣ a → b ≠ 0 → (a / b ∣ c ↔ a 
∣ b * c)
-/
lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b ≠ 0) : a / b ∣ c ↔ a ∣ b * c :=
  ediv_dvd_iff_dvd_mul h hb
/-
**Int.mul_dvd_of_dvd_div** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b
参数：hcb : c ∣ b；h : a ∣ b / c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.mul_dvd_of_dvd_ediv`：∀ {a b c : ℤ}, c ∣ b → a ∣ b / c → c * a ∣ b
-/
lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  mul_dvd_of_dvd_ediv hcb h
/-
**Int.dvd_div_of_mul_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a
参数：h : a * b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.dvd_ediv_of_mul_dvd`：∀ {a b c : ℤ}, a * b ∣ c → b ∣ c / a
-/
lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a :=
  dvd_ediv_of_mul_dvd h
/-
**Int.dvd_div_iff_mul_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b
参数：hbc : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b := by
  simp [hbc]

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
/-
**Int.exists_lt_and_lt_iff_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：exists_lt_and_lt_iff_not_dvd (m : Int) (hn : 0 < n) : (exists k, n * k < m
 ∧ m < n * (k + 1)) ↔ ¬n ∣ m
参数：m : Int；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.not_dvd_iff_lt_mul_succ`：∀ {n : ℤ} (m : ℤ), 0 < n → (¬n ∣ m ↔ ∃ k, n
 * k < m ∧ m < n * (k + 1))

--- 原说明 ---
If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (
k + 1)`
  for some `k`.
-/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m :=
  (not_dvd_iff_lt_mul_succ m hn).symm
/-
**Int.eq_mul_div_of_mul_eq_mul_of_dvd_left** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b != 0) (hbc : b ∣ c) (h : b * 
a = c * d) : a = c / b * d
参数：hb : b != 0；hbc : b ∣ c；h : b * a = c * d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_ediv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → a * b / a = b
· 使用定理 `Int.mul_eq_mul_left_iff`：∀ {a b c : ℤ}, c ≠ 0 → (c * a = c * b ↔ a = b)
· 使用定理 `Int.mul_assoc`：∀ (a b c : ℤ), a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = c / b * d := by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h
/-
**Int.ofNat_add_negSucc_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：ofNat_add_negSucc_of_ge {m n : Nat} (h : n.succ <= m) : ofNat m + -[n+1] =
 ofNat (m - n.succ)
参数：h : n.succ <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.negSucc_eq`：∀ (n : ℕ), Int.negSucc n = -(↑n + 1)
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_one`：↑1 = 1
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Int.sub_eq_add_neg`：∀ {a b : ℤ}, a - b = a + -b
· 使用定理 `Int.natCast_sub`：∀ {n m : ℕ}, n ≤ m → ↑(m - n) = ↑m - ↑n
-/
lemma ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq, ofNat_eq_natCast, ofNat_eq_natCast, ← Int.natCast_one, ← Int.natCast_add,
    ← Int.sub_eq_add_neg, ← Int.natCast_sub h]

/-! #### `/` and ordering -/

/-
**Int.le_iff_pos_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a <= b ↔ 0 < b
参数：ha : 0 < a；hab : a ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.lt_of_lt_of_le`：∀ {a b c : ℤ}, a < b → b ≤ c → a < c
· 使用定理 `Int.le_of_dvd`：∀ {a b : ℤ}, 0 < b → a ∣ b → a ≤ b

--- 原说明 ---
#### `/` and ordering
-/
lemma le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a ≤ b ↔ 0 < b :=
  ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩
/-
**Int.le_add_iff_lt_of_dvd_sub** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b <= c ↔ b <
 c
参数：ha : 0 < a；hab : a ∣ c - b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_le_iff_le_sub`：∀ {a b c : ℤ}, a + b ≤ c ↔ a ≤ c - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sub_pos`：∀ {a b : ℤ}, 0 < a - b ↔ b < a
· 使用引理 `Int.le_iff_pos_of_dvd`：le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a 
<= b ↔ 0 < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b ≤ c ↔ b < c := by
  rw [Int.add_le_iff_le_sub, ← Int.sub_pos, le_iff_pos_of_dvd ha hab]

/-! ### sign -/

/-
**Int.sign_add_eq_of_sign_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：sign_add_eq_of_sign_eq : forall {m n : Int}, m.sign = n.sign -> (m + n).si
gn = n.sign
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### sign
-/
lemma sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  lia

/-! ### toNat -/

/-
The following lemma is non-confluent with
```
simp only [*, @Int.lt_toNat, CharP.cast_eq_zero, @Nat.cast_pred, Int.ofNat_toNat]
```
from the default simp set, which simplifies the LHS to `max i 0 - 1`.
Therefore we mark this lemma as `@[simp high]`.
-/
@[simp high]
/-
**Int.toNat_pred_coe_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：toNat_pred_coe_of_pos {i : Int} (h : 0 < i) : ((i.toNat - 1 : Nat) : Int) 
= i - 1
参数：h : 0 < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_pred_of_pos`：∀ {n : ℕ}, 0 < n → ↑(n - 1) = ↑n - 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.le_of_lt`：∀ {a b : ℤ}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The following lemma is non-confluent with
```
simp only [*, @Int.lt_toNat, CharP.cast_eq_zero, @Nat.cast_pred, Int.ofNat_toNat
]
```
from the default simp set, which simplifies the LHS to `max i 0 - 1`.
Therefore we mark this lemma as `@[simp high]`.
-/
lemma toNat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]
/-
**Int.toNat_lt_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：toNat_lt_of_ne_zero {n : Nat} (hn : n != 0) : m.toNat < n ↔ m < n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNat_lt_of_ne_zero {n : ℕ} (hn : n ≠ 0) : m.toNat < n ↔ m < n := by lia

/-- The modulus of an integer by another as a natural. Uses the E-rounding convention. -/
/-
**Int.natMod** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：natMod (m n : Int) : Nat
参数：m n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modulus of an integer by another as a natural. Uses the E-rounding conventio
n.
-/
def natMod (m n : ℤ) : ℕ := (m % n).toNat
/-
**Int.natMod_lt** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natMod_lt {n : Nat} (hn : n != 0) : m.natMod n < n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.toNat_lt_of_ne_zero`：toNat_lt_of_ne_zero {n : Nat} (hn : n != 0) : m
.toNat < n ↔ m < n
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
-/
lemma natMod_lt {n : ℕ} (hn : n ≠ 0) : m.natMod n < n :=
  (toNat_lt_of_ne_zero hn).2 <| emod_lt_of_pos _ <| by lia

/-- For use in `Mathlib/Tactic/NormNum/Pow.lean` -/
/-
**Int.pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m : ℤ) (n : ℕ), m.pow n = m ^ n
参数：m : ℤ；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For use in `Mathlib/Tactic/NormNum/Pow.lean`
-/
@[simp] lemma pow_eq (m : ℤ) (n : ℕ) : m.pow n = m ^ n := rfl
/-
**Int.gcd_ofNat_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m n : ℕ), (↑m).gcd (Int.negSucc n) = m.gcd (n + 1)
参数：m n : ℕ；↑m；Int.negSucc n；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For use in `Mathlib/Tactic/NormNum/Pow.lean`
-/
@[simp] lemma gcd_ofNat_negSucc (m n : ℕ) : gcd m (negSucc n) = m.gcd (n + 1) := by simp [gcd]
/-
**Int.gcd_negSucc_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m n : ℕ), (Int.negSucc m).gcd ↑n = (m + 1).gcd n
参数：m n : ℕ；Int.negSucc m；m + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For use in `Mathlib/Tactic/NormNum/Pow.lean`
-/
@[simp] lemma gcd_negSucc_ofNat (m n : ℕ) : gcd (negSucc m) n = (m + 1).gcd n := by simp [gcd]
/-
**Int.gcd_negSucc_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (m n : ℕ), (Int.negSucc m).gcd (Int.negSucc n) = (m + 1).gcd (n + 1)
参数：m n : ℕ；Int.negSucc m；Int.negSucc n；m + 1；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For use in `Mathlib/Tactic/NormNum/Pow.lean`
-/
@[simp] lemma gcd_negSucc_negSucc (m n : ℕ) :
    (negSucc m).gcd (negSucc n) = (m + 1).gcd (n + 1) := by simp [gcd]
/-
**Int.gcd_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_right_comm (a b c : Int) : gcd (gcd a b) c = gcd (gcd a c) b
参数：a b c : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.gcd_assoc`：∀ (a b c : ℤ), (↑(a.gcd b)).gcd c = a.gcd ↑(b.gcd c)
· 使用定理 `Int.gcd_comm`：∀ (a b : ℤ), a.gcd b = b.gcd a
-/
theorem gcd_right_comm (a b c : ℤ) : gcd (gcd a b) c = gcd (gcd a c) b := by
  rw [gcd_assoc, gcd_assoc, gcd_comm b c]

end Int

