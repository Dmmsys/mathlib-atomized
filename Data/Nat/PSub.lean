/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Partial predecessor and partial subtraction on the natural numbers

The usual definition of natural number subtraction (`Nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `Nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `Option` type instead:

## Main definitions

- `Nat.ppred`: a partial predecessor operation
- `Nat.psub`: a partial subtraction operation

-/

@[expose] public section

namespace Nat

/-- Partial predecessor operation. Returns `ppred n = some m`
  if `n = m + 1`, otherwise `none`. -/
/-
**Nat.ppred** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → Option ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial predecessor operation. Returns `ppred n = some m`
  if `n = m + 1`, otherwise `none`.
-/
def ppred : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n

@[simp]
/-
**Nat.ppred_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ppred_zero : ppred 0 = none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ppred_zero : ppred 0 = none := rfl

@[simp]
/-
**Nat.ppred_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ppred_succ {n : Nat} : ppred (succ n) = some n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ppred_succ {n : ℕ} : ppred (succ n) = some n := rfl

/-- Partial subtraction operation. Returns `psub m n = some k`
  if `m = n + k`, otherwise `none`. -/
/-
**Nat.psub** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → Option ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial subtraction operation. Returns `psub m n = some k`
  if `m = n + k`, otherwise `none`.
-/
def psub (m : ℕ) : ℕ → Option ℕ
  | 0 => some m
  | n + 1 => psub m n >>= ppred

@[simp]
/-
**Nat.psub_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：psub_zero {m : Nat} : psub m 0 = some m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem psub_zero {m : ℕ} : psub m 0 = some m := rfl

@[simp]
/-
**Nat.psub_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：psub_succ {m n : Nat} : psub m (succ n) = psub m n >>= ppred
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem psub_succ {m n : ℕ} : psub m (succ n) = psub m n >>= ppred := rfl
/-
**Nat.pred_eq_ppred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pred_eq_ppred (n : Nat) : pred n = (ppred n).getD 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pred_eq_ppred (n : ℕ) : pred n = (ppred n).getD 0 := by cases n <;> rfl
/-
**Nat.sub_eq_psub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m n : ℕ), m - n = (m.psub n).getD 0
参数：m n : ℕ；m.psub n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_eq_psub (m : ℕ) : ∀ n, m - n = (psub m n).getD 0
  | 0 => rfl
  | n + 1 => (pred_eq_ppred (m - n)).trans <| by rw [sub_eq_psub m n, psub]; cases psub m n <;> rfl

@[simp]
/-
**Nat.ppred_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, n.ppred = some m ↔ m.succ = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ppred_eq_some {m : ℕ} : ∀ {n}, ppred n = some m ↔ succ m = n
  | 0 => by constructor <;> intro h <;> contradiction
  | n + 1 => by constructor <;> intro h <;> injection h <;> subst m <;> rfl

@[simp]
/-
**Nat.ppred_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.ppred = none ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem ppred_eq_none : ∀ {n : ℕ}, ppred n = none ↔ n = 0
  | 0 => by simp
  | n + 1 => by constructor <;> intro <;> contradiction
/-
**Nat.psub_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n k : ℕ}, m.psub n = some k ↔ k + n = m
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem psub_eq_some {m : ℕ} : ∀ {n k}, psub m n = some k ↔ k + n = m
  | 0, k => by simp [eq_comm]
  | n + 1, k => by
    apply Option.bind_eq_some_iff.trans
    simp only [psub_eq_some, ppred_eq_some]
    simp [add_comm, add_left_comm]
/-
**Nat.psub_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：psub_eq_none {m n : Nat} : psub m n = none ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.psub_eq_some`：∀ {m n k : ℕ}, m.psub n = some k ↔ k + n = m
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem psub_eq_none {m n : ℕ} : psub m n = none ↔ m < n := by
  rcases s : psub m n
  · simp only [true_iff]
    refine lt_of_not_ge fun h => ?_
    obtain ⟨k, e⟩ := le.dest h
    injection s.symm.trans (psub_eq_some.2 <| (add_comm _ _).trans e)
  · grind [psub_eq_some]
/-
**Nat.ppred_eq_pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ppred_eq_pred {n} (h : 0 < n) : ppred n = some (pred n)
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ppred_eq_some`：∀ {m n : ℕ}, n.ppred = some m ↔ m.succ = n
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem ppred_eq_pred {n} (h : 0 < n) : ppred n = some (pred n) :=
  ppred_eq_some.2 <| succ_pred_eq_of_pos h
/-
**Nat.psub_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：psub_eq_sub {m n} (h : n <= m) : psub m n = some (m - n)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.psub_eq_some`：∀ {m n k : ℕ}, m.psub n = some k ↔ k + n = m
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
theorem psub_eq_sub {m n} (h : n ≤ m) : psub m n = some (m - n) :=
  psub_eq_some.2 <| Nat.sub_add_cancel h
/-
**Nat.psub_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：psub_add (m n k) : psub m (n + k) = (do psub (← psub m n) k)
参数：m n k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Option.bind_fun_some`：∀ {α : Type u_1} (x : Option α), x.bind some = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `instLawfulMonadOption`：LawfulMonad Option
-/
theorem psub_add (m n k) :
    psub m (n + k) = (do psub (← psub m n) k) := by
    induction k with
    | zero => simp
    | succ n ih => simp only [ih, add_succ, psub_succ, bind_assoc]

/-- Same as `psub`, but with a more efficient implementation. -/
@[inline]
/-
**Nat.psub'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：psub' (m n : Nat) : Option Nat
参数：m n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Same as `psub`, but with a more efficient implementation.
-/
def psub' (m n : ℕ) : Option ℕ :=
  if n ≤ m then some (m - n) else none
/-
**Nat.psub'_eq_psub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m n : ℕ), m.psub' n = m.psub n
参数：m n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.psub'.eq_1`：∀ (m n : ℕ), m.psub' n = if n ≤ m then some (m - n) else
 none
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.psub_eq_sub`：psub_eq_sub {m n} (h : n <= m) : psub m n = some (m - n
)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.psub_eq_none`：psub_eq_none {m n : Nat} : psub m n = none ↔ m < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem psub'_eq_psub (m n) : psub' m n = psub m n := by
  rw [psub']
  split_ifs with h
  · exact (psub_eq_sub h).symm
  · exact (psub_eq_none.2 (not_le.1 h)).symm

end Nat

