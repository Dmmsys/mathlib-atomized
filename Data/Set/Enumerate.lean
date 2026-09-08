/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Common
public import Mathlib.Data.Set.Insert

/-!
# Set enumeration

This file allows enumeration of sets given a choice function.
The definition does not assume `sel` actually is a choice function, i.e. `sel s ∈ s` and
`sel s = none ↔ s = ∅`. These assumptions are added to the lemmas needing them.
-/

@[expose] public section

assert_not_exists RelIso

noncomputable section

open Function

namespace Set

section Enumerate

variable {α : Type*} (sel : Set α → Option α)

/-- Given a choice function `sel`, enumerates the elements of a set in the order
`a 0 = sel s`, `a 1 = sel (s \ {a 0})`, `a 2 = sel (s \ {a 0, a 1})`, ... and stops when
`sel (s \ {a 0, ..., a n}) = none`. Note that we don't require `sel` to be a choice function. -/
/-
**Set.enumerate** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → (Set α → Option α) → Set α → ℕ → Option α
参数：Set α → Option α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a choice function `sel`, enumerates the elements of a set in the order
`a 0 = sel s`, `a 1 = sel (s \ {a 0})`, `a 2 = sel (s \ {a 0, a 1})`, ... and st
ops when
`sel (s \ {a 0, ..., a n}) = none`. Note that we don't require `sel` to be a cho
ice function.
-/
def enumerate : Set α → ℕ → Option α
  | s, 0 => sel s
  | s, n + 1 => do
    let a ← sel s
    enumerate (s \ {a}) n
/-
**Set.enumerate_eq_none_of_sel** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (sel : Set α → Option α) {s : Set α}, sel s = none → ∀ {n
 : ℕ}, Set.enumerate sel s n = none
参数：sel : Set α → Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : ∀ {n}, enumerate sel s n = none
  | 0 => by simp [h, enumerate]
  | n + 1 => by simp [h, enumerate]
/-
**Set.enumerate_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：enumerate_eq_none : forall {s n₁ n₂}, enumerate sel s n₁ = none -> n₁ <= n
₂ -> enumerate sel s n₂ = none | _, 0, _ => fun h _ => enumerate_eq_none_of_sel 
sel h | s, n + 1, m => fun h hm => by cases hs : sel s · exact enumerate_eq_none
_of_sel sel hs · cases m with | zero => contradiction | succ m' => simp only [en
umerate, hs] at h ⊢ have hm : n <= m'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem enumerate_eq_none :
    ∀ {s n₁ n₂}, enumerate sel s n₁ = none → n₁ ≤ n₂ → enumerate sel s n₂ = none
  | _, 0, _ => fun h _ ↦ enumerate_eq_none_of_sel sel h
  | s, n + 1, m => fun h hm ↦ by
    cases hs : sel s
    · exact enumerate_eq_none_of_sel sel hs
    · cases m with
      | zero => contradiction
      | succ m' =>
        simp only [enumerate, hs] at h ⊢
        have hm : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm
/-
**Set.enumerate_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：enumerate_mem (h_sel : forall s a, sel s = some a -> a in s) : forall {s n
 a}, enumerate sel s n = some a -> a in s | s, 0, a => h_sel s a | s, n + 1, a =
> by cases h : sel s with | none => simp [enumerate_eq_none_of_sel, h] | some a'
 => simp only [enumerate, h] exact fun h' : enumerate sel (s \ {a'}) n = some a 
=> have : a in s \ {a'}
参数：h_sel : forall s a, sel s = some a -> a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem enumerate_mem (h_sel : ∀ s a, sel s = some a → a ∈ s) :
    ∀ {s n a}, enumerate sel s n = some a → a ∈ s
  | s, 0, a => h_sel s a
  | s, n + 1, a => by
    cases h : sel s with
    | none => simp [enumerate_eq_none_of_sel, h]
    | some a' =>
      simp only [enumerate, h]
      exact fun h' : enumerate sel (s \ {a'}) n = some a ↦
        have : a ∈ s \ {a'} := enumerate_mem h_sel h'
        this.left
/-
**Set.enumerate_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：enumerate_inj {n₁ n₂ : Nat} {a : α} {s : Set α} (h_sel : forall s a, sel s
 = some a -> a in s) (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂
 = some a) : n₁ = n₂
参数：h_sel : forall s a, sel s = some a -> a in s；h₁ : enumerate sel s n₁ = some a
；h₂ : enumerate sel s n₂ = some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.enumerate_mem`：enumerate_mem (h_sel : forall s a, sel s = some a -> 
a in s) : forall {s n a}, enumerate sel s n = some a -> a in s | s, 0, a => h_se
l s a |…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : Set α} (h_sel : ∀ s a, sel s = some a → a ∈ s)
    (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂ = some a) : n₁ = n₂ := by
  wlog! hn : n₁ ≤ n₂ generalizing n₁ n₂
  · exact (this h₂ h₁ hn.le).symm
  rcases Nat.le.dest hn with ⟨m, rfl⟩
  clear hn
  induction n₁ generalizing s with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      have h' : enumerate sel (s \ {a}) m = some a := by
        simp_all only [enumerate, Nat.add_eq, zero_add]; exact h₂
      have : a ∈ s \ {a} := enumerate_mem sel h_sel h'
      simp_all
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by lia] at h₂
    cases h : sel s <;> simp_all [enumerate]; tauto

end Enumerate

end Set

