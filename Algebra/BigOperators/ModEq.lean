/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# Congruence modulo natural and integer numbers for big operators

In this file we prove various versions of the following theorem:
if `f i ≡ g i [MOD n]` for all `i ∈ s`, then `∏ i ∈ s, f i ≡ ∏ i ∈ s, g i [MOD n]`,
and similarly for sums.

We prove it for lists, multisets, and finsets, as well as for natural and integer numbers.
-/

public section

namespace Nat

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

namespace ModEq

/-
**Nat.ModEq.listProd_map** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：listProd_map (h : forall x in l, f x ≡ g x [MOD n]) : (l.map f).prod ≡ (l.
map g).prod [MOD n]
参数：h : forall x in l, f x ≡ g x [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.ModEq.mul`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a * c 
≡ b * d [MOD n]
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) :
    (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)
/-
**Nat.ModEq.listProd_map_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：listProd_map_one (h : forall x in l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1
 [MOD n]
参数：h : forall x in l, f x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.listProd_map`：listProd_map (h : forall x in l, f x ≡ g x [MOD 
n]) : (l.map f).prod ≡ (l.map g).prod [MOD n]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1 [MOD n] :=
  (listProd_map h).trans <| by simp [ModEq.refl]
/-
**Nat.ModEq.listProd_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：listProd_one {l : List Nat} (h : forall x in l, x ≡ 1 [MOD n]) : l.prod ≡ 
1 [MOD n]
参数：h : forall x in l, x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `Nat.ModEq.listProd_map_one`：listProd_map_one (h : forall x in l, f x ≡ 1
 [MOD n]) : (l.map f).prod ≡ 1 [MOD n]
-/
theorem listProd_one {l : List ℕ} (h : ∀ x ∈ l, x ≡ 1 [MOD n]) : l.prod ≡ 1 [MOD n] := by
  simpa using listProd_map_one h
/-
**Nat.ModEq.listSum_map** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：listSum_map (h : forall x in l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.ma
p g).sum [MOD n]
参数：h : forall x in l, f x ≡ g x [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)
/-
**Nat.ModEq.listSum_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：listSum_map_zero (h : forall x in l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 
[MOD n]
参数：h : forall x in l, f x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Nat.ModEq.listSum_map`：listSum_map (h : forall x in l, f x ≡ g x [MOD n]
) : (l.map f).sum ≡ (l.map g).sum [MOD n]
-/
theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 [MOD n] := by
  simpa using listSum_map h
/-
**Nat.ModEq.listSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：listSum_zero {l : List Nat} (h : forall x in l, x ≡ 0 [MOD n]) : l.sum ≡ 0
 [MOD n]
参数：h : forall x in l, x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Nat.ModEq.listSum_map`：listSum_map (h : forall x in l, f x ≡ g x [MOD n]
) : (l.map f).sum ≡ (l.map g).sum [MOD n]
-/
theorem listSum_zero {l : List ℕ} (h : ∀ x ∈ l, x ≡ 0 [MOD n]) : l.sum ≡ 0 [MOD n] := by
  simpa using listSum_map h
/-
**Nat.ModEq.multisetProd_map** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：multisetProd_map {s : Multiset α} (h : forall x in s, f x ≡ g x [MOD n]) :
 (s.map f).prod ≡ (s.map g).prod [MOD n]
参数：h : forall x in s, f x ≡ g x [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.listProd_map`：listProd_map (h : forall x in l, f x ≡ g x [MOD 
n]) : (l.map f).prod ≡ (l.map g).prod [MOD n]
-/
theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).prod ≡ (s.map g).prod [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h
/-
**Nat.ModEq.multisetProd_map_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：multisetProd_map_one {s : Multiset α} (h : forall x in s, f x ≡ 1 [MOD n])
 : (s.map f).prod ≡ 1 [MOD n]
参数：h : forall x in s, f x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.ModEq.multisetProd_map`：multisetProd_map {s : Multiset α} (h : foral
l x in s, f x ≡ g x [MOD n]) : (s.map f).prod ≡ (s.map g).prod [MOD n]
-/
theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) :
    (s.map f).prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map h
/-
**Nat.ModEq.multisetProd_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：multisetProd_one {s : Multiset Nat} (h : forall x in s, x ≡ 1 [MOD n]) : s
.prod ≡ 1 [MOD n]
参数：h : forall x in s, x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Nat.ModEq.multisetProd_map_one`：multisetProd_map_one {s : Multiset α} (h
 : forall x in s, f x ≡ 1 [MOD n]) : (s.map f).prod ≡ 1 [MOD n]
-/
theorem multisetProd_one {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 1 [MOD n]) : s.prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map_one h
/-
**Nat.ModEq.multisetSum_map** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：multisetSum_map {s : Multiset α} (h : forall x in s, f x ≡ g x [MOD n]) : 
(s.map f).sum ≡ (s.map g).sum [MOD n]
参数：h : forall x in s, f x ≡ g x [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.listSum_map`：listSum_map (h : forall x in l, f x ≡ g x [MOD n]
) : (l.map f).sum ≡ (l.map g).sum [MOD n]
-/
theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).sum ≡ (s.map g).sum [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h
/-
**Nat.ModEq.multisetSum_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：multisetSum_map_zero {s : Multiset α} (h : forall x in s, f x ≡ 0 [MOD n])
 : (s.map f).sum ≡ 0 [MOD n]
参数：h : forall x in s, f x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Nat.ModEq.multisetSum_map`：multisetSum_map {s : Multiset α} (h : forall 
x in s, f x ≡ g x [MOD n]) : (s.map f).sum ≡ (s.map g).sum [MOD n]
-/
theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) :
    (s.map f).sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h
/-
**Nat.ModEq.multisetSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：multisetSum_zero {s : Multiset Nat} (h : forall x in s, x ≡ 0 [MOD n]) : s
.sum ≡ 0 [MOD n]
参数：h : forall x in s, x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Nat.ModEq.multisetSum_map`：multisetSum_map {s : Multiset α} (h : forall 
x in s, f x ≡ g x [MOD n]) : (s.map f).sum ≡ (s.map g).sum [MOD n]
-/
theorem multisetSum_zero {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 0 [MOD n]) : s.sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

@[gcongr]
/-
**Nat.ModEq.prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {f g : α → ℕ} {s : Finset α},   (∀ x ∈ s, f x ≡ g
 x [MOD n]) → ∏ x ∈ s, f x ≡ ∏ x ∈ s, g x [MOD n]
参数：∀ x ∈ s, f x ≡ g x [MOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.multisetProd_map`：multisetProd_map {s : Multiset α} (h : foral
l x in s, f x ≡ g x [MOD n]) : (s.map f).prod ≡ (s.map g).prod [MOD n]
-/
protected theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [MOD n] :=
  .multisetProd_map (s := s.1) h
/-
**Nat.ModEq.prod_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：prod_one {s : Finset α} (h : forall x in s, f x ≡ 1 [MOD n]) : ∏ x in s, f
 x ≡ 1 [MOD n]
参数：h : forall x in s, f x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Nat.ModEq.prod`：∀ {α : Type u_1} {n : ℕ} {f g : α → ℕ} {s : Finset α},  
 (∀ x ∈ s, f x ≡ g x [MOD n]) → ∏ x ∈ s, f x ≡ ∏ x ∈ s, g x [MOD n]
-/
theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) : ∏ x ∈ s, f x ≡ 1 [MOD n] := by
  simpa using ModEq.prod h

@[gcongr]
/-
**Nat.ModEq.sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {f g : α → ℕ} {s : Finset α},   (∀ x ∈ s, f x ≡ g
 x [MOD n]) → ∑ x ∈ s, f x ≡ ∑ x ∈ s, g x [MOD n]
参数：∀ x ∈ s, f x ≡ g x [MOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.multisetSum_map`：multisetSum_map {s : Multiset α} (h : forall 
x in s, f x ≡ g x [MOD n]) : (s.map f).sum ≡ (s.map g).sum [MOD n]
-/
protected theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [MOD n] :=
  .multisetSum_map (s := s.1) h
/-
**Nat.ModEq.sum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：sum_zero {s : Finset α} (h : forall x in s, f x ≡ 0 [MOD n]) : ∑ x in s, f
 x ≡ 0 [MOD n]
参数：h : forall x in s, f x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Nat.ModEq.sum`：∀ {α : Type u_1} {n : ℕ} {f g : α → ℕ} {s : Finset α},   
(∀ x ∈ s, f x ≡ g x [MOD n]) → ∑ x ∈ s, f x ≡ ∑ x ∈ s, g x [MOD n]
-/
theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) : ∑ x ∈ s, f x ≡ 0 [MOD n] := by
  simpa using ModEq.sum h

end ModEq

/-
**Nat.prod_modEq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α} (hf : forall x in s,
 x != a -> f x ≡ 1 [MOD n]) : (∏ x in s, f x) ≡ if a in s then f a else 1 [MOD n
]
参数：hf : forall x in s, x != a -> f x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Finset.prod_eq_ite`：prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι ->
 M} (a : ι) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s, f x = if a in s 
then f a…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf
/-
**Nat.prod_modEq_single** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_modEq_single {s : Finset α} {a : α} (ha : a ∉ s -> f a ≡ 1 [MOD n]) (
hf : forall x in s, x != a -> f x ≡ 1 [MOD n]) : (∏ x in s, f x) ≡ f a [MOD n]
参数：ha : a ∉ s -> f a ≡ 1 [MOD n]；hf : forall x in s, x != a -> f x ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption
/-
**Nat.sum_modEq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α} (hf : forall x in s, 
x != a -> f x ≡ 0 [MOD n]) : (∑ x in s, f x) ≡ if a in s then f a else 0 [MOD n]
参数：hf : forall x in s, x != a -> f x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.sum_eq_ite`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠
 a → f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf
/-
**Nat.sum_modEq_single** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_modEq_single {s : Finset α} {a : α} (ha : a ∉ s -> f a ≡ 0 [MOD n]) (h
f : forall x in s, x != a -> f x ≡ 0 [MOD n]) : (∑ x in s, f x) ≡ f a [MOD n]
参数：ha : a ∉ s -> f a ≡ 0 [MOD n]；hf : forall x in s, x != a -> f x ≡ 0 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Nat

namespace Int

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

namespace ModEq

/-
**Int.ModEq.listProd_map** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：listProd_map (h : forall x in l, f x ≡ g x [ZMOD n]) : (l.map f).prod ≡ (l
.map g).prod [ZMOD n]
参数：h : forall x in l, f x ≡ g x [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.ModEq.mul`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a * 
c ≡ b * d [ZMOD n]
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) :
    (l.map f).prod ≡ (l.map g).prod [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)
/-
**Int.ModEq.listProd_map_one** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：listProd_map_one (h : forall x in l, f x ≡ 1 [ZMOD n]) : (l.map f).prod ≡ 
1 [ZMOD n]
参数：h : forall x in l, f x ≡ 1 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.trans`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ 
c [ZMOD n]
· 使用定理 `Int.ModEq.listProd_map`：listProd_map (h : forall x in l, f x ≡ g x [ZMOD
 n]) : (l.map f).prod ≡ (l.map g).prod [ZMOD n]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [ZMOD n]) : (l.map f).prod ≡ 1 [ZMOD n] :=
  (listProd_map h).trans <| by simp
/-
**Int.ModEq.listProd_one** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：listProd_one {l : List Int} (h : forall x in l, x ≡ 1 [ZMOD n]) : l.prod ≡
 1 [ZMOD n]
参数：h : forall x in l, x ≡ 1 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `Int.ModEq.listProd_map_one`：listProd_map_one (h : forall x in l, f x ≡ 1
 [ZMOD n]) : (l.map f).prod ≡ 1 [ZMOD n]
-/
theorem listProd_one {l : List ℤ} (h : ∀ x ∈ l, x ≡ 1 [ZMOD n]) : l.prod ≡ 1 [ZMOD n] := by
  simpa using listProd_map_one h
/-
**Int.ModEq.listSum_map** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：listSum_map (h : forall x in l, f x ≡ g x [ZMOD n]) : (l.map f).sum ≡ (l.m
ap g).sum [ZMOD n]
参数：h : forall x in l, f x ≡ g x [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.ModEq.add`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a + 
c ≡ b + d [ZMOD n]
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)
/-
**Int.ModEq.listSum_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：listSum_map_zero (h : forall x in l, f x ≡ 0 [ZMOD n]) : (l.map f).sum ≡ 0
 [ZMOD n]
参数：h : forall x in l, f x ≡ 0 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Int.ModEq.listSum_map`：listSum_map (h : forall x in l, f x ≡ g x [ZMOD n
]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n]
-/
theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [ZMOD n]) : (l.map f).sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map h
/-
**Int.ModEq.listSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：listSum_zero {l : List Int} (h : forall x in l, x ≡ 0 [ZMOD n]) : l.sum ≡ 
0 [ZMOD n]
参数：h : forall x in l, x ≡ 0 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `Int.ModEq.listSum_map_zero`：listSum_map_zero (h : forall x in l, f x ≡ 0
 [ZMOD n]) : (l.map f).sum ≡ 0 [ZMOD n]
-/
theorem listSum_zero {l : List ℤ} (h : ∀ x ∈ l, x ≡ 0 [ZMOD n]) : l.sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map_zero h
/-
**Int.ModEq.multisetProd_map** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：multisetProd_map {s : Multiset α} (h : forall x in s, f x ≡ g x [ZMOD n]) 
: (s.map f).prod ≡ (s.map g).prod [ZMOD n]
参数：h : forall x in s, f x ≡ g x [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.listProd_map`：listProd_map (h : forall x in l, f x ≡ g x [ZMOD
 n]) : (l.map f).prod ≡ (l.map g).prod [ZMOD n]
-/
theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (s.map f).prod ≡ (s.map g).prod [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h
/-
**Int.ModEq.multisetProd_map_one** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：multisetProd_map_one {s : Multiset α} (h : forall x in s, f x ≡ 1 [ZMOD n]
) : (s.map f).prod ≡ 1 [ZMOD n]
参数：h : forall x in s, f x ≡ 1 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Int.ModEq.multisetProd_map`：multisetProd_map {s : Multiset α} (h : foral
l x in s, f x ≡ g x [ZMOD n]) : (s.map f).prod ≡ (s.map g).prod [ZMOD n]
-/
theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) :
    (s.map f).prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map h
/-
**Int.ModEq.multisetProd_one** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：multisetProd_one {s : Multiset Int} (h : forall x in s, x ≡ 1 [ZMOD n]) : 
s.prod ≡ 1 [ZMOD n]
参数：h : forall x in s, x ≡ 1 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Int.ModEq.multisetProd_map_one`：multisetProd_map_one {s : Multiset α} (h
 : forall x in s, f x ≡ 1 [ZMOD n]) : (s.map f).prod ≡ 1 [ZMOD n]
-/
theorem multisetProd_one {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 1 [ZMOD n]) : s.prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map_one h
/-
**Int.ModEq.multisetSum_map** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：multisetSum_map {s : Multiset α} (h : forall x in s, f x ≡ g x [ZMOD n]) :
 (s.map f).sum ≡ (s.map g).sum [ZMOD n]
参数：h : forall x in s, f x ≡ g x [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.listSum_map`：listSum_map (h : forall x in l, f x ≡ g x [ZMOD n
]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n]
-/
theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (s.map f).sum ≡ (s.map g).sum [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h
/-
**Int.ModEq.multisetSum_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：multisetSum_map_zero {s : Multiset α} (h : forall x in s, f x ≡ 0 [ZMOD n]
) : (s.map f).sum ≡ 0 [ZMOD n]
参数：h : forall x in s, f x ≡ 0 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Int.ModEq.multisetSum_map`：multisetSum_map {s : Multiset α} (h : forall 
x in s, f x ≡ g x [ZMOD n]) : (s.map f).sum ≡ (s.map g).sum [ZMOD n]
-/
theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (s.map f).sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map h
/-
**Int.ModEq.multisetSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：multisetSum_zero {s : Multiset Int} (h : forall x in s, x ≡ 0 [ZMOD n]) : 
s.sum ≡ 0 [ZMOD n]
参数：h : forall x in s, x ≡ 0 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Int.ModEq.multisetSum_map_zero`：multisetSum_map_zero {s : Multiset α} (h
 : forall x in s, f x ≡ 0 [ZMOD n]) : (s.map f).sum ≡ 0 [ZMOD n]
-/
theorem multisetSum_zero {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 0 [ZMOD n]) : s.sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map_zero h

@[gcongr]
/-
**Int.ModEq.prod** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {α : Type u_1} {n : ℤ} {f g : α → ℤ} {s : Finset α},   (∀ x ∈ s, f x ≡ g
 x [ZMOD n]) → ∏ x ∈ s, f x ≡ ∏ x ∈ s, g x [ZMOD n]
参数：∀ x ∈ s, f x ≡ g x [ZMOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.multisetProd_map`：multisetProd_map {s : Multiset α} (h : foral
l x in s, f x ≡ g x [ZMOD n]) : (s.map f).prod ≡ (s.map g).prod [ZMOD n]
-/
protected theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [ZMOD n] :=
  .multisetProd_map (s := s.1) h
/-
**Int.ModEq.prod_one** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：prod_one {s : Finset α} (h : forall x in s, f x ≡ 1 [ZMOD n]) : ∏ x in s, 
f x ≡ 1 [ZMOD n]
参数：h : forall x in s, f x ≡ 1 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Int.ModEq.prod`：∀ {α : Type u_1} {n : ℤ} {f g : α → ℤ} {s : Finset α},  
 (∀ x ∈ s, f x ≡ g x [ZMOD n]) → ∏ x ∈ s, f x ≡ ∏ x ∈ s, g x [ZMOD n]
-/
theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) : ∏ x ∈ s, f x ≡ 1 [ZMOD n] := by
  simpa using ModEq.prod h

@[gcongr]
/-
**Int.ModEq.sum** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {α : Type u_1} {n : ℤ} {f g : α → ℤ} {s : Finset α},   (∀ x ∈ s, f x ≡ g
 x [ZMOD n]) → ∑ x ∈ s, f x ≡ ∑ x ∈ s, g x [ZMOD n]
参数：∀ x ∈ s, f x ≡ g x [ZMOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.multisetSum_map`：multisetSum_map {s : Multiset α} (h : forall 
x in s, f x ≡ g x [ZMOD n]) : (s.map f).sum ≡ (s.map g).sum [ZMOD n]
-/
protected theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [ZMOD n] :=
  .multisetSum_map (s := s.1) h
/-
**Int.ModEq.sum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {α : Type u_1} {n : ℤ} {f : α → ℤ} {s : Finset α}, (∀ x ∈ s, f x ≡ 0 [ZM
OD n]) → ∑ x ∈ s, f x ≡ 0 [ZMOD n]
参数：∀ x ∈ s, f x ≡ 0 [ZMOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.multisetSum_map_zero`：multisetSum_map_zero {s : Multiset α} (h
 : forall x in s, f x ≡ 0 [ZMOD n]) : (s.map f).sum ≡ 0 [ZMOD n]
-/
protected theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ 0 [ZMOD n] :=
  .multisetSum_map_zero (s := s.1) h

end ModEq

/-
**Int.prod_modEq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α} (hf : forall x in s,
 x != a -> f x ≡ 1 [ZMOD n]) : (∏ x in s, f x) ≡ if a in s then f a else 1 [ZMOD
 n]
参数：hf : forall x in s, x != a -> f x ≡ 1 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.modEq_natAbs`：modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_prod`：cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Fi
nset ι) : (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Finset.prod_eq_ite`：prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι ->
 M} (a : ι) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s, f x = if a in s 
then f a…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod,
    apply_ite Int.cast] at *
  exact Finset.prod_eq_ite _ hf
/-
**Int.prod_modEq_single** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：prod_modEq_single {s : Finset α} {a : α} (ha : a ∉ s -> f a ≡ 1 [ZMOD n]) 
(hf : forall x in s, x != a -> f x ≡ 1 [ZMOD n]) : (∏ x in s, f x) ≡ f a [ZMOD n
]
参数：ha : a ∉ s -> f a ≡ 1 [ZMOD n]；hf : forall x in s, x != a -> f x ≡ 1 [ZMOD n]
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.modEq_natAbs`：modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_prod`：cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Fi
nset ι) : (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption
/-
**Int.sum_modEq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α} (hf : forall x in s, 
x != a -> f x ≡ 0 [ZMOD n]) : (∑ x in s, f x) ≡ if a in s then f a else 0 [ZMOD 
n]
参数：hf : forall x in s, x != a -> f x ≡ 0 [ZMOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.modEq_natAbs`：modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Finset.sum_eq_ite`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠
 a → f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf
/-
**Int.sum_modEq_single** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sum_modEq_single {s : Finset α} {a : α} (ha : a ∉ s -> f a ≡ 0 [ZMOD n]) (
hf : forall x in s, x != a -> f x ≡ 0 [ZMOD n]) : (∑ x in s, f x) ≡ f a [ZMOD n]
参数：ha : a ∉ s -> f a ≡ 0 [ZMOD n]；hf : forall x in s, x != a -> f x ≡ 0 [ZMOD n]
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.modEq_natAbs`：modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Int

