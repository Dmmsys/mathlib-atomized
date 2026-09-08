/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic

/-!
# Dense orders and finsets

We prove that in a dense order, there's always an element lying in between any two finite sets of
elements.
-/

public section

variable {α : Type*} [LinearOrder α] [DenselyOrdered α]

/-
**Finset.exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_between {s t : Finset α} (hs : s.Nonempty) (ht : t.Nonempty)
 (H : forall x in s, forall y in t, x < y) : exists b, (forall x in s, x < b) ∧ 
(forall y in t, b < y)
参数：hs : s.Nonempty；ht : t.Nonempty；H : forall x in s, forall y in t, x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finset.exists_between {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert! _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp
/-
**Finset.exists_between'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_between' (s t : Finset α) [NoMaxOrder α] [NoMinOrder α] [Non
empty α] (H : forall x in s, forall y in t, x < y) : exists b, (forall x in s, x
 < b) ∧ (forall y in t, b < y)
参数：s t : Finset α；H : forall x in s, forall y in t, x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_between`：Finset.exists_between {s t : Finset α} (hs : s.No
nempty) (ht : t.Nonempty) (H : forall x in s, forall y in t, x < y) : exists b, 
(forall x i…
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem Finset.exists_between' (s t : Finset α) [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p ↦ ⟨p, by simp_all⟩
/-
**Set.Finite.exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.exists_between {s t : Set α} (hsf : s.Finite) (hs : s.Nonempty)
 (htf : t.Finite) (ht : t.Nonempty) (H : forall x in s, forall y in t, x < y) : 
exists b, (forall x in s, x < b) ∧ (forall y in t, b < y)
参数：hsf : s.Finite；hs : s.Nonempty；htf : t.Finite；ht : t.Nonempty；H : forall x in
 s, forall y in t, x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.exists_between`：Finset.exists_between {s t : Finset α} (hs : s.No
nempty) (ht : t.Nonempty) (H : forall x in s, forall y in t, x < y) : exists b, 
(forall x i…
-/
theorem Set.Finite.exists_between {s t : Set α}
    (hsf : s.Finite) (hs : s.Nonempty) (htf : t.Finite) (ht : t.Nonempty)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert!
    Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset) (by simpa) (by simpa)
      (by simpa) using
    1; simp
/-
**Set.Finite.exists_between'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.exists_between' [NoMaxOrder α] [NoMinOrder α] [Nonempty α] {s t
 : Set α} (hs : s.Finite) (ht : t.Finite) (H : forall x in s, forall y in t, x <
 y) : exists b, (forall x in s, x < b) ∧ (forall y in t, b < y)
参数：hs : s.Finite；ht : t.Finite；H : forall x in s, forall y in t, x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.exists_between'`：Finset.exists_between' (s t : Finset α) [NoMaxOr
der α] [NoMinOrder α] [Nonempty α] (H : forall x in s, forall y in t, x < y) : e
xists b, (fo…
-/
theorem Set.Finite.exists_between' [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert! hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp
