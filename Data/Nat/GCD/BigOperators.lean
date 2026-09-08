/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! # Lemmas about coprimality with big products.

These lemmas are kept separate from `Data.Nat.GCD.Basic` in order to minimize imports.
-/

public section


namespace Nat

variable {ι : Type*}

/-
**Nat.coprime_list_prod_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_list_prod_left_iff {l : List Nat} {k : Nat} : Coprime l.prod k ↔ f
orall n in l, Coprime n k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_one_left_eq_true`：∀ (n : ℕ), Nat.Coprime 1 n = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_list_prod_left_iff {l : List ℕ} {k : ℕ} :
    Coprime l.prod k ↔ ∀ n ∈ l, Coprime n k := by
  induction l <;> simp [Nat.coprime_mul_iff_left, *]
/-
**Nat.coprime_list_prod_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_list_prod_right_iff {k : Nat} {l : List Nat} : Coprime k l.prod ↔ 
forall n in l, Coprime k n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_list_prod_right_iff {k : ℕ} {l : List ℕ} :
    Coprime k l.prod ↔ ∀ n ∈ l, Coprime k n := by
  simp_rw [coprime_comm (n := k), coprime_list_prod_left_iff]
/-
**Nat.coprime_multiset_prod_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_multiset_prod_left_iff {m : Multiset Nat} {k : Nat} : Coprime m.pr
od k ↔ forall n in m, Coprime n k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.coprime_list_prod_left_iff`：coprime_list_prod_left_iff {l : List Nat
} {k : Nat} : Coprime l.prod k ↔ forall n in l, Coprime n k
-/
theorem coprime_multiset_prod_left_iff {m : Multiset ℕ} {k : ℕ} :
    Coprime m.prod k ↔ ∀ n ∈ m, Coprime n k := by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_left_iff
/-
**Nat.coprime_multiset_prod_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_multiset_prod_right_iff {k : Nat} {m : Multiset Nat} : Coprime k m
.prod ↔ forall n in m, Coprime k n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.coprime_list_prod_right_iff`：coprime_list_prod_right_iff {k : Nat} {
l : List Nat} : Coprime k l.prod ↔ forall n in l, Coprime k n
-/
theorem coprime_multiset_prod_right_iff {k : ℕ} {m : Multiset ℕ} :
    Coprime k m.prod ↔ ∀ n ∈ m, Coprime k n := by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_right_iff
/-
**Nat.coprime_prod_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_prod_left_iff {t : Finset ι} {s : ι -> Nat} {x : Nat} : Coprime (∏
 i in t, s i) x ↔ forall i in t, Coprime (s i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.coprime_multiset_prod_left_iff`：coprime_multiset_prod_left_iff {m : 
Multiset Nat} {k : Nat} : Coprime m.prod k ↔ forall n in m, Coprime n k
-/
theorem coprime_prod_left_iff {t : Finset ι} {s : ι → ℕ} {x : ℕ} :
    Coprime (∏ i ∈ t, s i) x ↔ ∀ i ∈ t, Coprime (s i) x := by
  simpa using coprime_multiset_prod_left_iff (m := t.val.map s)
/-
**Nat.coprime_prod_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_prod_right_iff {x : Nat} {t : Finset ι} {s : ι -> Nat} : Coprime x
 (∏ i in t, s i) ↔ forall i in t, Coprime x (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.coprime_multiset_prod_right_iff`：coprime_multiset_prod_right_iff {k 
: Nat} {m : Multiset Nat} : Coprime k m.prod ↔ forall n in m, Coprime k n
-/
theorem coprime_prod_right_iff {x : ℕ} {t : Finset ι} {s : ι → ℕ} :
    Coprime x (∏ i ∈ t, s i) ↔ ∀ i ∈ t, Coprime x (s i) := by
  simpa using coprime_multiset_prod_right_iff (m := t.val.map s)

/-- See `IsCoprime.prod_left` for the corresponding lemma about `IsCoprime` -/
alias ⟨_, Coprime.prod_left⟩ := coprime_prod_left_iff

/-- See `IsCoprime.prod_right` for the corresponding lemma about `IsCoprime` -/
alias ⟨_, Coprime.prod_right⟩ := coprime_prod_right_iff

/-
**Nat.coprime_fintype_prod_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_fintype_prod_left_iff [Fintype ι] {s : ι -> Nat} {x : Nat} : Copri
me (∏ i, s i) x ↔ forall i, Coprime (s i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_fintype_prod_left_iff [Fintype ι] {s : ι → ℕ} {x : ℕ} :
    Coprime (∏ i, s i) x ↔ ∀ i, Coprime (s i) x := by
  simp [coprime_prod_left_iff]
/-
**Nat.coprime_fintype_prod_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_fintype_prod_right_iff [Fintype ι] {x : Nat} {s : ι -> Nat} : Copr
ime x (∏ i, s i) ↔ forall i, Coprime x (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_fintype_prod_right_iff [Fintype ι] {x : ℕ} {s : ι → ℕ} :
    Coprime x (∏ i, s i) ↔ ∀ i, Coprime x (s i) := by
  simp [coprime_prod_right_iff]

end Nat

