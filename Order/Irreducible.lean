/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Irreducible and prime elements in an order

This file defines irreducible and prime elements in an order and shows that in a well-founded
lattice every element decomposes as a supremum of irreducible elements.

An element is sup-irreducible (resp. inf-irreducible) if it isn't `⊥` and can't be written as the
supremum of any strictly smaller elements. An element is sup-prime (resp. inf-prime) if it isn't `⊥`
and is greater than the supremum of any two elements less than it.

Primality implies irreducibility in general. The converse only holds in distributive lattices.
Both hold for all (non-minimal) elements in a linear order.

## Main declarations

* `SupIrred a`: Sup-irreducibility, `a` isn't minimal and `a = b ⊔ c → a = b ∨ a = c`
* `InfIrred a`: Inf-irreducibility, `a` isn't maximal and `a = b ⊓ c → a = b ∨ a = c`
* `SupPrime a`: Sup-primality, `a` isn't minimal and `a ≤ b ⊔ c → a ≤ b ∨ a ≤ c`
* `InfIrred a`: Inf-primality, `a` isn't maximal and `a ≥ b ⊓ c → a ≥ b ∨ a ≥ c`
* `exists_supIrred_decomposition`/`exists_infIrred_decomposition`: Decomposition into irreducibles
  in a well-founded semilattice.
-/

@[expose] public section


open Finset OrderDual

variable {ι α : Type*}

/-! ### Irreducible and prime elements -/


section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
/-
**SupIrred** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SupIrred (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sup-irreducible element is a non-bottom element which isn't the supremum of an
ything smaller.
-/
def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
/-
**SupPrime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SupPrime (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sup-prime element is a non-bottom element which isn't less than the supremum o
f anything
smaller.
-/
def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c
/-
**SupIrred.not_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a
参数：ha : SupIrred a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1
/-
**SupPrime.not_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a
参数：ha : SupPrime a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1
/-
**IsMin.not_supIrred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a
参数：ha : IsMin a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha
/-
**IsMin.not_supPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a
参数：ha : IsMin a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha

@[simp]
/-
**not_supIrred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_supIrred : ¬SupIrred a ↔ IsMin a ∨ exists b c, b ⊔ c = a ∧ b < a ∧ c <
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SupIrred.eq_1`：∀ {α : Type u_2} [inst : SemilatticeSup α] (a : α), SupIr
red a = (¬IsMin a ∧ ∀ ⦃b c : α⦄, b ⊔ c = a → b = a ∨ c = a)
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred, not_and_or]
  push Not
  rw [exists₂_congr]
  simp +contextual [@eq_comm _ _ a]

@[simp]
/-
**not_supPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_supPrime : ¬SupPrime a ↔ IsMin a ∨ exists b c, a <= b ⊔ c ∧ ¬a <= b ∧ 
¬a <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SupPrime.eq_1`：∀ {α : Type u_2} [inst : SemilatticeSup α] (a : α), SupPr
ime a = (¬IsMin a ∧ ∀ ⦃b c : α⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c)
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  rw [SupPrime, not_and_or]; push Not; rfl
/-
**SupPrime.supIrred** 是 Mathlib 中的一个定理，位于命名空间 `SupPrime`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] {a : α}, SupPrime a → SupIrred 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
protected theorem SupPrime.supIrred : SupPrime a → SupIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge
/-
**SupPrime.le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupPrime.le_sup (ha : SupPrime a) : a <= b ⊔ c ↔ a <= b ∨ a <= c
参数：ha : SupPrime a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
-/
theorem SupPrime.le_sup (ha : SupPrime a) : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c :=
  ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩

variable [OrderBot α] {s : Finset ι} {f : ι → α}

@[simp]
/-
**not_supIrred_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_supIrred_bot : ¬SupIrred (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_supIrred`：IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem not_supIrred_bot : ¬SupIrred (⊥ : α) :=
  isMin_bot.not_supIrred

@[simp]
/-
**not_supPrime_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_supPrime_bot : ¬SupPrime (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_supPrime`：IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem not_supPrime_bot : ¬SupPrime (⊥ : α) :=
  isMin_bot.not_supPrime
/-
**SupIrred.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupIrred.ne_bot (ha : SupIrred a) : a != ⊥
参数：ha : SupIrred a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_supIrred_bot`：not_supIrred_bot : ¬SupIrred (⊥ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SupIrred.ne_bot (ha : SupIrred a) : a ≠ ⊥ := by rintro rfl; exact not_supIrred_bot ha
/-
**SupPrime.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupPrime.ne_bot (ha : SupPrime a) : a != ⊥
参数：ha : SupPrime a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_supPrime_bot`：not_supPrime_bot : ¬SupPrime (⊥ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SupPrime.ne_bot (ha : SupPrime a) : a ≠ ⊥ := by rintro rfl; exact not_supPrime_bot ha
/-
**SupIrred.finset_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.sup f = a) : exists i in s
, f i = a
参数：ha : SupIrred a；h : s.sup f = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SupIrred.ne_bot`：SupIrred.ne_bot (ha : SupIrred a) : a != ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
-/
theorem SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.sup f = a) : ∃ i ∈ s, f i = a := by
  classical
  induction s using Finset.induction with
  | empty => simpa [ha.ne_bot] using h.symm
  | insert i s _ ih =>
    simp only [exists_mem_insert] at ih ⊢
    rw [sup_insert] at h
    exact (ha.2 h).imp_right ih
/-
**SupPrime.le_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SupPrime.le_finset_sup (ha : SupPrime a) : a <= s.sup f ↔ exists i in s, a
 <= f i
参数：ha : SupPrime a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SupPrime.ne_bot`：SupPrime.ne_bot (ha : SupPrime a) : a != ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `SupPrime.le_sup`：SupPrime.le_sup (ha : SupPrime a) : a <= b ⊔ c ↔ a <= b
 ∨ a <= c
-/
theorem SupPrime.le_finset_sup (ha : SupPrime a) : a ≤ s.sup f ↔ ∃ i ∈ s, a ≤ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp [ha.ne_bot]
  | insert i s _ ih => simp only [exists_mem_insert, sup_insert, ha.le_sup, ih]

variable [WellFoundedLT α]

/-- In a well-founded lattice, any element is the supremum of finitely many sup-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
/-
**exists_supIrred_decomposition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_supIrred_decomposition (a : α) : exists s : Finset α, s.sup id = a 
∧ forall ⦃b⦄, b in s -> SupIrred b
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_supIrred`：not_supIrred : ¬SupIrred a ↔ IsMin a ∨ exists b c, b ⊔ c =
 a ∧ b < a ∧ c < a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.forall_mem_union`：forall_mem_union {p : α -> Prop} : (forall a in
 s union t, p a) ↔ (forall a in s, p a) ∧ forall a in t, p a

--- 原说明 ---
In a well-founded lattice, any element is the supremum of finitely many sup-irre
ducible
elements. This is the order-theoretic analogue of prime factorisation.
-/
theorem exists_supIrred_decomposition (a : α) :
    ∃ s : Finset α, s.sup id = a ∧ ∀ ⦃b⦄, b ∈ s → SupIrred b := by
  classical
  apply WellFoundedLT.induction a _
  clear a
  rintro a ih
  by_cases ha : SupIrred a
  · exact ⟨{a}, by simp [ha]⟩
  rw [not_supIrred] at ha
  obtain ha | ⟨b, c, rfl, hb, hc⟩ := ha
  · exact ⟨∅, by simp [ha.eq_bot]⟩
  obtain ⟨s, rfl, hs⟩ := ih _ hb
  obtain ⟨t, rfl, ht⟩ := ih _ hc
  exact ⟨s ∪ t, sup_union, forall_mem_union.2 ⟨hs, ht⟩⟩

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] {a b c : α}

/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/
/-
**InfIrred** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InfIrred (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inf-irreducible element is a non-top element which isn't the infimum of anyth
ing bigger.
-/
def InfIrred (a : α) : Prop :=
  ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a

/-- An inf-prime element is a non-top element which isn't bigger than the infimum of anything
bigger. -/
/-
**InfPrime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InfPrime (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inf-prime element is a non-top element which isn't bigger than the infimum of
 anything
bigger.
-/
def InfPrime (a : α) : Prop :=
  ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c ≤ a → b ≤ a ∨ c ≤ a

@[simp]
/-
**IsMax.not_infIrred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMax.not_infIrred (ha : IsMax a) : ¬InfIrred a
参数：ha : IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMax.not_infIrred (ha : IsMax a) : ¬InfIrred a := fun h => h.1 ha

@[simp]
/-
**IsMax.not_infPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMax.not_infPrime (ha : IsMax a) : ¬InfPrime a
参数：ha : IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMax.not_infPrime (ha : IsMax a) : ¬InfPrime a := fun h => h.1 ha

@[simp]
/-
**not_infIrred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_infIrred : ¬InfIrred a ↔ IsMax a ∨ exists b c, b ⊓ c = a ∧ a < b ∧ a <
 c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_supIrred`：not_supIrred : ¬SupIrred a ↔ IsMin a ∨ exists b c, b ⊔ c =
 a ∧ b < a ∧ c < a
-/
theorem not_infIrred : ¬InfIrred a ↔ IsMax a ∨ ∃ b c, b ⊓ c = a ∧ a < b ∧ a < c :=
  @not_supIrred αᵒᵈ _ _

@[simp]
/-
**not_infPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_infPrime : ¬InfPrime a ↔ IsMax a ∨ exists b c, b ⊓ c <= a ∧ ¬b <= a ∧ 
¬c <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_supPrime`：not_supPrime : ¬SupPrime a ↔ IsMin a ∨ exists b c, a <= b 
⊔ c ∧ ¬a <= b ∧ ¬a <= c
-/
theorem not_infPrime : ¬InfPrime a ↔ IsMax a ∨ ∃ b c, b ⊓ c ≤ a ∧ ¬b ≤ a ∧ ¬c ≤ a :=
  @not_supPrime αᵒᵈ _ _
/-
**InfPrime.infIrred** 是 Mathlib 中的一个定理，位于命名空间 `InfPrime`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] {a : α}, InfPrime a → InfIrred 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
protected theorem InfPrime.infIrred : InfPrime a → InfIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.le
/-
**InfPrime.inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InfPrime.inf_le (ha : InfPrime a) : b ⊓ c <= a ↔ b <= a ∨ c <= a
参数：ha : InfPrime a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
· 使用定理 `inf_le_of_right_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}
, b ≤ c → a ⊓ b ≤ c
-/
theorem InfPrime.inf_le (ha : InfPrime a) : b ⊓ c ≤ a ↔ b ≤ a ∨ c ≤ a :=
  ⟨fun h => ha.2 h, fun h => h.elim inf_le_of_left_le inf_le_of_right_le⟩

variable [OrderTop α] {s : Finset ι} {f : ι → α}
/-
**not_infIrred_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_infIrred_top : ¬InfIrred (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.not_infIrred`：IsMax.not_infIrred (ha : IsMax a) : ¬InfIrred a
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem not_infIrred_top : ¬InfIrred (⊤ : α) :=
  isMax_top.not_infIrred
/-
**not_infPrime_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_infPrime_top : ¬InfPrime (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.not_infPrime`：IsMax.not_infPrime (ha : IsMax a) : ¬InfPrime a
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem not_infPrime_top : ¬InfPrime (⊤ : α) :=
  isMax_top.not_infPrime
/-
**InfIrred.ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InfIrred.ne_top (ha : InfIrred a) : a != ⊤
参数：ha : InfIrred a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_infIrred_top`：not_infIrred_top : ¬InfIrred (⊤ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem InfIrred.ne_top (ha : InfIrred a) : a ≠ ⊤ := by rintro rfl; exact not_infIrred_top ha
/-
**InfPrime.ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InfPrime.ne_top (ha : InfPrime a) : a != ⊤
参数：ha : InfPrime a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_infPrime_top`：not_infPrime_top : ¬InfPrime (⊤ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem InfPrime.ne_top (ha : InfPrime a) : a ≠ ⊤ := by rintro rfl; exact not_infPrime_top ha
/-
**InfIrred.finset_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InfIrred.finset_inf_eq : InfIrred a -> s.inf f = a -> exists i in s, f i =
 a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupIrred.finset_sup_eq`：SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.
sup f = a) : exists i in s, f i = a
-/
theorem InfIrred.finset_inf_eq : InfIrred a → s.inf f = a → ∃ i ∈ s, f i = a :=
  @SupIrred.finset_sup_eq _ αᵒᵈ _ _ _ _ _
/-
**InfPrime.finset_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InfPrime.finset_inf_le (ha : InfPrime a) : s.inf f <= a ↔ exists i in s, f
 i <= a
参数：ha : InfPrime a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupPrime.le_finset_sup`：SupPrime.le_finset_sup (ha : SupPrime a) : a <= 
s.sup f ↔ exists i in s, a <= f i
-/
theorem InfPrime.finset_inf_le (ha : InfPrime a) : s.inf f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  @SupPrime.le_finset_sup _ αᵒᵈ _ _ _ _ _ ha

variable [WellFoundedGT α]

/-- In a cowell-founded lattice, any element is the infimum of finitely many inf-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
/-
**exists_infIrred_decomposition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_infIrred_decomposition (a : α) : exists s : Finset α, s.inf id = a 
∧ forall ⦃b⦄, b in s -> InfIrred b
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_supIrred_decomposition`：exists_supIrred_decomposition (a : α) : e
xists s : Finset α, s.sup id = a ∧ forall ⦃b⦄, b in s -> SupIrred b
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ

--- 原说明 ---
In a cowell-founded lattice, any element is the infimum of finitely many inf-irr
educible
elements. This is the order-theoretic analogue of prime factorisation.
-/
theorem exists_infIrred_decomposition (a : α) :
    ∃ s : Finset α, s.inf id = a ∧ ∀ ⦃b⦄, b ∈ s → InfIrred b :=
  exists_supIrred_decomposition (α := αᵒᵈ) _

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup α]

@[simp]
/-
**infIrred_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infIrred_toDual {a : α} : InfIrred (toDual a) ↔ SupIrred a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infIrred_toDual {a : α} : InfIrred (toDual a) ↔ SupIrred a :=
  Iff.rfl

@[simp]
/-
**infPrime_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infPrime_toDual {a : α} : InfPrime (toDual a) ↔ SupPrime a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infPrime_toDual {a : α} : InfPrime (toDual a) ↔ SupPrime a :=
  Iff.rfl

@[simp]
/-
**supIrred_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supIrred_ofDual {a : αᵒᵈ} : SupIrred (ofDual a) ↔ InfIrred a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem supIrred_ofDual {a : αᵒᵈ} : SupIrred (ofDual a) ↔ InfIrred a :=
  Iff.rfl

@[simp]
/-
**supPrime_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supPrime_ofDual {a : αᵒᵈ} : SupPrime (ofDual a) ↔ InfPrime a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem supPrime_ofDual {a : αᵒᵈ} : SupPrime (ofDual a) ↔ InfPrime a :=
  Iff.rfl

alias ⟨_, SupIrred.dual⟩ := infIrred_toDual

alias ⟨_, SupPrime.dual⟩ := infPrime_toDual

alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual

alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

@[simp]
/-
**supIrred_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supIrred_toDual {a : α} : SupIrred (toDual a) ↔ InfIrred a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem supIrred_toDual {a : α} : SupIrred (toDual a) ↔ InfIrred a :=
  Iff.rfl

@[simp]
/-
**supPrime_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supPrime_toDual {a : α} : SupPrime (toDual a) ↔ InfPrime a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem supPrime_toDual {a : α} : SupPrime (toDual a) ↔ InfPrime a :=
  Iff.rfl

@[simp]
/-
**infIrred_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infIrred_ofDual {a : αᵒᵈ} : InfIrred (ofDual a) ↔ SupIrred a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infIrred_ofDual {a : αᵒᵈ} : InfIrred (ofDual a) ↔ SupIrred a :=
  Iff.rfl

@[simp]
/-
**infPrime_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infPrime_ofDual {a : αᵒᵈ} : InfPrime (ofDual a) ↔ SupPrime a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infPrime_ofDual {a : αᵒᵈ} : InfPrime (ofDual a) ↔ SupPrime a :=
  Iff.rfl

alias ⟨_, InfIrred.dual⟩ := supIrred_toDual

alias ⟨_, InfPrime.dual⟩ := supPrime_toDual

alias ⟨_, SupIrred.ofDual⟩ := infIrred_ofDual

alias ⟨_, SupPrime.ofDual⟩ := infPrime_ofDual

end SemilatticeInf

section DistribLattice

variable [DistribLattice α] {a : α}

@[simp]
/-
**supPrime_iff_supIrred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supPrime_iff_supIrred : SupPrime a ↔ SupIrred a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupPrime.supIrred`：∀ {α : Type u_2} [inst : SemilatticeSup α] {a : α}, S
upPrime a → SupIrred a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
-/
theorem supPrime_iff_supIrred : SupPrime a ↔ SupIrred a :=
  ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩

@[simp]
/-
**infPrime_iff_infIrred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infPrime_iff_infIrred : InfPrime a ↔ InfIrred a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfPrime.infIrred`：∀ {α : Type u_2} [inst : SemilatticeInf α] {a : α}, I
nfPrime a → InfIrred a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
theorem infPrime_iff_infIrred : InfPrime a ↔ InfIrred a :=
  ⟨InfPrime.infIrred,
    And.imp_right fun h b c => by simp_rw [← sup_eq_left, sup_inf_left]; exact @h _ _⟩

protected alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred
protected alias ⟨_, InfIrred.infPrime⟩ := infPrime_iff_infIrred

end DistribLattice

section LinearOrder

variable [LinearOrder α] {a : α}

/-
**supPrime_iff_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supPrime_iff_not_isMin : SupPrime a ↔ ¬IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem supPrime_iff_not_isMin : SupPrime a ↔ ¬IsMin a :=
  and_iff_left <| by simp
/-
**infPrime_iff_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infPrime_iff_not_isMax : InfPrime a ↔ ¬IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem infPrime_iff_not_isMax : InfPrime a ↔ ¬IsMax a :=
  and_iff_left <| by simp

@[simp]
/-
**supIrred_iff_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supIrred_iff_not_isMin : SupIrred a ↔ ¬IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem supIrred_iff_not_isMin : SupIrred a ↔ ¬IsMin a :=
  and_iff_left fun _ _ => by simpa only [max_eq_iff] using Or.imp And.left And.left

@[simp]
/-
**infIrred_iff_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infIrred_iff_not_isMax : InfIrred a ↔ ¬IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem infIrred_iff_not_isMax : InfIrred a ↔ ¬IsMax a :=
  and_iff_left fun _ _ => by simpa only [min_eq_iff] using Or.imp And.left And.left

end LinearOrder

