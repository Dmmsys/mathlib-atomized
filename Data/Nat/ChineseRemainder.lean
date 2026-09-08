/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.Ring.Nat

/-!
# Chinese Remainder Theorem

This file provides definitions and theorems for the Chinese Remainder Theorem. These are used in
Gödel's Beta function, which is used in proving Gödel's incompleteness theorems.

## Main result

- `chineseRemainderOfList`: Definition of the Chinese remainder of a list

## Tags

Chinese Remainder Theorem, Gödel, beta function
-/

@[expose] public section

open scoped Function -- required for scoped `on` notation
namespace Nat

variable {ι : Type*}

/-
**Nat.modEq_list_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：modEq_list_prod_iff {a b} {l : List Nat} (co : l.Pairwise Coprime) : a ≡ b
 [MOD l.prod] ↔ forall i, a ≡ b [MOD l.get i]
参数：co : l.Pairwise Coprime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_list_prod_right_iff`：coprime_list_prod_right_iff {k : Nat} {
l : List Nat} : Coprime k l.prod ↔ forall n in l, Coprime k n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.modEq_and_modEq_iff_modEq_mul`：modEq_and_modEq_iff_modEq_mul {a b m 
n : Nat} (hmn : m.Coprime n) : a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n]
· 使用定理 `List.Pairwise.of_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α → α 
→ Prop}, List.Pairwise R (a :: l) → List.Pairwise R l
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma modEq_list_prod_iff {a b} {l : List ℕ} (co : l.Pairwise Coprime) :
    a ≡ b [MOD l.prod] ↔ ∀ i, a ≡ b [MOD l.get i] := by
  induction l with
  | nil => simp [modEq_one]
  | cons m l ih =>
    have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp only [List.prod_cons, ← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co),
      List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp_all
    · intro h; exact ⟨h 0, fun i => h i.succ⟩
/-
**Nat.modEq_list_map_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：modEq_list_map_prod_iff {a b} {s : ι -> Nat} {l : List ι} (co : l.Pairwise
 (Coprime on s)) : a ≡ b [MOD (l.map s).prod] ↔ forall i in l, a ≡ b [MOD s i]
参数：co : l.Pairwise (Coprime on s)。
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
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.modEq_and_modEq_iff_modEq_mul`：modEq_and_modEq_iff_modEq_mul {a b m 
n : Nat} (hmn : m.Coprime n) : a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n]
· 使用定理 `List.Pairwise.of_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α → α 
→ Prop}, List.Pairwise R (a :: l) → List.Pairwise R l
-/
lemma modEq_list_map_prod_iff {a b} {s : ι → ℕ} {l : List ι} (co : l.Pairwise (Coprime on s)) :
    a ≡ b [MOD (l.map s).prod] ↔ ∀ i ∈ l, a ≡ b [MOD s i] := by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

variable (a s : ι → ℕ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The natural number less than `(l.map s).prod` congruent to
`a i` mod `s i` for all  `i ∈ l`. -/
/-
**Nat.chineseRemainderOfList** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfList : (l : List ι) -> l.Pairwise (Coprime on s) -> { k 
// forall i in l, k ≡ a i [MOD s i] } | [], _ => ⟨0, by simp⟩ | i :: l, co => by
 have : Coprime (s i) (l.map s).prod
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural number less than `(l.map s).prod` congruent to
`a i` mod `s i` for all  `i ∈ l`.
-/
def chineseRemainderOfList : (l : List ι) → l.Pairwise (Coprime on s) →
    { k // ∀ i ∈ l, k ≡ a i [MOD s i] }
  | [],     _  => ⟨0, by simp⟩
  | i :: l, co => by
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    have ih := chineseRemainderOfList l co.of_cons
    have k := chineseRemainder this (a i) ih
    use k
    simp only [List.mem_cons, forall_eq_or_imp, k.prop.1, true_and]
    intro j hj
    exact ((modEq_list_map_prod_iff co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)
/-
**Nat.chineseRemainderOfList_nil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {ι : Type u_1} (a s : ι → ℕ), ↑(Nat.chineseRemainderOfList a s [] ⋯) = 0
参数：a s : ι → ℕ；Nat.chineseRemainderOfList a s [] ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem chineseRemainderOfList_nil :
    (chineseRemainderOfList a s [] List.Pairwise.nil : ℕ) = 0 := rfl
/-
**Nat.chineseRemainderOfList_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfList_lt_prod (l : List ι) (co : l.Pairwise (Coprime on s
)) (hs : forall i in l, s i != 0) : chineseRemainderOfList a s l co < (l.map s).
prod
参数：l : List ι；co : l.Pairwise (Coprime on s)；hs : forall i in l, s i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Nat.chineseRemainder_lt_mul`：chineseRemainder_lt_mul (co : n.Coprime m) 
(a b : Nat) (hn : n != 0) (hm : m != 0) : ↑(chineseRemainder co a b) < n * m
· 使用定理 `List.Pairwise.of_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α → α 
→ Prop}, List.Pairwise R (a :: l) → List.Pairwise R l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem chineseRemainderOfList_lt_prod (l : List ι)
    (co : l.Pairwise (Coprime on s)) (hs : ∀ i ∈ l, s i ≠ 0) :
    chineseRemainderOfList a s l co < (l.map s).prod := by
  cases l with
  | nil => simp
  | cons i l =>
    simp only [chineseRemainderOfList, List.map_cons, List.prod_cons]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    refine chineseRemainder_lt_mul this (a i) (chineseRemainderOfList a s l co.of_cons)
      (hs i List.mem_cons_self) ?_
    simp only [ne_eq, List.prod_eq_zero_iff, List.mem_map, not_exists, not_and]
    intro j hj
    exact hs j (List.mem_cons_of_mem _ hj)
/-
**Nat.chineseRemainderOfList_modEq_unique** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfList_modEq_unique (l : List ι) (co : l.Pairwise (Coprime
 on s)) {z} (hz : forall i in l, z ≡ a i [MOD s i]) : z ≡ chineseRemainderOfList
 a s l co [MOD (l.map s).prod]
参数：l : List ι；co : l.Pairwise (Coprime on s)；hz : forall i in l, z ≡ a i [MOD s 
i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Nat.chineseRemainder_modEq_unique`：chineseRemainder_modEq_unique (co : n
.Coprime m) {a b z} (hzan : z ≡ a [MOD n]) (hzbm : z ≡ b [MOD m]) : z ≡ chineseR
emainder co a b [MOD n …
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.Pairwise.of_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α → α 
→ Prop}, List.Pairwise R (a :: l) → List.Pairwise R l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem chineseRemainderOfList_modEq_unique (l : List ι)
    (co : l.Pairwise (Coprime on s)) {z} (hz : ∀ i ∈ l, z ≡ a i [MOD s i]) :
    z ≡ chineseRemainderOfList a s l co [MOD (l.map s).prod] := by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    exact chineseRemainder_modEq_unique this
      (hz i List.mem_cons_self) (ih co.of_cons (fun j hj => hz j (List.mem_cons_of_mem _ hj)))
/-
**Nat.chineseRemainderOfList_perm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfList_perm {l l' : List ι} (hl : l.Perm l') (hs : forall 
i in l, s i != 0) (co : l.Pairwise (Coprime on s)) : (chineseRemainderOfList a s
 l co : Nat) = chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr)
参数：hl : l.Perm l'；hs : forall i in l, s i != 0；co : l.Pairwise (Coprime on s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.perm`：∀ {α : Type u_1} {R : α → α → Prop} {l l' : List α},
   List.Pairwise R l → l.Perm l' → (∀ {x y : α}, R x y → R y x) → List.Pairwise 
R l'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用引理 `Nat.ModEq.eq_of_lt_of_lt`：eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m
) (hb : b < m) : a = b
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.chineseRemainderOfList_modEq_unique`：chineseRemainderOfList_modEq_un
ique (l : List ι) (co : l.Pairwise (Coprime on s)) {z} (hz : forall i in l, z ≡ 
a i [MOD s i]) : z ≡ chineseR…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `Nat.chineseRemainderOfList_lt_prod`：chineseRemainderOfList_lt_prod (l : 
List ι) (co : l.Pairwise (Coprime on s)) (hs : forall i in l, s i != 0) : chines
eRemainderOfList a s l c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem chineseRemainderOfList_perm {l l' : List ι} (hl : l.Perm l')
    (hs : ∀ i ∈ l, s i ≠ 0) (co : l.Pairwise (Coprime on s)) :
    (chineseRemainderOfList a s l co : ℕ) =
    chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr) := by
  let z := chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr)
  have hlp : (l.map s).prod = (l'.map s).prod := List.Perm.prod_eq (List.Perm.map s hl)
  exact (chineseRemainderOfList_modEq_unique a s l co (z := z)
    (fun i hi => z.prop i (hl.symm.mem_iff.mpr hi))).symm.eq_of_lt_of_lt
      (chineseRemainderOfList_lt_prod _ _ _ _ hs)
      (by rw [hlp]
          exact chineseRemainderOfList_lt_prod _ _ _ _
            (by simpa [List.Perm.mem_iff hl.symm] using hs))

/-- The natural number less than `(m.map s).prod` congruent to
`a i` mod `s i` for all  `i ∈ m`. -/
/-
**Nat.chineseRemainderOfMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfMultiset {m : Multiset ι} : m.Nodup -> (forall i in m, s
 i != 0) -> Set.Pairwise {x | x in m} (Coprime on s) -> { k // forall i in m, k 
≡ a i [MOD s i] }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural number less than `(m.map s).prod` congruent to
`a i` mod `s i` for all  `i ∈ m`.
-/
def chineseRemainderOfMultiset {m : Multiset ι} :
    m.Nodup → (∀ i ∈ m, s i ≠ 0) → Set.Pairwise {x | x ∈ m} (Coprime on s) →
    { k // ∀ i ∈ m, k ≡ a i [MOD s i] } :=
  Quotient.recOn m
    (fun l nod _ co =>
      chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
    (fun l l' (pp : l.Perm l') ↦
      funext fun nod' : l'.Nodup =>
      have nod : l.Nodup := pp.symm.nodup_iff.mp nod'
      funext fun hs' : ∀ i ∈ l', s i ≠ 0 =>
      have hs : ∀ i ∈ l, s i ≠ 0 := by simpa [List.Perm.mem_iff pp] using hs'
      funext fun co' : Set.Pairwise {x | x ∈ l'} (Coprime on s) =>
      have co : Set.Pairwise {x | x ∈ l} (Coprime on s) := by simpa [List.Perm.mem_iff pp] using co'
      have lco : l.Pairwise (Coprime on s) := List.Nodup.pairwise_of_forall_ne nod co
      have : ∀ {m' e nod'' hs'' co''}, @Eq.ndrec (Multiset ι) l
        (fun m ↦ m.Nodup → (∀ i ∈ m, s i ≠ 0) →
          Set.Pairwise {x | x ∈ m} (Coprime on s) → { k // ∀ i ∈ m, k ≡ a i [MOD s i] })
        (fun nod _ co ↦ chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
          m' e nod'' hs'' co'' =
        (chineseRemainderOfList a s l lco : ℕ) := by
          rintro _ rfl _ _ _; rfl
      by ext; exact this.trans <| chineseRemainderOfList_perm a s pp hs lco)
/-
**Nat.chineseRemainderOfMultiset_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfMultiset_lt_prod {m : Multiset ι} (nod : m.Nodup) (hs : 
forall i in m, s i != 0) (pp : Set.Pairwise {x | x in m} (Coprime on s)) : chine
seRemainderOfMultiset a s nod hs pp < (m.map s).prod
参数：nod : m.Nodup；hs : forall i in m, s i != 0；pp : Set.Pairwise {x | x in m} (Co
prime on s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.chineseRemainderOfList_lt_prod`：chineseRemainderOfList_lt_prod (l : 
List ι) (co : l.Pairwise (Coprime on s)) (hs : forall i in l, s i != 0) : chines
eRemainderOfList a s l c…
· 使用定理 `List.Nodup.pairwise_of_forall_ne`：∀ {α : Type u} {l : List α} {r : α → α
 → Prop}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) → List.Pairwise r l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem chineseRemainderOfMultiset_lt_prod {m : Multiset ι}
    (nod : m.Nodup) (hs : ∀ i ∈ m, s i ≠ 0) (pp : Set.Pairwise {x | x ∈ m} (Coprime on s)) :
    chineseRemainderOfMultiset a s nod hs pp < (m.map s).prod := by
  induction m using Quot.ind with | _ l
  unfold chineseRemainderOfMultiset
  simpa using! chineseRemainderOfList_lt_prod a s l
    (List.Nodup.pairwise_of_forall_ne nod pp) (by simpa using! hs)

/-- The natural number less than `∏ i ∈ t, s i` congruent to
`a i` mod `s i` for all  `i ∈ t`. -/
/-
**Nat.chineseRemainderOfFinset** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfFinset (t : Finset ι) (hs : forall i in t, s i != 0) (pp
 : Set.Pairwise t (Coprime on s)) : { k // forall i in t, k ≡ a i [MOD s i] }
参数：t : Finset ι；hs : forall i in t, s i != 0；pp : Set.Pairwise t (Coprime on s)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup

--- 原说明 ---
The natural number less than `∏ i ∈ t, s i` congruent to
`a i` mod `s i` for all  `i ∈ t`.
-/
def chineseRemainderOfFinset (t : Finset ι)
    (hs : ∀ i ∈ t, s i ≠ 0) (pp : Set.Pairwise t (Coprime on s)) :
    { k // ∀ i ∈ t, k ≡ a i [MOD s i] } := by
  simpa using chineseRemainderOfMultiset a s t.nodup (by simpa using hs) (by simpa using pp)
/-
**Nat.chineseRemainderOfFinset_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainderOfFinset_lt_prod {t : Finset ι} (hs : forall i in t, s i !
= 0) (pp : Set.Pairwise t (Coprime on s)) : chineseRemainderOfFinset a s t hs pp
 < ∏ i in t, s i
参数：hs : forall i in t, s i != 0；pp : Set.Pairwise t (Coprime on s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.chineseRemainderOfMultiset_lt_prod`：chineseRemainderOfMultiset_lt_pr
od {m : Multiset ι} (nod : m.Nodup) (hs : forall i in m, s i != 0) (pp : Set.Pai
rwise {x | x in m} (Coprime …
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem chineseRemainderOfFinset_lt_prod {t : Finset ι}
    (hs : ∀ i ∈ t, s i ≠ 0) (pp : Set.Pairwise t (Coprime on s)) :
    chineseRemainderOfFinset a s t hs pp < ∏ i ∈ t, s i := by
  simpa [chineseRemainderOfFinset] using
    chineseRemainderOfMultiset_lt_prod a s t.nodup (by simpa using hs) (by simpa using pp)

end Nat

