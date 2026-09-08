/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Tactic.Common
public import Batteries.Data.List.Lemmas

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively.
-/

public section

assert_not_exists Monoid Set.range

open Nat

variable {α β : Type*}

namespace List

@[simp]
/-
**List.countP_lt_length_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：countP_lt_length_iff {l : List α} {p : α -> Bool} : l.countP p < l.length 
↔ exists a in l, p a = false
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem countP_lt_length_iff {l : List α} {p : α → Bool} :
    l.countP p < l.length ↔ ∃ a ∈ l, p a = false := by
  simp [Nat.lt_iff_le_and_ne, countP_le_length]

variable [BEq α] [LawfulBEq α] {l l₁ l₂ : List α}

@[simp]
/-
**List.count_lt_length_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_lt_length_iff {a : α} : l.count a < l.length ↔ exists b in l, b != a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem count_lt_length_iff {a : α} : l.count a < l.length ↔ ∃ b ∈ l, b ≠ a := by simp [count]
/-
**List.countP_erase** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：countP_erase (p : α -> Bool) (l : List α) (a : α) : countP p (l.erase a) =
 countP p l - if a in l ∧ p a then 1 else 0
参数：p : α -> Bool；l : List α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma countP_erase (p : α → Bool) (l : List α) (a : α) :
    countP p (l.erase a) = countP p l - if a ∈ l ∧ p a then 1 else 0 := by
  grind [countP_eq_length_filter]
/-
**List.count_diff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α) (l₁ l₂ : List α),   
List.count a (l₁.diff l₂) = List.count a l₁ - List.count a l₂
参数：a : α；l₁ l₂ : List α；l₁.diff l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma count_diff (a : α) (l₁ : List α) :
    ∀ l₂, count a (l₁.diff l₂) = count a l₁ - count a l₂
  | [] => rfl
  | b :: l₂ => by
    simp only [diff_cons, count_diff, count_erase, beq_iff_eq, Nat.sub_right_comm, count_cons,
      Nat.sub_add_eq]
/-
**List.countP_diff** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：countP_diff (hl : l₂ <+~ l₁) (p : α -> Bool) : countP p (l₁.diff l₂) = cou
ntP p l₁ - countP p l₂
参数：hl : l₂ <+~ l₁；p : α -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_eq_of_eq_add`：∀ {a b c : ℕ}, a = c + b → a - b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.countP_append`：∀ {α : Type u_1} {p : α → Bool} {l₁ l₂ : List α}, Li
st.countP p (l₁ ++ l₂) = List.countP p l₁ + List.countP p l₂
· 使用定理 `List.Perm.countP_eq`：∀ {α : Type u_1} (p : α → Bool) {l₁ l₂ : List α}, l
₁.Perm l₂ → List.countP p l₁ = List.countP p l₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.subperm_append_diff_self_of_count_le`：∀ {α : Type u_1} [inst : BEq 
α] [LawfulBEq α] {l₁ l₂ : List α},   (∀ x ∈ l₁, List.count x l₁ ≤ List.count x l
₂) → (l₁ ++ l₂.diff l₁).Perm l₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.subperm_ext_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ 
l₂ : List α},   l₁.Subperm l₂ ↔ ∀ x ∈ l₁, List.count x l₁ ≤ List.count x l₂
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
-/
lemma countP_diff (hl : l₂ <+~ l₁) (p : α → Bool) :
    countP p (l₁.diff l₂) = countP p l₁ - countP p l₂ := by
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [← countP_append]
  exact ((subperm_append_diff_self_of_count_le <| subperm_ext_iff.1 hl).symm.trans
    perm_append_comm).countP_eq _

@[simp]
/-
**List.count_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_map_of_injective [BEq β] [LawfulBEq β] (l : List α) (f : α -> β) (hf
 : Function.Injective f) (x : α) : count (f x) (map f l) = count x l
参数：l : List α；f : α -> β；hf : Function.Injective f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.countP_map`：∀ {α : Type u_2} {β : Type u_1} {p : β → Bool} {f : α →
 β} {l : List α},   List.countP p (List.map f l) = List.countP (p ∘ f) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.beq_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α
] [LawfulBEq α] [inst_2 : BEq β] [LawfulBEq β] {f : α → β},   Function.Injective
 f → ∀ {a b : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_map_of_injective [BEq β] [LawfulBEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map]
  unfold Function.comp
  simp only [hf.beq_eq]

end List

