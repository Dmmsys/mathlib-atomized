/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Translating pairwise relations on sets to lists

On a list with no duplicates, the condition of `Set.Pairwise` and `List.Pairwise` are equivalent.
-/

public section


variable {α : Type*} {r : α → α → Prop}

namespace List

variable {l : List α}

/-
**List.Nodup.pairwise_of_set_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l : List α} {r : α → α → Prop}, l.Nodup → {x | x ∈ l}.Pa
irwise r → List.Pairwise r l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.pairwise_of_forall_ne`：∀ {α : Type u} {l : List α} {r : α → α
 → Prop}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) → List.Pairwise r l
-/
theorem Nodup.pairwise_of_set_pairwise {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : {x | x ∈ l}.Pairwise r) : l.Pairwise r :=
  hl.pairwise_of_forall_ne h

@[simp]
/-
**List.Nodup.pairwise_coe** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {l : List α} [Std.Symm r], l.Nodup → (
{a | a ∈ l}.Pairwise r ↔ List.Pairwise r l)
参数：{a | a ∈ l}.Pairwise r ↔ List.Pairwise r l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
-/
theorem Nodup.pairwise_coe [Std.Symm r] (hl : l.Nodup) :
    { a | a ∈ l }.Pairwise r ↔ l.Pairwise r := by
  induction l with | nil => simp | cons a l ih => ?_
  rw [List.nodup_cons] at hl
  have : ∀ b ∈ l, ¬a = b → r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.ofPred_or, Set.pairwise_insert_of_symm, ih hl.2, and_comm, forall₂_congr this]

end List

