/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Forall2
/-!
# List sections

This file proves some stuff about `List.sections` (definition in `Data.List.Defs`). A section of a
list of lists `[l₁, ..., lₙ]` is a list whose `i`-th element comes from the `i`-th list.
-/

public section


open Nat Function

namespace List

variable {α β : Type*}

/-
**List.mem_sections** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sections {L : List (List α)} {f} : f in sections L ↔ Forall₂ (· in ·) 
f L
参数：List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_sections {L : List (List α)} {f} : f ∈ sections L ↔ Forall₂ (· ∈ ·) f L := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction L generalizing f
    · cases mem_singleton.1 h
      exact Forall₂.nil
    simp only [sections, mem_flatMap, mem_map] at h
    rcases h with ⟨_, _, _, _, rfl⟩
    simp only [*, forall₂_cons, true_and]
  · induction h with
    | nil => simp only [sections, mem_singleton]
    | @cons a l f L al fL fs =>
      simp only [sections, mem_flatMap, mem_map]
      exact ⟨f, fs, a, al, rfl⟩
/-
**List.mem_sections_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sections_length {L : List (List α)} {f} (h : f in sections L) : length
 f = length L
参数：List α；h : f in sections L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.length_eq`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Pro
p} {l₁ : List α} {l₂ : List β},   List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_sections`：mem_sections {L : List (List α)} {f} : f in sections 
L ↔ Forall₂ (· in ·) f L
-/
theorem mem_sections_length {L : List (List α)} {f} (h : f ∈ sections L) : length f = length L :=
  (mem_sections.1 h).length_eq

open scoped Relator in
/-
**List.rel_sections** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → β → Prop},   Relator.LiftFun (Lis
t.Forall₂ (List.Forall₂ r)) (List.Forall₂ (List.Forall₂ r)) List.sections List.s
ections
参数：List.Forall₂ (List.Forall₂ r)；List.Forall₂ (List.Forall₂ r)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `List.rel_flatMap`：rel_flatMap : (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P
) (Function.swap List.flatMap) (Function.swap List.flatMap)
· 使用定理 `List.rel_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} {R : α → β → Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun R 
P)…
-/
theorem rel_sections {r : α → β → Prop} :
    (Forall₂ (Forall₂ r) ⇒ Forall₂ (Forall₂ r)) sections sections
  | _, _, Forall₂.nil => Forall₂.cons Forall₂.nil Forall₂.nil
  | _, _, Forall₂.cons h₀ h₁ =>
    rel_flatMap (rel_sections h₁) fun _ _ hl => rel_map (fun _ _ ha => Forall₂.cons ha hl) h₀

end List

