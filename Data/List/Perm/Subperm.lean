/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Basic
public import Batteries.Tactic.Trans
public import Mathlib.Data.List.Perm.Basic

/-!
# List Sub-permutations

This file develops theory about the `List.Subperm` relation.

## Notation

The notation `<+~` is used for sub-permutations.
-/

public section

open Nat

namespace List
variable {α : Type*} {l l₁ l₂ : List α} {a : α}

open Perm

section Subperm

attribute [trans] Subperm.trans

end Subperm

/-- See also `List.subperm_ext_iff`. -/
/-
**List.subperm_iff_count** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：subperm_iff_count [DecidableEq α] : l₁ <+~ l₂ ↔ forall a, count a l₁ <= co
unt a l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.subperm_ext_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ 
l₂ : List α},   l₁.Subperm l₂ ↔ ∀ x ∈ l₁, List.count x l₁ ≤ List.count x l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
See also `List.subperm_ext_iff`.
-/
lemma subperm_iff_count [DecidableEq α] : l₁ <+~ l₂ ↔ ∀ a, count a l₁ ≤ count a l₂ :=
  subperm_ext_iff.trans <| forall_congr' fun a ↦ by
    by_cases ha : a ∈ l₁ <;> simp [ha, count_eq_zero_of_not_mem]
/-
**List.subperm_iff** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：subperm_iff : l₁ <+~ l₂ ↔ exists l, l ~ l₂ ∧ l₁ <+ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.exists_perm_append`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.S
ublist l₂ → ∃ l, l₂.Perm (l₁ ++ l)
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.Perm.append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (t₁ : List α),
 l₁.Perm l₂ → (l₁ ++ t₁).Perm (l₂ ++ t₁)
· 使用定理 `List.IsPrefix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁
.Sublist l₂
· 使用定理 `List.prefix_append`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁ <+: l₁ ++ l₂
· 使用定理 `List.Subperm.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Subperm l₂ 
→ l₂.Subperm l₃ → l₁.Subperm l₃
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Perm.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Su
bperm l₂
-/
lemma subperm_iff : l₁ <+~ l₂ ↔ ∃ l, l ~ l₂ ∧ l₁ <+ l := by
  refine ⟨?_, fun ⟨l, h₁, h₂⟩ ↦ h₂.subperm.trans h₁.subperm⟩
  rintro ⟨l, h₁, h₂⟩
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩
/-
**List.subperm_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} {a : α}, l.Subperm [a] ↔ l = [] ∨ l = [a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.subperm_iff`：subperm_iff : l₁ <+~ l₂ ↔ exists l, l ~ l₂ ∧ l₁ <+ l
· 使用定理 `List.sublist_singleton`：∀ {α : Type u} {l : List α} {a : α}, l.Sublist [
a] ↔ l = [] ∨ l = [a]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.perm_singleton`：∀ {α : Type u_1} {a : α} {l : List α}, l.Perm [a] ↔
 l = [a]
· 使用定理 `List.nil_subperm`：∀ {α : Type u_1} {l : List α}, [].Subperm l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Subperm.refl`：∀ {α : Type u_1} (l : List α), l.Subperm l
-/
@[simp] lemma subperm_singleton_iff : l <+~ [a] ↔ l = [] ∨ l = [a] := by
  constructor
  · rw [subperm_iff]
    rintro ⟨s, hla, h⟩
    rwa [perm_singleton.mp hla, sublist_singleton] at h
  · rintro (rfl | rfl)
    exacts [nil_subperm, Subperm.refl _]
/-
**List.subperm_cons_self** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：subperm_cons_self : l <+~ a :: l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.sublist_cons_self`：∀ {α : Type u_1} (a : α) (l : List α), l.Sublist
 (a :: l)
-/
lemma subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons_self _ _⟩

protected alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons
/-
**List.Subperm.append** 是 Mathlib 中的一个定理，位于命名空间 `List.Subperm`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Subperm l₂ → r₁.Subperm r₂ → (
l₁ ++ r₁).Subperm (l₂ ++ r₂)
参数：l₁ ++ r₁；l₂ ++ r₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
-/
theorem Subperm.append {l₁ l₂ r₁ r₂ : List α} :
    l₁ <+~ l₂ → r₁ <+~ r₂ → (l₁ ++ r₁) <+~ (l₂ ++ r₂)
  | ⟨l, hl_perm, hl_sub⟩, ⟨r, hr_perm, hr_sub⟩ =>
    ⟨l ++ r, hl_perm.append hr_perm, hl_sub.append hr_sub⟩
/-
**List.map_subperm_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_subperm_map_iff {α β} {l₁ l₂ : List α} {f : α -> β} (hf : Function.Inj
ective f) : (l₁.map f) <+~ (l₂.map f) ↔ l₁ <+~ l₂ where mpr a
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.sublist_map_iff`：∀ {β : Type u_1} {α : Type u_2} {l₂ : List α} {l₁ 
: List β} {f : α → β},   l₁.Sublist (List.map f l₂) ↔ ∃ l', l'.Sublist l₂ ∧ l₁ =
 List.map …
· 使用定理 `List.map_perm_map_iff`：map_perm_map_iff {l' : List α} {f : α -> β} (hf :
 f.Injective) : map f l ~ map f l' ↔ l ~ l'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
theorem map_subperm_map_iff {α β} {l₁ l₂ : List α} {f : α → β} (hf : Function.Injective f) :
    (l₁.map f) <+~ (l₂.map f) ↔ l₁ <+~ l₂ where
  mpr a := by
    obtain ⟨l, hl_perm, hl_sub⟩ := a
    exact ⟨l.map f, hl_perm.map f, hl_sub.map f⟩
  mp a := by
    obtain ⟨w, ⟨perm, sublist⟩⟩ := a
    obtain ⟨x, ⟨sublistₓ, mapₓ⟩⟩ := sublist_map_iff.mp sublist
    use x
    constructor
    · rw [mapₓ] at perm
      exact (map_perm_map_iff hf).mp perm
    · exact sublistₓ

alias ⟨_, Subperm.map⟩ := map_subperm_map_iff
/-
**List.Nodup.subperm** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ → l₁.Subperm l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.subperm_of_subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup → l₁
 ⊆ l₂ → l₁.Subperm l₂
-/
protected theorem Nodup.subperm (d : Nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
  subperm_of_subset d H

end List

