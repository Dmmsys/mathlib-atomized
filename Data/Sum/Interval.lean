/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite intervals in a disjoint union

This file provides the `LocallyFiniteOrder` instance for the disjoint sum and linear sum of two
orders and calculates the cardinality of their finite intervals.
-/

@[expose] public section


open Function Sum

namespace Finset

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

section SumLift₂

variable (f f₁ g₁ : α₁ → β₁ → Finset γ₁) (g f₂ g₂ : α₂ → β₂ → Finset γ₂)

/-- Lifts maps `α₁ → β₁ → Finset γ₁` and `α₂ → β₂ → Finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be generalized to `Alternative` functors if we can
make sure to keep computability and universe polymorphism. -/
@[simp]
/-
**Finset.sumLift** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts maps `α₁ → β₁ → Finset γ₁` and `α₂ → β₂ → Finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be generalized to `Alternative` fu
nctors if we can
make sure to keep computability and universe polymorphism.
-/
def sumLift₂ : ∀ (_ : α₁ ⊕ α₂) (_ : β₁ ⊕ β₂), Finset (γ₁ ⊕ γ₂)
  | inl a, inl b => (f a b).map Embedding.inl
  | inl _, inr _ => ∅
  | inr _, inl _ => ∅
  | inr a, inr b => (g a b).map Embedding.inr

variable {f f₁ g₁ g f₂ g₂} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}
/-
**Finset.mem_sumLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_sumLift₂ :
    c ∈ sumLift₂ f g a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁) ∨
        ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ := by
  constructor
  · rcases a with a | a <;> rcases b with b | b
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h ↦ (notMem_empty _ h).elim
    · refine fun h ↦ (notMem_empty _ h).elim
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩
  · rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩) <;> exact mem_map_of_mem _ h
/-
**Finset.inl_mem_sumLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_mem_sumLift₂ {c₁ : γ₁} :
    inl c₁ ∈ sumLift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ := by
  rw [mem_sumLift₂, or_iff_left]
  · simp only [inl.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h
/-
**Finset.inr_mem_sumLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_mem_sumLift₂ {c₂ : γ₂} :
    inr c₂ ∈ sumLift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ := by
  rw [mem_sumLift₂, or_iff_right]
  · simp only [inr.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h
/-
**Finset.sumLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLift₂_eq_empty :
    sumLift₂ f g a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅) ∧
        ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor <;>
    · rintro a b rfl rfl
      exact map_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · rfl
  · rfl
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)
/-
**Finset.sumLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLift₂_nonempty :
    (sumLift₂ f g a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).Nonempty) ∨
        ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLift₂_eq_empty, not_and_or, not_forall, exists_prop]
/-
**Finset.sumLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) :
    ∀ a b, sumLift₂ f₁ f₂ a b ⊆ sumLift₂ g₁ g₂ a b
  | inl _, inl _ => map_subset_map.2 (h₁ _ _)
  | inl _, inr _ => Subset.rfl
  | inr _, inl _ => Subset.rfl
  | inr _, inr _ => map_subset_map.2 (h₂ _ _)

end SumLift₂

section SumLexLift
variable (f₁ f₁' : α₁ → β₁ → Finset γ₁) (f₂ f₂' : α₂ → β₂ → Finset γ₂)
  (g₁ g₁' : α₁ → β₂ → Finset γ₁) (g₂ g₂' : α₁ → β₂ → Finset γ₂)

/-- Lifts maps `α₁ → β₁ → Finset γ₁`, `α₂ → β₂ → Finset γ₂`, `α₁ → β₂ → Finset γ₁`,
`α₂ → β₂ → Finset γ₂`  to a map `α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be generalized to
alternative monads if we can make sure to keep computability and universe polymorphism. -/
/-
**Finset.sumLexLift** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α₁ : Type u_1} →   {α₂ : Type u_2} →     {β₁ : Type u_3} →       {β₂ : Ty
pe u_4} →         {γ₁ : Type u_5} →           {γ₂ : Type u_6} →             (α₁ 
→ β₁ → Finset γ₁) →               (α₂ → β₂ → Finset γ₂) →                 (α₁ → 
β₂ → Finset γ₁) → (α₁ → β₂ → Finset γ₂) → α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)
参数：α₁ → β₁ → Finset γ₁；α₂ → β₂ → Finset γ₂；α₁ → β₂ → Finset γ₁；α₁ → β₂ → Finset 
γ₂；γ₁ ⊕ γ₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)

--- 原说明 ---
Lifts maps `α₁ → β₁ → Finset γ₁`, `α₂ → β₂ → Finset γ₂`, `α₁ → β₂ → Finset γ₁`,
`α₂ → β₂ → Finset γ₂`  to a map `α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be
 generalized to
alternative monads if we can make sure to keep computability and universe polymo
rphism.
-/
def sumLexLift : α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)
  | inl a, inl b => (f₁ a b).map Embedding.inl
  | inl a, inr b => (g₁ a b).disjSum (g₂ a b)
  | inr _, inl _ => ∅
  | inr a, inr b => (f₂ a b).map ⟨_, inr_injective⟩

@[simp]
/-
**Finset.sumLexLift_inl_inl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_inl_inl (a : α₁) (b : β₁) : sumLexLift f₁ f₂ g₁ g₂ (inl a) (inl
 b) = (f₁ a b).map Embedding.inl
参数：a : α₁；b : β₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumLexLift_inl_inl (a : α₁) (b : β₁) :
    sumLexLift f₁ f₂ g₁ g₂ (inl a) (inl b) = (f₁ a b).map Embedding.inl := rfl

@[simp]
/-
**Finset.sumLexLift_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_inl_inr (a : α₁) (b : β₂) : sumLexLift f₁ f₂ g₁ g₂ (inl a) (inr
 b) = (g₁ a b).disjSum (g₂ a b)
参数：a : α₁；b : β₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumLexLift_inl_inr (a : α₁) (b : β₂) :
    sumLexLift f₁ f₂ g₁ g₂ (inl a) (inr b) = (g₁ a b).disjSum (g₂ a b) := rfl

@[simp]
/-
**Finset.sumLexLift_inr_inl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_inr_inl (a : α₂) (b : β₁) : sumLexLift f₁ f₂ g₁ g₂ (inr a) (inl
 b) = ∅
参数：a : α₂；b : β₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumLexLift_inr_inl (a : α₂) (b : β₁) : sumLexLift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅ := rfl

@[simp]
/-
**Finset.sumLexLift_inr_inr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_inr_inr (a : α₂) (b : β₂) : sumLexLift f₁ f₂ g₁ g₂ (inr a) (inr
 b) = (f₂ a b).map ⟨_, inr_injective⟩
参数：a : α₂；b : β₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumLexLift_inr_inr (a : α₂) (b : β₂) :
    sumLexLift f₁ f₂ g₁ g₂ (inr a) (inr b) = (f₂ a b).map ⟨_, inr_injective⟩ := rfl

variable {f₁ g₁ f₂ g₂ f₁' g₁' f₂' g₂'} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}
/-
**Finset.mem_sumLexLift** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_sumLexLift : c in sumLexLift f₁ f₂ g₁ g₂ a b ↔ (exists a₁ b₁ c₁, a = i
nl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ in f₁ a₁ b₁) ∨ (exists a₁ b₂ c₁, a = inl a₁
 ∧ b = inr b₂ ∧ c = inl c₁ ∧ c₁ in g₁ a₁ b₂) ∨ (exists a₁ b₂ c₂, a = inl a₁ ∧ b 
= inr b₂ ∧ c = inr c₂ ∧ c₂ in g₂ a₁ b₂) ∨ exists a₂ b₂ c₂, a = inr a₂ ∧ b = inr 
b₂ ∧ c = inr c₂ ∧ c₂ in f₂ a₂ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sumLexLift.eq_1`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3
} {β₂ : Type u_4} {γ₁ : Type u_5} {γ₂ : Type u_6}   (f₁ : α₁ → β₁ → Finset γ₁) (
f₂ : α₂ → β₂…
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_disjSum`：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s ∧
 inl a = x) ∨ exists b, b in t ∧ inr b = x
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Finset.sumLexLift.eq_4`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3
} {β₂ : Type u_4} {γ₁ : Type u_5} {γ₂ : Type u_6}   (f₁ : α₁ → β₁ → Finset γ₁) (
f₂ : α₂ → β₂…
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.inl_mem_disjSum`：inl_mem_disjSum : inl a in s.disjSum t ↔ a in s
· 使用定理 `Finset.inr_mem_disjSum`：inr_mem_disjSum : inr b in s.disjSum t ↔ b in t
-/
lemma mem_sumLexLift :
    c ∈ sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
        (∃ a₁ b₂ c₁, a = inl a₁ ∧ b = inr b₂ ∧ c = inl c₁ ∧ c₁ ∈ g₁ a₁ b₂) ∨
          (∃ a₁ b₂ c₂, a = inl a₁ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
            ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ f₂ a₂ b₂ := by
  constructor
  · obtain a | a := a <;> obtain b | b := b
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h ↦ (mem_disjSum.1 h).elim ?_ ?_
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩)
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inr <| Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩)
    · exact fun h ↦ (notMem_empty _ h).elim
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr (Or.inr <| Or.inr <| ⟨a, b, c, rfl, rfl, rfl, hc⟩)
  · rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩ |
      ⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩)
    · exact mem_map_of_mem _ hc
    · exact inl_mem_disjSum.2 hc
    · exact inr_mem_disjSum.2 hc
    · exact mem_map_of_mem _ hc
/-
**Finset.inl_mem_sumLexLift** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inl_mem_sumLexLift {c₁ : γ₁} : inl c₁ in sumLexLift f₁ f₂ g₁ g₂ a b ↔ (exi
sts a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ in f₁ a₁ b₁) ∨ exists a₁ b₂, a = inl a₁ 
∧ b = inr b₂ ∧ c₁ in g₁ a₁ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inl_mem_sumLexLift {c₁ : γ₁} :
    inl c₁ ∈ sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
        ∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₁ ∈ g₁ a₁ b₂ := by
  simp [mem_sumLexLift]
/-
**Finset.inr_mem_sumLexLift** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inr_mem_sumLexLift {c₂ : γ₂} : inr c₂ in sumLexLift f₁ f₂ g₁ g₂ a b ↔ (exi
sts a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₂ in g₂ a₁ b₂) ∨ exists a₂ b₂, a = inr a₂ 
∧ b = inr b₂ ∧ c₂ in f₂ a₂ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inr_mem_sumLexLift {c₂ : γ₂} :
    inr c₂ ∈ sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
        ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ f₂ a₂ b₂ := by
  simp [mem_sumLexLift]
/-
**Finset.sumLexLift_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_mono (hf₁ : forall a b, f₁ a b subseteq f₁' a b) (hf₂ : forall 
a b, f₂ a b subseteq f₂' a b) (hg₁ : forall a b, g₁ a b subseteq g₁' a b) (hg₂ :
 forall a b, g₂ a b subseteq g₂' a b) (a : α₁ oplus α₂) (b : β₁ oplus β₂) : sumL
exLift f₁ f₂ g₁ g₂ a b subseteq sumLexLift f₁' f₂' g₁' g₂' a b
参数：hf₁ : forall a b, f₁ a b subseteq f₁' a b；hf₂ : forall a b, f₂ a b subseteq f
₂' a b；hg₁ : forall a b, g₁ a b subseteq g₁' a b；hg₂ : forall a b, g₂ a b subset
eq g₂' a b；a : α₁ oplus α₂；b : β₁ oplus β₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.map_subset_map`：map_subset_map {s₁ s₂ : Finset α} : s₁.map f subs
eteq s₂.map f ↔ s₁ subseteq s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjSum_mono`：disjSum_mono (hs : s₁ subseteq s₂) (ht : t₁ subsete
q t₂) : s₁.disjSum t₁ subseteq s₂.disjSum t₂
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
lemma sumLexLift_mono (hf₁ : ∀ a b, f₁ a b ⊆ f₁' a b) (hf₂ : ∀ a b, f₂ a b ⊆ f₂' a b)
    (hg₁ : ∀ a b, g₁ a b ⊆ g₁' a b) (hg₂ : ∀ a b, g₂ a b ⊆ g₂' a b) (a : α₁ ⊕ α₂)
    (b : β₁ ⊕ β₂) : sumLexLift f₁ f₂ g₁ g₂ a b ⊆ sumLexLift f₁' f₂' g₁' g₂' a b := by
  cases a <;> cases b
  exacts [map_subset_map.2 (hf₁ _ _), disjSum_mono (hg₁ _ _) (hg₂ _ _), Subset.rfl,
    map_subset_map.2 (hf₂ _ _)]
/-
**Finset.sumLexLift_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_eq_empty : sumLexLift f₁ f₂ g₁ g₂ a b = ∅ ↔ (forall a₁ b₁, a = 
inl a₁ -> b = inl b₁ -> f₁ a₁ b₁ = ∅) ∧ (forall a₁ b₂, a = inl a₁ -> b = inr b₂ 
-> g₁ a₁ b₂ = ∅ ∧ g₂ a₁ b₂ = ∅) ∧ forall a₂ b₂, a = inr a₂ -> b = inr b₂ -> f₂ a
₂ b₂ = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.map_eq_empty`：map_eq_empty : s.map f = ∅ ↔ s = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjSum_eq_empty`：disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t 
= ∅
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.disjSum_empty`：disjSum_empty : s.disjSum (∅ : Finset β) = s.map E
mbedding.inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumLexLift_eq_empty :
    sumLexLift f₁ f₂ g₁ g₂ a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f₁ a₁ b₁ = ∅) ∧
        (∀ a₁ b₂, a = inl a₁ → b = inr b₂ → g₁ a₁ b₂ = ∅ ∧ g₂ a₁ b₂ = ∅) ∧
          ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → f₂ a₂ b₂ = ∅ := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ?_⟩
  any_goals rintro a b rfl rfl; exact map_eq_empty.1 h
  · rintro a b rfl rfl; exact disjSum_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · simp [h.2.1 _ _ rfl rfl]
  · rfl
  · exact map_eq_empty.2 (h.2.2 _ _ rfl rfl)
/-
**Finset.sumLexLift_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumLexLift_nonempty : (sumLexLift f₁ f₂ g₁ g₂ a b).Nonempty ↔ (exists a₁ b
₁, a = inl a₁ ∧ b = inl b₁ ∧ (f₁ a₁ b₁).Nonempty) ∨ (exists a₁ b₂, a = inl a₁ ∧ 
b = inr b₂ ∧ ((g₁ a₁ b₂).Nonempty ∨ (g₂ a₁ b₂).Nonempty)) ∨ exists a₂ b₂, a = in
r a₂ ∧ b = inr b₂ ∧ (f₂ a₂ b₂).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sumLexLift_nonempty :
    (sumLexLift f₁ f₂ g₁ g₂ a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f₁ a₁ b₁).Nonempty) ∨
        (∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ ((g₁ a₁ b₂).Nonempty ∨ (g₂ a₁ b₂).Nonempty)) ∨
          ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (f₂ a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLexLift_eq_empty, not_and_or, exists_prop, not_forall]

end SumLexLift
end Finset

open Finset

namespace Sum

variable {α β : Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

section LocallyFiniteOrder
variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]

/-
**Sum.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder (α oplus β) where finsetIcc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (α ⊕ β) where
  finsetIcc := sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

variable (a₁ a₂ : α) (b₁ b₂ : β)
/-
**Sum.Icc_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Icc_inl_inl : Icc (inl a₁ : α oplus β) (inl a₂) = (Icc a₁ a₂).map Embeddin
g.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_inl_inl : Icc (inl a₁ : α ⊕ β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl :=
  rfl
/-
**Sum.Ico_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ico_inl_inl : Ico (inl a₁ : α oplus β) (inl a₂) = (Ico a₁ a₂).map Embeddin
g.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_inl_inl : Ico (inl a₁ : α ⊕ β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl :=
  rfl
/-
**Sum.Ioc_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioc_inl_inl : Ioc (inl a₁ : α oplus β) (inl a₂) = (Ioc a₁ a₂).map Embeddin
g.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inl_inl : Ioc (inl a₁ : α ⊕ β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl :=
  rfl
/-
**Sum.Ioo_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioo_inl_inl : Ioo (inl a₁ : α oplus β) (inl a₂) = (Ioo a₁ a₂).map Embeddin
g.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inl_inl : Ioo (inl a₁ : α ⊕ β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl :=
  rfl

@[simp]
/-
**Sum.Icc_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Ico_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Ioc_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Ioo_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Icc_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Ico_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Ioc_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
/-
**Sum.Ioo_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ :=
  rfl
/-
**Sum.Icc_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Icc_inr_inr : Icc (inr b₁ : α oplus β) (inr b₂) = (Icc b₁ b₂).map Embeddin
g.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_inr_inr : Icc (inr b₁ : α ⊕ β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr :=
  rfl
/-
**Sum.Ico_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ico_inr_inr : Ico (inr b₁ : α oplus β) (inr b₂) = (Ico b₁ b₂).map Embeddin
g.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_inr_inr : Ico (inr b₁ : α ⊕ β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr :=
  rfl
/-
**Sum.Ioc_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioc_inr_inr : Ioc (inr b₁ : α oplus β) (inr b₂) = (Ioc b₁ b₂).map Embeddin
g.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inr_inr : Ioc (inr b₁ : α ⊕ β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr :=
  rfl
/-
**Sum.Ioo_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioo_inr_inr : Ioo (inr b₁ : α oplus β) (inr b₂) = (Ioo b₁ b₂).map Embeddin
g.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inr_inr : Ioo (inr b₁ : α ⊕ β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr :=
  rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [Preorder α] [Preorder β] [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]

/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyFiniteOrderBot (α ⊕ β) where
  finsetIic := Sum.elim (Iic · |>.map .inl) (Iic · |>.map .inr)
  finsetIio := Sum.elim (Iio · |>.map .inl) (Iio · |>.map .inr)
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

variable (a : α) (b : β)
/-
**Sum.Iic_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Iic_inl : Iic (inl a : α oplus β) = (Iic a).map Embedding.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_inl : Iic (inl a : α ⊕ β) = (Iic a).map Embedding.inl := rfl
/-
**Sum.Iic_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Iic_inr : Iic (inr b : α oplus β) = (Iic b).map Embedding.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_inr : Iic (inr b : α ⊕ β) = (Iic b).map Embedding.inr := rfl
/-
**Sum.Iio_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Iio_inl : Iio (inl a : α oplus β) = (Iio a).map Embedding.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_inl : Iio (inl a : α ⊕ β) = (Iio a).map Embedding.inl := rfl
/-
**Sum.Iio_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Iio_inr : Iio (inr b : α oplus β) = (Iio b).map Embedding.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_inr : Iio (inr b : α ⊕ β) = (Iio b).map Embedding.inr := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [Preorder α] [Preorder β] [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β]

/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyFiniteOrderTop (α ⊕ β) where
  finsetIci := Sum.elim (Ici · |>.map .inl) (Ici · |>.map .inr)
  finsetIoi := Sum.elim (Ioi · |>.map .inl) (Ioi · |>.map .inr)
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

variable (a : α) (b : β)
/-
**Sum.Ici_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ici_inl : Ici (inl a : α oplus β) = (Ici a).map Embedding.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_inl : Ici (inl a : α ⊕ β) = (Ici a).map Embedding.inl := rfl
/-
**Sum.Ici_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ici_inr : Ici (inr b : α oplus β) = (Ici b).map Embedding.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_inr : Ici (inr b : α ⊕ β) = (Ici b).map Embedding.inr := rfl
/-
**Sum.Ioi_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioi_inl : Ioi (inl a : α oplus β) = (Ioi a).map Embedding.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioi_inl : Ioi (inl a : α ⊕ β) = (Ioi a).map Embedding.inl := rfl
/-
**Sum.Ioi_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：Ioi_inr : Ioi (inr b : α oplus β) = (Ioi b).map Embedding.inr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioi_inr : Ioi (inr b : α ⊕ β) = (Ioi b).map Embedding.inr := rfl

end LocallyFiniteOrderTop

end Disjoint

/-! ### Lexicographical sum of orders -/

namespace Lex

section LocallyFiniteOrder
variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot β]

/-
**Sum.Lex.locallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：locallyFiniteOrder : LocallyFiniteOrder (α oplusₗ β) where finsetIcc a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance locallyFiniteOrder : LocallyFiniteOrder (α ⊕ₗ β) where
  finsetIcc a b :=
    (sumLexLift Icc Icc (fun a _ => Ici a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIco a b :=
    (sumLexLift Ico Ico (fun a _ => Ici a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoc a b :=
    (sumLexLift Ioc Ioc (fun a _ => Ioi a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoo a b :=
    (sumLexLift Ioo Ioo (fun a _ => Ioi a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

variable (a a₁ a₂ : α) (b b₁ b₂ : β)
/-
**Sum.Lex.Icc_inl_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Icc_inl_inl : Icc (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Icc a₁ a₂).map (Embe
dding.inl.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Icc_inl_inl :
    Icc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Icc a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl
/-
**Sum.Lex.Ico_inl_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ico_inl_inl : Ico (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Ico a₁ a₂).map (Embe
dding.inl.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Ico_inl_inl :
    Ico (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ico a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl
/-
**Sum.Lex.Ioc_inl_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioc_inl_inl : Ioc (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Ioc a₁ a₂).map (Embe
dding.inl.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Ioc_inl_inl :
    Ioc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioc a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl
/-
**Sum.Lex.Ioo_inl_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioo_inl_inl : Ioo (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Ioo a₁ a₂).map (Embe
dding.inl.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Ioo_inl_inl :
    Ioo (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioo a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

@[simp]
/-
**Sum.Lex.Icc_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Icc_inl_inr : Icc (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iic b)).map toLex.
toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Icc_inl_inr : Icc (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iic b)).map toLex.toEmbedding := rfl

@[simp]
/-
**Sum.Lex.Ico_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ico_inl_inr : Ico (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iio b)).map toLex.
toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ico_inl_inr : Ico (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iio b)).map toLex.toEmbedding := rfl

@[simp]
/-
**Sum.Lex.Ioc_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioc_inl_inr : Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iic b)).map toLex.
toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioc_inl_inr : Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iic b)).map toLex.toEmbedding := rfl

@[simp]
/-
**Sum.Lex.Ioo_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioo_inl_inr : Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iio b)).map toLex.
toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioo_inl_inr : Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iio b)).map toLex.toEmbedding := rfl

@[simp]
/-
**Sum.Lex.Icc_inr_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Icc_inr_inl : Icc (inrₗ b) (inlₗ a) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Icc_inr_inl : Icc (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
/-
**Sum.Lex.Ico_inr_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ico_inr_inl : Ico (inrₗ b) (inlₗ a) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ico_inr_inl : Ico (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
/-
**Sum.Lex.Ioc_inr_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioc_inr_inl : Ioc (inrₗ b) (inlₗ a) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioc_inr_inl : Ioc (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
/-
**Sum.Lex.Ioo_inr_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioo_inr_inl : Ioo (inrₗ b) (inlₗ a) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioo_inr_inl : Ioo (inrₗ b) (inlₗ a) = ∅ := rfl
/-
**Sum.Lex.Icc_inr_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Icc_inr_inr : Icc (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Icc b₁ b₂).map (Embe
dding.inr.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Icc_inr_inr :
    Icc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Icc b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl
/-
**Sum.Lex.Ico_inr_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ico_inr_inr : Ico (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Ico b₁ b₂).map (Embe
dding.inr.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Ico_inr_inr :
    Ico (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ico b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl
/-
**Sum.Lex.Ioc_inr_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioc_inr_inr : Ioc (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Ioc b₁ b₂).map (Embe
dding.inr.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Ioc_inr_inr :
    Ioc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioc b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl
/-
**Sum.Lex.Ioo_inr_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioo_inr_inr : Ioo (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Ioo b₁ b₂).map (Embe
dding.inr.trans toLex.toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma Ioo_inr_inr :
    Ioo (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioo b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [Preorder α] [Preorder β] [Fintype α] [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]

/-
**Sum.Lex.instLocallyFiniteOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：instLocallyFiniteOrderBot : LocallyFiniteOrderBot (α oplusₗ β) where finse
tIic
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (α ⊕ₗ β) where
  finsetIic := Sum.elim
    (Iic · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iic x) |>.map toLex.toEmbedding) ∘ ofLex
  finsetIio := Sum.elim
    (Iio · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iio x) |>.map toLex.toEmbedding) ∘ ofLex
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

variable (a : α) (b : β)
/-
**Sum.Lex.Iic_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Iic_inl : Iic (inlₗ a : α oplusₗ β) = (Iic a).map (Embedding.inl.trans toL
ex.toEmbedding)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iic_inl : Iic (inlₗ a : α ⊕ₗ β) = (Iic a).map (Embedding.inl.trans toLex.toEmbedding) := rfl
/-
**Sum.Lex.Iic_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Iic_inr : Iic (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iic b)).map to
Lex.toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iic_inr : Iic (inrₗ b : α ⊕ₗ β) = (Finset.univ.disjSum (Iic b)).map toLex.toEmbedding := rfl
/-
**Sum.Lex.Iio_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Iio_inl : Iio (inlₗ a : α oplusₗ β) = (Iio a).map (Embedding.inl.trans toL
ex.toEmbedding)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iio_inl : Iio (inlₗ a : α ⊕ₗ β) = (Iio a).map (Embedding.inl.trans toLex.toEmbedding) := rfl
/-
**Sum.Lex.Iio_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Iio_inr : Iio (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iio b)).map to
Lex.toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iio_inr : Iio (inrₗ b : α ⊕ₗ β) = (Finset.univ.disjSum (Iio b)).map toLex.toEmbedding := rfl

end LocallyFiniteOrderBot

/-- TODO: `LocallyFiniteOrder.toLocallyFiniteOrderBot` is probably a bad instance, as it forms
a diamond with this instance, and constructs data from data. We should consider removing it. -/
/-
**Sum.Lex.** 是 Mathlib 中的一个示例，位于命名空间 `Sum.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: `LocallyFiniteOrder.toLocallyFiniteOrderBot` is probably a bad instance, a
s it forms
a diamond with this instance, and constructs data from data. We should consider 
removing it.
-/
example [Fintype α] [Preorder α] [Preorder β] [OrderBot α] [OrderBot β] [OrderTop α]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] :
    LocallyFiniteOrder.toLocallyFiniteOrderBot = instLocallyFiniteOrderBot (α := α) (β := β) := by
  try with_reducible_and_instances rfl -- fails
  try rfl -- fails
  exact Subsingleton.elim _ _

section LocallyFiniteOrderTop
variable [Preorder α] [Preorder β] [LocallyFiniteOrderTop α] [Fintype β] [LocallyFiniteOrderTop β]

/-
**Sum.Lex.instLocallyFiniteOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：instLocallyFiniteOrderTop : LocallyFiniteOrderTop (α oplusₗ β) where finse
tIci
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (α ⊕ₗ β) where
  finsetIci := Sum.elim
    (fun x => (Ici x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ici · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finsetIoi := Sum.elim
    (fun x => (Ioi x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ioi · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

variable (a : α) (b : β)
/-
**Sum.Lex.Ici_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ici_inl : Ici (inlₗ a : α oplusₗ β) = ((Ici a).disjSum Finset.univ).map to
Lex.toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ici_inl : Ici (inlₗ a : α ⊕ₗ β) = ((Ici a).disjSum Finset.univ).map toLex.toEmbedding := rfl
/-
**Sum.Lex.Ici_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ici_inr : Ici (inrₗ b : α oplusₗ β) = (Ici b).map (Embedding.inr.trans toL
ex.toEmbedding)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ici_inr : Ici (inrₗ b : α ⊕ₗ β) = (Ici b).map (Embedding.inr.trans toLex.toEmbedding) := rfl
/-
**Sum.Lex.Ioi_inl** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioi_inl : Ioi (inlₗ a : α oplusₗ β) = ((Ioi a).disjSum Finset.univ).map to
Lex.toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioi_inl : Ioi (inlₗ a : α ⊕ₗ β) = ((Ioi a).disjSum Finset.univ).map toLex.toEmbedding := rfl
/-
**Sum.Lex.Ioi_inr** 是 Mathlib 中的一个引理，位于命名空间 `Sum.Lex`。
形式化陈述：Ioi_inr : Ioi (inrₗ b : α oplusₗ β) = (Ioi b).map (Embedding.inr.trans toL
ex.toEmbedding)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ioi_inr : Ioi (inrₗ b : α ⊕ₗ β) = (Ioi b).map (Embedding.inr.trans toLex.toEmbedding) := rfl

end LocallyFiniteOrderTop

end Lex
end Sum

