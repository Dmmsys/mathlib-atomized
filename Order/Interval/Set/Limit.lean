/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.SetIsMax
public import Mathlib.Order.SuccPred.Limit

/-!
# Limit elements in Set.Ici

If `J` is a linearly ordered type, `j : J`,
and `m : Set.Ici j` is successor limit, then
`↑m : J` is also successor limit.

-/

public section

universe u

namespace Set.Ici

/-
**Set.Ici.isSuccLimit_coe** 是 Mathlib 中的一个引理，位于命名空间 `Set.Ici`。
形式化陈述：isSuccLimit_coe {J : Type u} [LinearOrder J] {j : J} (m : Set.Ici j) (hm :
 Order.IsSuccLimit m) : Order.IsSuccLimit m.1
参数：m : Set.Ici j；hm : Order.IsSuccLimit m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.not_isMin_coe`：not_isMin_coe (hm : ¬ IsMin m) : ¬ IsMin m.1
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `not_covBy_iff`：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c 
< b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma isSuccLimit_coe {J : Type u} [LinearOrder J] {j : J}
    (m : Set.Ici j) (hm : Order.IsSuccLimit m) :
    Order.IsSuccLimit m.1 :=
  ⟨Set.not_isMin_coe _ hm.1, fun b ↦ by
    simp only [CovBy, not_lt, not_and, not_forall, not_le]
    intro hb
    by_cases hb' : j ≤ b
    · have := hm.2 ⟨b, hb'⟩
      rw [not_covBy_iff (by exact hb)] at this
      obtain ⟨⟨x, h₁⟩, h₂, h₃⟩ := this
      refine ⟨x, h₂, h₃⟩
    · simp only [not_le] at hb'
      refine ⟨j, hb', ?_⟩
      by_contra!
      apply hm.1
      rintro ⟨k, hk⟩ _
      exact this.trans (by simpa using hk)⟩

end Set.Ici

