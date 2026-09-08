/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Lemmas about `Nat.card` and `ENNReal`
-/

public section

namespace ENNReal

/-
**ENNReal.toReal_enatCard** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (α : Type u_1), (↑(ENat.card α)).toReal = ↑(Nat.card α)
参数：α : Type u_1；↑(ENat.card α)；Nat.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
@[simp] lemma toReal_enatCard (α : Type*) : ENNReal.toReal (ENat.card α) = Nat.card α := by
  cases finite_or_infinite α <;> simp [ENat.card_eq_coe_natCard]

end ENNReal

