/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Opposites

/-!
# Results about `IsRegular` and `MulOpposite`
-/

public section

variable {R} [Mul R]
open MulOpposite

@[to_additive (attr := simp)]
/-
**isLeftRegular_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRightRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
-/
theorem isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRightRegular a :=
  opEquiv.comp_injective _ |>.trans <| opEquiv.injective_comp _ |>.symm

@[to_additive (attr := simp)]
/-
**isRightRegular_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_op {a : R} : IsRightRegular (op a) ↔ IsLeftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
-/
theorem isRightRegular_op {a : R} : IsRightRegular (op a) ↔ IsLeftRegular a :=
  opEquiv.comp_injective _ |>.trans <| opEquiv.injective_comp _ |>.symm

@[to_additive (attr := simp)]
/-
**isRegular_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_op {a : R} : IsRegular (op a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isRegular_op {a : R} : IsRegular (op a) ↔ IsRegular a := by
  simp [isRegular_iff, and_comm]

@[to_additive] protected alias ⟨_, IsLeftRegular.op⟩ := isLeftRegular_op
@[to_additive] protected alias ⟨_, IsRightRegular.op⟩ := isRightRegular_op
@[to_additive] protected alias ⟨_, IsRegular.op⟩ := isRegular_op

@[to_additive (attr := simp)]
/-
**isLeftRegular_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_unop {a : Rᵐᵒᵖ} : IsLeftRegular a.unop ↔ IsRightRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isRightRegular_op`：isRightRegular_op {a : R} : IsRightRegular (op a) ↔ I
sLeftRegular a
-/
theorem isLeftRegular_unop {a : Rᵐᵒᵖ} : IsLeftRegular a.unop ↔ IsRightRegular a :=
  isRightRegular_op.symm

@[to_additive (attr := simp)]
/-
**isRightRegular_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_unop {a : Rᵐᵒᵖ} : IsRightRegular a.unop ↔ IsLeftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isLeftRegular_op`：isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRi
ghtRegular a
-/
theorem isRightRegular_unop {a : Rᵐᵒᵖ} : IsRightRegular a.unop ↔ IsLeftRegular a :=
  isLeftRegular_op.symm

@[to_additive (attr := simp)]
/-
**isRegular_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_unop {a : Rᵐᵒᵖ} : IsRegular a.unop ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isRegular_op`：isRegular_op {a : R} : IsRegular (op a) ↔ IsRegular a
-/
theorem isRegular_unop {a : Rᵐᵒᵖ} : IsRegular a.unop ↔ IsRegular a :=
  isRegular_op.symm

@[to_additive] protected alias ⟨_, IsLeftRegular.unop⟩ := isLeftRegular_unop
@[to_additive] protected alias ⟨_, IsRightRegular.unop⟩ := isRightRegular_unop
@[to_additive] protected alias ⟨_, IsRegular.unop⟩ := isRegular_unop
