/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `ULift`
-/

public section

universe u v

variable {α} {R : Type v}

namespace ULift

section
variable [Mul R]

@[to_additive (attr := simp)]
/-
**ULift.isLeftRegular_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isLeftRegular_up {a : R} : IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
-/
theorem isLeftRegular_up {a : R} : IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular a :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

@[to_additive (attr := simp)]
/-
**ULift.isRightRegular_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isRightRegular_up {a : R} : IsRightRegular (ULift.up.{u} a) ↔ IsRightRegul
ar a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
-/
theorem isRightRegular_up {a : R} : IsRightRegular (ULift.up.{u} a) ↔ IsRightRegular a :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

@[to_additive (attr := simp)]
/-
**ULift.isRegular_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ IsRegular a
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
theorem isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ IsRegular a := by
  simp [isRegular_iff]

@[to_additive (attr := simp)]
/-
**ULift.isLeftRegular_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isLeftRegular_down {a : ULift.{u} R} : IsLeftRegular a.down ↔ IsLeftRegula
r a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ULift.isLeftRegular_up`：isLeftRegular_up {a : R} : IsLeftRegular (ULift.
up.{u} a) ↔ IsLeftRegular a
-/
theorem isLeftRegular_down {a : ULift.{u} R} : IsLeftRegular a.down ↔ IsLeftRegular a :=
  isLeftRegular_up.symm

@[to_additive (attr := simp)]
/-
**ULift.isRightRegular_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isRightRegular_down {a : ULift.{u} R} : IsRightRegular a.down ↔ IsRightReg
ular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ULift.isRightRegular_up`：isRightRegular_up {a : R} : IsRightRegular (ULi
ft.up.{u} a) ↔ IsRightRegular a
-/
theorem isRightRegular_down {a : ULift.{u} R} : IsRightRegular a.down ↔ IsRightRegular a :=
  isRightRegular_up.symm

@[to_additive (attr := simp)]
/-
**ULift.isRegular_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isRegular_down {a : ULift.{u} R} : IsRegular a.down ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ULift.isRegular_up`：isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ 
IsRegular a
-/
theorem isRegular_down {a : ULift.{u} R} : IsRegular a.down ↔ IsRegular a :=
  isRegular_up.symm

end

@[simp]
/-
**ULift.isSMulRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：isSMulRegular_iff [SMul α R] {r : α} : IsSMulRegular (ULift R) r ↔ IsSMulR
egular R r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
-/
theorem isSMulRegular_iff [SMul α R] {r : α} :
    IsSMulRegular (ULift R) r ↔ IsSMulRegular R r :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

end ULift

