/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `Prod`
-/

public section

variable {α R S : Type*}

section
variable [Mul R] [Mul S]

@[to_additive (attr := simp)]
/-
**Prod.isLeftRegular_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.isLeftRegular_mk {a : R} {b : S} : IsLeftRegular (a, b) ↔ IsLeftRegul
ar a ∧ IsLeftRegular b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.map_injective`：map_injective [Nonempty α] [Nonempty β] {f : α -> γ}
 {g : β -> δ} : Injective (map f g) ↔ Injective f ∧ Injective g
-/
theorem Prod.isLeftRegular_mk {a : R} {b : S} :
    IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

@[to_additive (attr := simp)]
/-
**Prod.isRightRegular_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.isRightRegular_mk {a : R} {b : S} : IsRightRegular (a, b) ↔ IsRightRe
gular a ∧ IsRightRegular b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Prod.map_injective`：map_injective [Nonempty α] [Nonempty β] {f : α -> γ}
 {g : β -> δ} : Injective (map f g) ↔ Injective f ∧ Injective g
-/
theorem Prod.isRightRegular_mk {a : R} {b : S} :
    IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm <| Prod.map_injective |>.symm

@[to_additive (attr := simp)]
/-
**Prod.isRegular_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsReg
ular b
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
theorem Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b := by
  simp [isRegular_iff, and_and_and_comm]

@[to_additive]
/-
**IsLeftRegular.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRe
gular b) : IsLeftRegular (a, b)
参数：ha : IsLeftRegular a；hb : IsLeftRegular b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.isLeftRegular_mk`：Prod.isLeftRegular_mk {a : R} {b : S} : IsLeftReg
ular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b
-/
theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
    IsLeftRegular (a, b) := Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
/-
**IsRightRegular.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRigh
tRegular b) : IsRightRegular (a, b)
参数：ha : IsRightRegular a；hb : IsRightRegular b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.isRightRegular_mk`：Prod.isRightRegular_mk {a : R} {b : S} : IsRight
Regular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b
-/
theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
    IsRightRegular (a, b) := Prod.isRightRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
/-
**IsRegular.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) : I
sRegular (a, b)
参数：ha : IsRegular a；hb : IsRegular b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.isRegular_mk`：Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) 
↔ IsRegular a ∧ IsRegular b
-/
theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
    IsRegular (a, b) := Prod.isRegular_mk.2 ⟨ha, hb⟩

end

@[simp]
/-
**Prod.isSMulRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.isSMulRegular_iff [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempt
y S] : IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.map_injective`：map_injective [Nonempty α] [Nonempty β] {f : α -> γ}
 {g : β -> δ} : Injective (map f g) ↔ Injective f ∧ Injective g
-/
theorem Prod.isSMulRegular_iff [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S] :
    IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r :=
  Prod.map_injective
