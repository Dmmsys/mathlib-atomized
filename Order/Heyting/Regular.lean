/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.GaloisConnection.Basic

/-!
# Heyting regular elements

This file defines Heyting regular elements, elements of a Heyting algebra that are their own double
complement, and proves that they form a Boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `IsRegular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `Regular`: The subtype of Heyting-regular elements.
* `Regular.BooleanAlgebra`: Heyting-regular elements form a Boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

@[expose] public section

-- We want the theorems in this file to be intuitionistic.
set_option linter.unusedDecidableInType false

open Function

variable {α : Type*}

namespace Heyting

section Compl

variable [Compl α] {a : α}

/-- An element of a Heyting algebra is regular if its double complement is itself. -/
/-
**Heyting.IsRegular** 是 Mathlib 中的一个定义，位于命名空间 `Heyting`。
形式化陈述：IsRegular (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of a Heyting algebra is regular if its double complement is itself.
-/
def IsRegular (a : α) : Prop :=
  aᶜᶜ = a
/-
**Heyting.IsRegular.eq** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.IsRegular`。
形式化陈述：∀ {α : Type u_1} [inst : Compl α] {a : α}, Heyting.IsRegular a → aᶜᶜ = a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsRegular.eq : IsRegular a → aᶜᶜ = a :=
  id
/-
**Heyting.IsRegular.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Heyting.IsRegular`。
形式化陈述：{α : Type u_1} → [inst : Compl α] → [DecidableEq α] → DecidablePred Heytin
g.IsRegular
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsRegular.decidablePred [DecidableEq α] : @DecidablePred α IsRegular := fun _ =>
  ‹DecidableEq α› _ _

end Compl

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

/-
**Heyting.isRegular_bot** 是 Mathlib 中的一个定理，位于命名空间 `Heyting`。
形式化陈述：isRegular_bot : IsRegular (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Heyting.IsRegular.eq_1`：∀ {α : Type u_1} [inst : Compl α] (a : α), Heyti
ng.IsRegular a = (aᶜᶜ = a)
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
· 使用定理 `compl_top`：compl_top : (⊤ : α)ᶜ = ⊥
-/
theorem isRegular_bot : IsRegular (⊥ : α) := by rw [IsRegular, compl_bot, compl_top]
/-
**Heyting.isRegular_top** 是 Mathlib 中的一个定理，位于命名空间 `Heyting`。
形式化陈述：isRegular_top : IsRegular (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Heyting.IsRegular.eq_1`：∀ {α : Type u_1} [inst : Compl α] (a : α), Heyti
ng.IsRegular a = (aᶜᶜ = a)
· 使用定理 `compl_top`：compl_top : (⊤ : α)ᶜ = ⊥
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
-/
theorem isRegular_top : IsRegular (⊤ : α) := by rw [IsRegular, compl_top, compl_bot]
/-
**Heyting.IsRegular.inf** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.IsRegular`。
形式化陈述：∀ {α : Type u_1} [inst : HeytingAlgebra α] {a b : α},   Heyting.IsRegular 
a → Heyting.IsRegular b → Heyting.IsRegular (a ⊓ b)
参数：a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Heyting.IsRegular.eq_1`：∀ {α : Type u_1} [inst : Compl α] (a : α), Heyti
ng.IsRegular a = (aᶜᶜ = a)
· 使用定理 `compl_compl_inf_distrib`：compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ =
 aᶜᶜ ⊓ bᶜᶜ
· 使用定理 `Heyting.IsRegular.eq`：∀ {α : Type u_1} [inst : Compl α] {a : α}, Heyting
.IsRegular a → aᶜᶜ = a
-/
theorem IsRegular.inf (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⊓ b) := by
  rw [IsRegular, compl_compl_inf_distrib, ha.eq, hb.eq]
/-
**Heyting.IsRegular.himp** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.IsRegular`。
形式化陈述：∀ {α : Type u_1} [inst : HeytingAlgebra α] {a b : α},   Heyting.IsRegular 
a → Heyting.IsRegular b → Heyting.IsRegular (a ⇨ b)
参数：a ⇨ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Heyting.IsRegular.eq_1`：∀ {α : Type u_1} [inst : Compl α] (a : α), Heyti
ng.IsRegular a = (aᶜᶜ = a)
· 使用定理 `compl_compl_himp_distrib`：compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ
 = aᶜᶜ ⇨ bᶜᶜ
· 使用定理 `Heyting.IsRegular.eq`：∀ {α : Type u_1} [inst : Compl α] {a : α}, Heyting
.IsRegular a → aᶜᶜ = a
-/
theorem IsRegular.himp (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⇨ b) := by
  rw [IsRegular, compl_compl_himp_distrib, ha.eq, hb.eq]
/-
**Heyting.isRegular_compl** 是 Mathlib 中的一个定理，位于命名空间 `Heyting`。
形式化陈述：isRegular_compl (a : α) : IsRegular aᶜ
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_compl_compl`：compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ
-/
theorem isRegular_compl (a : α) : IsRegular aᶜ :=
  compl_compl_compl _
/-
**Heyting.IsRegular.disjoint_compl_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.I
sRegular`。
形式化陈述：∀ {α : Type u_1} [inst : HeytingAlgebra α] {a b : α}, Heyting.IsRegular a 
→ (Disjoint aᶜ b ↔ b ≤ a)
参数：Disjoint aᶜ b ↔ b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_compl_iff_disjoint_left`：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjo
int b a
· 使用定理 `Heyting.IsRegular.eq`：∀ {α : Type u_1} [inst : Compl α] {a : α}, Heyting
.IsRegular a → aᶜᶜ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem IsRegular.disjoint_compl_left_iff (ha : IsRegular a) :
    Disjoint aᶜ b ↔ b ≤ a := by rw [← le_compl_iff_disjoint_left, ha.eq]
/-
**Heyting.IsRegular.disjoint_compl_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.
IsRegular`。
形式化陈述：∀ {α : Type u_1} [inst : HeytingAlgebra α] {a b : α}, Heyting.IsRegular b 
→ (Disjoint a bᶜ ↔ a ≤ b)
参数：Disjoint a bᶜ ↔ a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `Heyting.IsRegular.eq`：∀ {α : Type u_1} [inst : Compl α] {a : α}, Heyting
.IsRegular a → aᶜᶜ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem IsRegular.disjoint_compl_right_iff (hb : IsRegular b) :
    Disjoint a bᶜ ↔ a ≤ b := by rw [← le_compl_iff_disjoint_right, hb.eq]

-- See note [reducible non-instances]
/-- A Heyting algebra with regular excluded middle is a Boolean algebra. -/
/-
**Heyting._root_.BooleanAlgebra.ofRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Heyting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Heyting algebra with regular excluded middle is a Boolean algebra.
-/
abbrev _root_.BooleanAlgebra.ofRegular (h : ∀ a : α, IsRegular (a ⊔ aᶜ)) : BooleanAlgebra α :=
  have : ∀ a : α, IsCompl a aᶜ := fun a =>
    ⟨disjoint_compl_right,
      codisjoint_iff.2 <| by rw [← (h a), compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun _ _ =>
      eq_of_forall_le_iff fun _ => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun _ => (this _).1.le_bot
    top_le_sup_compl := fun _ => (this _).2.top_le }

variable (α)

/-- The Boolean algebra of Heyting regular elements. -/
/-
**Heyting.Regular** 是 Mathlib 中的一个定义，位于命名空间 `Heyting`。
形式化陈述：Regular : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Boolean algebra of Heyting regular elements.
-/
def Regular : Type _ :=
  { a : α // IsRegular a }

variable {α}

namespace Regular

/-- The coercion `Regular α → α` -/
/-
**Heyting.Regular.val** 是 Mathlib 中的一个定义，位于命名空间 `Heyting.Regular`。
形式化陈述：{α : Type u_1} → [inst : HeytingAlgebra α] → Heyting.Regular α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion `Regular α → α`
-/
@[coe] def val : Regular α → α :=
  Subtype.val
/-
**Heyting.Regular.prop** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：prop : forall a : Regular α, IsRegular a.val
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem prop : ∀ a : Regular α, IsRegular a.val := Subtype.prop
/-
**Heyting.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (Regular α) α := ⟨Regular.val⟩
/-
**Heyting.Regular.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_injective : Injective ((↑) : Regular α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_injective : Injective ((↑) : Regular α → α) :=
  Subtype.coe_injective

@[simp]
/-
**Heyting.Regular.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_inj {a b : Regular α} : (a : α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
-/
theorem coe_inj {a b : Regular α} : (a : α) = b ↔ a = b :=
  Subtype.coe_inj
/-
**Heyting.Regular.top** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
形式化陈述：top : Top (Regular α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Heyting.isRegular_top`：isRegular_top : IsRegular (⊤ : α)
-/
instance top : Top (Regular α) :=
  ⟨⟨⊤, isRegular_top⟩⟩
/-
**Heyting.Regular.bot** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
形式化陈述：bot : Bot (Regular α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Heyting.isRegular_bot`：isRegular_bot : IsRegular (⊥ : α)
-/
instance bot : Bot (Regular α) :=
  ⟨⟨⊥, isRegular_bot⟩⟩
/-
**Heyting.Regular.inf** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
形式化陈述：inf : Min (Regular α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inf : Min (Regular α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩
/-
**Heyting.Regular.himp** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
形式化陈述：himp : HImp (Regular α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance himp : HImp (Regular α) :=
  ⟨fun a b => ⟨a ⇨ b, a.2.himp b.2⟩⟩
/-
**Heyting.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Compl (Regular α) :=
  ⟨fun a => ⟨aᶜ, isRegular_compl _⟩⟩

@[simp, norm_cast]
/-
**Heyting.Regular.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_top : ((⊤ : Regular α) : α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Regular α) : α) = ⊤ :=
  rfl

@[simp, norm_cast]
/-
**Heyting.Regular.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_bot : ((⊥ : Regular α) : α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : Regular α) : α) = ⊥ :=
  rfl

@[simp, norm_cast]
/-
**Heyting.Regular.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_inf (a b : Regular α) : (↑(a ⊓ b) : α) = (a : α) ⊓ b
参数：a b : Regular α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (a b : Regular α) : (↑(a ⊓ b) : α) = (a : α) ⊓ b :=
  rfl

@[simp, norm_cast]
/-
**Heyting.Regular.coe_himp** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_himp (a b : Regular α) : (↑(a ⇨ b) : α) = (a : α) ⇨ b
参数：a b : Regular α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_himp (a b : Regular α) : (↑(a ⇨ b) : α) = (a : α) ⇨ b :=
  rfl

@[simp, norm_cast]
/-
**Heyting.Regular.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_compl (a : Regular α) : (↑aᶜ : α) = (a : α)ᶜ
参数：a : Regular α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compl (a : Regular α) : (↑aᶜ : α) = (a : α)ᶜ :=
  rfl
/-
**Heyting.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Regular α) :=
  ⟨⊥⟩
/-
**Heyting.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Regular α) :=
  PartialOrder.lift _ coe_injective
/-
**Heyting.Regular.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
形式化陈述：boundedOrder : BoundedOrder (Regular α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Heyting.Regular.coe_top`：coe_top : ((⊤ : Regular α) : α) = ⊤
· 使用定理 `Heyting.Regular.coe_bot`：coe_bot : ((⊥ : Regular α) : α) = ⊥
-/
instance boundedOrder : BoundedOrder (Regular α) :=
  BoundedOrder.lift ((↑) : Regular α → α) (fun _ _ => id) coe_top coe_bot

@[simp, norm_cast]
/-
**Heyting.Regular.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_le_coe {a b : Regular α} : (a : α) <= b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe {a b : Regular α} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl

@[simp, norm_cast]
/-
**Heyting.Regular.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_lt_coe {a b : Regular α} : (a : α) < b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe {a b : Regular α} : (a : α) < b ↔ a < b :=
  Iff.rfl

/-- **Regularization** of `a`. The smallest regular element greater than `a`. -/
/-
**Heyting.Regular.toRegular** 是 Mathlib 中的一个定义，位于命名空间 `Heyting.Regular`。
形式化陈述：toRegular : α ->o Regular α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Regularization** of `a`. The smallest regular element greater than `a`.
-/
def toRegular : α →o Regular α :=
  ⟨fun a => ⟨aᶜᶜ, isRegular_compl _⟩, fun _ _ h =>
    coe_le_coe.1 <| compl_le_compl <| compl_le_compl h⟩

@[simp, norm_cast]
/-
**Heyting.Regular.coe_toRegular** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_toRegular (a : α) : (toRegular a : α) = aᶜᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRegular (a : α) : (toRegular a : α) = aᶜᶜ :=
  rfl

@[simp]
/-
**Heyting.Regular.toRegular_coe** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：toRegular_coe (a : Regular α) : toRegular (a : α) = a
参数：a : Regular α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Heyting.Regular.coe_injective`：coe_injective : Injective ((↑) : Regular 
α -> α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toRegular_coe (a : Regular α) : toRegular (a : α) = a :=
  coe_injective a.2

/-- The Galois insertion between `Regular.toRegular` and `coe`. -/
/-
**Heyting.Regular.gi** 是 Mathlib 中的一个定义，位于命名空间 `Heyting.Regular`。
形式化陈述：gi : GaloisInsertion toRegular ((↑) : Regular α -> α) where choice a ha
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois insertion between `Regular.toRegular` and `coe`.
-/
def gi : GaloisInsertion toRegular ((↑) : Regular α → α) where
  choice a ha := ⟨a, ha.antisymm le_compl_compl⟩
  gc _ b :=
    coe_le_coe.symm.trans <|
      ⟨le_compl_compl.trans, fun h => (compl_anti <| compl_anti h).trans_eq b.2⟩
  le_l_u _ := le_compl_compl
  choice_eq _ ha := coe_injective <| le_compl_compl.antisymm ha
/-
**Heyting.Regular.lattice** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
形式化陈述：lattice : Lattice (Regular α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice : Lattice (Regular α) :=
  gi.liftLattice

@[simp, norm_cast]
/-
**Heyting.Regular.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_sup (a b : Regular α) : (↑(a ⊔ b) : α) = ((a : α) ⊔ b)ᶜᶜ
参数：a b : Regular α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (a b : Regular α) : (↑(a ⊔ b) : α) = ((a : α) ⊔ b)ᶜᶜ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Heyting.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `Heyting.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanAlgebra (Regular α) :=
  { Regular.lattice, Regular.boundedOrder, Regular.himp,
    Regular.instCompl with
    le_sup_inf := fun a b c =>
      coe_le_coe.1 <| by
        dsimp
        rw [sup_inf_left, compl_compl_inf_distrib]
    inf_compl_le_bot := fun _ => coe_le_coe.1 <| disjoint_iff_inf_le.1 disjoint_compl_right
    top_le_sup_compl := fun a =>
      coe_le_coe.1 <| by
        dsimp
        rw [compl_sup, inf_compl_eq_bot, compl_bot]
    himp_eq := fun a b =>
      coe_injective
        (by
          dsimp
          rw [compl_sup, a.prop.eq]
          refine eq_of_forall_le_iff fun c => le_himp_iff.trans ?_
          rw [le_compl_iff_disjoint_right, disjoint_left_comm]
          rw [b.prop.disjoint_compl_left_iff]) }

@[simp, norm_cast]
/-
**Heyting.Regular.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Heyting.Regular`。
形式化陈述：coe_sdiff (a b : Regular α) : (↑(a \ b) : α) = (a : α) ⊓ bᶜ
参数：a b : Regular α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sdiff (a b : Regular α) : (↑(a \ b) : α) = (a : α) ⊓ bᶜ :=
  rfl

end Regular

end HeytingAlgebra

variable [BooleanAlgebra α]

/-
**Heyting.isRegular_of_boolean** 是 Mathlib 中的一个定理，位于命名空间 `Heyting`。
形式化陈述：isRegular_of_boolean : forall a : α, IsRegular a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem isRegular_of_boolean : ∀ a : α, IsRegular a :=
  compl_compl

/-- A decidable proposition is intuitionistically Heyting-regular. -/
/-
**Heyting.isRegular_of_decidable** 是 Mathlib 中的一个定理，位于命名空间 `Heyting`。
形式化陈述：isRegular_of_decidable (p : Prop) [Decidable p] : IsRegular p
参数：p : Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_not`：∀ {p : Prop} [Decidable p], ¬¬p ↔ p

--- 原说明 ---
A decidable proposition is intuitionistically Heyting-regular.
-/
theorem isRegular_of_decidable (p : Prop) [Decidable p] : IsRegular p :=
  propext <| Decidable.not_not

end Heyting

