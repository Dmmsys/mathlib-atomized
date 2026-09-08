/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Batteries.Logic
public import Mathlib.Init

/-!
# Extra facts about `PProd`
-/

@[expose] public section


open Function

variable {α β γ δ : Sort*}

namespace PProd

/-
**PProd.mk.injArrow** 是 Mathlib 中的一个定义，位于命名空间 `PProd.mk`。
形式化陈述：{α : Type u_5} →   {β : Type u_6} →     {x₁ : α} → {y₁ : β} → {x₂ : α} → {
y₂ : β} → (x₁, y₁) = (x₂, y₂) → ⦃P : Sort u_7⦄ → (x₁ = x₂ → y₁ = y₂ → P) → P
参数：x₁, y₁；x₂, y₂。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk.injArrow {α : Type*} {β : Type*} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort*⦄, (x₁ = x₂ → y₁ = y₂ → P) → P := by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]
/-
**PProd.mk.eta** 是 Mathlib 中的一个定理，位于命名空间 `PProd.mk`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {p : α ×' β}, ⟨p.fst, p.snd⟩ = p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  rfl

@[simp]
/-
**PProd.** 是 Mathlib 中的一个定理，位于命名空间 `PProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : PProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩

@[simp]
/-
**PProd.** 是 Mathlib 中的一个定理，位于命名空间 `PProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «exists» {p : PProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩
/-
**PProd.forall'** 是 Mathlib 中的一个定理，位于命名空间 `PProd`。
形式化陈述：forall' {p : α -> β -> Prop} : (forall x : PProd α β, p x.1 x.2) ↔ forall 
a b, p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PProd.forall`：∀ {α : Sort u_1} {β : Sort u_2} {p : α ×' β → Prop}, (∀ (x
 : α ×' β), p x) ↔ ∀ (a : α) (b : β), p ⟨a, b⟩
-/
theorem forall' {p : α → β → Prop} : (∀ x : PProd α β, p x.1 x.2) ↔ ∀ a b, p a b :=
  PProd.forall
/-
**PProd.exists'** 是 Mathlib 中的一个定理，位于命名空间 `PProd`。
形式化陈述：exists' {p : α -> β -> Prop} : (exists x : PProd α β, p x.1 x.2) ↔ exists 
a b, p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PProd.exists`：∀ {α : Sort u_1} {β : Sort u_2} {p : α ×' β → Prop}, (∃ x,
 p x) ↔ ∃ a b, p ⟨a, b⟩
-/
theorem exists' {p : α → β → Prop} : (∃ x : PProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  PProd.exists

end PProd

/-
**Function.Injective.pprod_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.pprod_map {f : α -> β} {g : γ -> δ} (hf : Injective f) 
(hg : Injective g) : Injective (fun x => ⟨f x.1, g x.2⟩ : PProd α γ -> PProd β δ
)
参数：hf : Injective f；hg : Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem Function.Injective.pprod_map {f : α → β} {g : γ → δ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x ↦ ⟨f x.1, g x.2⟩ : PProd α γ → PProd β δ) := fun _ _ h ↦
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)
