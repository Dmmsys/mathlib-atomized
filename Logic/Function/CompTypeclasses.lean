/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Init

/-!
# Propositional typeclasses on several maps

This file contains typeclasses that are used in the definition of
equivariant maps in the spirit what was initially developed
by Frédéric Dupuis and Heather Macbeth for linear maps.

* `CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `CompTriple.IsId φ`, which expresses that `φ = id`

TODO :
* align with RingHomCompTriple

-/

public section

section CompTriple

/-- Class of composing triples -/
/-
**CompTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} → {N : Type u_2} → {P : Type u_3} → (M → N) → (N → P) → out
Param (M → P) → Prop
参数：M → N；N → P；M → P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class of composing triples
-/
class CompTriple {M N P : Type*} (φ : M → N) (ψ : N → P) (χ : outParam (M → P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

/-- Class of Id maps -/
/-
**CompTriple.IsId** 是 Mathlib 中的一个归纳类型，位于命名空间 `CompTriple`。
形式化陈述：{M : Type u_1} → (M → M) → Prop
参数：M → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class of Id maps
-/
class IsId {M : Type*} (σ : M → M) : Prop where
  eq_id : σ = id
/-
**CompTriple.** 是 Mathlib 中的一个实例，位于命名空间 `CompTriple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} : IsId (@id M) where
  eq_id := rfl
/-
**CompTriple.instComp_id** 是 Mathlib 中的一个实例，位于命名空间 `CompTriple`。
形式化陈述：instComp_id {N P : Type*} {φ : N -> N} [IsId φ] {ψ : N -> P} : CompTriple 
φ ψ ψ where comp_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.IsId.eq_id`：∀ {M : Type u_1} {σ : M → M} [self : CompTriple.I
sId σ], σ = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instComp_id {N P : Type*} {φ : N → N} [IsId φ] {ψ : N → P} :
    CompTriple φ ψ ψ where
  comp_eq := by simp only [IsId.eq_id, Function.comp_id]
/-
**CompTriple.instId_comp** 是 Mathlib 中的一个实例，位于命名空间 `CompTriple`。
形式化陈述：instId_comp {M N : Type*} {φ : M -> N} {ψ : N -> N} [IsId ψ] : CompTriple 
φ ψ φ where comp_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.IsId.eq_id`：∀ {M : Type u_1} {σ : M → M} [self : CompTriple.I
sId σ], σ = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instId_comp {M N : Type*} {φ : M → N} {ψ : N → N} [IsId ψ] :
    CompTriple φ ψ φ where
  comp_eq := by simp only [IsId.eq_id, Function.id_comp]

/-- `φ`, `ψ` and `ψ ∘ φ` for a `CompTriple`. -/
/-
**CompTriple.comp** 是 Mathlib 中的一个定理，位于命名空间 `CompTriple`。
形式化陈述：comp {M N P : Type*} {φ : M -> N} {ψ : N -> P} : CompTriple φ ψ (ψ.comp φ)
 where comp_eq
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`φ`, `ψ` and `ψ ∘ φ` for a `CompTriple`.
-/
theorem comp {M N P : Type*}
    {φ : M → N} {ψ : N → P} :
    CompTriple φ ψ (ψ.comp φ) where
  comp_eq := rfl
/-
**CompTriple.comp_inv** 是 Mathlib 中的一个引理，位于命名空间 `CompTriple`。
形式化陈述：comp_inv {M N : Type*} {φ : M -> N} {ψ : N -> M} (h : Function.RightInvers
e φ ψ) {χ : M -> M} [IsId χ] : CompTriple φ ψ χ where comp_eq
参数：h : Function.RightInverse φ ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.RightInverse.id`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f
 : α → β}, Function.RightInverse g f → f ∘ g = id
· 使用定理 `CompTriple.IsId.eq_id`：∀ {M : Type u_1} {σ : M → M} [self : CompTriple.I
sId σ], σ = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_inv {M N : Type*} {φ : M → N} {ψ : N → M}
    (h : Function.RightInverse φ ψ) {χ : M → M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, h.id]
/-
**CompTriple.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CompTriple`。
形式化陈述：comp_apply {M N P : Type*} {φ : M -> N} {ψ : N -> P} {χ : M -> P} (h : Com
pTriple φ ψ χ) (x : M) : ψ (φ x) = χ x
参数：h : CompTriple φ ψ χ；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma comp_apply {M N P : Type*}
    {φ : M → N} {ψ : N → P} {χ : M → P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, Function.comp_apply]

end CompTriple

end CompTriple

