/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Hom.Basic

/-!
# Preimages of intervals under order embeddings

In this file we prove that the preimage of an interval in the codomain under an `OrderEmbedding`
is an interval in the domain.

Note that similar statements about images require the range to be order-connected.
-/

public section

open Set

namespace OrderEmbedding

variable {α β : Type*}

section Preorder

variable [Preorder α] [Preorder β] (e : α ↪o β) (x y : α)

/-
**OrderEmbedding.preimage_Ici** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ici (e x) = Set.Ici x
参数：e : α ↪o β；x : α；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
@[to_dual (attr := simp)] theorem preimage_Ici : e ⁻¹' Ici (e x) = Ici x := ext fun _ ↦ e.le_iff_le
/-
**OrderEmbedding.preimage_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ioi (e x) = Set.Ioi x
参数：e : α ↪o β；x : α；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
@[to_dual (attr := simp)] theorem preimage_Ioi : e ⁻¹' Ioi (e x) = Ioi x := ext fun _ ↦ e.lt_iff_lt
/-
**OrderEmbedding.preimage_Icc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Icc (e x) (e y) = Set.Icc x y
参数：e : α ↪o β；x y : α；e x；e y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem preimage_Icc : e ⁻¹' Icc (e x) (e y) = Icc x y := by ext; simp
/-
**OrderEmbedding.preimage_Ico** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ico (e x) (e y) = Set.Ico x y
参数：e : α ↪o β；x y : α；e x；e y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem preimage_Ico : e ⁻¹' Ico (e x) (e y) = Ico x y := by ext; simp
/-
**OrderEmbedding.preimage_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioc (e x) (e y) = Set.Ioc x y
参数：e : α ↪o β；x y : α；e x；e y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem preimage_Ioc : e ⁻¹' Ioc (e x) (e y) = Ioc x y := by ext; simp
/-
**OrderEmbedding.preimage_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioo (e x) (e y) = Set.Ioo x y
参数：e : α ↪o β；x y : α；e x；e y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem preimage_Ioo : e ⁻¹' Ioo (e x) (e y) = Ioo x y := by ext; simp

end Preorder

variable [LinearOrder α]

/-
**OrderEmbedding.preimage_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Lattice β
] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.uIcc (e x) (e y) = Set.uIcc x y
参数：e : α ↪o β；x y : α；e x；e y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OrderEmbedding.preimage_Icc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Icc (e x) (e
 y) = Set.Icc x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
-/
@[simp] theorem preimage_uIcc [Lattice β] (e : α ↪o β) (x y : α) :
    e ⁻¹' (uIcc (e x) (e y)) = uIcc x y := by
  cases le_total x y <;> simp [*]
/-
**OrderEmbedding.preimage_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : LinearOrd
er β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.uIoc (e x) (e y) = Set.uIoc x y
参数：e : α ↪o β；x y : α；e x；e y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OrderEmbedding.preimage_Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioc (e x) (e
 y) = Set.Ioc x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.uIoc_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoc a b = Set.Ioc b a
-/
@[simp] theorem preimage_uIoc [LinearOrder β] (e : α ↪o β) (x y : α) :
    e ⁻¹' (uIoc (e x) (e y)) = uIoc x y := by
  cases le_total x y <;> simp [*]

end OrderEmbedding

