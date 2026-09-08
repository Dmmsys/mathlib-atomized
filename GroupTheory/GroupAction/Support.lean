/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Support of an element under an action

Given an action of a group `G` on a type `α`, we say that a set `s : Set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open scoped Pointwise

variable {G H α β : Type*}

namespace MulAction

section SMul

variable (G) [SMul G α] [SMul G β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive /-- A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`. -/]
/-
**MulAction.Supports** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：Supports (s : Set α) (b : β)
参数：s : Set α；b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`.
-/
def Supports (s : Set α) (b : β) :=
  ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b

variable {s t : Set α} {a : α} {b : β}

@[to_additive]
/-
**MulAction.supports_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：supports_of_mem (ha : a in s) : Supports G s a
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem supports_of_mem (ha : a ∈ s) : Supports G s a := fun _ h => h ha

variable {G}

@[to_additive]
/-
**MulAction.Supports.mono** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Supports`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} {β : Type u_4} [inst : SMul G α] [inst_1 :
 SMul G β] {s t : Set α} {b : β},   s ⊆ t → MulAction.Supports G s b → MulAction
.Supports G t b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Supports.mono (h : s ⊆ t) (hs : Supports G s b) : Supports G t b := fun _ hg =>
  (hs _) fun _ ha => hg <| h ha

end SMul

variable [Group H] [SMul G α] [SMul G β] [MulAction H α] [SMul H β] [SMulCommClass G H β]
  [SMulCommClass G H α] {s : Set α} {b : β}

-- TODO: This should work without `SMulCommClass`
@[to_additive]
/-
**MulAction.Supports.smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Supports`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} {α : Type u_3} {β : Type u_4} [inst : Grou
p H] [inst_1 : SMul G α] [inst_2 : SMul G β]   [inst_3 : MulAction H α] [inst_4 
: SMul H β] [SMulCommClass G H β] [SMulCommClass G H α] {s : Set α} {b : β} (g :
 H),   MulAction.Supports G s b → MulAction.Supports G (g • s) (g • b)
参数：g : H；g • s；g • b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用引理 `smul_left_cancel_iff`：smul_left_cancel_iff (g : α) {x y : β} : g • x = g
 • y ↔ x = y
-/
theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) := by
  rintro g' hg'
  rw [smul_comm, h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this

end MulAction

