/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Init

/-!
# Coequalizer of a pair of functions

The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) that
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`.

In this file we define the coequalizer and provide the basic API.
-/

@[expose] public section

universe v

namespace Function

/-- The relation generating the equivalence relation used for defining `Function.coequalizer`. -/
/-
**Function.Coequalizer.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `Function.Coequalizer`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → (α → β) → β → β → Prop
参数：α → β；α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation generating the equivalence relation used for defining `Function.coe
qualizer`.
-/
inductive Coequalizer.Rel {α β : Type*} (f g : α → β) : β → β → Prop where
  | intro (x : α) : Rel f g (f x) (g x)

/-- The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) that
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`. -/
/-
**Function.Coequalizer** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Coequalizer {α : Type*} {β : Type v} (f g : α -> β) : Type v
参数：f g : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) th
at
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`.
-/
def Coequalizer {α : Type*} {β : Type v} (f g : α → β) : Type v :=
  Quot (Function.Coequalizer.Rel f g)

namespace Coequalizer

variable {α β : Type*} (f g : α → β)

/-- The canonical projection to the coequalizer. -/
/-
**Function.Coequalizer.mk** 是 Mathlib 中的一个定义，位于命名空间 `Function.Coequalizer`。
形式化陈述：mk (x : β) : Coequalizer f g
参数：x : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection to the coequalizer.
-/
def mk (x : β) : Coequalizer f g :=
  Quot.mk _ x
/-
**Function.Coequalizer.condition** 是 Mathlib 中的一个引理，位于命名空间 `Function.Coequalizer
`。
形式化陈述：condition (x : α) : mk f g (f x) = mk f g (g x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma condition (x : α) : mk f g (f x) = mk f g (g x) :=
  Quot.sound (.intro x)
/-
**Function.Coequalizer.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Function.Coequal
izer`。
形式化陈述：mk_surjective : Function.Surjective (mk f g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
lemma mk_surjective : Function.Surjective (mk f g) :=
  Quot.exists_rep

/-- Any map `u : β → γ` with `u ∘ f = u ∘ g` factors via `Function.Coequalizer.mk`. -/
/-
**Function.Coequalizer.desc** 是 Mathlib 中的一个定义，位于命名空间 `Function.Coequalizer`。
形式化陈述：desc {γ : Type*} (u : β -> γ) (hu : u ∘ f = u ∘ g) : Coequalizer f g -> γ
参数：u : β -> γ；hu : u ∘ f = u ∘ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any map `u : β → γ` with `u ∘ f = u ∘ g` factors via `Function.Coequalizer.mk`.
-/
def desc {γ : Type*} (u : β → γ) (hu : u ∘ f = u ∘ g) : Coequalizer f g → γ :=
  Quot.lift u (fun _ _ (.intro e) ↦ congrFun hu e)
/-
**Function.Coequalizer.desc_mk** 是 Mathlib 中的一个定理，位于命名空间 `Function.Coequalizer`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f g : α → β) {γ : Type u_3} (u : β → γ) (
hu : u ∘ f = u ∘ g) (x : β),   Function.Coequalizer.desc f g u hu (Function.Coeq
ualizer.mk f g x) = u x
参数：f g : α → β；u : β → γ；hu : u ∘ f = u ∘ g；x : β；Function.Coequalizer.mk f g x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma desc_mk {γ : Type*} (u : β → γ) (hu : u ∘ f = u ∘ g) (x : β) :
    desc f g u hu (mk f g x) = u x :=
  rfl

end Function.Coequalizer

