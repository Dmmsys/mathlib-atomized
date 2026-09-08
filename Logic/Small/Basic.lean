/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Logic.Equiv.Set

/-!
# Instances and theorems for `Small`.

In particular we prove `small_of_injective` and `small_of_surjective`.
-/

public section

assert_not_exists Countable

universe u w v v'

-- TODO(timotree3): lower the priority on this instance?
-- This instance applies to every synthesis problem of the form `Small ↥s` for some set `s`,
-- but we have lots of instances of `Small` for specific set constructions.
/-
**small_subtype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_subtype (α : Type v) [Small.{w} α] (P : α -> Prop) : Small.{w} { x /
/ P x }
参数：α : Type v；P : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance small_subtype (α : Type v) [Small.{w} α] (P : α → Prop) : Small.{w} { x // P x } :=
  small_map (equivShrink α).subtypeEquivOfSubtype'
/-
**small_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α -> β} (h
f : Function.Injective f) : Small.{u} α
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
-/
theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α → β}
    (hf : Function.Injective f) : Small.{u} α :=
  small_map (Equiv.ofInjective f hf)
/-
**small_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α -> β} (
hf : Function.Surjective f) : Small.{u} β
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α → β}
    (hf : Function.Surjective f) : Small.{u} β :=
  small_of_injective (Function.injective_surjInv hf)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α := by
  rcases isEmpty_or_nonempty α with ⟨⟩
  · apply small_map (Equiv.equivPEmpty α)
  · apply small_map Equiv.punitOfNonemptyOfSubsingleton

/-- This can be seen as a version of `small_of_surjective` in which the function `f` doesn't
actually land in `β` but in some larger type `γ` related to `β` via an injective function `g`.
-/
/-
**small_of_injective_of_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_of_injective_of_exists {α : Type v} {β : Type w} {γ : Type v'} [Smal
l.{u} α] (f : α -> γ) {g : β -> γ} (hg : Function.Injective g) (h : forall b : β
, exists a : α, f a = g b) : Small.{u} β
参数：f : α -> γ；hg : Function.Injective g；h : forall b : β, exists a : α, f a = g 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `small_subsingleton`：∀ (α : Type v) [Subsingleton α], Small.{w, v} α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α

--- 原说明 ---
This can be seen as a version of `small_of_surjective` in which the function `f`
 doesn't
actually land in `β` but in some larger type `γ` related to `β` via an injective
 function `g`.
-/
theorem small_of_injective_of_exists {α : Type v} {β : Type w} {γ : Type v'} [Small.{u} α]
    (f : α → γ) {g : β → γ} (hg : Function.Injective g) (h : ∀ b : β, ∃ a : α, f a = g b) :
    Small.{u} β := by
  by_cases hβ : Nonempty β
  · refine small_of_surjective (f := Function.invFun g ∘ f) (fun b => ?_)
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [Function.comp_apply, ha, Function.leftInverse_invFun hg]⟩
  · simp only [not_nonempty_iff] at hβ
    infer_instance

/-!
We don't define `Countable.toSmall` in this file, to keep imports to `Logic` to a minimum.
-/

/-
**small_Pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_Pi {α} (β : α -> Type*) [Small.{w} α] [forall a, Small.{w} (β a)] : 
Small.{w} (forall a, β a)
参数：β : α -> Type*；β a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Shrink.congr_simp`：∀ (α α_1 : Type v) (e_α : α = α_1) [inst : Small.{w, 
v} α], Shrink.{w, v} α = Shrink.{w, v} α_1

--- 原说明 ---
We don't define `Countable.toSmall` in this file, to keep imports to `Logic` to 
a minimum.
-/
instance small_Pi {α} (β : α → Type*) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (∀ a, β a) :=
  ⟨⟨∀ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩
/-
**small_prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩
/-
**small_sum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α ⊕ β) :=
  ⟨⟨Shrink α ⊕ Shrink β, ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩
/-
**small_set** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_set {α} [Small.{w} α] : Small.{w} (Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩
/-
**small_quot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_quot {α : Type u} [Small.{v} α] (r : α -> α -> Prop) : Small.{v} (Qu
ot r)
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
instance small_quot {α : Type u} [Small.{v} α] (r : α → α → Prop) : Small.{v} (Quot r) :=
  small_of_surjective Quot.mk_surjective
/-
**small_quotient** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_quotient {α : Type u} [Small.{v} α] (s : Setoid α) : Small.{v} (Quot
ient s)
参数：s : Setoid α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
instance small_quotient {α : Type u} [Small.{v} α] (s : Setoid α) : Small.{v} (Quotient s) :=
  small_of_surjective Quotient.mk_surjective
/-
**small_orderDual** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_orderDual {α : Type*} [h : Small.{v} α] : Small.{v} αᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_orderDual {α : Type*} [h : Small.{v} α] : Small.{v} αᵒᵈ := h
