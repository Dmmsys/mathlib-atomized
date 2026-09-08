/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.ExistsUnique
public import Mathlib.Logic.Nonempty
public import Mathlib.Logic.Nontrivial.Defs
public import Batteries.Tactic.Init
public import Mathlib.Order.Defs.Unbundled

import Mathlib.Tactic.Attr.Register

/-!
# Miscellaneous function constructions and lemmas
-/

@[expose] public section

open Function

universe u v w x

namespace Function

section

variable {α β γ : Sort*} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `Function.eval x : (∀ x, β x) → β x`. -/
/-
**Function.eval** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{α : Sort u_1} → {β : α → Sort u_4} → (x : α) → ((x : α) → β x) → β x
参数：x : α；(x : α) → β x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a function at an argument. Useful if you want to talk about the partial
ly applied
  `Function.eval x : (∀ x, β x) → β x`.
-/
@[reducible, simp] def eval {β : α → Sort*} (x : α) (f : ∀ x, β x) : β x := f x
/-
**Function.eval_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：eval_apply {β : α -> Sort*} (x : α) (f : forall x, β x) : eval x f = f x
参数：x : α；f : forall x, β x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a function at an argument. Useful if you want to talk about the partial
ly applied
  `Function.eval x : (∀ x, β x) → β x`.
-/
theorem eval_apply {β : α → Sort*} (x : α) (f : ∀ x, β x) : eval x f = f x :=
  rfl
/-
**Function.const_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_def {y : β} : (fun _ : α => y) = const α y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_def {y : β} : (fun _ : α ↦ y) = const α y :=
  rfl
/-
**Function.const_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_injective [Nonempty α] : Injective (const α : β -> α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem const_injective [Nonempty α] : Injective (const α : β → α → β) := fun _ _ h ↦
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]
/-
**Function.const_inj** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.const_injective`：const_injective [Nonempty α] : Injective (cons
t α : β -> α -> β)
-/
theorem const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂ :=
  ⟨fun h ↦ const_injective h, fun h ↦ h ▸ rfl⟩

section onFun

/-
**Function.onFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：onFun_apply (f : β -> β -> γ) (g : α -> β) (a b : α) : onFun f g a b = f (
g a) (g b)
参数：f : β -> β -> γ；g : α -> β；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem onFun_apply (f : β → β → γ) (g : α → β) (a b : α) : onFun f g a b = f (g a) (g b) :=
  rfl
/-
**Function.onFun_onFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：onFun_onFun_eq {δ : Sort*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β) : (
f.onFun g).onFun h = f.onFun (g ∘ h)
参数：f : α -> α -> γ；g : β -> α；h : δ -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem onFun_onFun_eq {δ : Sort*} (f : α → α → γ) (g : β → α) (h : δ → β) :
    (f.onFun g).onFun h = f.onFun (g ∘ h) := rfl
/-
**Function.onFun_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：onFun_comp_eq {δ : Sort*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β) : f.
onFun (g ∘ h) = (f.onFun g).onFun h
参数：f : α -> α -> γ；g : β -> α；h : δ -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem onFun_comp_eq {δ : Sort*} (f : α → α → γ) (g : β → α) (h : δ → β) :
    f.onFun (g ∘ h) = (f.onFun g).onFun h := rfl

variable (r : β → β → Prop) (f : α → β)
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] : Std.Refl (r on f) where
  refl _ := refl_of r _
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] : Std.Irrefl (r on f) where
  irrefl _ := irrefl_of r _
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Symm r] : Std.Symm (r on f) where
  symm _ _ := symm_of r

variable {f} in
/-
**Function.Injective.antisymm_onFun** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injectiv
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β → Prop) {f : α → β},   Function
.Injective f → ∀ [Std.Antisymm r], Std.Antisymm (Function.onFun r f)
参数：r : β → β → Prop；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymm_of`：antisymm_of (r : α -> α -> Prop) [Std.Antisymm r] {a b : α}
 : r a b -> r b a -> a = b
-/
theorem Injective.antisymm_onFun (hinj : f.Injective) [Std.Antisymm r] : Std.Antisymm (r on f) where
  antisymm _ _ hab hba := hinj <| antisymm_of r hab hba
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Asymm r] : Std.Asymm (r on f) where
  asymm _ _ := asymm_of r
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans β r] : IsTrans α (r on f) where
  trans _ _ _ := trans_of r
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Total r] : Std.Total (r on f) where
  total _ _ := total_of r _ _

variable {f} in
/-
**Function.Injective.trichotomous_onFun** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inje
ctive`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β → Prop) {f : α → β},   Function
.Injective f → ∀ [Std.Trichotomous r], Std.Trichotomous (Function.onFun r f)
参数：r : β → β → Prop；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
-/
theorem Injective.trichotomous_onFun (hinj : f.Injective) [Std.Trichotomous r] :
    Std.Trichotomous (r on f) where
  trichotomous a b hab hba := hinj <| Std.Trichotomous.trichotomous (f a) (f b) hab hba
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEquiv β r] : IsEquiv α (r on f) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPreorder β r] : IsPreorder α (r on f) where

variable {f} in
/-
**Function.Injective.isPartialOrder_onFun** 是 Mathlib 中的一个定理，位于命名空间 `Function.In
jective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β → Prop) {f : α → β},   Function
.Injective f → ∀ [IsPartialOrder β r], IsPartialOrder α (Function.onFun r f)
参数：r : β → β → Prop；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.antisymm_onFun`：∀ {α : Sort u_1} {β : Sort u_2} (r : 
β → β → Prop) {f : α → β},   Function.Injective f → ∀ [Std.Antisymm r], Std.Anti
symm (Function.onFun r …
· 使用定理 `IsPartialOrder.toAntisymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : I
sPartialOrder α r], Std.Antisymm r
· 使用定理 `Function.instIsPreorderOnFun`：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β
 → Prop) (f : α → β) [IsPreorder β r], IsPreorder α (Function.onFun r f)
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
-/
theorem Injective.isPartialOrder_onFun (hinj : f.Injective) [IsPartialOrder β r] :
    IsPartialOrder α (r on f) :=
  { hinj.antisymm_onFun r with }

variable {f} in
/-
**Function.Injective.isLinearOrder_onFun** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inj
ective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β → Prop) {f : α → β},   Function
.Injective f → ∀ [IsLinearOrder β r], IsLinearOrder α (Function.onFun r f)
参数：r : β → β → Prop；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isPartialOrder_onFun`：∀ {α : Sort u_1} {β : Sort u_2}
 (r : β → β → Prop) {f : α → β},   Function.Injective f → ∀ [IsPartialOrder β r]
, IsPartialOrder α (Function.…
· 使用定理 `IsLinearOrder.toIsPartialOrder`：∀ {α : Sort u_1} {r : α → α → Prop} [sel
f : IsLinearOrder α r], IsPartialOrder α r
· 使用定理 `Function.instTotalOnFun`：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β → Pr
op) (f : α → β) [Std.Total r], Std.Total (Function.onFun r f)
· 使用定理 `IsLinearOrder.toTotal`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsLin
earOrder α r], Std.Total r
-/
theorem Injective.isLinearOrder_onFun (hinj : f.Injective) [IsLinearOrder β r] :
    IsLinearOrder α (r on f) :=
  { hinj.isPartialOrder_onFun r with }
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStrictOrder β r] : IsStrictOrder α (r on f) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStrictWeakOrder β r] : IsStrictWeakOrder α (r on f) where
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

variable {f} in
/-
**Function.Injective.isStrictTotalOrder_onFun** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Injective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (r : β → β → Prop) {f : α → β},   Function
.Injective f → ∀ [IsStrictTotalOrder β r], IsStrictTotalOrder α (Function.onFun 
r f)
参数：r : β → β → Prop；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.trichotomous_onFun`：∀ {α : Sort u_1} {β : Sort u_2} (
r : β → β → Prop) {f : α → β},   Function.Injective f → ∀ [Std.Trichotomous r], 
Std.Trichotomous (Function.…
· 使用定理 `IsStrictTotalOrder.toTrichotomous`：∀ {α : Sort u_1} {lt : α → α → Prop} 
[self : IsStrictTotalOrder α lt], Std.Trichotomous lt
· 使用定理 `Function.instIsStrictOrderOnFun`：∀ {α : Sort u_1} {β : Sort u_2} (r : β 
→ β → Prop) (f : α → β) [IsStrictOrder β r], IsStrictOrder α (Function.onFun r f
)
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
-/
theorem Injective.isStrictTotalOrder_onFun (hinj : f.Injective) [IsStrictTotalOrder β r] :
    IsStrictTotalOrder α (r on f) :=
  { hinj.trichotomous_onFun r with }

end onFun

/-
**Function.hfunext** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> Sort v} {f : forall 
a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a', a ≍ a' -> f a ≍ f'
 a') : f ≍ f'
参数：hα : α = α'；h : forall a a', a ≍ a' -> f a ≍ f' a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `type_eq_of_heq`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → α = β
-/
lemma hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀ a, β a} {f' : ∀ a, β' a}
    (hα : α = α') (h : ∀ a a', a ≍ a' → f a ≍ f' a') : f ≍ f' := by
  subst hα
  have : ∀ a, f a ≍ f' a := fun a ↦ h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  grind
/-
**Function.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ != f₂ ↔ exists a, f₁ 
a != f₂ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
-/
theorem ne_iff {β : α → Sort*} {f₁ f₂ : ∀ a, β a} : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a :=
  funext_iff.not.trans not_forall
/-
**Function.funext_iff_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：funext_iff_of_subsingleton [Subsingleton α] {g : α -> β} (x y : α) : f x =
 g y ↔ f = g
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma funext_iff_of_subsingleton [Subsingleton α] {g : α → β} (x y : α) :
    f x = g y ↔ f = g := by
  refine ⟨fun h ↦ funext fun z ↦ ?_, fun h ↦ ?_⟩
  · rwa [Subsingleton.elim x z, Subsingleton.elim y z] at h
  · rw [h, Subsingleton.elim x y]

section swap

/-
**Function.swap_lt** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：swap_lt {α} [LT α] : swap (· < · : α -> α -> _) = (· > ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_lt {α} [LT α] : swap (· < · : α → α → _) = (· > ·) := rfl
/-
**Function.swap_le** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：swap_le {α} [LE α] : swap (· <= · : α -> α -> _) = (· >= ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_le {α} [LE α] : swap (· ≤ · : α → α → _) = (· ≥ ·) := rfl
/-
**Function.swap_gt** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：swap_gt {α} [LT α] : swap (· > · : α -> α -> _) = (· < ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_gt {α} [LT α] : swap (· > · : α → α → _) = (· < ·) := rfl
/-
**Function.swap_ge** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：swap_ge {α} [LE α] : swap (· >= · : α -> α -> _) = (· <= ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_ge {α} [LE α] : swap (· ≥ · : α → α → _) = (· ≤ ·) := rfl

variable (r : α → α → Prop)
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] : Std.Refl (swap r) where
  refl := refl_of r
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] : Std.Irrefl (swap r) where
  irrefl := irrefl_of r
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Symm r] : Std.Symm (swap r) where
  symm _ _ := symm_of r
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Antisymm r] : Std.Antisymm (swap r) where
  antisymm _ _ hab hba := antisymm_of r hab hba |>.symm
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Asymm r] : Std.Asymm (swap r) where
  asymm _ _ := asymm_of r
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans α r] : IsTrans α (swap r) where
  trans _ _ _ hab hbc := trans_of r hbc hab
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Total r] : Std.Total (swap r) where
  total _ _ := total_of r _ _
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Trichotomous r] : Std.Trichotomous (swap r) where
  trichotomous a b hab hba := Std.Trichotomous.trichotomous a b hba hab
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEquiv α r] : IsEquiv α (swap r) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPreorder α r] : IsPreorder α (swap r) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPartialOrder α r] : IsPartialOrder α (swap r) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLinearOrder α r] : IsLinearOrder α (swap r) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStrictOrder α r] : IsStrictOrder α (swap r) where
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStrictWeakOrder α r] : IsStrictWeakOrder α (swap r) where
  incomp_trans a b c hab hbc := IsStrictWeakOrder.incomp_trans a b c hab.symm hbc.symm |>.symm
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) where

end swap

/-
**Function.Bijective.injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Bijective f → Functi
on.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem Bijective.injective {f : α → β} (hf : Bijective f) : Injective f := hf.1
/-
**Function.Bijective.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Bijective f → Functi
on.Surjective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem Bijective.surjective {f : α → β} (hf : Bijective f) : Surjective f := hf.2
/-
**Function.not_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：not_injective_iff : ¬ Injective f ↔ exists a b, f a = f b ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_injective_iff : ¬ Injective f ↔ ∃ a b, f a = f b ∧ a ≠ b := by
  simp only [Injective, not_forall, exists_prop]
/-
**Function.not_injective_const** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} [Nontrivial α] {b : β}, ¬Function.Injectiv
e fun x => b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.not_injective_iff`：not_injective_iff : ¬ Injective f ↔ exists a
 b, f a = f b ∧ a != b
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
-/
@[simp] lemma not_injective_const {α β : Type*} [Nontrivial α] {b : β} :
    ¬ Injective (fun _ : α ↦ b) := by
  rw [not_injective_iff]
  obtain ⟨a₁, a₂, h⟩ := exists_pair_ne α
  exact ⟨a₁, a₂, rfl, h⟩

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
/-
**Function.Injective.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → {f : α → β} → [DecidableEq β] → Function
.Injective f → DecidableEq α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b

--- 原说明 ---
If the co-domain `β` of an injective function `f : α → β` has decidable equality
, then
the domain `α` also has decidable equality.
-/
protected def Injective.decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α :=
  fun _ _ ↦ decidable_of_iff _ I.eq_iff
/-
**Function.Injective.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α},   
Function.Injective (f ∘ g) → Function.Injective g
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Injective.of_comp {g : γ → α} (I : Injective (f ∘ g)) : Injective g :=
  fun _ _ h ↦ I <| congr_arg f h

@[simp]
/-
**Function.Injective.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Inj
ective f → ∀ (g : γ → α), Function.Injective (f ∘ g) ↔ Function.Injective g
参数：g : γ → α；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
-/
theorem Injective.of_comp_iff (hf : Injective f) (g : γ → α) :
    Injective (f ∘ g) ↔ Injective g :=
  ⟨Injective.of_comp, hf.comp⟩
/-
**Function.Injective.of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective
`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α},   
Function.Injective (f ∘ g) → Function.Surjective g → Function.Injective f
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Injective.of_comp_right {g : γ → α} (I : Injective (f ∘ g)) (hg : Surjective g) :
    Injective f := fun x y h ↦ by
  obtain ⟨x, rfl⟩ := hg x
  obtain ⟨y, rfl⟩ := hg y
  exact congr_arg g (I h)
/-
**Function.Surjective.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Surjective.bijective₂_of_injective {g : γ → α} (hf : Surjective f) (hg : Surjective g)
    (I : Injective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨I.of_comp_right hg, hf⟩, I.of_comp, hg⟩

@[simp]
/-
**Function.Injective.of_comp_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`
。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β) {g : γ → α},   
Function.Bijective g → (Function.Injective (f ∘ g) ↔ Function.Injective f)
参数：f : α → β；Function.Injective (f ∘ g) ↔ Function.Injective f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp_right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Surjec
tive g → Function.Inje…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
theorem Injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : Bijective g) :
    Injective (f ∘ g) ↔ Injective f :=
  ⟨fun I ↦ I.of_comp_right hg.2, fun h ↦ h.comp hg.injective⟩
/-
**Function.Injective.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {ι : Sort u_4} {α : ι → Sort u_5} {β : ι → Sort u_6} {f : (i : ι) → α i 
→ β i},   (∀ (i : ι), Function.Injective (f i)) → Function.Injective (Pi.map f)
参数：i : ι；∀ (i : ι), Function.Injective (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem Injective.piMap {ι : Sort*} {α β : ι → Sort*} {f : ∀ i, α i → β i}
    (hf : ∀ i, Injective (f i)) : Injective (Pi.map f) := fun _ _ h ↦
  funext fun i ↦ hf i <| congrFun h _

/-- Composition by an injective function on the left is itself injective. -/
/-
**Function.Injective.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {g : β → γ}, Function.Injec
tive g → Function.Injective fun x => g ∘ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.piMap`：∀ {ι : Sort u_4} {α : ι → Sort u_5} {β : ι → S
ort u_6} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Injective (f i)) → Fu
nction.Injecti…

--- 原说明 ---
Composition by an injective function on the left is itself injective.
-/
theorem Injective.comp_left {g : β → γ} (hg : Injective g) : Injective (g ∘ · : (α → β) → α → γ) :=
  .piMap fun _ ↦ hg
/-
**Function.injective_comp_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：injective_comp_left_iff [Nonempty α] {g : β -> γ} : Injective (g ∘ · : (α 
-> β) -> α -> γ) ↔ Injective g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
-/
theorem injective_comp_left_iff [Nonempty α] {g : β → γ} :
    Injective (g ∘ · : (α → β) → α → γ) ↔ Injective g :=
  ⟨fun h b₁ b₂ eq ↦ Nonempty.elim ‹_›
    (congr_fun <| h (a₁ := fun _ ↦ b₁) (a₂ := fun _ ↦ b₂) <| funext fun _ ↦ eq), (·.comp_left)⟩
/-
**Function.injective_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} [Subsingleton α] (f : α → β), Function.Inj
ective f
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[nontriviality] theorem injective_of_subsingleton [Subsingleton α] (f : α → β) : Injective f :=
  fun _ _ _ ↦ Subsingleton.elim _ _
/-
**Function.bijective_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u_1} [Subsingleton α] (f : α → α), Function.Bijective f
参数：f : α → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[nontriviality] theorem bijective_of_subsingleton [Subsingleton α] (f : α → α) : Bijective f :=
  ⟨injective_of_subsingleton f, fun a ↦ ⟨a, Subsingleton.elim ..⟩⟩
/-
**Function.Injective.dite** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (p : α → Prop) [inst : DecidablePred p] {f
 : { a // p a } → β} {f' : { a // ¬p a } → β},   Function.Injective f →     Func
tion.Injective f' →       (∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f'
 ⟨x', hx'⟩) →         Function.Injective fun x => if h : p x then f ⟨x, h⟩ else 
f' ⟨x, h⟩
参数：p : α → Prop；∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Injective.dite (p : α → Prop) [DecidablePred p]
    {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
    (hf : Injective f) (hf' : Injective f')
    (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
    Function.Injective (fun x ↦ if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) := fun x₁ x₂ h => by
  grind
/-
**Function.Surjective.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α},   
Function.Surjective (f ∘ g) → Function.Surjective f
参数：f ∘ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Surjective.of_comp {g : γ → α} (S : Surjective (f ∘ g)) : Surjective f := fun y ↦
  let ⟨x, h⟩ := S y
  ⟨g x, h⟩

@[simp]
/-
**Function.Surjective.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective
`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β) {g : γ → α},   
Function.Surjective g → (Function.Surjective (f ∘ g) ↔ Function.Surjective f)
参数：f : α → β；Function.Surjective (f ∘ g) ↔ Function.Surjective f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
-/
theorem Surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : Surjective g) :
    Surjective (f ∘ g) ↔ Surjective f :=
  ⟨Surjective.of_comp, fun h ↦ h.comp hg⟩
/-
**Function.Surjective.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α},   
Function.Surjective (f ∘ g) → Function.Injective f → Function.Surjective g
参数：f ∘ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Surjective.of_comp_left {g : γ → α} (S : Surjective (f ∘ g)) (hf : Injective f) :
    Surjective g := fun a ↦ let ⟨c, hc⟩ := S (f a); ⟨c, hf hc⟩
/-
**Function.Injective.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Injective.bijective₂_of_surjective {g : γ → α} (hf : Injective f) (hg : Injective g)
    (S : Surjective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨hf, S.of_comp⟩, hg, S.of_comp_left hf⟩

@[simp]
/-
**Function.Surjective.of_comp_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Bij
ective f → ∀ (g : γ → α), Function.Surjective (f ∘ g) ↔ Function.Surjective g
参数：g : γ → α；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Injec
tive f → Function.Surj…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
theorem Surjective.of_comp_iff' (hf : Bijective f) (g : γ → α) :
    Surjective (f ∘ g) ↔ Surjective g :=
  ⟨fun S ↦ S.of_comp_left hf.1, hf.surjective.comp⟩
/-
**Function.decidableEqPFun** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
形式化陈述：decidableEqPFun (p : Prop) [Decidable p] (α : p -> Type*) [forall hp, Deci
dableEq (α hp)] : DecidableEq (forall hp, α hp) | f, g => decidable_of_iff (fora
ll hp, f hp = g hp) funext_iff.symm  protected theorem Surjective.forall (hf : S
urjective f) {p : β -> Prop} : (forall y, p y) ↔ forall x, p (f x)
参数：p : Prop；α : p -> Type*；α hp。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEqPFun (p : Prop) [Decidable p] (α : p → Type*) [∀ hp, DecidableEq (α hp)] :
    DecidableEq (∀ hp, α hp)
  | f, g => decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm
/-
**Function.Surjective.forall** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},   Function.Surjective f → ∀ {
p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f x)
参数：∀ (y : β), p y；x : α；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Surjective.forall (hf : Surjective f) {p : β → Prop} :
    (∀ y, p y) ↔ ∀ x, p (f x) :=
  ⟨fun h x ↦ h (f x), fun h y ↦
    let ⟨x, hx⟩ := hf y
    hx ▸ h x⟩
/-
**Function.Surjective.forall** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},   Function.Surjective f → ∀ {
p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f x)
参数：∀ (y : β), p y；x : α；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Surjective.forall₂ (hf : Surjective f) {p : β → β → Prop} :
    (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
  hf.forall.trans <| forall_congr' fun _ ↦ hf.forall
/-
**Function.Surjective.forall** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},   Function.Surjective f → ∀ {
p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f x)
参数：∀ (y : β), p y；x : α；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Surjective.forall₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.forall.trans <| forall_congr' fun _ ↦ hf.forall₂
/-
**Function.Surjective.exists** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Surjective f → ∀ {p 
: β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
参数：∃ y, p y；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Surjective.exists (hf : Surjective f) {p : β → Prop} :
    (∃ y, p y) ↔ ∃ x, p (f x) :=
  ⟨fun ⟨y, hy⟩ ↦
    let ⟨x, hx⟩ := hf y
    ⟨x, hx.symm ▸ hy⟩,
    fun ⟨x, hx⟩ ↦ ⟨f x, hx⟩⟩
/-
**Function.Surjective.exists** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Surjective f → ∀ {p 
: β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
参数：∃ y, p y；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Surjective.exists₂ (hf : Surjective f) {p : β → β → Prop} :
    (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
  hf.exists.trans <| exists_congr fun _ ↦ hf.exists
/-
**Function.Surjective.exists** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Surjective f → ∀ {p 
: β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
参数：∃ y, p y；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Surjective.exists₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.exists.trans <| exists_congr fun _ ↦ hf.exists₂
/-
**Function.Surjective.injective_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.S
urjective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β}, Function.Surje
ctive f → Function.Injective fun g => g ∘ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem Surjective.injective_comp_right (hf : Surjective f) : Injective fun g : β → γ ↦ g ∘ f :=
  fun _ _ h ↦ funext <| hf.forall.2 <| congr_fun h
/-
**Function.injective_comp_right_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on`。
形式化陈述：injective_comp_right_iff_surjective {γ : Type*} [Nontrivial γ] : Injective
 (fun g : β -> γ => g ∘ f) ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
-/
theorem injective_comp_right_iff_surjective {γ : Type*} [Nontrivial γ] :
    Injective (fun g : β → γ ↦ g ∘ f) ↔ Surjective f := by
  refine ⟨not_imp_not.mp fun not_surj inj ↦ not_subsingleton γ ⟨fun c c' ↦ ?_⟩,
    (·.injective_comp_right)⟩
  have ⟨b₀, hb⟩ := not_forall.mp not_surj
  classical have := inj (a₁ := fun _ ↦ c) (a₂ := (if · = b₀ then c' else c)) ?_
  · simpa using congr_fun this b₀
  ext a; simp only [comp_apply, if_neg fun h ↦ hb ⟨a, h⟩]
/-
**Function.Surjective.right_cancellable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surj
ective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Sur
jective f → ∀ {g₁ g₂ : β → γ}, g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
-/
protected theorem Surjective.right_cancellable (hf : Surjective f) {g₁ g₂ : β → γ} :
    g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff
/-
**Function.surjective_of_right_cancellable_Prop** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion`。
形式化陈述：surjective_of_right_cancellable_Prop (h : forall g₁ g₂ : β -> Prop, g₁ ∘ f
 = g₂ ∘ f -> g₁ = g₂) : Surjective f
参数：h : forall g₁ g₂ : β -> Prop, g₁ ∘ f = g₂ ∘ f -> g₁ = g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.injective_comp_right_iff_surjective`：injective_comp_right_iff_s
urjective {γ : Type*} [Nontrivial γ] : Injective (fun g : β -> γ => g ∘ f) ↔ Sur
jective f
· 使用定理 `instNontrivialProp`：Nontrivial Prop
-/
theorem surjective_of_right_cancellable_Prop (h : ∀ g₁ g₂ : β → Prop, g₁ ∘ f = g₂ ∘ f → g₁ = g₂) :
    Surjective f :=
  injective_comp_right_iff_surjective.mp h
/-
**Function.bijective_iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bijective_iff_existsUnique (f : α -> β) : Bijective f ↔ forall b : β, exis
ts! a : α, f a = b
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
-/
theorem bijective_iff_existsUnique (f : α → β) : Bijective f ↔ ∀ b : β, ∃! a : α, f a = b :=
  ⟨fun hf b ↦
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun _ ha' ↦ hf.injective (ha'.trans ha.symm)⟩,
    fun he ↦ ⟨fun {_a a'} h ↦ (he (f a')).unique h rfl, fun b ↦ (he b).exists⟩⟩

/-- Shorthand for using projection notation with `Function.bijective_iff_existsUnique`. -/
/-
**Function.Bijective.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`
。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Bijective f → ∀ (b :
 β), ∃! a, f a = b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b

--- 原说明 ---
Shorthand for using projection notation with `Function.bijective_iff_existsUniqu
e`.
-/
protected theorem Bijective.existsUnique {f : α → β} (hf : Bijective f) (b : β) :
    ∃! a : α, f a = b :=
  (bijective_iff_existsUnique f).mp hf b
/-
**Function.Bijective.existsUnique_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Biject
ive`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Bijective f → ∀ {p :
 β → Prop}, (∃! y, p y) ↔ ∃! x, p (f x)
参数：∃! y, p y；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Bijective.existsUnique_iff {f : α → β} (hf : Bijective f) {p : β → Prop} :
    (∃! y, p y) ↔ ∃! x, p (f x) :=
  ⟨fun ⟨y, hpy, hy⟩ ↦
    let ⟨x, hx⟩ := hf.surjective y
    ⟨x, by simpa [hx], fun z (hz : p (f z)) ↦ hf.injective <| hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ ↦
    ⟨f x, hpx, fun y hy ↦
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ congr_arg f (hx _ (by simpa [hz]))⟩⟩
/-
**Function.Bijective.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β) {g : γ → α},   
Function.Bijective g → (Function.Bijective (f ∘ g) ↔ Function.Bijective f)
参数：f : α → β；Function.Bijective (f ∘ g) ↔ Function.Bijective f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `Function.Surjective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Surjective g → (Function.Surjective 
(f ∘ g) ↔ Function.Su…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
theorem Bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : Bijective g) :
    Bijective (f ∘ g) ↔ Bijective f :=
  and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)
/-
**Function.Bijective.of_comp_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`
。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Bij
ective f → ∀ (g : γ → α), Function.Bijective (f ∘ g) ↔ Function.Bijective g
参数：g : γ → α；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Surjective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Surjectiv
e (f ∘ g) ↔ Function.S…
-/
theorem Bijective.of_comp_iff' {f : α → β} (hf : Bijective f) (g : γ → α) :
    Function.Bijective (f ∘ g) ↔ Function.Bijective g :=
  and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)
/-
**Function.Bijective.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`
。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : γ → α},   
Function.Bijective (f ∘ g) → Function.Injective f → Function.Bijective g
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.of_comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Injec
tive f → Function.Surj…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Bijective.of_comp_left {f : α → β} {g : γ → α} (hfg : Function.Bijective (f ∘ g))
    (hf : Function.Injective f) : Function.Bijective g :=
  ⟨hfg.1.of_comp, hfg.2.of_comp_left hf⟩

/-- If `f : α → α → β` is surjective, then every endofunction on `β` has a fixed point.
This is an instance of Lawvere's fixed-point theorem applied to the category of types
and functions. It is the diagonal argument underlying `cantor_surjective` and
`cantor_injective`. -/
/-
**Function.exists_fixed_point_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function`
。
形式化陈述：exists_fixed_point_of_surjective {α β : Type*} (f : α -> α -> β) (hf : Sur
jective f) (g : β -> β) : exists x, g x = x
参数：f : α -> α -> β；hf : Surjective f；g : β -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
If `f : α → α → β` is surjective, then every endofunction on `β` has a fixed poi
nt.
This is an instance of Lawvere's fixed-point theorem applied to the category of 
types
and functions. It is the diagonal argument underlying `cantor_surjective` and
`cantor_injective`.
-/
theorem exists_fixed_point_of_surjective {α β : Type*} (f : α → α → β)
    (hf : Surjective f) (g : β → β) : ∃ x, g x = x :=
  let ⟨a, ha⟩ := hf fun a => g (f a a)
  ⟨f a a, (congr_fun ha a).symm⟩

/-- **Cantor's diagonal argument** implies that there are no surjective functions from `α`
to `Set α`. -/
/-
**Function.cantor_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：cantor_surjective {α} (f : α -> Set α) : ¬Surjective f
参数：f : α -> Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_not_self`：∀ {a : Prop}, ¬(a ↔ ¬a)
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
**Cantor's diagonal argument** implies that there are no surjective functions fr
om `α`
to `Set α`.
-/
theorem cantor_surjective {α} (f : α → Set α) : ¬Surjective f := fun hf ↦
  let ⟨a, ha⟩ := hf {a | a ∉ f a}
  iff_not_self <| .of_eq <| congrArg (a ∈ ·) ha

/-- **Cantor's diagonal argument** implies that there are no injective functions from `Set α`
to `α`. -/
/-
**Function.cantor_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_4} (f : Set α → α), ¬Function.Injective f
参数：f : Set α → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.cantor_surjective`：cantor_surjective {α} (f : α -> Set α) : ¬Su
rjective f
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b

--- 原说明 ---
**Cantor's diagonal argument** implies that there are no injective functions fro
m `Set α`
to `α`.
-/
theorem cantor_injective {α : Type*} (f : Set α → α) : ¬Injective f
  | i => cantor_surjective (fun a ↦ {b | ∀ U, a = f U → b ∈ U}) <|
         RightInverse.surjective (fun U ↦ Set.ext fun _ ↦ ⟨fun h ↦ h U rfl, fun h _ e ↦ i e ▸ h⟩)

/-- There is no surjection from `α : Type u` into `Type (max u v)`. This theorem
  demonstrates why `Type : Type` would be inconsistent in Lean. -/
/-
**Function.not_surjective_Type** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：not_surjective_Type {α : Type u} (f : α -> Type max u v) : ¬Surjective f
参数：f : α -> Type max u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cast_cast`：∀ {α β γ : Sort u_1} (ha : α = β) (hb : β = γ) (a : α), cast 
hb (cast ha a) = cast ⋯ a
· 使用定理 `Function.cantor_injective`：∀ {α : Type u_4} (f : Set α → α), ¬Function.I
njective f

--- 原说明 ---
There is no surjection from `α : Type u` into `Type (max u v)`. This theorem
  demonstrates why `Type : Type` would be inconsistent in Lean.
-/
theorem not_surjective_Type {α : Type u} (f : α → Type max u v) : ¬Surjective f := by
  intro hf
  let T : Type max u v := Sigma f
  cases hf (Set T) with | intro U hU =>
  let g : Set T → T := fun s ↦ ⟨U, cast hU.symm s⟩
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [g, cast_cast, cast_eq] at this
      assumption
    · congr
  exact cantor_injective g hg

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
/-
**Function.IsPartialInv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：IsPartialInv {α β} (f : α -> β) (g : β -> Option α) : Prop
参数：f : α -> β；g : β -> Option α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`.
-/
def IsPartialInv {α β} (f : α → β) (g : β → Option α) : Prop :=
  ∀ x y, g y = some x ↔ f x = y
/-
**Function.IsPartialInv.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPartialInv`。
形式化陈述：∀ {α : Type u_4} {β : Sort u_5} {f : α → β} {g : β → Option α}, Function.I
sPartialInv f g → ∀ (x : α), g (f x) = some x
参数：x : α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsPartialInv.eq {α β} {f : α → β} {g} (H : IsPartialInv f g) (x) : g (f x) = some x :=
  (H _ _).2 rfl
/-
**Function.IsPartialInv.get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPartialInv`
。
形式化陈述：∀ {α : Type u_4} {β : Sort u_5} {f : α → β} {g : β → Option α},   Function
.IsPartialInv f g → ∀ (x : β) (h : (g x).isSome = true), f ((g x).get h) = x
参数：x : β；h : (g x).isSome = true；(g x).get h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.eq_some_of_isSome`：∀ {α : Type u_1} {o : Option α} (h : o.isSome 
= true), o = some (o.get h)
-/
theorem IsPartialInv.get_eq {α β} {f : α → β} {g} (H : IsPartialInv f g) (x) (h : g x |>.isSome) :
    f (g x |>.get h) = x :=
  (H _ _).1 (Option.eq_some_of_isSome h)
/-
**Function.IsPartialInv.surjective_getD** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPa
rtialInv`。
形式化陈述：∀ {α : Type u_4} {β : Sort u_5} {f : α → β} {g : β → Option α},   Function
.IsPartialInv f g → ∀ (x : α), Function.Surjective fun x_1 => (g x_1).getD x
参数：x : α；g x_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsPartialInv.eq`：∀ {α : Type u_4} {β : Sort u_5} {f : α → β} {g
 : β → Option α}, Function.IsPartialInv f g → ∀ (x : α), g (f x) = some x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsPartialInv.surjective_getD {α β} {f : α → β} {g} (H : IsPartialInv f g) (x) :
    Function.Surjective (g · |>.getD x) :=
  fun y => ⟨f y, by simp [H.eq]⟩

@[deprecated (since := "2026-03-11")] alias isPartialInv_left := IsPartialInv.eq
/-
**Function.IsPartialInv.injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPartialI
nv`。
形式化陈述：∀ {α : Type u_4} {β : Sort u_5} {f : α → β} {g : β → Option α}, Function.I
sPartialInv f g → Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some.inj`：∀ {α : Type u} {val val_1 : α}, some val = some val_1 →
 val = val_1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsPartialInv.injective {α β} {f : α → β} {g} (H : IsPartialInv f g) :
    Injective f := fun _ _ h ↦
  Option.some.inj <| ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

@[deprecated (since := "2026-03-11")] alias injective_of_isPartialInv := IsPartialInv.injective
/-
**Function.injective_of_isPartialInv_right** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：injective_of_isPartialInv_right {α β} {f : α -> β} {g} (H : IsPartialInv f
 g) (x y b) (h₁ : b in g x) (h₂ : b in g y) : x = y
参数：H : IsPartialInv f g；x y b；h₁ : b in g x；h₂ : b in g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem injective_of_isPartialInv_right {α β} {f : α → β} {g} (H : IsPartialInv f g) (x y b)
    (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
  ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)
/-
**Function.IsPartialInv.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPartialInv`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {γ : Sort u_6} {f : α → β} {g : β → Option
 α} {h : β → γ} {i : γ → Option β},   Function.IsPartialInv f g → Function.IsPar
tialInv h i → Function.IsPartialInv (h ∘ f) fun x => (i x).bind g
参数：h ∘ f；i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsPartialInv.comp {α β γ} {f : α → β} {g : β → Option α} {h : β → γ} {i : γ → Option β}
    (hf : IsPartialInv f g) (hh : IsPartialInv h i) :
    IsPartialInv (h ∘ f) (i · |>.bind g) := by
  intros a b
  simp [Option.bind_eq_some_iff, hh _, hf _]
/-
**Function.LeftInverse.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f : α → β}, Function.LeftInve
rse g f → ∀ (x : α), g (f x) = x
参数：x : α；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LeftInverse.eq {g : β → α} {f : α → β} (h : LeftInverse g f) (x : α) : g (f x) = x := h x
/-
**Function.RightInverse.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f : α → β}, Function.RightInv
erse g f → ∀ (x : β), f (g x) = x
参数：x : β；g x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RightInverse.eq {g : β → α} {f : α → β} (h : RightInverse g f) (x : β) : f (g x) = x := h x
/-
**Function.LeftInverse.comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInvers
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse f g → f ∘ g = id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem LeftInverse.comp_eq_id {f : α → β} {g : β → α} (h : LeftInverse f g) : f ∘ g = id :=
  funext h
/-
**Function.leftInverse_iff_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：leftInverse_iff_comp {f : α -> β} {g : β -> α} : LeftInverse f g ↔ f ∘ g =
 id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem leftInverse_iff_comp {f : α → β} {g : β → α} : LeftInverse f g ↔ f ∘ g = id :=
  ⟨LeftInverse.comp_eq_id, congr_fun⟩
/-
**Function.RightInverse.comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInve
rse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}, Function.RightInv
erse f g → g ∘ f = id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem RightInverse.comp_eq_id {f : α → β} {g : β → α} (h : RightInverse f g) : g ∘ f = id :=
  funext h
/-
**Function.rightInverse_iff_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：rightInverse_iff_comp {f : α -> β} {g : β -> α} : RightInverse f g ↔ g ∘ f
 = id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem rightInverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨RightInverse.comp_eq_id, congr_fun⟩
/-
**Function.LeftInverse.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : β → α} {h 
: β → γ} {i : γ → β},   Function.LeftInverse f g → Function.LeftInverse h i → Fu
nction.LeftInverse (h ∘ f) (g ∘ i)
参数：h ∘ f；g ∘ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem LeftInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : LeftInverse f g)
    (hh : LeftInverse h i) : LeftInverse (h ∘ f) (g ∘ i) :=
  fun a ↦ show h (f (g (i a))) = a by rw [hf (i a), hh a]
/-
**Function.RightInverse.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : β → α} {h 
: β → γ} {i : γ → β},   Function.RightInverse f g → Function.RightInverse h i → 
Function.RightInverse (h ∘ f) (g ∘ i)
参数：h ∘ f；g ∘ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β},   Function.LeftInverse f g → 
Function.LeftIn…
-/
theorem RightInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : RightInverse f g)
    (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=
  LeftInverse.comp hh hf
/-
**Function.LeftInverse.rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInve
rse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse g f → Function.RightInverse f g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftInverse.rightInverse {f : α → β} {g : β → α} (h : LeftInverse g f) : RightInverse f g :=
  h
/-
**Function.RightInverse.leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInv
erse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}, Function.RightInv
erse g f → Function.LeftInverse f g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightInverse.leftInverse {f : α → β} {g : β → α} (h : RightInverse g f) : LeftInverse f g :=
  h
/-
**Function.LeftInverse.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInvers
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse f g → Function.Surjective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Function.LeftInverse.rightInverse`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β} {g : β → α}, Function.LeftInverse g f → Function.RightInverse f g
-/
theorem LeftInverse.surjective {f : α → β} {g : β → α} (h : LeftInverse f g) : Surjective f :=
  h.rightInverse.surjective
/-
**Function.RightInverse.injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInver
se`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α}, Function.RightInv
erse f g → Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Function.RightInverse.leftInverse`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β} {g : β → α}, Function.RightInverse g f → Function.LeftInverse f g
-/
theorem RightInverse.injective {f : α → β} {g : β → α} (h : RightInverse f g) : Injective f :=
  h.leftInverse.injective
/-
**Function.LeftInverse.rightInverse_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.LeftInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α},   Function.LeftIn
verse f g → Function.Injective f → Function.RightInverse f g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftInverse.rightInverse_of_injective {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hf : Injective f) : RightInverse f g :=
  fun x ↦ hf <| h (f x)
/-
**Function.LeftInverse.rightInverse_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Fun
ction.LeftInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α},   Function.LeftIn
verse f g → Function.Surjective g → Function.RightInverse f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem LeftInverse.rightInverse_of_surjective {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hg : Surjective g) : RightInverse f g :=
  fun x ↦ let ⟨y, hy⟩ := hg x; hy ▸ congr_arg g (h y)
/-
**Function.RightInverse.leftInverse_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Fun
ction.RightInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α},   Function.RightI
nverse f g → Function.Surjective f → Function.LeftInverse f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInverse_of_surjective`：∀ {α : Sort u_1} {β : S
ort u_2} {f : α → β} {g : β → α},   Function.LeftInverse f g → Function.Surjecti
ve g → Function.RightInverse f g
-/
theorem RightInverse.leftInverse_of_surjective {f : α → β} {g : β → α} :
    RightInverse f g → Surjective f → LeftInverse f g :=
  LeftInverse.rightInverse_of_surjective
/-
**Function.RightInverse.leftInverse_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.RightInverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g : β → α},   Function.RightI
nverse f g → Function.Injective g → Function.LeftInverse f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInverse_of_injective`：∀ {α : Sort u_1} {β : So
rt u_2} {f : α → β} {g : β → α},   Function.LeftInverse f g → Function.Injective
 f → Function.RightInverse f g
-/
theorem RightInverse.leftInverse_of_injective {f : α → β} {g : β → α} :
    RightInverse f g → Injective g → LeftInverse f g :=
  LeftInverse.rightInverse_of_injective
/-
**Function.LeftInverse.eq_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftI
nverse`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {g₁ g₂ : β → α},   Function.Le
ftInverse g₁ f → Function.RightInverse g₂ f → g₁ = g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
theorem LeftInverse.eq_rightInverse {f : α → β} {g₁ g₂ : β → α} (h₁ : LeftInverse g₁ f)
    (h₂ : RightInverse g₂ f) : g₁ = g₂ :=
  calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp_id]
     _ = g₂ := by rw [← comp_assoc, h₁.comp_eq_id, id_comp]

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
/-
**Function.partialInv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：partialInv {α β} (f : α -> β) (b : β) : Option α
参数：f : α -> β；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can use choice to construct explicitly a partial inverse for
  a given injective function `f`.
-/
noncomputable def partialInv {α β} (f : α → β) (b : β) : Option α :=
  open scoped Classical in
  if h : ∃ a, f a = b then some (Classical.choose h) else none
/-
**Function.Injective.isPartialInv** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`
。
形式化陈述：∀ {α : Type u_4} {β : Sort u_5} {f : α → β}, Function.Injective f → Functi
on.IsPartialInv f (Function.partialInv f)
参数：Function.partialInv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Injective.isPartialInv {α β} {f : α → β} (I : Injective f) : IsPartialInv f (partialInv f)
  | a, b =>
  ⟨fun h =>
    open scoped Classical in
    have hpi : partialInv f b = if h : ∃ a, f a = b then some (Classical.choose h) else none :=
      rfl
    if h' : ∃ a, f a = b
    then by rw [hpi, dif_pos h'] at h
            injection h with h
            subst h
            apply Classical.choose_spec h'
    else by rw [hpi, dif_neg h'] at h; contradiction,
  fun e => e ▸ have h : ∃ a', f a' = f a := ⟨_, rfl⟩
              (dif_pos h).trans (congr_arg _ (I <| Classical.choose_spec h))⟩

@[deprecated (since := "2026-03-11")] alias partialInv_of_injective := Injective.isPartialInv
/-
**Function.partialInv_left** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：partialInv_left {α β} {f : α -> β} (I : Injective f) : forall x, partialIn
v f (f x) = some x
参数：I : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPartialInv.eq`：∀ {α : Type u_4} {β : Sort u_5} {f : α → β} {g
 : β → Option α}, Function.IsPartialInv f g → ∀ (x : α), g (f x) = some x
· 使用定理 `Function.Injective.isPartialInv`：∀ {α : Type u_4} {β : Sort u_5} {f : α 
→ β}, Function.Injective f → Function.IsPartialInv f (Function.partialInv f)
-/
theorem partialInv_left {α β} {f : α → β} (I : Injective f) : ∀ x, partialInv f (f x) = some x :=
  I.isPartialInv.eq

end

section InvFun

variable {α β : Sort*} [Nonempty α] {f : α → β} {b : β}

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
-- Explicit Sort so that `α` isn't inferred to be Prop via `exists_prop_decidable`
/-
**Function.invFun** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：invFun {α : Sort u} {β} [Nonempty α] (f : α -> β) : β -> α
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
  open scoped Classical in
  fun y ↦ if h : (∃ x, f x = y) then h.choose else Classical.arbitrary α
/-
**Function.invFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFun_eq (h : exists a, f a = b) : f (invFun f b) = b
参数：h : exists a, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_eq (h : ∃ a, f a = b) : f (invFun f b) = b := by
  simp only [invFun, dif_pos h, h.choose_spec]
/-
**Function.apply_invFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：apply_invFun_apply {α β : Type*} {f : α -> β} {a : α} : f (@invFun _ _ ⟨a⟩
 f (f a)) = f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
-/
theorem apply_invFun_apply {α β : Type*} {f : α → β} {a : α} :
    f (@invFun _ _ ⟨a⟩ f (f a)) = f a :=
  @invFun_eq _ _ ⟨a⟩ _ _ ⟨_, rfl⟩
/-
**Function.invFun_neg** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFun_neg (h : ¬exists a, f a = b) : invFun f b = Classical.choice ‹_›
参数：h : ¬exists a, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem invFun_neg (h : ¬∃ a, f a = b) : invFun f b = Classical.choice ‹_› :=
  dif_neg h
/-
**Function.invFun_eq_of_injective_of_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Fun
ction`。
形式化陈述：invFun_eq_of_injective_of_rightInverse {g : β -> α} (hf : Injective f) (hg
 : RightInverse g f) : invFun f = g
参数：hf : Injective f；hg : RightInverse g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
-/
theorem invFun_eq_of_injective_of_rightInverse {g : β → α} (hf : Injective f)
    (hg : RightInverse g f) : invFun f = g :=
  funext fun b ↦
    hf
      (by
        rw [hg b]
        exact invFun_eq ⟨g b, hg b⟩)
/-
**Function.rightInverse_invFun** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：rightInverse_invFun (hf : Surjective f) : RightInverse (invFun f) f
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
-/
theorem rightInverse_invFun (hf : Surjective f) : RightInverse (invFun f) f :=
  fun b ↦ invFun_eq <| hf b
/-
**Function.leftInverse_invFun** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：leftInverse_invFun (hf : Injective f) : LeftInverse (invFun f) f
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
-/
theorem leftInverse_invFun (hf : Injective f) : LeftInverse (invFun f) f :=
  fun b ↦ hf <| invFun_eq ⟨b, rfl⟩
/-
**Function.invFun_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFun_surjective (hf : Injective f) : Surjective (invFun f)
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
-/
theorem invFun_surjective (hf : Injective f) : Surjective (invFun f) :=
  (leftInverse_invFun hf).surjective
/-
**Function.invFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFun_comp (hf : Injective f) : invFun f ∘ f = id
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
-/
theorem invFun_comp (hf : Injective f) : invFun f ∘ f = id :=
  funext <| leftInverse_invFun hf
/-
**Function.Injective.hasLeftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injectiv
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} [Nonempty α] {f : α → β}, Function.Injecti
ve f → Function.HasLeftInverse f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
-/
theorem Injective.hasLeftInverse (hf : Injective f) : HasLeftInverse f :=
  ⟨invFun f, leftInverse_invFun hf⟩
/-
**Function.injective_iff_hasLeftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：injective_iff_hasLeftInverse : Injective f ↔ HasLeftInverse f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.hasLeftInverse`：∀ {α : Sort u_1} {β : Sort u_2} [None
mpty α] {f : α → β}, Function.Injective f → Function.HasLeftInverse f
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
-/
theorem injective_iff_hasLeftInverse : Injective f ↔ HasLeftInverse f :=
  ⟨Injective.hasLeftInverse, HasLeftInverse.injective⟩

end InvFun

section SurjInv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}

/-- The inverse of a surjective function. (Unlike `invFun`, this does not require
  `α` to be inhabited.) -/
/-
**Function.surjInv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：surjInv {f : α -> β} (h : Surjective f) (b : β) : α
参数：h : Surjective f；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a surjective function. (Unlike `invFun`, this does not require
  `α` to be inhabited.)
-/
noncomputable def surjInv {f : α → β} (h : Surjective f) (b : β) : α :=
  Classical.choose (h b)
/-
**Function.surjInv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：surjInv_eq (h : Surjective f) (b) : f (surjInv h b) = b
参数：h : Surjective f；b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem surjInv_eq (h : Surjective f) (b) : f (surjInv h b) = b :=
  Classical.choose_spec (h b)

@[simp]
/-
**Function.comp_surjInv** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：comp_surjInv (hf : f.Surjective) : f ∘ f.surjInv hf = id
参数：hf : f.Surjective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
-/
lemma comp_surjInv (hf : f.Surjective) : f ∘ f.surjInv hf = id :=
  funext (Function.surjInv_eq _)
/-
**Function.rightInverse_surjInv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：rightInverse_surjInv (hf : Surjective f) : RightInverse (surjInv hf) f
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
-/
theorem rightInverse_surjInv (hf : Surjective f) : RightInverse (surjInv hf) f :=
  surjInv_eq hf
/-
**Function.leftInverse_surjInv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：leftInverse_surjInv (hf : Bijective f) : LeftInverse (surjInv hf.2) f
参数：hf : Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.rightInverse_of_injective_of_leftInverse`：∀ {α : Sort u_1} {β :
 Sort u_2} {f : α → β} {g : β → α},   Function.Injective f → Function.LeftInvers
e f g → Function.RightInverse f g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
-/
theorem leftInverse_surjInv (hf : Bijective f) : LeftInverse (surjInv hf.2) f :=
  rightInverse_of_injective_of_leftInverse hf.1 (rightInverse_surjInv hf.2)
/-
**Function.Surjective.hasRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjec
tive`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f : α → β}, Function.Surjective f → Function.
HasRightInverse f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
-/
theorem Surjective.hasRightInverse (hf : Surjective f) : HasRightInverse f :=
  ⟨_, rightInverse_surjInv hf⟩
/-
**Function.surjective_iff_hasRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：surjective_iff_hasRightInverse : Surjective f ↔ HasRightInverse f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用定理 `Function.HasRightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.HasRightInverse f → Function.Surjective f
-/
theorem surjective_iff_hasRightInverse : Surjective f ↔ HasRightInverse f :=
  ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩
/-
**Function.bijective_iff_has_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bijective_iff_has_inverse : Bijective f ↔ exists g, LeftInverse g f ∧ Righ
tInverse g f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.leftInverse_surjInv`：leftInverse_surjInv (hf : Bijective f) : L
eftInverse (surjInv hf.2) f
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
-/
theorem bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f :=
  ⟨fun hf ↦ ⟨_, leftInverse_surjInv hf, rightInverse_surjInv hf.2⟩, fun ⟨_, gl, gr⟩ ↦
    ⟨gl.injective, gr.surjective⟩⟩
/-
**Function.injective_surjInv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：injective_surjInv (h : Surjective f) : Injective (surjInv h)
参数：h : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
-/
theorem injective_surjInv (h : Surjective f) : Injective (surjInv h) :=
  (rightInverse_surjInv h).injective
/-
**Function.surjective_to_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α -> β)
 : Surjective f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α → β) :
    Surjective f :=
  fun _ ↦ let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩
/-
**Function.Surjective.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → Sort u_3} {f : (i : ι) → α i 
→ β i},   (∀ (i : ι), Function.Surjective (f i)) → Function.Surjective (Pi.map f
)
参数：i : ι；∀ (i : ι), Function.Surjective (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
-/
theorem Surjective.piMap {ι : Sort*} {α β : ι → Sort*} {f : ∀ i, α i → β i}
    (hf : ∀ i, Surjective (f i)) : Surjective (Pi.map f) := fun g ↦
  ⟨fun i ↦ surjInv (hf i) (g i), funext fun _ ↦ rightInverse_surjInv _ _⟩

/-- Composition by a surjective function on the left is itself surjective. -/
/-
**Function.Surjective.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} {g : β → γ}, Function.Surjective 
g → Function.Surjective fun x => g ∘ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.piMap`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → 
Sort u_3} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Surjective (f i)) → 
Function.Surjec…

--- 原说明 ---
Composition by a surjective function on the left is itself surjective.
-/
theorem Surjective.comp_left {g : β → γ} (hg : Surjective g) :
    Surjective (g ∘ · : (α → β) → α → γ) :=
  .piMap fun _ ↦ hg
/-
**Function.surjective_comp_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：surjective_comp_left_iff [Nonempty α] {g : β -> γ} : Surjective (g ∘ · : (
α -> β) -> α -> γ) ↔ Surjective g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Function.Surjective.comp_left`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} 
{g : β → γ}, Function.Surjective g → Function.Surjective fun x => g ∘ x
-/
theorem surjective_comp_left_iff [Nonempty α] {g : β → γ} :
    Surjective (g ∘ · : (α → β) → α → γ) ↔ Surjective g := by
  refine ⟨fun h c ↦ Nonempty.elim ‹_› fun a ↦ ?_, (·.comp_left)⟩
  have ⟨f, hf⟩ := h fun _ ↦ c
  exact ⟨f a, congr_fun hf _⟩
/-
**Function.Bijective.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → Sort u_3} {f : (i : ι) → α i 
→ β i},   (∀ (i : ι), Function.Bijective (f i)) → Function.Bijective (Pi.map f)
参数：i : ι；∀ (i : ι), Function.Bijective (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.piMap`：∀ {ι : Sort u_4} {α : ι → Sort u_5} {β : ι → S
ort u_6} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Injective (f i)) → Fu
nction.Injecti…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.piMap`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → 
Sort u_3} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Surjective (f i)) → 
Function.Surjec…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Bijective.piMap {ι : Sort*} {α β : ι → Sort*} {f : ∀ i, α i → β i}
    (hf : ∀ i, Bijective (f i)) : Bijective (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, .piMap fun i ↦ (hf i).2⟩

/-- Composition by a bijective function on the left is itself bijective. -/
/-
**Function.Bijective.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} {g : β → γ}, Function.Bijective g
 → Function.Bijective fun x => g ∘ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Surjective.comp_left`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} 
{g : β → γ}, Function.Surjective g → Function.Surjective fun x => g ∘ x
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f

--- 原说明 ---
Composition by a bijective function on the left is itself bijective.
-/
theorem Bijective.comp_left {g : β → γ} (hg : Bijective g) :
    Bijective (g ∘ · : (α → β) → α → γ) :=
  ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

end SurjInv

section Update

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α]
  {f : (a : α) → β a} {a : α} {b : β a}


/-- Replacing the value of a function at a given point by a given value. -/
@[grind]
/-
**Function.update** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：update (f : forall a, β a) (a' : α) (v : β a') (a : α) : β a
参数：f : forall a, β a；a' : α；v : β a'；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Replacing the value of a function at a given point by a given value.
-/
def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

@[simp]
/-
**Function.update_self** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_self (a : α) (v : β a) (f : forall a, β a) : update f a v a = v
参数：a : α；v : β a；f : forall a, β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem update_self (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

@[simp]
/-
**Function.update_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_of_ne {a a' : α} (h : a != a') (v : β a') (f : forall a, β a) : upd
ate f a' v a = f a
参数：h : a != a'；v : β a'；f : forall a, β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem update_of_ne {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=
  dif_neg h

/--
A congruence lemma for `Function.update`, specialized for the non-dependent case. Without this,
`simp` can't rewrite in the fourth argument `a` because the result type depends on `a`.
See also https://github.com/leanprover/lean4/issues/12478.
-/
@[congr]
/-
**Function.update_congr** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f₁ = f₂) {a'₁ a'₂ : α} (ha
' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (ha : a₁ = a₂) : Function.
update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂
参数：hf : f₁ = f₂；ha' : a'₁ = a'₂；hv : v₁ = v₂；ha : a₁ = a₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence lemma for `Function.update`, specialized for the non-dependent case
. Without this,
`simp` can't rewrite in the fourth argument `a` because the result type depends 
on `a`.
See also https://github.com/leanprover/lean4/issues/12478.
-/
lemma update_congr {β : Sort*}
    {f₁ f₂ : α → β} (hf : f₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂)
    {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (ha : a₁ = a₂) :
    Function.update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂ := by
  subst hf; subst ha'; subst hv; subst ha; rfl

/-- On non-dependent functions, `Function.update` can be expressed as an `ite` -/
/-
**Function.update_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_apply {β : Sort*} (f : α -> β) (a' : α) (b : β) (a : α) : update f 
a' b a = if a = a' then b else f a
参数：f : α -> β；a' : α；b : β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b

--- 原说明 ---
On non-dependent functions, `Function.update` can be expressed as an `ite`
-/
theorem update_apply {β : Sort*} (f : α → β) (a' : α) (b : β) (a : α) :
    update f a' b a = if a = a' then b else f a := by
  rcases Decidable.eq_or_ne a a' with rfl | hne <;> simp [*]

@[nontriviality]
/-
**Function.update_eq_const_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_eq_const_of_subsingleton [Subsingleton α] (a : α) (v : α') (f : α -
> α') : update f a v = const α v
参数：a : α；v : α'；f : α -> α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem update_eq_const_of_subsingleton [Subsingleton α] (a : α) (v : α') (f : α → α') :
    update f a v = const α v :=
  funext fun a' ↦ Subsingleton.elim a a' ▸ update_self ..
/-
**Function.surjective_eval** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：surjective_eval {α : Sort u} {β : α -> Sort v} [h : forall a, Nonempty (β 
a)] (a : α) : Surjective (eval a : (forall a, β a) -> β a)
参数：β a；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem surjective_eval {α : Sort u} {β : α → Sort v} [h : ∀ a, Nonempty (β a)] (a : α) :
    Surjective (eval a : (∀ a, β a) → β a) := fun b ↦
  ⟨@update _ _ (Classical.decEq α) (fun a ↦ (h a).some) a b,
   @update_self _ _ (Classical.decEq α) _ _ _⟩
/-
**Function.update_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_injective (f : forall a, β a) (a' : α) : Injective (update f a')
参数：f : forall a, β a；a' : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem update_injective (f : ∀ a, β a) (a' : α) : Injective (update f a') := fun v v' h ↦ by
  have := congr_fun h a'
  rwa [update_self, update_self] at this
/-
**Function.forall_update_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：forall_update_iff (f : forall a, β a) {a : α} {b : β a} (p : forall a, β a
 -> Prop) : (forall x, p x (update f a b x)) ↔ p a b ∧ forall x, x != a -> p x (
f x)
参数：f : forall a, β a；p : forall a, β a -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_forall_ne`：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔
 forall b, p b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma forall_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
    (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) := by
  rw [← and_forall_ne a, update_self]
  simp +contextual
/-
**Function.exists_update_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：exists_update_iff (f : forall a, β a) {a : α} {b : β a} (p : forall a, β a
 -> Prop) : (exists x, p x (update f a b x)) ↔ p a b ∨ exists x != a, p x (f x)
参数：f : forall a, β a；p : forall a, β a -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
    (∃ x, p x (update f a b x)) ↔ p a b ∨ ∃ x ≠ a, p x (f x) := by
  rw [← not_forall_not, forall_update_iff f fun a b ↦ ¬p a b]
  simp [-not_and, not_and_or]
/-
**Function.update_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_eq_iff {a : α} {b : β a} {f g : forall a, β a} : update f a b = g ↔
 b = g a ∧ forall x != a, f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
-/
theorem update_eq_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    update f a b = g ↔ b = g a ∧ ∀ x ≠ a, f x = g x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ y = g x
/-
**Function.eq_update_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：eq_update_iff {a : α} {b : β a} {f g : forall a, β a} : g = update f a b ↔
 g a = b ∧ forall x != a, g x = f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
-/
theorem eq_update_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    g = update f a b ↔ g a = b ∧ ∀ x ≠ a, g x = f x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ g x = y
/-
**Function.update_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u} {β : α → Sort v} [inst : DecidableEq α] {f : (a : α) → β a}
 {a : α} {b : β a},   Function.update f a b = f ↔ b = f a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma update_eq_self_iff : update f a b = f ↔ b = f a := by simp [update_eq_iff]
/-
**Function.eq_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u} {β : α → Sort v} [inst : DecidableEq α] {f : (a : α) → β a}
 {a : α} {b : β a},   f = Function.update f a b ↔ f a = b
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma eq_update_self_iff : f = update f a b ↔ f a = b := by simp [eqComm]
/-
**Function.ne_update_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：ne_update_self_iff : f != update f a b ↔ f a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.eq_update_self_iff`：∀ {α : Sort u} {β : α → Sort v} [inst : Dec
idableEq α] {f : (a : α) → β a} {a : α} {b : β a},   f = Function.update f a b ↔
 f a = b
-/
lemma ne_update_self_iff : f ≠ update f a b ↔ f a ≠ b := eq_update_self_iff.not
/-
**Function.update_ne_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：update_ne_self_iff : update f a b != f ↔ b != f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.update_eq_self_iff`：∀ {α : Sort u} {β : α → Sort v} [inst : Dec
idableEq α] {f : (a : α) → β a} {a : α} {b : β a},   Function.update f a b = f ↔
 b = f a
-/
lemma update_ne_self_iff : update f a b ≠ f ↔ b ≠ f a := update_eq_self_iff.not

@[simp]
/-
**Function.update_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_eq_self (a : α) (f : forall a, β a) : update f a (f a) = f
参数：a : α；f : forall a, β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.update_eq_iff`：update_eq_iff {a : α} {b : β a} {f g : forall a,
 β a} : update f a b = g ↔ b = g a ∧ forall x != a, f x = g x
-/
theorem update_eq_self (a : α) (f : ∀ a, β a) : update f a (f a) = f :=
  update_eq_iff.2 ⟨rfl, fun _ _ ↦ rfl⟩
/-
**Function.update_comp_eq_of_forall_ne'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_eq_of_forall_ne' {α'} (g : forall a, β a) {f : α' -> α} {i : α
} (a : β i) (h : forall x, f x != i) : (fun j => (update g i a) (f j)) = fun j =
> g (f j)
参数：g : forall a, β a；a : β i；h : forall x, f x != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem update_comp_eq_of_forall_ne' {α'} (g : ∀ a, β a) {f : α' → α} {i : α} (a : β i)
    (h : ∀ x, f x ≠ i) : (fun j ↦ (update g i a) (f j)) = fun j ↦ g (f j) :=
  funext fun _ ↦ update_of_ne (h _) _ _

variable [DecidableEq α']

/-- Non-dependent version of `Function.update_comp_eq_of_forall_ne'` -/
/-
**Function.update_comp_eq_of_forall_ne** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_eq_of_forall_ne {α β : Sort*} (g : α' -> β) {f : α -> α'} {i :
 α'} (a : β) (h : forall x, f x != i) : update g i a ∘ f = g ∘ f
参数：g : α' -> β；a : β；h : forall x, f x != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_forall_ne'`：update_comp_eq_of_forall_ne' {α'}
 (g : forall a, β a) {f : α' -> α} {i : α} (a : β i) (h : forall x, f x != i) : 
(fun j => (update g i a) (f…

--- 原说明 ---
Non-dependent version of `Function.update_comp_eq_of_forall_ne'`
-/
theorem update_comp_eq_of_forall_ne {α β : Sort*} (g : α' → β) {f : α → α'} {i : α'} (a : β)
    (h : ∀ x, f x ≠ i) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h
/-
**Function.update_comp_eq_of_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_eq_of_injective' (g : forall a, β a) {f : α' -> α} (hf : Funct
ion.Injective f) (i : α') (a : β (f i)) : (fun j => update g (f i) a (f j)) = up
date (fun i => g (f i)) i a
参数：g : forall a, β a；hf : Function.Injective f；i : α'；a : β (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.eq_update_iff`：eq_update_iff {a : α} {b : β a} {f g : forall a,
 β a} : g = update f a b ↔ g a = b ∧ forall x != a, g x = f x
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem update_comp_eq_of_injective' (g : ∀ a, β a) {f : α' → α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) : (fun j ↦ update g (f i) a (f j)) = update (fun i ↦ g (f i)) i a :=
  eq_update_iff.2 ⟨update_self .., fun _ hj ↦ update_of_ne (hf.ne hj) _ _⟩
/-
**Function.update_apply_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_apply_of_injective (g : forall a, β a) {f : α' -> α} (hf : Function
.Injective f) (i : α') (a : β (f i)) (j : α') : update g (f i) a (f j) = update 
(fun i => g (f i)) i a j
参数：g : forall a, β a；hf : Function.Injective f；i : α'；a : β (f i)；j : α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Function.update_comp_eq_of_injective'`：update_comp_eq_of_injective' (g :
 forall a, β a) {f : α' -> α} (hf : Function.Injective f) (i : α') (a : β (f i))
 : (fun j => update g (f i)…
-/
theorem update_apply_of_injective
    (g : ∀ a, β a) {f : α' → α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) (j : α') :
    update g (f i) a (f j) = update (fun i ↦ g (f i)) i a j :=
  congr_fun (update_comp_eq_of_injective' g hf i a) j

/-- Non-dependent version of `Function.update_comp_eq_of_injective'` -/
/-
**Function.update_comp_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_eq_of_injective {β : Sort*} (g : α' -> β) {f : α -> α'} (hf : 
Function.Injective f) (i : α) (a : β) : Function.update g (f i) a ∘ f = Function
.update (g ∘ f) i a
参数：g : α' -> β；hf : Function.Injective f；i : α；a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_injective'`：update_comp_eq_of_injective' (g :
 forall a, β a) {f : α' -> α} (hf : Function.Injective f) (i : α') (a : β (f i))
 : (fun j => update g (f i)…

--- 原说明 ---
Non-dependent version of `Function.update_comp_eq_of_injective'`
-/
theorem update_comp_eq_of_injective {β : Sort*} (g : α' → β) {f : α → α'}
    (hf : Function.Injective f) (i : α) (a : β) :
    Function.update g (f i) a ∘ f = Function.update (g ∘ f) i a :=
  update_comp_eq_of_injective' g hf i a

/-- Recursors can be pushed inside `Function.update`.

The `ctor` argument should be a one-argument constructor like `Sum.inl`,
and `recursor` should be an inductive recursor partially applied in all but that constructor,
such as `(Sum.rec · g)`.

In future, we should build some automation to generate applications like `Option.rec_update` for all
/-
**Function.types.** 是 Mathlib 中的一个归纳类型，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
inductive types. -/
@[nolint unusedArguments]
/-
**Function.rec_update** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：rec_update {ι κ : Sort*} {α : κ -> Sort*} [DecidableEq ι] [DecidableEq κ] 
{ctor : ι -> κ} (_ : Function.Injective ctor) (recursor : ((i : ι) -> α (ctor i)
) -> ((i : κ) -> α i)) (h : forall f i, recursor f (ctor i) = f i) (h2 : forall 
f₁ f₂ k, (forall i, ctor i != k) -> recursor f₁ k = recursor f₂ k) (f : (i : ι) 
-> α (ctor i)) (i : ι) (x : α (ctor i)) : recursor (update f i x) = update (recu
rsor f) (ctor i) x
参数：_ : Function.Injective ctor；recursor : ((i : ι) -> α (ctor i)) -> ((i : κ) ->
 α i)；h : forall f i, recursor f (ctor i) = f i；h2 : forall f₁ f₂ k, (forall i, 
ctor i != k) -> recursor f₁ k = recursor f₂ k；f : (i : ι) -> α (ctor i)；i : ι；x 
: α (ctor i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursors can be pushed inside `Function.update`.

The `ctor` argument should be a one-argument constructor like `Sum.inl`,
and `recursor` should be an inductive recursor partially applied in all but that
 constructor,
such as `(Sum.rec · g)`.

In future, we should build some automation to generate applications like `Option
.rec_update` for all
inductive types.
-/
lemma rec_update {ι κ : Sort*} {α : κ → Sort*} [DecidableEq ι] [DecidableEq κ]
    {ctor : ι → κ} (_ : Function.Injective ctor)
    (recursor : ((i : ι) → α (ctor i)) → ((i : κ) → α i))
    (h : ∀ f i, recursor f (ctor i) = f i)
    (h2 : ∀ f₁ f₂ k, (∀ i, ctor i ≠ k) → recursor f₁ k = recursor f₂ k)
    (f : (i : ι) → α (ctor i)) (i : ι) (x : α (ctor i)) :
    recursor (update f i x) = update (recursor f) (ctor i) x := by
  grind

@[simp]
/-
**Function._root_.Option.rec_update** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Option.rec_update {α : Type*} {β : Option α → Sort*} [DecidableEq α]
    (f : β none) (g : ∀ a, β (.some a)) (a : α) (x : β (.some a)) :
    Option.rec f (update g a x) = update (Option.rec f g) (.some a) x :=
  Function.rec_update (@Option.some.inj _) (Option.rec f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _
/-
**Function.apply_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι -> Sort*} (f : forall i,
 α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j : ι) : f j (update g i v j
) = update (fun k => f k (g k)) i (f i v) j
参数：f : forall i, α i -> β i；g : forall i, α i；i : ι；v : α i；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_update {ι : Sort*} [DecidableEq ι] {α β : ι → Sort*} (f : ∀ i, α i → β i)
    (g : ∀ i, α i) (i : ι) (v : α i) (j : ι) :
    f j (update g i v j) = update (fun k ↦ f k (g k)) i (f i v) j := by
  grind
/-
**Function.apply_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι -> Sort*} (f : forall i,
 α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j : ι) : f j (update g i v j
) = update (fun k => f k (g k)) i (f i v) j
参数：f : forall i, α i -> β i；g : forall i, α i；i : ι；v : α i；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_update₂ {ι : Sort*} [DecidableEq ι] {α β γ : ι → Sort*} (f : ∀ i, α i → β i → γ i)
    (g : ∀ i, α i) (h : ∀ i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
    f j (update g i v j) (update h i w j) = update (fun k ↦ f k (g k) (h k)) i (f i v w) j := by
  grind
/-
**Function.pred_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：pred_update (P : forall ⦃a⦄, β a -> Prop) (f : forall a, β a) (a' : α) (v 
: β a') (a : α) : P (update f a' v a) ↔ a = a' ∧ P v ∨ a != a' ∧ P (f a)
参数：P : forall ⦃a⦄, β a -> Prop；f : forall a, β a；a' : α；v : β a'；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pred_update (P : ∀ ⦃a⦄, β a → Prop) (f : ∀ a, β a) (a' : α) (v : β a') (a : α) :
    P (update f a' v a) ↔ a = a' ∧ P v ∨ a ≠ a' ∧ P (f a) := by
  grind
/-
**Function.comp_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：comp_update {α' : Sort*} {β : Sort*} (f : α' -> β) (g : α -> α') (i : α) (
v : α') : f ∘ update g i v = update (f ∘ g) i (f v)
参数：f : α' -> β；g : α -> α'；i : α；v : α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.apply_update`：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι
 -> Sort*} (f : forall i, α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j :
 ι) : f j (…
-/
theorem comp_update {α' : Sort*} {β : Sort*} (f : α' → β) (g : α → α') (i : α) (v : α') :
    f ∘ update g i v = update (f ∘ g) i (f v) :=
  funext <| apply_update _ _ _ _
/-
**Function.update_comm** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comm {α} [DecidableEq α] {β : α -> Sort*} {a b : α} (h : a != b) (v
 : β a) (w : β b) (f : forall a, β a) : update (update f a v) b w = update (upda
te f b w) a v
参数：h : a != b；v : β a；w : β b；f : forall a, β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_comm {α} [DecidableEq α] {β : α → Sort*} {a b : α} (h : a ≠ b) (v : β a) (w : β b)
    (f : ∀ a, β a) : update (update f a v) b w = update (update f b w) a v := by
  grind

@[simp]
/-
**Function.update_idem** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_idem {α} [DecidableEq α] {β : α -> Sort*} {a : α} (v w : β a) (f : 
forall a, β a) : update (update f a v) a w = update f a w
参数：v w : β a；f : forall a, β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_idem {α} [DecidableEq α] {β : α → Sort*} {a : α} (v w : β a) (f : ∀ a, β a) :
    update (update f a v) a w = update f a w := by
  grind

@[simp]
/-
**Function._root_.Pi.map_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.map_update {ι : Sort*} [DecidableEq ι] {α β : ι → Sort*}
    {f : ∀ i, α i → β i}
    (g : ∀ i, α i) (i : ι) (a : α i) :
    Pi.map f (Function.update g i a) = Function.update (Pi.map f g) i (f i a) := by
  ext j
  obtain rfl | hij := eq_or_ne j i <;> simp [*]

@[simp]
/-
**Function._root_.Pi.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.map_injective
    {ι : Sort*} {α β : ι → Sort*} [∀ i, Nonempty (α i)] {f : ∀ i, α i → β i} :
    Injective (Pi.map f) ↔ ∀ i, Injective (f i) where
  mp h i x y hxy := by
    classical
    have : Inhabited (∀ i, α i) := ⟨fun _ => Classical.choice inferInstance⟩
    replace h := @h (Function.update default i x) (Function.update default i y) ?_
    · simpa using congrFun h i
    rw [Pi.map_update, Pi.map_update, hxy]
  mpr := .piMap

end Update

noncomputable section Extend

variable {α β γ : Sort*} {f : α → β}

/-- Extension of a function `g : α → γ` along a function `f : α → β`.

For every `a : α`, `f a` is sent to `g a`. `f` might not be surjective, so we use an auxiliary
function `j : β → γ` by sending `b : β` not in the range of `f` to `j b`. If you do not care about
the behavior outside the range, `j` can be used as a junk value by setting it to be `0` or
`Classical.arbitrary` (assuming `γ` is nonempty).

This definition is mathematically meaningful only when `f a₁ = f a₂ → g a₁ = g a₂` (spelled
`g.FactorsThrough f`). In particular this holds if `f` is injective.

A typical use case is extending a function from a subtype to the entire type. If you wish to extend
`g : {b : β // p b} → γ` to a function `β → γ`, you should use `Function.extend Subtype.val g j`. -/
/-
**Function.extend** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：extend (f : α -> β) (g : α -> γ) (j : β -> γ) : β -> γ
参数：f : α -> β；g : α -> γ；j : β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of a function `g : α → γ` along a function `f : α → β`.

For every `a : α`, `f a` is sent to `g a`. `f` might not be surjective, so we us
e an auxiliary
function `j : β → γ` by sending `b : β` not in the range of `f` to `j b`. If you
 do not care about
the behavior outside the range, `j` can be used as a junk value by setting it to
 be `0` or
`Classical.arbitrary` (assuming `γ` is nonempty).

This definition is mathematically meaningful only when `f a₁ = f a₂ → g a₁ = g a
₂` (spelled
`g.FactorsThrough f`). In particular this holds if `f` is injective.

A typical use case is extending a function from a subtype to the entire type. If
 you wish to extend
`g : {b : β // p b} → γ` to a function `β → γ`, you should use `Function.extend 
Subtype.val g j`.
-/
def extend (f : α → β) (g : α → γ) (j : β → γ) : β → γ := fun b ↦
  open scoped Classical in
  if h : ∃ a, f a = b then g (Classical.choose h) else j b

/-- g factors through f : `f a = f b → g a = g b` -/
/-
**Function.FactorsThrough** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：FactorsThrough (g : α -> γ) (f : α -> β) : Prop
参数：g : α -> γ；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
g factors through f : `f a = f b → g a = g b`
-/
def FactorsThrough (g : α → γ) (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f a = f b → g a = g b
/-
**Function.extend_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) (b : β) [Decidable (exi
sts a, f a = b)] : extend f g e' b = if h : exists a, f a = b then g (Classical.
choose h) else e' b
参数：f : α -> β；g : α -> γ；e' : β -> γ；b : β；exists a, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem extend_def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [Decidable (∃ a, f a = b)] :
    extend f g e' b = if h : ∃ a, f a = b then g (Classical.choose h) else e' b := by
  unfold extend
  congr
/-
**Function.Injective.factorsThrough** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injectiv
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Inj
ective f → ∀ (g : α → γ), Function.FactorsThrough g f
参数：g : α → γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma Injective.factorsThrough (hf : Injective f) (g : α → γ) : g.FactorsThrough f :=
  fun _ _ h => congr_arg g (hf h)
/-
**Function.FactorsThrough.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Facto
rsThrough`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : α → γ},   
Function.FactorsThrough g f → ∀ (e' : β → γ) (a : α), Function.extend f g e' (f 
a) = g a
参数：e' : β → γ；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `exists_apply_eq_apply`：∀ {α : Sort u_2} {β : Sort u_1} (f : α → β) (a' :
 α), ∃ a, f a = f a'
-/
lemma FactorsThrough.extend_apply {g : α → γ} (hf : g.FactorsThrough f) (e' : β → γ) (a : α) :
    extend f g e' (f a) = g a := by
  classical
  simp only [extend_def, dif_pos, exists_apply_eq_apply]
  exact hf (Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]
/-
**Function.Injective.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`
。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Inj
ective f → ∀ (g : α → γ) (e' : β → γ) (a : α), Function.extend f g e' (f a) = g 
a
参数：g : α → γ；e' : β → γ；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FactorsThrough.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ
 : Sort u_3} {f : α → β} {g : α → γ},   Function.FactorsThrough g f → ∀ (e' : β 
→ γ) (a : α), Function.ext…
· 使用定理 `Function.Injective.factorsThrough`：∀ {α : Sort u_1} {β : Sort u_2} {γ : 
Sort u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ), Function.FactorsT
hrough g f
-/
theorem Injective.extend_apply (hf : Injective f) (g : α → γ) (e' : β → γ) (a : α) :
    extend f g e' (f a) = g a :=
  (hf.factorsThrough g).extend_apply e' a

@[simp]
/-
**Function.extend_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β) (hb : ¬exists a, f a = b)
 : extend f g e' b = e' b
参数：g : α -> γ；e' : β -> γ；b : β；hb : ¬exists a, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_apply' (g : α → γ) (e' : β → γ) (b : β) (hb : ¬∃ a, f a = b) :
    extend f g e' b = e' b := by
  classical
  simp [Function.extend_def, hb]

@[simp]
/-
**Function.extend_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_id (g : α -> γ) (e' : α -> γ) : extend id g e' = g
参数：g : α -> γ；e' : α -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem extend_id (g : α → γ) (e' : α → γ) :
    extend id g e' = g :=
  funext <| injective_id.extend_apply g _
/-
**Function.Injective.extend_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {γ : Sort u_3} {α₁ : Sort u_4} {α₂ : Sort u_5} {α₃ : Sort u_6} {f₁₂ : α₁
 → α₂},   Function.Injective f₁₂ →     ∀ {f₂₃ : α₂ → α₃},       Function.Injecti
ve f₂₃ →         ∀ (g : α₁ → γ) (e' : α₃ → γ),           Function.extend (f₂₃ ∘ 
f₁₂) g e' = Function.extend f₂₃ (Function.extend f₁₂ g (e' ∘ f₂₃)) e'
参数：g : α₁ → γ；e' : α₃ → γ；f₂₃ ∘ f₁₂；Function.extend f₁₂ g (e' ∘ f₂₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem Injective.extend_comp {α₁ α₂ α₃ : Sort*} {f₁₂ : α₁ → α₂} (h₁₂ : Function.Injective f₁₂)
    {f₂₃ : α₂ → α₃} (h₂₃ : Function.Injective f₂₃) (g : α₁ → γ) (e' : α₃ → γ) :
    extend (f₂₃ ∘ f₁₂) g e' = extend f₂₃ (extend f₁₂ g (e' ∘ f₂₃)) e' := by
  ext a
  by_cases h₃ : ∃ b, f₂₃ b = a
  · obtain ⟨b, rfl⟩ := h₃
    rw [Injective.extend_apply h₂₃]
    by_cases h₂ : ∃ c, f₁₂ c = b
    · obtain ⟨c, rfl⟩ := h₂
      rw [h₁₂.extend_apply]
      exact (h₂₃.comp h₁₂).extend_apply _ _ _
    · rw [extend_apply' _ _ _ h₂, extend_apply', comp_apply]
      exact fun h ↦ h₂ (Exists.casesOn h fun c hc ↦ Exists.intro c (h₂₃ hc))
  · rw [extend_apply' _ _ _ h₃, extend_apply']
    exact fun h ↦ h₃ (Exists.casesOn h fun c hc ↦ Exists.intro (f₁₂ c) (hc))
/-
**Function.factorsThrough_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：factorsThrough_iff (g : α -> γ) [Nonempty γ] : g.FactorsThrough f ↔ exists
 (e : β -> γ), g = e ∘ f
参数：g : α -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.FactorsThrough.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ
 : Sort u_3} {f : α → β} {g : α → γ},   Function.FactorsThrough g f → ∀ (e' : β 
→ γ) (a : α), Function.ext…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma factorsThrough_iff (g : α → γ) [Nonempty γ] : g.FactorsThrough f ↔ ∃ (e : β → γ), g = e ∘ f :=
  ⟨fun hf => ⟨extend f g (const β (Classical.arbitrary γ)),
      funext (fun x => by simp only [comp_apply, hf.extend_apply])⟩,
  fun h _ _ hf => by rw [Classical.choose_spec h, comp_apply, comp_apply, hf]⟩
/-
**Function.apply_extend** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：apply_extend {δ} {g : α -> γ} (F : γ -> δ) (f : α -> β) (e' : β -> γ) (b :
 β) : F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b
参数：F : γ -> δ；f : α -> β；e' : β -> γ；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
-/
lemma apply_extend {δ} {g : α → γ} (F : γ → δ) (f : α → β) (e' : β → γ) (b : β) :
    F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b :=
  open scoped Classical in apply_dite F _ _ _
/-
**Function.extend_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_injective (hf : Injective f) (e' : β -> γ) : Injective fun g => ext
end f g e'
参数：hf : Injective f；e' : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
-/
theorem extend_injective (hf : Injective f) (e' : β → γ) : Injective fun g ↦ extend f g e' := by
  intro g₁ g₂ hg
  refine funext fun x ↦ ?_
  have H := congr_fun hg (f x)
  simp only [hf.extend_apply] at H
  exact H
/-
**Function.FactorsThrough.extend_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Factor
sThrough`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} {g : α → γ} (e'
 : β → γ),   Function.FactorsThrough g f → Function.extend f g e' ∘ f = g
参数：e' : β → γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.FactorsThrough.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ
 : Sort u_3} {f : α → β} {g : α → γ},   Function.FactorsThrough g f → ∀ (e' : β 
→ γ) (a : α), Function.ext…
-/
lemma FactorsThrough.extend_comp {g : α → γ} (e' : β → γ) (hf : FactorsThrough g f) :
    extend f g e' ∘ f = g :=
  funext fun a => hf.extend_apply e' a

@[simp]
/-
**Function.extend_const** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：extend_const (f : α -> β) (c : γ) : extend f (fun _ => c) (fun _ => c) = f
un _ => c
参数：f : α -> β；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_id`：∀ {c : Prop} [inst : Decidable c] {α : Sort u_1} (t : α), (if c 
then t else t) = t
-/
lemma extend_const (f : α → β) (c : γ) : extend f (fun _ ↦ c) (fun _ ↦ c) = fun _ ↦ c :=
  funext fun _ ↦ open scoped Classical in ite_id _

@[simp]
/-
**Function.extend_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_comp (hf : Injective f) (g : α -> γ) (e' : β -> γ) : extend f g e' 
∘ f = g
参数：hf : Injective f；g : α -> γ；e' : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
-/
theorem extend_comp (hf : Injective f) (g : α → γ) (e' : β → γ) : extend f g e' ∘ f = g :=
  funext fun a ↦ hf.extend_apply g e' a
/-
**Function.Injective.surjective_comp_right'** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Injective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β},   Function.Inj
ective f → ∀ (g₀ : β → γ), Function.Surjective fun g => g ∘ f
参数：g₀ : β → γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.extend_comp`：extend_comp (hf : Injective f) (g : α -> γ) (e' : 
β -> γ) : extend f g e' ∘ f = g
-/
theorem Injective.surjective_comp_right' (hf : Injective f) (g₀ : β → γ) :
    Surjective fun g : β → γ ↦ g ∘ f :=
  fun g ↦ ⟨extend f g g₀, Function.extend_comp hf _ _⟩
/-
**Function.Injective.surjective_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.I
njective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β} [Nonempty γ],  
 Function.Injective f → Function.Surjective fun g => g ∘ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.surjective_comp_right'`：∀ {α : Sort u_1} {β : Sort u_
2} {γ : Sort u_3} {f : α → β},   Function.Injective f → ∀ (g₀ : β → γ), Function
.Surjective fun g => g ∘ f
-/
theorem Injective.surjective_comp_right [Nonempty γ] (hf : Injective f) :
    Surjective fun g : β → γ ↦ g ∘ f :=
  hf.surjective_comp_right' fun _ ↦ Classical.choice ‹_›
/-
**Function.surjective_comp_right_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on`。
形式化陈述：surjective_comp_right_iff_injective {γ : Type*} [Nontrivial γ] : Surjectiv
e (fun g : β -> γ => g ∘ f) ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Function.Injective.surjective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β} [Nonempty γ],   Function.Injective f → Function.Sur
jective fun g => g ∘ f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
-/
theorem surjective_comp_right_iff_injective {γ : Type*} [Nontrivial γ] :
    Surjective (fun g : β → γ ↦ g ∘ f) ↔ Injective f := by
  classical
  refine ⟨not_imp_not.mp fun not_inj surj ↦ not_subsingleton γ ⟨fun c c' ↦ ?_⟩,
    (·.surjective_comp_right)⟩
  simp only [Injective, not_forall] at not_inj
  have ⟨a₁, a₂, eq, ne⟩ := not_inj
  have ⟨f, hf⟩ := surj (if · = a₂ then c else c')
  have h₁ := congr_fun hf a₁
  have h₂ := congr_fun hf a₂
  simp only [comp_apply, if_neg ne, reduceIte] at h₁ h₂
  rw [← h₁, eq, h₂]
/-
**Function.Bijective.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β}, Function.Bijec
tive f → Function.Bijective fun g => g ∘ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.leftInverse_surjInv`：leftInverse_surjInv (hf : Bijective f) : L
eftInverse (surjInv hf.2) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Bijective.comp_right (hf : Bijective f) : Bijective fun g : β → γ ↦ g ∘ f :=
  ⟨hf.surjective.injective_comp_right, fun g ↦
    ⟨g ∘ surjInv hf.surjective,
     by simp only [comp_assoc g _ f, (leftInverse_surjInv hf).comp_eq_id, comp_id]⟩⟩

end Extend

namespace FactorsThrough

/-
**Function.FactorsThrough.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Function.FactorsThrough
`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.FactorsThrough f f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem rfl {α β : Sort*} {f : α → β} : FactorsThrough f f := fun _ _ ↦ id
/-
**Function.FactorsThrough.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.FactorsT
hrough`。
形式化陈述：comp_left {α β γ δ : Sort*} {f : α -> β} {g : α -> γ} (h : FactorsThrough 
g f) (g' : γ -> δ) : FactorsThrough (g' ∘ g) f
参数：h : FactorsThrough g f；g' : γ -> δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comp_left {α β γ δ : Sort*} {f : α → β} {g : α → γ} (h : FactorsThrough g f) (g' : γ → δ) :
    FactorsThrough (g' ∘ g) f := fun _x _y hxy ↦
  congr_arg g' (h hxy)
/-
**Function.FactorsThrough.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Factors
Through`。
形式化陈述：comp_right {α β γ δ : Sort*} {f : α -> β} {g : α -> γ} (h : FactorsThrough
 g f) (g' : δ -> α) : FactorsThrough (g ∘ g') (f ∘ g')
参数：h : FactorsThrough g f；g' : δ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_right {α β γ δ : Sort*} {f : α → β} {g : α → γ} (h : FactorsThrough g f) (g' : δ → α) :
    FactorsThrough (g ∘ g') (f ∘ g') := fun _x _y hxy ↦
  h hxy

end FactorsThrough

section CurryAndUncurry

/-
**Function.uncurry_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：uncurry_def {α β γ} (f : α -> β -> γ) : uncurry f = fun p => f p.1 p.2
参数：f : α -> β -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_def {α β γ} (f : α → β → γ) : uncurry f = fun p ↦ f p.1 p.2 :=
  rfl
/-
**Function.uncurry_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：uncurry_injective {α β γ} : Function.Injective (uncurry : (α -> β -> γ) ->
 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Function.curry_uncurry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α → β → φ), Function.curry (Function.uncurry f) = f
-/
theorem uncurry_injective {α β γ} : Function.Injective (uncurry : (α → β → γ) → _) :=
  LeftInverse.injective curry_uncurry
/-
**Function.curry_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：curry_injective {α β γ} : Function.Injective (curry : (α × β -> γ) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
-/
theorem curry_injective {α β γ} : Function.Injective (curry : (α × β → γ) → _) :=
  LeftInverse.injective uncurry_curry
/-
**Function.uncurry_flip** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：uncurry_flip {α β γ} (f : α -> β -> γ) : uncurry (flip f) = uncurry f ∘ Pr
od.swap
参数：f : α -> β -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_flip {α β γ} (f : α → β → γ) : uncurry (flip f) = uncurry f ∘ Prod.swap :=
  rfl
/-
**Function.flip_curry** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：flip_curry {α β γ} (f : α × β -> γ) : flip (curry f) = curry (f ∘ Prod.swa
p)
参数：f : α × β -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_curry {α β γ} (f : α × β → γ) : flip (curry f) = curry (f ∘ Prod.swap) :=
  rfl
/-
**Function.curry_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：curry_update {α α' β : Type*} [DecidableEq α] [DecidableEq α'] (f : α × α'
 -> β) (aa' : α × α') (b : β) : curry (Function.update f aa' b) = Function.updat
e (curry f) aa'.1 (Function.update (curry f aa'.1) aa'.2 b)
参数：f : α × α' -> β；aa' : α × α'；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem curry_update {α α' β : Type*} [DecidableEq α] [DecidableEq α']
    (f : α × α' → β) (aa' : α × α') (b : β) :
    curry (Function.update f aa' b) =
      Function.update (curry f) aa'.1 (Function.update (curry f aa'.1) aa'.2 b) := by
  ext a a'
  let ⟨a₂, a₂'⟩ := aa'
  obtain rfl | ha := eq_or_ne a a₂ <;> obtain rfl | ha' := eq_or_ne a' a₂' <;> simp [*]
/-
**Function.uncurry_update_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：uncurry_update_update {α α' β : Type*} [DecidableEq α] [DecidableEq α'] (f
 : α -> α' -> β) (a : α) (a' : α') (b : β) : uncurry (Function.update f a (Funct
ion.update (f a) a' b)) = Function.update (uncurry f) (a, a') b
参数：f : α -> α' -> β；a : α；a' : α'；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.curry_injective`：curry_injective {α β γ} : Function.Injective (
curry : (α × β -> γ) -> _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.curry_update`：curry_update {α α' β : Type*} [DecidableEq α] [De
cidableEq α'] (f : α × α' -> β) (aa' : α × α') (b : β) : curry (Function.update 
f aa' b) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uncurry_update_update {α α' β : Type*} [DecidableEq α] [DecidableEq α']
    (f : α → α' → β) (a : α) (a' : α') (b : β) :
    uncurry (Function.update f a (Function.update (f a) a' b)) =
      Function.update (uncurry f) (a, a') b := by
  apply curry_injective
  simp [curry_update]

end CurryAndUncurry

section Uncurry

variable {α β γ δ : Type*}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
/-
**Function.HasUncurry** 是 Mathlib 中的一个归纳类型，位于命名空间 `Function`。
形式化陈述：Type u_5 → outParam (Type u_6) → outParam (Type u_7) → Type (max (max u_5 
u_6) u_7)
参数：Type u_6；Type u_7；max (max u_5 u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Records a way to turn an element of `α` into a function from `β` to `γ`. The mos
t generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps.
-/
class HasUncurry (α : Type*) (β : outParam Type*) (γ : outParam Type*) where
  /-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
  `f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
  for bundled maps. -/
  uncurry : α → β → γ

@[inherit_doc] prefix:max "↿" => HasUncurry.uncurry
/-
**Function.hasUncurryBase** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
形式化陈述：hasUncurryBase : HasUncurry (α -> β) α β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasUncurryBase : HasUncurry (α → β) α β :=
  ⟨id⟩
/-
**Function.hasUncurryInduction** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
形式化陈述：hasUncurryInduction [HasUncurry β γ δ] : HasUncurry (α -> β) (α × γ) δ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasUncurryInduction [HasUncurry β γ δ] : HasUncurry (α → β) (α × γ) δ :=
  ⟨fun f p ↦ ↿(f p.1) p.2⟩

end Uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
/-
**Function.Involutive** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Involutive {α} (f : α -> α) : Prop
参数：f : α -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is involutive, if `f ∘ f = id`.
-/
def Involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x
/-
**Function._root_.Bool.involutive_not** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bool.involutive_not : Involutive not :=
  Bool.not_not

namespace Involutive

variable {α : Sort u} {f : α → α} (h : Involutive f)

include h

@[simp]
/-
**Function.Involutive.comp_self** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：comp_self : f ∘ f = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem comp_self : f ∘ f = id :=
  funext h
/-
**Function.Involutive.leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive
`。
形式化陈述：∀ {α : Sort u} {f : α → α}, Function.Involutive f → Function.LeftInverse f
 f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem leftInverse : LeftInverse f f := h
/-
**Function.Involutive.leftInverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involu
tive`。
形式化陈述：leftInverse_iff {g : α -> α} : g.LeftInverse f ↔ g = f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Involutive.leftInverse`：∀ {α : Sort u} {f : α → α}, Function.In
volutive f → Function.LeftInverse f f
-/
theorem leftInverse_iff {g : α → α} :
    g.LeftInverse f ↔ g = f :=
  ⟨fun hg ↦ funext fun x ↦ by rw [← h x, hg, h], fun he ↦ he ▸ h.leftInverse⟩
/-
**Function.Involutive.rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutiv
e`。
形式化陈述：∀ {α : Sort u} {f : α → α}, Function.Involutive f → Function.RightInverse 
f f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem rightInverse : RightInverse f f := h
/-
**Function.Involutive.injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：∀ {α : Sort u} {f : α → α}, Function.Involutive f → Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Function.Involutive.leftInverse`：∀ {α : Sort u} {f : α → α}, Function.In
volutive f → Function.LeftInverse f f
-/
protected theorem injective : Injective f := h.leftInverse.injective
/-
**Function.Involutive.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`
。
形式化陈述：∀ {α : Sort u} {f : α → α}, Function.Involutive f → Function.Surjective f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem surjective : Surjective f := fun x ↦ ⟨f x, h x⟩
/-
**Function.Involutive.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：∀ {α : Sort u} {f : α → α}, Function.Involutive f → Function.Bijective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
-/
protected theorem bijective : Bijective f := ⟨h.injective, h.surjective⟩

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
/-
**Function.Involutive.ite_not** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：∀ {α : Sort u} {f : α → α},   Function.Involutive f → ∀ (P : Prop) [inst :
 Decidable P] (x : α), f (if P then x else f x) = if ¬P then x else f x
参数：P : Prop；x : α；if P then x else f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x

--- 原说明 ---
Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition i
n the `ite`.
-/
protected theorem ite_not (P : Prop) [Decidable P] (x : α) :
    f (ite P x (f x)) = ite (¬P) x (f x) := by rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `Function.Injective.eq_iff`. -/
/-
**Function.Involutive.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：∀ {α : Sort u} {f : α → α}, Function.Involutive f → ∀ {x y : α}, f x = y ↔
 x = f y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f

--- 原说明 ---
An involution commutes across an equality. Compare to `Function.Injective.eq_iff
`.
-/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y :=
  h.injective.eq_iff' (h y)

end Involutive

/-
**Function.not_involutive** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：not_involutive : Involutive Not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
lemma not_involutive : Involutive Not := fun _ ↦ propext not_not
/-
**Function.not_injective** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：not_injective : Injective Not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用引理 `Function.not_involutive`：not_involutive : Involutive Not
-/
lemma not_injective : Injective Not := not_involutive.injective
/-
**Function.not_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：not_surjective : Surjective Not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用引理 `Function.not_involutive`：not_involutive : Involutive Not
-/
lemma not_surjective : Surjective Not := not_involutive.surjective
/-
**Function.not_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：not_bijective : Bijective Not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用引理 `Function.not_involutive`：not_involutive : Involutive Not
-/
lemma not_bijective : Bijective Not := not_involutive.bijective

@[simp]
/-
**Function.symm_apply_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：symm_apply_eq_iff {α : Sort*} {f : α -> α} : Std.Symm (f · = ·) ↔ Involuti
ve f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma symm_apply_eq_iff {α : Sort*} {f : α → α} : Std.Symm (f · = ·) ↔ Involutive f := by
  simp [symm_def, Involutive]

@[deprecated (since := "2026-06-10")] alias symmetric_apply_eq_iff := symm_apply_eq_iff

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
/-
**Function.Injective2** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Injective2 {α β γ : Sort*} (f : α -> β -> γ) : Prop
参数：f : α -> β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → 
γ` being injective.
-/
def Injective2 {α β γ : Sort*} (f : α → β → γ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace Injective2

variable {α β γ : Sort*} {f : α → β → γ}

/-- A binary injective function is injective when only the left argument varies. -/
/-
**Function.Injective2.left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective2`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β → γ},   Function
.Injective2 f → ∀ (b : β), Function.Injective fun a => f a b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A binary injective function is injective when only the left argument varies.
-/
protected theorem left (hf : Injective2 f) (b : β) : Function.Injective fun a ↦ f a b :=
  fun _ _ h ↦ (hf h).left

/-- A binary injective function is injective when only the right argument varies. -/
/-
**Function.Injective2.right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective2`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β → γ},   Function
.Injective2 f → ∀ (a : α), Function.Injective (f a)
参数：a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A binary injective function is injective when only the right argument varies.
-/
protected theorem right (hf : Injective2 f) (a : α) : Function.Injective (f a) :=
  fun _ _ h ↦ (hf h).right
/-
**Function.Injective2.uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective2`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {γ : Type u_6} {f : α → β → γ},   Function
.Injective2 f → Function.Injective (Function.uncurry f)
参数：Function.uncurry f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
protected theorem uncurry {α β γ : Type*} {f : α → β → γ} (hf : Injective2 f) :
    Function.Injective (uncurry f) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h ↦ (hf h).elim (congr_arg₂ _)

/-- As a map from the left argument to a unary function, `f` is injective. -/
/-
**Function.Injective2.left'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective2`。
形式化陈述：left' (hf : Injective2 f) [Nonempty β] : Function.Injective f
参数：hf : Injective2 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {f : α → β → γ},   Function.Injective2 f → ∀ (b : β), Function.Injective fun a 
=> f a b
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
As a map from the left argument to a unary function, `f` is injective.
-/
theorem left' (hf : Injective2 f) [Nonempty β] : Function.Injective f := fun _ _ h ↦
  let ⟨b⟩ := ‹Nonempty β›
  hf.left b <| (congr_fun h b :)

/-- As a map from the right argument to a unary function, `f` is injective. -/
/-
**Function.Injective2.right'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective2`。
形式化陈述：right' (hf : Injective2 f) [Nonempty α] : Function.Injective fun b a => f 
a b
参数：hf : Injective2 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β → γ},   Function.Injective2 f → ∀ (a : α), Function.Injective (f a)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
As a map from the right argument to a unary function, `f` is injective.
-/
theorem right' (hf : Injective2 f) [Nonempty α] : Function.Injective fun b a ↦ f a b :=
  fun _ _ h ↦
    let ⟨a⟩ := ‹Nonempty α›
    hf.right a <| (congr_fun h a :)
/-
**Function.Injective2.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective2`。
形式化陈述：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b
₁ = b₂
参数：hf : Injective2 f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h ↦ hf h, fun ⟨h1, h2⟩ ↦ congr_arg₂ f h1 h2⟩

end Injective2

section Sometimes

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
/-
**Function.sometimes** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：sometimes {α β} [Nonempty β] (f : α -> β) : β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sometimes f` evaluates to some value of `f`, if it exists. This function is esp
ecially
interesting in the case where `α` is a proposition, in which case `f` is necessa
rily a
constant function, so that `sometimes f = f a` for all `a`.
-/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
  open scoped Classical in
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›
/-
**Function.sometimes_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：sometimes_eq {p : Prop} {α} [Nonempty α] (f : p -> α) (a : p) : sometimes 
f = f a
参数：f : p -> α；a : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
  dif_pos ⟨a⟩
/-
**Function.sometimes_spec** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：sometimes_spec {p : Prop} {α} [Nonempty α] (P : α -> Prop) (f : p -> α) (a
 : p) (h : P (f a)) : P (sometimes f)
参数：P : α -> Prop；f : p -> α；a : p；h : P (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.sometimes_eq`：sometimes_eq {p : Prop} {α} [Nonempty α] (f : p -
> α) (a : p) : sometimes f = f a
-/
theorem sometimes_spec {p : Prop} {α} [Nonempty α] (P : α → Prop) (f : p → α) (a : p)
    (h : P (f a)) : P (sometimes f) := by
  rwa [sometimes_eq]

end Sometimes

end Function

variable {α β : Sort*}

/-- A relation `r : α → β → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`. -/
/-
**forall_existsUnique_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：forall_existsUnique_iff {r : α -> β -> Prop} : (forall a, exists! b, r a b
) ↔ exists f : α -> β, forall {a b}, r a b ↔ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A relation `r : α → β → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`.
-/
lemma forall_existsUnique_iff {r : α → β → Prop} :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → β, ∀ {a b}, r a b ↔ f a = b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · refine ⟨fun a ↦ (h a).choose, fun hr ↦ ?_, fun h' ↦ h' ▸ ?_⟩
    exacts [((h _).choose_spec.2 _ hr).symm, (h _).choose_spec.1]
  · rintro ⟨f, hf⟩
    simp [hf]

/-- A relation `r : α → β → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`. -/
/-
**forall_existsUnique_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：forall_existsUnique_iff' {r : α -> β -> Prop} : (forall a, exists! b, r a 
b) ↔ exists f : α -> β, r = (f · = ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A relation `r : α → β → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`.
-/
lemma forall_existsUnique_iff' {r : α → β → Prop} :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → β, r = (f · = ·) := by
  simp [forall_existsUnique_iff, funext_iff]

/-- A symmetric relation `r : α → α → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some involutive function `f`. -/
/-
**Std.Symm.forall_existsUnique_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Std.Symm`。
形式化陈述：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Symm r],   (∀ (a : α), ∃! b, r a 
b) ↔ ∃ f, Function.Involutive f ∧ r = fun x1 x2 => f x1 = x2
参数：∀ (a : α), ∃! b, r a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `forall_existsUnique_iff'`：forall_existsUnique_iff' {r : α -> β -> Prop} 
: (forall a, exists! b, r a b) ↔ exists f : α -> β, r = (f · = ·)
· 使用引理 `Function.symm_apply_eq_iff`：symm_apply_eq_iff {α : Sort*} {f : α -> α} :
 Std.Symm (f · = ·) ↔ Involutive f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A symmetric relation `r : α → α → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some involutive function `f`.
-/
protected lemma Std.Symm.forall_existsUnique_iff' {r : α → α → Prop} [Std.Symm r] :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → α, Involutive f ∧ r = (f · = ·) := by
  refine ⟨fun h ↦ ?_, fun ⟨f, _, hf⟩ ↦ forall_existsUnique_iff'.2 ⟨f, hf⟩⟩
  rcases forall_existsUnique_iff'.1 h with ⟨f, rfl : r = _⟩
  exact ⟨f, symm_apply_eq_iff.1 ‹_›, rfl⟩

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff' := Std.Symm.forall_existsUnique_iff'

/-- A symmetric relation `r : α → α → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some involutive function `f`. -/
/-
**Std.Symm.forall_existsUnique_iff** 是 Mathlib 中的一个定理，位于命名空间 `Std.Symm`。
形式化陈述：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Symm r],   (∀ (a : α), ∃! b, r a 
b) ↔ ∃ f, Function.Involutive f ∧ ∀ {a b : α}, r a b ↔ f a = b
参数：∀ (a : α), ∃! b, r a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A symmetric relation `r : α → α → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some involutive function `f`.
-/
protected lemma Std.Symm.forall_existsUnique_iff {r : α → α → Prop} [Std.Symm r] :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → α, Involutive f ∧ ∀ {a b}, r a b ↔ f a = b := by
  simp [Std.Symm.forall_existsUnique_iff', funext_iff]

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff := Std.Symm.forall_existsUnique_iff

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
/-
**Set.piecewise** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.piecewise {α : Type u} {β : α -> Sort v} (s : Set α) (f g : forall i, 
β i) [forall j, Decidable (j in s)] : forall i, β i
参数：s : Set α；f g : forall i, β i；j in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its
 complement.
-/
def Set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀ i, β i)
    [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i ↦ if i ∈ s then f i else g i


/-! ### Bijectivity of `Eq.rec`, `Eq.mp`, `Eq.mpr`, and `cast` -/

/-
**eq_rec_on_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {C : α → Sort u_3} {a a' : α} (h : a = a'), Function.Bije
ctive fun x => h ▸ x
参数：h : a = a'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Bijectivity of `Eq.rec`, `Eq.mp`, `Eq.mpr`, and `cast`
-/
theorem eq_rec_on_bijective {C : α → Sort*} :
    ∀ {a a' : α} (h : a = a'), Function.Bijective (@Eq.ndrec _ _ C · _ h)
  | _, _, rfl => ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩
/-
**eq_mp_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h)
参数：h : α = β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h) := by
  -- TODO: mathlib3 uses `eq_rec_on_bijective`, difference in elaboration here
  -- due to `@[macro_inline]` possibly?
  cases h
  exact ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩
/-
**eq_mpr_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h
)
参数：h : α = β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h) := by
  cases h
  exact ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩
/-
**cast_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h)
参数：h : α = β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h) := by
  cases h
  exact ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

/-! Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway. -/

@[simp]
/-
**eq_rec_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_rec_inj {a a' : α} (h : a = a') {C : α -> Type*} (x y : C a) : (Eq.ndre
c x h : C a') = Eq.ndrec y h ↔ x = y
参数：h : a = a'；x y : C a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `eq_rec_on_bijective`：∀ {α : Sort u_1} {C : α → Sort u_3} {a a' : α} (h :
 a = a'), Function.Bijective fun x => h ▸ x

--- 原说明 ---
Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `s
imp`, and
is trivial anyway.
-/
theorem eq_rec_inj {a a' : α} (h : a = a') {C : α → Type*} (x y : C a) :
    (Eq.ndrec x h : C a') = Eq.ndrec y h ↔ x = y :=
  (eq_rec_on_bijective h).injective.eq_iff

@[simp]
/-
**cast_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cast_inj {α β : Type u} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = 
y
参数：h : α = β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `cast_bijective`：cast_bijective {α β : Sort _} (h : α = β) : Function.Bij
ective (cast h)
-/
theorem cast_inj {α β : Type u} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
  (cast_bijective h).injective.eq_iff
/-
**Function.LeftInverse.eq_rec_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.eq_rec_eq {γ : β -> Sort v} {f : α -> β} {g : β -> α}
 (h : Function.LeftInverse g f) (C : forall a : α, γ (f a)) (a : α) : -- TODO: m
athlib3 uses `(congr_arg f (h a)).rec (C (g (f a)))` for LHS @Eq.rec β (f (g (f 
a))) (fun x _ => γ x) (C (g (f a))) (f a) (congr_arg f (h a)) = C a
参数：h : Function.LeftInverse g f；C : forall a : α, γ (f a)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `eqRec_heq`：∀ {α : Sort u} {φ : α → Sort v} {a a' : α} (h : a = a') (p : 
φ a), Eq.recOn h p ≍ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Function.LeftInverse.eq_rec_eq {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).rec (C (g (f a)))` for LHS
    @Eq.rec β (f (g (f a))) (fun x _ ↦ γ x) (C (g (f a))) (f a) (congr_arg f (h a)) = C a :=
  eq_of_heq <| (eqRec_heq _ _).trans <| by rw [h]
/-
**Function.LeftInverse.eq_rec_on_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.eq_rec_on_eq {γ : β -> Sort v} {f : α -> β} {g : β ->
 α} (h : Function.LeftInverse g f) (C : forall a : α, γ (f a)) (a : α) : -- TODO
: mathlib3 uses `(congr_arg f (h a)).recOn (C (g (f a)))` for LHS @Eq.recOn β (f
 (g (f a))) (fun x _ => γ x) (f a) (congr_arg f (h a)) (C (g (f a))) = C a
参数：h : Function.LeftInverse g f；C : forall a : α, γ (f a)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.eq_rec_eq`：Function.LeftInverse.eq_rec_eq {γ : β ->
 Sort v} {f : α -> β} {g : β -> α} (h : Function.LeftInverse g f) (C : forall a 
: α, γ (f a)) (a : α…
-/
theorem Function.LeftInverse.eq_rec_on_eq {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).recOn (C (g (f a)))` for LHS
    @Eq.recOn β (f (g (f a))) (fun x _ ↦ γ x) (f a) (congr_arg f (h a)) (C (g (f a))) = C a :=
  h.eq_rec_eq _ _
/-
**Function.LeftInverse.cast_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.cast_eq {γ : β -> Sort v} {f : α -> β} {g : β -> α} (
h : Function.LeftInverse g f) (C : forall a : α, γ (f a)) (a : α) : cast (congr_
arg (fun a => γ (f a)) (h a)) (C (g (f a))) = C a
参数：h : Function.LeftInverse g f；C : forall a : α, γ (f a)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.LeftInverse.cast_eq {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    cast (congr_arg (fun a ↦ γ (f a)) (h a)) (C (g (f a))) = C a := by
  grind

/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
/-
**Set.SeparatesPoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.SeparatesPoints {α β : Type*} (A : Set (α -> β)) : Prop
参数：A : Set (α -> β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of functions "separates points"
if for each pair of distinct points there is a function taking different values 
on them.
-/
def Set.SeparatesPoints {α β : Type*} (A : Set (α → β)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y → ∃ f ∈ A, f x ≠ f y
/-
**Set.separatesPoints_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.separatesPoints_mono {α β : Type*} {A B : Set (α -> β)} (hAB : A subse
teq B) (hA : Set.SeparatesPoints A) : Set.SeparatesPoints B
参数：α -> β；hAB : A subseteq B；hA : Set.SeparatesPoints A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.separatesPoints_mono {α β : Type*} {A B : Set (α → β)} (hAB : A ⊆ B)
    (hA : Set.SeparatesPoints A) : Set.SeparatesPoints B := by
  intro x y hne
  obtain ⟨f, hfA, hne'⟩ := hA hne
  exact ⟨f, hAB hfA, hne'⟩
/-
**InvImage.equivalence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InvImage.equivalence {α : Sort u} {β : Sort v} (r : β -> β -> Prop) (f : α
 -> β) (h : Equivalence r) : Equivalence (InvImage r f)
参数：r : β -> β -> Prop；f : α -> β；h : Equivalence r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
-/
theorem InvImage.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
    (h : Equivalence r) : Equivalence (InvImage r f) :=
  ⟨fun _ ↦ h.1 _, h.symm, h.trans⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*} {r : α → β → Prop} {x : α × β} [Decidable (r x.1 x.2)] :
    Decidable (uncurry r x) :=
  ‹Decidable _›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*} {r : α × β → Prop} {a : α} {b : β} [Decidable (r (a, b))] :
    Decidable (curry r a b) :=
  ‹Decidable _›

namespace Pi

variable {ι : Type*}

/-
**Pi.map_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：Pi.map_id {f : α -> C} [HasProduct f] : Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ 
f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_id {α : ι → Type*} : Pi.map (fun i => @id (α i)) = id := rfl
/-
**Pi.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_3} {α : ι → Type u_4}, (Pi.map fun i a => a) = fun x => x
参数：Pi.map fun i a => a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_id' {α : ι → Type*} : Pi.map (fun i (a : α i) => a) = fun x ↦ x := rfl
/-
**Pi.map_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：Pi.map_comp_map {f g h : α -> C} [HasProduct f] [HasProduct g] [HasProduct
 h] (q : forall (a : α), f a ⟶ g a) (q' : forall (a : α), g a ⟶ h a) : Pi.map q 
≫ Pi.map q' = Pi.map (fun a => q a ≫ q' a)
参数：q : forall (a : α), f a ⟶ g a；q' : forall (a : α), g a ⟶ h a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_map {α β γ : ι → Type*} (f : ∀ i, α i → β i) (g : ∀ i, β i → γ i) :
    Pi.map g ∘ Pi.map f = Pi.map fun i => g i ∘ f i :=
  rfl

end Pi

