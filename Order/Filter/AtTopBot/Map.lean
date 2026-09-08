/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Set.OrderIso

/-!
# Map and comap of `Filter.atTop` and `Filter.atBot`
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace OrderIso

open Filter

variable [Preorder α] [Preorder β]

@[simp]
/-
**OrderIso.comap_atTop** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：comap_atTop (e : α ≃o β) : comap e atTop = atTop
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sor
t u_5} [inst : InfSet α] {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α),
 ⨅ x, g (f x) = ⨅ y…
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `OrderIso.preimage_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder 
α] [inst_1 : Preorder β] (e : α ≃o β) (b : β),   ⇑e ⁻¹' Set.Ici b = Set.Ici (e.s
ymm b)
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_atTop (e : α ≃o β) : comap e atTop = atTop := by
  simp [atTop, ← e.surjective.iInf_comp]

@[simp]
/-
**OrderIso.comap_atBot** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：comap_atBot (e : α ≃o β) : comap e atBot = atBot
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.comap_atTop`：comap_atTop (e : α ≃o β) : comap e atTop = atTop
-/
theorem comap_atBot (e : α ≃o β) : comap e atBot = atBot :=
  e.dual.comap_atTop

@[simp]
/-
**OrderIso.map_atTop** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = atTop
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.comap_atTop`：comap_atTop (e : α ≃o β) : comap e atTop = atTop
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
-/
theorem map_atTop (e : α ≃o β) : map (e : α → β) atTop = atTop := by
  rw [← e.comap_atTop, map_comap_of_surjective e.surjective]

@[simp]
/-
**OrderIso.map_atBot** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_atBot (e : α ≃o β) : map (e : α -> β) atBot = atBot
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
-/
theorem map_atBot (e : α ≃o β) : map (e : α → β) atBot = atBot :=
  e.dual.map_atTop
/-
**OrderIso.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：tendsto_atTop (e : α ≃o β) : Tendsto e atTop atTop
参数：e : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
-/
theorem tendsto_atTop (e : α ≃o β) : Tendsto e atTop atTop :=
  e.map_atTop.le
/-
**OrderIso.tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：tendsto_atBot (e : α ≃o β) : Tendsto e atBot atBot
参数：e : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `OrderIso.map_atBot`：map_atBot (e : α ≃o β) : map (e : α -> β) atBot = at
Bot
-/
theorem tendsto_atBot (e : α ≃o β) : Tendsto e atBot atBot :=
  e.map_atBot.le

@[simp]
/-
**OrderIso.tendsto_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：tendsto_atTop_iff {l : Filter γ} {f : γ -> α} (e : α ≃o β) : Tendsto (fun 
x => e (f x)) l atTop ↔ Tendsto f l atTop
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.comap_atTop`：comap_atTop (e : α ≃o β) : comap e atTop = atTop
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_atTop_iff {l : Filter γ} {f : γ → α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atTop ↔ Tendsto f l atTop := by
  rw [← e.comap_atTop, tendsto_comap_iff, Function.comp_def]

@[simp]
/-
**OrderIso.tendsto_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：tendsto_atBot_iff {l : Filter γ} {f : γ -> α} (e : α ≃o β) : Tendsto (fun 
x => e (f x)) l atBot ↔ Tendsto f l atBot
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.tendsto_atTop_iff`：tendsto_atTop_iff {l : Filter γ} {f : γ -> α
} (e : α ≃o β) : Tendsto (fun x => e (f x)) l atTop ↔ Tendsto f l atTop
-/
theorem tendsto_atBot_iff {l : Filter γ} {f : γ → α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atBot ↔ Tendsto f l atBot :=
  e.dual.tendsto_atTop_iff

end OrderIso

