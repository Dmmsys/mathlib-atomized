/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-! # Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

public section

open Function

namespace Set

variable {α : Type*} {s t u : Set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
/-
**Set.inclusion** 是 Mathlib 中的一个缩写定义，位于命名空间 `Set`。
形式化陈述：inclusion (h : s subseteq t) : s -> t
参数：h : s subseteq t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`inclusion` is the "identity" function between two subsets `s` and `t`, where `s
 ⊆ t`
-/
abbrev inclusion (h : s ⊆ t) : s → t := fun x ↦ ⟨x, h x.prop⟩
/-
**Set.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_self (x : s) : inclusion Subset.rfl x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem inclusion_self (x : s) : inclusion Subset.rfl x = x :=
  rfl
/-
**Set.inclusion_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_eq_id (h : s subseteq s) : inclusion h = id
参数：h : s subseteq s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_eq_id (h : s ⊆ s) : inclusion h = id :=
  rfl
/-
**Set.inclusion_eq_subtype_map** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_eq_subtype_map (h : s subseteq t) : inclusion h = Subtype.map id
 h
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_eq_subtype_map (h : s ⊆ t) : inclusion h = Subtype.map id h :=
  rfl

@[simp]
/-
**Set.inclusion_mk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_mk {h : s subseteq t} (a : α) (ha : a in s) : inclusion h ⟨a, ha
⟩ = ⟨a, h ha⟩
参数：a : α；ha : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl
/-
**Set.inclusion_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_right (h : s subseteq t) (x : t) (m : (x : α) in s) : inclusion 
h ⟨x, m⟩ = x
参数：h : s subseteq t；x : t；m : (x : α) in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x :=
  rfl

@[simp]
/-
**Set.inclusion_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_inclusion (hst : s subseteq t) (htu : t subseteq u) (x : s) : in
clusion htu (inclusion hst x) = inclusion (hst.trans htu) x
参数：hst : s subseteq t；htu : t subseteq u；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x :=
  rfl

@[simp]
/-
**Set.inclusion_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_comp_inclusion {α} {s t u : Set α} (hst : s subseteq t) (htu : t
 subseteq u) : inclusion htu ∘ inclusion hst = inclusion (hst.trans htu)
参数：hst : s subseteq t；htu : t subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inclusion_inclusion`：inclusion_inclusion (hst : s subseteq t) (htu :
 t subseteq u) (x : s) : inclusion htu (inclusion hst x) = inclusion (hst.trans 
htu) x
-/
theorem inclusion_comp_inclusion {α} {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
  funext (inclusion_inclusion hst htu)

@[simp]
/-
**Set.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_inclusion (h : s subseteq t) (x : s) : (inclusion h x : α) = (x : α)
参数：h : s subseteq t；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl
/-
**Set.val_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：val_comp_inclusion (h : s subseteq t) : Subtype.val ∘ inclusion h = Subtyp
e.val
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_comp_inclusion (h : s ⊆ t) : Subtype.val ∘ inclusion h = Subtype.val :=
  rfl
/-
**Set.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_injective (h : s subseteq t) : (inclusion h).Injective
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem inclusion_injective (h : s ⊆ t) : (inclusion h).Injective :=
  Subtype.map_injective h injective_id
/-
**Set.inclusion_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_inj (h : s subseteq t) {x y : s} : inclusion h x = inclusion h y
 ↔ x = y
参数：h : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem inclusion_inj (h : s ⊆ t) {x y : s} : inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff
/-
**Set.eq_of_inclusion_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_inclusion_surjective {s t : Set α} {h : s subseteq t} (h_surj : Func
tion.Surjective (inclusion h)) : s = t
参数：h_surj : Function.Surjective (inclusion h)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t}
    (h_surj : Function.Surjective (inclusion h)) : s = t :=
  h.antisymm fun x hx ↦ by grind [h_surj ⟨x, hx⟩]
/-
**Set.inclusion_le_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_le_inclusion [LE α] {s t : Set α} (h : s subseteq t) {x y : s} :
 inclusion h x <= inclusion h y ↔ x <= y
参数：h : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inclusion_le_inclusion [LE α] {s t : Set α} (h : s ⊆ t) {x y : s} :
    inclusion h x ≤ inclusion h y ↔ x ≤ y := .rfl
/-
**Set.inclusion_lt_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inclusion_lt_inclusion [LT α] {s t : Set α} (h : s subseteq t) {x y : s} :
 inclusion h x < inclusion h y ↔ x < y
参数：h : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inclusion_lt_inclusion [LT α] {s t : Set α} (h : s ⊆ t) {x y : s} :
    inclusion h x < inclusion h y ↔ x < y := .rfl

end Set

