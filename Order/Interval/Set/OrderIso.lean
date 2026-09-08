/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Hom.Set

/-!
# Lemmas about images of intervals under order isomorphisms.
-/

@[expose] public section

open Set

namespace OrderIso

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[to_dual (attr := simp)]
/-
**OrderIso.preimage_Iic** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b = Iic (e.symm b)
参数：e : α ≃o β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b = Iic (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[to_dual (attr := simp)]
/-
**OrderIso.preimage_Iio** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b = Iio (e.symm b)
参数：e : α ≃o β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b = Iio (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp, to_dual self]
/-
**OrderIso.preimage_Icc** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a b = Icc (e.symm a) (e.sy
mm b)
参数：e : α ≃o β；a b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.preimage_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder 
α] [inst_1 : Preorder β] (e : α ≃o β) (b : β),   ⇑e ⁻¹' Set.Ici b = Set.Ici (e.s
ymm b)
· 使用定理 `OrderIso.preimage_Iic`：preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b =
 Iic (e.symm b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]

@[to_dual (attr := simp) (reorder := a b)]
/-
**OrderIso.preimage_Ico** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' Ico a b = Ico (e.symm a) (e.sy
mm b)
参数：e : α ≃o β；a b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.preimage_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder 
α] [inst_1 : Preorder β] (e : α ≃o β) (b : β),   ⇑e ⁻¹' Set.Ici b = Set.Ici (e.s
ymm b)
· 使用定理 `OrderIso.preimage_Iio`：preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b =
 Iio (e.symm b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]

@[simp, to_dual self]
/-
**OrderIso.preimage_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' Ioo a b = Ioo (e.symm a) (e.sy
mm b)
参数：e : α ≃o β；a b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.preimage_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder 
α] [inst_1 : Preorder β] (e : α ≃o β) (b : β),   ⇑e ⁻¹' Set.Ioi b = Set.Ioi (e.s
ymm b)
· 使用定理 `OrderIso.preimage_Iio`：preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b =
 Iio (e.symm b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]
/-
**OrderIso.image_Iic** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e a)
参数：e : α ≃o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `OrderIso.preimage_Iic`：preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b =
 Iic (e.symm b)
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
-/
theorem image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e a) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Iic, e.symm_symm]

@[to_dual (attr := simp)]
/-
**OrderIso.image_Iio** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e a)
参数：e : α ≃o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `OrderIso.preimage_Iio`：preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b =
 Iio (e.symm b)
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
-/
theorem image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e a) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Iio, e.symm_symm]

@[simp, to_dual self]
/-
**OrderIso.image_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Ioo (e a) (e b)
参数：e : α ≃o β；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `OrderIso.preimage_Ioo`：preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' Ioo a
 b = Ioo (e.symm a) (e.symm b)
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
-/
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Ioo (e a) (e b) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Ioo, e.symm_symm]

@[to_dual (attr := simp) (reorder := a b)]
/-
**OrderIso.image_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Ioc (e a) (e b)
参数：e : α ≃o β；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `OrderIso.preimage_Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder 
α] [inst_1 : Preorder β] (e : α ≃o β) (b a : β),   ⇑e ⁻¹' Set.Ioc b a = Set.Ioc 
(e.symm b) …
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
-/
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Ioc (e a) (e b) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Ioc, e.symm_symm]

@[simp, to_dual self]
/-
**OrderIso.image_Icc** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Icc (e a) (e b)
参数：e : α ≃o β；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `OrderIso.preimage_Icc`：preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a
 b = Icc (e.symm a) (e.symm b)
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
-/
theorem image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Icc (e a) (e b) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Icc, e.symm_symm]

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
@[to_dual
/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/]
/-
**OrderIso.IicTop** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：IicTop {α : Type*} [Preorder α] [OrderTop α] : Iic (⊤ : α) ≃o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IicTop {α : Type*} [Preorder α] [OrderTop α] : Iic (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (· ∈ Iic (⊤ : α)) fun _ => le_top with
    map_rel_iff' := @fun x y => by rfl }

end OrderIso

