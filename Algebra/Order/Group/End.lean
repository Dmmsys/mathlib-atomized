/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Data.FunLike.IsApply

/-!
# Relation isomorphisms form a group

This file contains `Monoid` instances for `RelHom` and `OrderHom`, where multiplication is
given by composition. Likewise there is a `Group` instance for `RelIso`. Because `OrderIso`
is an abbreviation for `RelIso`, there is no need for an additional instance.

## TODO

+ Rename the `mul_def`/`one_def` lemmas to `mul_eq_comp`/`one_eq_id`.
+ Use the `IsMulApplyEqComp` and `IsOneApplyEqSelf` classes for `RelHom` and `RelIso`.
-/

@[expose] public section

assert_not_exists MulAction MonoidWithZero

variable {α : Type*} {r : α → α → Prop}

namespace RelHom

/-
**RelHom.** 是 Mathlib 中的一个实例，位于命名空间 `RelHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (r →r r) where
  one := .id r
  mul := .comp
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
/-
**RelHom.one_def** 是 Mathlib 中的一个引理，位于命名空间 `RelHom`。
形式化陈述：one_def : (1 : r ->r r) = .id r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : r →r r) = .id r := rfl
/-
**RelHom.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `RelHom`。
形式化陈述：mul_def (f g : r ->r r) : (f * g) = f.comp g
参数：f g : r ->r r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : r →r r) : (f * g) = f.comp g := rfl
/-
**RelHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_one : ⇑(1 : r →r r) = id := rfl
/-
**RelHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (f g : r →r r), ⇑(f * g) = ⇑f ∘ ⇑g
参数：f g : r →r r；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mul (f g : r →r r) : ⇑(f * g) = f ∘ g := rfl
/-
**RelHom.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelHom`。
形式化陈述：one_apply (a : α) : (1 : r ->r r) a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply (a : α) : (1 : r →r r) a = a := rfl
/-
**RelHom.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelHom`。
形式化陈述：mul_apply (e₁ e₂ : r ->r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x)
参数：e₁ e₂ : r ->r r；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply (e₁ e₂ : r →r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelHom

namespace RelEmbedding

/-
**RelEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (r ↪r r) where
  one := .refl r
  mul f g := g.trans f
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
/-
**RelEmbedding.one_def** 是 Mathlib 中的一个引理，位于命名空间 `RelEmbedding`。
形式化陈述：one_def : (1 : r ↪r r) = .refl r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : r ↪r r) = .refl r := rfl
/-
**RelEmbedding.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `RelEmbedding`。
形式化陈述：mul_def (f g : r ↪r r) : (f * g) = g.trans f
参数：f g : r ↪r r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : r ↪r r) : (f * g) = g.trans f := rfl
/-
**RelEmbedding.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_one : ⇑(1 : r ↪r r) = id := rfl
/-
**RelEmbedding.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (f g : r ↪r r), ⇑(f * g) = ⇑f ∘ ⇑g
参数：f g : r ↪r r；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mul (f g : r ↪r r) : ⇑(f * g) = f ∘ g := rfl
/-
**RelEmbedding.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelEmbedding`。
形式化陈述：one_apply (a : α) : (1 : r ↪r r) a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply (a : α) : (1 : r ↪r r) a = a := rfl
/-
**RelEmbedding.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelEmbedding`。
形式化陈述：mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x)
参数：e₁ e₂ : r ↪r r；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelEmbedding

namespace RelIso

/-
**RelIso.** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (r ≃r r) where
  one := .refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := .symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.symm_apply_apply
/-
**RelIso.one_def** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：one_def : (1 : r ≃r r) = .refl r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : r ≃r r) = .refl r := rfl
/-
**RelIso.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：mul_def (f g : r ≃r r) : (f * g) = g.trans f
参数：f g : r ≃r r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : r ≃r r) : (f * g) = g.trans f := rfl
/-
**RelIso.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_one : ((1 : r ≃r r) : α → α) = id := rfl
/-
**RelIso.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (e₁ e₂ : r ≃r r), ⇑(e₁ * e₂) = ⇑e₁ ∘ ⇑
e₂
参数：e₁ e₂ : r ≃r r；e₁ * e₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ((e₁ * e₂) : α → α) = e₁ ∘ e₂ := rfl
/-
**RelIso.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：one_apply (x : α) : (1 : r ≃r r) x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply (x : α) : (1 : r ≃r r) x = x := rfl
/-
**RelIso.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x)
参数：e₁ e₂ : r ≃r r；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp]
/-
**RelIso.inv_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x
参数：e : r ≃r r；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.symm_apply_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : α), e.symm (e x) = x
-/
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

@[simp]
/-
**RelIso.apply_inv_self** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x
参数：e : r ≃r r；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
-/
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

end RelIso

namespace OrderHom

variable [Preorder α]

/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (α →o α) where mul f g := f.comp g
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (α →o α) where one := .id
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMulApplyEqComp (α →o α) α where mul_apply_eq_comp _ _ _ := rfl
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOneApplyEqSelf (α →o α) α where one_apply_eq_self _ := rfl
/-
**OrderHom.mul_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `OrderHom`。
形式化陈述：mul_eq_comp (f g : α ->o α) : (f * g : α ->o α) = f.comp g
参数：f g : α ->o α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_eq_comp (f g : α →o α) : (f * g : α →o α) = f.comp g := rfl
/-
**OrderHom.one_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `OrderHom`。
形式化陈述：one_eq_id : (1 : α ->o α) = .id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_eq_id : (1 : α →o α) = .id := rfl
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (α →o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom

