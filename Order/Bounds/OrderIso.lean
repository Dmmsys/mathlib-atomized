/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.Hom.Set

/-!
# Order isomorphisms and bounds.
-/

public section

open Set

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β)

/-
**OrderIso.upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：upperBounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Monotone.image_upperBounds_subset_upperBounds_image`：image_upperBounds_s
ubset_upperBounds_image : f '' upperBounds s subseteq upperBounds (f '' s)
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
theorem upperBounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s :=
  Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image
/-
**OrderIso.lowerBounds_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：lowerBounds_image {s : Set α} : lowerBounds (f '' s) = f '' lowerBounds s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.upperBounds_image`：upperBounds_image {s : Set α} : upperBounds 
(f '' s) = f '' upperBounds s
-/
theorem lowerBounds_image {s : Set α} : lowerBounds (f '' s) = f '' lowerBounds s :=
  @upperBounds_image αᵒᵈ βᵒᵈ _ _ f.dual _

@[simp]
/-
**OrderIso.isLUB_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x ↔ IsLUB s (f.symm x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.of_image`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: Preorder β] {f : α → β},   (∀ {x y : α}, f y ≤ f x ↔ y ≤ x) → ∀ {s : Set α} {x
 : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `OrderIso.symm_image_image`：symm_image_image (e : α ≃o β) (s : Set α) : e
.symm '' e '' s = s
-/
theorem isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x ↔ IsLUB s (f.symm x) :=
  ⟨fun h => IsLUB.of_image (by simp) ((f.apply_symm_apply x).symm ▸ h), fun h =>
    (IsLUB.of_image (by simp)) <| (f.symm_image_image s).symm ▸ h⟩
/-
**OrderIso.isLUB_image'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s) (f x) ↔ IsLUB s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.isLUB_image`：isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x
 ↔ IsLUB s (f.symm x)
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s) (f x) ↔ IsLUB s x := by
  rw [isLUB_image, f.symm_apply_apply]

@[simp]
/-
**OrderIso.isGLB_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isGLB_image {s : Set α} {x : β} : IsGLB (f '' s) x ↔ IsGLB s (f.symm x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isLUB_image`：isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x
 ↔ IsLUB s (f.symm x)
-/
theorem isGLB_image {s : Set α} {x : β} : IsGLB (f '' s) x ↔ IsGLB s (f.symm x) :=
  f.dual.isLUB_image
/-
**OrderIso.isGLB_image'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isGLB_image' {s : Set α} {x : α} : IsGLB (f '' s) (f x) ↔ IsGLB s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isLUB_image'`：isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s)
 (f x) ↔ IsLUB s x
-/
theorem isGLB_image' {s : Set α} {x : α} : IsGLB (f '' s) (f x) ↔ IsGLB s x :=
  f.dual.isLUB_image'

@[simp]
/-
**OrderIso.isLUB_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `OrderIso.isLUB_image`：isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x
 ↔ IsLUB s (f.symm x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x) := by
  rw [← f.symm_symm, ← image_eq_preimage_symm, isLUB_image]
/-
**OrderIso.isLUB_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isLUB_preimage' {s : Set β} {x : β} : IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s
 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.isLUB_preimage`：isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻
¹' s) x ↔ IsLUB s (f x)
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLUB_preimage' {s : Set β} {x : β} : IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s x := by
  rw [isLUB_preimage, f.apply_symm_apply]

@[simp]
/-
**OrderIso.isGLB_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isGLB_preimage {s : Set β} {x : α} : IsGLB (f ⁻¹' s) x ↔ IsGLB s (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isLUB_preimage`：isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻
¹' s) x ↔ IsLUB s (f x)
-/
theorem isGLB_preimage {s : Set β} {x : α} : IsGLB (f ⁻¹' s) x ↔ IsGLB s (f x) :=
  f.dual.isLUB_preimage
/-
**OrderIso.isGLB_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isGLB_preimage' {s : Set β} {x : β} : IsGLB (f ⁻¹' s) (f.symm x) ↔ IsGLB s
 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isLUB_preimage'`：isLUB_preimage' {s : Set β} {x : β} : IsLUB (f
 ⁻¹' s) (f.symm x) ↔ IsLUB s x
-/
theorem isGLB_preimage' {s : Set β} {x : β} : IsGLB (f ⁻¹' s) (f.symm x) ↔ IsGLB s x :=
  f.dual.isLUB_preimage'

end OrderIso

