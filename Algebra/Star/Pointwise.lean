/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise star operation on sets

This file defines the star operation pointwise on sets and provides the basic API.
Besides basic facts about how the star operation acts on sets (e.g., `(s ∩ t)⋆ = s⋆ ∩ t⋆`),
if `s t : Set α`, then under suitable assumption on `α`, it is shown

* `(s + t)⋆ = s⋆ + t⋆`
* `(s * t)⋆ = t⋆ + s⋆`
* `(s⁻¹)⋆ = (s⋆)⁻¹`
-/

@[expose] public section

namespace Set

open scoped Pointwise

local postfix:max "⋆" => star

variable {α : Type*} {s t : Set α} {a : α}

/-- The set `(star s : Set α)` is defined as `{x | star x ∈ s}` in the scope `Pointwise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`, see
`Set.image_star`. -/
@[instance_reducible]
/-
**Set.star** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → [Star α] → Star (Set α)
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `(star s : Set α)` is defined as `{x | star x ∈ s}` in the scope `Pointw
ise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`,
 see
`Set.image_star`.
-/
protected def star [Star α] : Star (Set α) := ⟨preimage Star.star⟩

scoped[Pointwise] attribute [instance] Set.star

@[simp]
/-
**Set.star_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_empty [Star α] : (∅ : Set α)⋆ = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_empty [Star α] : (∅ : Set α)⋆ = ∅ := rfl

@[simp]
/-
**Set.star_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_univ [Star α] : (univ : Set α)⋆ = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_univ [Star α] : (univ : Set α)⋆ = univ := rfl

@[simp]
/-
**Set.nonempty_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.nonempty_preimage`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β}, Function.Surjective f → ∀ {s : Set β}, (f ⁻¹' s).Nonempty ↔ s.Nonemp
ty
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
-/
theorem nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty :=
  star_involutive.surjective.nonempty_preimage
/-
**Set.Nonempty.star** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} [inst : InvolutiveStar α] {s : Set α}, s.Nonempty → (star
 s).Nonempty
参数：star s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_star`：nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Non
empty ↔ s.Nonempty
-/
theorem Nonempty.star [InvolutiveStar α] {s : Set α} (h : s.Nonempty) : s⋆.Nonempty :=
  nonempty_star.2 h

@[simp, push]
/-
**Set.mem_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_star [Star α] : a in s⋆ ↔ a⋆ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_star [Star α] : a ∈ s⋆ ↔ a⋆ ∈ s := Iff.rfl
/-
**Set.star_mem_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_mem_star [InvolutiveStar α] : a⋆ in s⋆ ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem star_mem_star [InvolutiveStar α] : a⋆ ∈ s⋆ ↔ a ∈ s := by simp only [mem_star, star_star]

@[simp]
/-
**Set.star_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_preimage [Star α] : Star.star ⁻¹' s = s⋆
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_preimage [Star α] : Star.star ⁻¹' s = s⋆ := rfl

@[simp]
/-
**Set.image_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_star [InvolutiveStar α] : Star.star '' s = s⋆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_star [InvolutiveStar α] : Star.star '' s = s⋆ := by
  simp only [← star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]

@[simp]
/-
**Set.inter_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_star [Star α] : (s inter t)⋆ = s⋆ inter t⋆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
-/
theorem inter_star [Star α] : (s ∩ t)⋆ = s⋆ ∩ t⋆ := preimage_inter

@[simp]
/-
**Set.union_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_star [Star α] : (s union t)⋆ = s⋆ union t⋆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_union`：preimage_union {s t : Set β} : f ⁻¹' (s union t) = f
 ⁻¹' s union f ⁻¹' t
-/
theorem union_star [Star α] : (s ∪ t)⋆ = s⋆ ∪ t⋆ := preimage_union

@[simp]
/-
**Set.iInter_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_star {ι : Sort*} [Star α] (s : ι -> Set α) : (⋂ i, s i)⋆ = ⋂ i, (s 
i)⋆
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
-/
theorem iInter_star {ι : Sort*} [Star α] (s : ι → Set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ :=
  preimage_iInter

@[simp]
/-
**Set.iUnion_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_star {ι : Sort*} [Star α] (s : ι -> Set α) : (⋃ i, s i)⋆ = ⋃ i, (s 
i)⋆
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
-/
theorem iUnion_star {ι : Sort*} [Star α] (s : ι → Set α) : (⋃ i, s i)⋆ = ⋃ i, (s i)⋆ :=
  preimage_iUnion

@[simp]
/-
**Set.compl_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_star [Star α] : sᶜ⋆ = s⋆ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
-/
theorem compl_star [Star α] : sᶜ⋆ = s⋆ᶜ := preimage_compl

@[simp]
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar α] : InvolutiveStar (Set α) where
  star_involutive s := by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

@[simp]
/-
**Set.star_subset_star** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_subset_star [InvolutiveStar α] {s t : Set α} : s⋆ subseteq t⋆ ↔ s sub
seteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.preimage_subset_preimage_iff`：∀ {α : Type u_1} {β : 
Type u_2} {f : α → β} {s t : Set β}, Function.Surjective f → (f ⁻¹' s ⊆ f ⁻¹' t 
↔ s ⊆ t)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem star_subset_star [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t⋆ ↔ s ⊆ t :=
  Equiv.Perm.star.surjective.preimage_subset_preimage_iff
/-
**Set.star_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_subset [InvolutiveStar α] {s t : Set α} : s⋆ subseteq t ↔ s subseteq 
t⋆
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.star_subset_star`：star_subset_star [InvolutiveStar α] {s t : Set α} 
: s⋆ subseteq t⋆ ↔ s subseteq t
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem star_subset [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t ↔ s ⊆ t⋆ := by
  rw [← star_subset_star, star_star]
/-
**Set.Finite.star** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : InvolutiveStar α] {s : Set α}, s.Finite → (star s
).Finite
参数：star s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
-/
theorem Finite.star [InvolutiveStar α] {s : Set α} (hs : s.Finite) : s⋆.Finite :=
  hs.preimage star_injective.injOn
/-
**Set.star_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：star_singleton {β : Type*} [InvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {
x⋆}
参数：x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_star`：mem_star [Star α] : a in s⋆ ↔ a⋆ in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `star_eq_iff_star_eq`：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : 
star r = s ↔ star s = r
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem star_singleton {β : Type*} [InvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {x⋆} := by
  ext1 y
  rw [mem_star, mem_singleton_iff, mem_singleton_iff, star_eq_iff_star_eq, eq_comm]
/-
**Set.star_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : StarMul α] (s t : Set α), star (
s * t) = star t * star s
参数：s t : Set α；s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem star_mul [Mul α] [StarMul α] (s t : Set α) : (s * t)⋆ = t⋆ * s⋆ := by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]
/-
**Set.star_add** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoid α] [inst_1 : StarAddMonoid α] (s t : Se
t α), star (s + t) = star s + star t
参数：s t : Set α；s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem star_add [AddMonoid α] [StarAddMonoid α] (s t : Set α) : (s + t)⋆ = s⋆ + t⋆ := by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]

@[simp]
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star α] [TrivialStar α] : TrivialStar (Set α) where
  star_trivial s := by
    rw [← star_preimage]
    ext1
    simp [star_trivial]
/-
**Set.star_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : StarMul α] (s : Set α), star s
⁻¹ = (star s)⁻¹
参数：s : Set α；star s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem star_inv [Group α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [mem_star, mem_inv, star_inv]
/-
**Set.star_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] [inst_1 : StarMul α] (s : Set α)
, star s⁻¹ = (star s)⁻¹
参数：s : Set α；star s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv₀`：star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = 
(star x)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem star_inv' [GroupWithZero α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [mem_star, mem_inv, star_inv₀]

end Set

@[simp]
/-
**StarMemClass.star_coe_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StarMemClass.star_coe_eq {S α : Type*} [InvolutiveStar α] [SetLike S α] [S
tarMemClass S α] (s : S) : star (s : Set α) = s
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `star_mem_iff`：star_mem_iff {S : Type*} [SetLike S R] [InvolutiveStar R] 
[StarMemClass S R] {s : S} {x : R} : star x in s ↔ x in s
-/
lemma StarMemClass.star_coe_eq {S α : Type*} [InvolutiveStar α] [SetLike S α]
    [StarMemClass S α] (s : S) : star (s : Set α) = s := by
  ext
  simpa using star_mem_iff
