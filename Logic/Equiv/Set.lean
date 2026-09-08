/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences and sets

In this file we provide lemmas linking equivalences to sets.

Some notable definitions are:

* `Equiv.ofInjective`: an injective function is (noncomputably) equivalent to its range.
* `Equiv.setCongr`: two equal sets are equivalent as types.
* `Equiv.Set.union`: a disjoint union of sets is equivalent to their `Sum`.

This file is separate from `Equiv/Basic` such that we do not require the full lattice structure
on sets before defining what an equivalence is.
-/

@[expose] public section


open Function Set

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace EquivLike

@[simp]
/-
**EquivLike.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：range_eq_univ {α : Type*} {β : Type*} {E : Type*} [EquivLike E α β] (e : E
) : range e = univ
参数：e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem range_eq_univ {α : Type*} {β : Type*} {E : Type*} [EquivLike E α β] (e : E) :
    range e = univ :=
  eq_univ_of_forall (EquivLike.toEquiv e).surjective

end EquivLike

namespace Equiv
variable {α β : Type*}

/-
**Equiv.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：range_eq_univ (e : α ≃ β) : range e = univ
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
-/
theorem range_eq_univ (e : α ≃ β) : range e = univ := EquivLike.range_eq_univ e
/-
**Equiv.image_symm_eq_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_symm_eq_preimage (e : α ≃ β) (s : Set β) : e.symm '' s = e ⁻¹' s
参数：e : α ≃ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.mem_image_iff_of_inverse`：mem_image_iff_of_inverse {f : α -> β} {g :
 β -> α} {b : β} {s : Set α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : b 
in f '' s ↔ g b in…
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
lemma image_symm_eq_preimage (e : α ≃ β) (s : Set β) : e.symm '' s = e ⁻¹' s := by
  ext; exact mem_image_iff_of_inverse e.right_inv e.left_inv
/-
**Equiv.image_eq_preimage_symm** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_eq_preimage_symm (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s
参数：e : α ≃ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma image_eq_preimage_symm (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.symm.image_symm_eq_preimage _

@[simp 1001]
/-
**Equiv._root_.Set.mem_image_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.mem_image_equiv {α β} {S : Set α} {f : α ≃ β} {x : β} :
    x ∈ f '' S ↔ f.symm x ∈ S :=
  Set.ext_iff.mp (image_eq_preimage_symm ..) x

-- Increased priority so this fires before `image_subset_iff`
@[simp high]
/-
**Equiv.symm_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s : Set α) (t : Set β), ⇑e.sy
mm '' t ⊆ s ↔ t ⊆ ⇑e '' s
参数：e : α ≃ β；s : Set α；t : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem symm_image_subset {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    e.symm '' t ⊆ s ↔ t ⊆ e '' s := by rw [image_subset_iff, image_eq_preimage_symm]

-- Increased priority so this fires before `image_subset_iff`
@[simp high]
/-
**Equiv.subset_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s : Set α) (t : Set β), s ⊆ ⇑
e.symm '' t ↔ ⇑e '' s ⊆ t
参数：e : α ≃ β；s : Set α；t : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_image_subset`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s 
: Set α) (t : Set β), ⇑e.symm '' t ⊆ s ↔ t ⊆ ⇑e '' s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
-/
protected theorem subset_symm_image {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    s ⊆ e.symm '' t ↔ e '' s ⊆ t :=
  calc
    s ⊆ e.symm '' t ↔ e.symm.symm '' s ⊆ t := by rw [e.symm.symm_image_subset]
    _ ↔ e '' s ⊆ t := by rw [e.symm_symm]

@[simp]
/-
**Equiv.symm_image_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' e '' s = s
参数：e : α ≃ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.image_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), g '' f '' s = s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.leftInverse_symm`：leftInverse_symm (f : α ≃ β) : LeftInverse f.sym
m f
-/
theorem symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' e '' s = s :=
  e.leftInverse_symm.image_image s
/-
**Equiv.eq_image_iff_symm_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) : t =
 e '' s ↔ e.symm '' t = s
参数：e : α ≃ β；s : Set α；t : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    t = e '' s ↔ e.symm '' t = s :=
  (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp]
/-
**Equiv.image_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' e.symm '' s = s
参数：e : α ≃ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp]
/-
**Equiv.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' e ⁻¹' s = s
参数：e : α ≃ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' e ⁻¹' s = s :=
  e.surjective.image_preimage s

@[simp]
/-
**Equiv.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' e '' s = s
参数：e : α ≃ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' e '' s = s :=
  e.injective.preimage_image s
/-
**Equiv.image_compl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (f : α ≃ β) (s : Set α), ⇑f '' sᶜ = (⇑f ''
 s)ᶜ
参数：f : α ≃ β；s : Set α；⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_compl_eq`：image_compl_eq {f : α -> β} {s : Set α} (H : Bijecti
ve f) : f '' sᶜ = (f '' s)ᶜ
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem image_compl {α β} (f : Equiv α β) (s : Set α) : f '' sᶜ = (f '' s)ᶜ :=
  image_compl_eq f.bijective

@[simp]
/-
**Equiv.symm_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s 
= s
参数：e : α ≃ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.preimage_preimage`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), f ⁻¹' g ⁻¹' s
 = s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
-/
theorem symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s :=
  e.rightInverse_symm.preimage_preimage s

@[simp]
/-
**Equiv.preimage_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' e.symm ⁻¹' s 
= s
参数：e : α ≃ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.preimage_preimage`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), f ⁻¹' g ⁻¹' s
 = s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.leftInverse_symm`：leftInverse_symm (f : α ≃ β) : LeftInverse f.sym
m f
-/
theorem preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' e.symm ⁻¹' s = s :=
  e.leftInverse_symm.preimage_preimage s
/-
**Equiv.preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s subseteq e ⁻¹' t
 ↔ s subseteq t
参数：e : α ≃ β；s t : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.preimage_subset_preimage_iff`：∀ {α : Type u_1} {β : 
Type u_2} {f : α → β} {s t : Set β}, Function.Surjective f → (f ⁻¹' s ⊆ f ⁻¹' t 
↔ s ⊆ t)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s ⊆ e ⁻¹' t ↔ s ⊆ t :=
  e.surjective.preimage_subset_preimage_iff
/-
**Equiv.image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s subseteq e '' t ↔ s 
subseteq t
参数：e : α ≃ β；s t : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s ⊆ e '' t ↔ s ⊆ t :=
  image_subset_image_iff e.injective

@[simp]
/-
**Equiv.image_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t
参数：e : α ≃ β；s t : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t :=
  image_eq_image e.injective
/-
**Equiv.preimage_eq_iff_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' 
t
参数：e : α ≃ β；s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {f : α -> β} (hf 
: Bijective f) {s t} : f ⁻¹' s = t ↔ s = f '' t
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' t :=
  Set.preimage_eq_iff_eq_image e.bijective
/-
**Equiv.eq_preimage_iff_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = 
t
参数：e : α ≃ β；s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {f : α -> β} (hf 
: Bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = t :=
  Set.eq_preimage_iff_image_eq e.bijective
/-
**Equiv.setOfPred_apply_symm_eq_image_setOfPred** 是 Mathlib 中的一个引理，位于命名空间 `Equiv
`。
形式化陈述：setOfPred_apply_symm_eq_image_setOfPred {α β} (e : α ≃ β) (p : α -> Prop) 
: {b | p (e.symm b)} = e '' {a | p a}
参数：e : α ≃ β；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Set.preimage_ofPred_eq`：preimage_ofPred_eq {p : α -> Prop} {f : β -> α} 
: f ⁻¹' { a | p a } = { a | p (f a) }
-/
lemma setOfPred_apply_symm_eq_image_setOfPred {α β} (e : α ≃ β) (p : α → Prop) :
    {b | p (e.symm b)} = e '' {a | p a} := by
  rw [Equiv.image_eq_preimage_symm, preimage_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_apply_symm_eq_image_setOf := setOfPred_apply_symm_eq_image_setOfPred

@[simp]
/-
**Equiv.prod_assoc_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} : Equiv.pr
odAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.prodAssoc_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u_11) 
(p : (α × β) × γ), (Equiv.prodAssoc α β γ) p = (p.1.1, p.1.2, p.2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  ext
  simp [and_assoc]

@[simp]
/-
**Equiv.prod_assoc_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prod_assoc_symm_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} : (Eq
uiv.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.prodAssoc_symm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u
_11) (p : α × β × γ), (Equiv.prodAssoc α β γ).symm p = ((p.1, p.2.1), p.2.2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_assoc_symm_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  ext
  simp [and_assoc]

-- `@[simp]` doesn't like these lemmas, as it uses `Set.image_congr'` to turn `Equiv.prodAssoc`
-- into a lambda expression and then unfold it.
/-
**Equiv.prod_assoc_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prod_assoc_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} : Equiv.prodA
ssoc α β γ '' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Equiv.prod_assoc_symm_preimage`：prod_assoc_symm_preimage {α β γ} {s : Se
t α} {t : Set β} {u : Set γ} : (Equiv.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = 
s ×ˢ t ×ˢ u
-/
theorem prod_assoc_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ '' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  simpa only [Equiv.image_eq_preimage_symm] using prod_assoc_symm_preimage
/-
**Equiv.prod_assoc_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：prod_assoc_symm_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} : (Equiv
.prodAssoc α β γ).symm '' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Equiv.prod_assoc_preimage`：prod_assoc_preimage {α β γ} {s : Set α} {t : 
Set β} {u : Set γ} : Equiv.prodAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u
-/
theorem prod_assoc_symm_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm '' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  simpa only [Equiv.image_eq_preimage_symm] using! prod_assoc_preimage

/-- A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`. -/
/-
**Equiv.setProdEquivSigma** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：setProdEquivSigma {α β : Type*} (s : Set (α × β)) : s ≃ Σ x : α, { y : β |
 (x, y) in s } where toFun x
参数：s : Set (α × β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`.
-/
def setProdEquivSigma {α β : Type*} (s : Set (α × β)) :
    s ≃ Σ x : α, { y : β | (x, y) ∈ s } where
  toFun x := ⟨x.1.1, x.1.2, by simp⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩

/-- The subtypes corresponding to equal sets are equivalent. -/
@[simps! apply symm_apply]
/-
**Equiv.setCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：setCongr {α : Type*} {s t : Set α} (h : s = t) : s ≃ t
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtypes corresponding to equal sets are equivalent.
-/
def setCongr {α : Type*} {s t : Set α} (h : s = t) : s ≃ t :=
  subtypeEquivProp <| h ▸ rfl

-- We could construct this using `Equiv.Set.image e s e.injective`,
-- but this definition provides an explicit inverse.
/-- A set is equivalent to its image under an equivalence.
-/
@[simps]
/-
**Equiv.image** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：image {α β : Type*} (e : α ≃ β) (s : Set α) : s ≃ e '' s where toFun x
参数：e : α ≃ β；s : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A set is equivalent to its image under an equivalence.
-/
def image {α β : Type*} (e : α ≃ β) (s : Set α) :
    s ≃ e '' s where
  toFun x := ⟨e x.1, by simp⟩
  invFun y :=
    ⟨e.symm y.1, by
      rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
      simpa using m⟩
  left_inv x := by simp
  right_inv y := by simp

section order

variable {α β : Type*} [Preorder α] [Preorder β] {e : α ≃ β} (s : Set α)

/-
**Equiv.image_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_monotone (hs : Monotone e) : Monotone (e.image s)
参数：hs : Monotone e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
-/
lemma image_monotone (hs : Monotone e) : Monotone (e.image s) :=
  hs.comp (Subtype.mono_coe _)
/-
**Equiv.image_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_antitone (hs : Antitone e) : Antitone (e.image s)
参数：hs : Antitone e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
-/
lemma image_antitone (hs : Antitone e) : Antitone (e.image s) :=
  hs.comp_monotone (Subtype.mono_coe _)
/-
**Equiv.image_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_strictMono (hs : StrictMono e) : StrictMono (e.image s)
参数：hs : StrictMono e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
-/
lemma image_strictMono (hs : StrictMono e) : StrictMono (e.image s) :=
  hs.comp (Subtype.strictMono_coe _)
/-
**Equiv.image_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_strictAnti (hs : StrictAnti e) : StrictAnti (e.image s)
参数：hs : StrictAnti e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.comp_strictMono`：StrictAnti.comp_strictMono (hg : StrictAnti 
g) (hf : StrictMono f) : StrictAnti (g ∘ f)
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
-/
lemma image_strictAnti (hs : StrictAnti e) : StrictAnti (e.image s) :=
  hs.comp_strictMono (Subtype.strictMono_coe _)

end order

namespace Set

/-- `univ α` is equivalent to `α`. -/
@[simps apply symm_apply]
/-
**Equiv.Set.univ** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：(α : Type u_3) → ↑Set.univ ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
`univ α` is equivalent to `α`.
-/
protected def univ (α) : @univ α ≃ α :=
  ⟨Subtype.val, fun a => ⟨a, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩

/-- An empty set is equivalent to the `Empty` type. -/
/-
**Equiv.Set.empty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：(α : Type u_3) → ↑∅ ≃ Empty
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅

--- 原说明 ---
An empty set is equivalent to the `Empty` type.
-/
protected def empty (α) : (∅ : Set α) ≃ Empty :=
  equivEmpty _

/-- An empty set is equivalent to a `PEmpty` type. -/
/-
**Equiv.Set.pempty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：(α : Type u_3) → ↑∅ ≃ PEmpty.{u_4}
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅

--- 原说明 ---
An empty set is equivalent to a `PEmpty` type.
-/
protected def pempty (α) : (∅ : Set α) ≃ PEmpty :=
  equivPEmpty _

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
/-
**Equiv.Set.union'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} →   {s t : Set α} → (p : α → Prop) → [DecidablePred p] → (∀
 x ∈ s, p x) → (∀ x ∈ t, ¬p x) → ↑(s ∪ t) ≃ ↑s ⊕ ↑t
参数：p : α → Prop；∀ x ∈ s, p x；∀ x ∈ t, ¬p x；s ∪ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equi
valent to
`s ⊕ t`.
-/
protected def union' {α} {s t : Set α} (p : α → Prop) [DecidablePred p] (hs : ∀ x ∈ s, p x)
    (ht : ∀ x ∈ t, ¬p x) : (s ∪ t : Set α) ≃ s ⊕ t where
  toFun x :=
    if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩
    else Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩
  invFun o :=
    match o with
    | Sum.inl x => ⟨x, Or.inl x.2⟩
    | Sum.inr x => ⟨x, Or.inr x.2⟩
  left_inv := fun ⟨x, h'⟩ => by by_cases h : p x <;> simp [h]
  right_inv o := by
    rcases o with (⟨x, h⟩ | ⟨x, h⟩) <;> [simp [hs _ h]; simp [ht _ h]]

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
/-
**Equiv.Set.union** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {s t : Set α} → [DecidablePred fun x => x ∈ s] → Disjoint
 s t → ↑(s ∪ t) ≃ ↑s ⊕ ↑t
参数：s ∪ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`.
-/
protected def union {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t) :
    (s ∪ t : Set α) ≃ s ⊕ t :=
  Set.union' (fun x => x ∈ s) (fun _ => id) fun _ xt xs => Set.disjoint_left.mp H xs xt
/-
**Equiv.Set.union_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：union_apply_left {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Di
sjoint s t) {a : (s union t : Set α)} (ha : ↑a in s) : Equiv.Set.union H a = Sum
.inl ⟨a, ha⟩
参数：H : Disjoint s t；s union t : Set α；ha : ↑a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem union_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    {a : (s ∪ t : Set α)} (ha : ↑a ∈ s) : Equiv.Set.union H a = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha
/-
**Equiv.Set.union_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：union_apply_right {α} {s t : Set α} [DecidablePred fun x => x in s] (H : D
isjoint s t) {a : (s union t : Set α)} (ha : ↑a in t) : Equiv.Set.union H a = Su
m.inr ⟨a, ha⟩
参数：H : Disjoint s t；s union t : Set α；ha : ↑a in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
-/
theorem union_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    {a : (s ∪ t : Set α)} (ha : ↑a ∈ t) : Equiv.Set.union H a = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => Set.disjoint_left.mp H h ha

@[simp]
/-
**Equiv.Set.union_symm_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x in s] (H
 : Disjoint s t) (a : s) : (Equiv.Set.union H).symm (Sum.inl a) = ⟨a, by simp⟩
参数：H : Disjoint s t；a : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    (a : s) : (Equiv.Set.union H).symm (Sum.inl a) = ⟨a, by simp⟩ :=
  rfl

@[simp]
/-
**Equiv.Set.union_symm_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x in s] (
H : Disjoint s t) (a : t) : (Equiv.Set.union H).symm (Sum.inr a) = ⟨a, by simp⟩
参数：H : Disjoint s t；a : t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    (a : t) : (Equiv.Set.union H).symm (Sum.inr a) = ⟨a, by simp⟩ :=
  rfl

/-- A singleton set is equivalent to a `PUnit` type. -/
/-
**Equiv.Set.singleton** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → (a : α) → ↑{a} ≃ PUnit.{u}
参数：a : α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
A singleton set is equivalent to a `PUnit` type.
-/
protected def singleton {α} (a : α) : ({a} : Set α) ≃ PUnit.{u} :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    subst x
    rfl, fun ⟨⟩ => rfl⟩
/-
**Equiv.Set._root_.Equiv.strictMono_setCongr** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Se
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.strictMono_setCongr {α : Type*} [Preorder α] {S T : Set α} (h : S = T) :
    StrictMono (setCongr h) := fun _ _ ↦ id

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Equiv.strictMono_setCongr := Equiv.strictMono_setCongr

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ PUnit`. -/
/-
**Equiv.Set.insert** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u} → {s : Set α} → [DecidablePred fun x => x ∈ s] → {a : α} → a 
∉ s → ↑(insert a s) ≃ ↑s ⊕ PUnit.{u + 1}
参数：insert a s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ PUnit`.
-/
protected def insert {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    (insert a s : Set α) ≃ s ⊕ PUnit.{u + 1} :=
  calc
    (insert a s : Set α) ≃ ↥(s ∪ {a}) := Equiv.setCongr (by simp)
    _ ≃ s ⊕ ({a} : Set α) := Equiv.Set.union <| by simpa
    _ ≃ s ⊕ PUnit.{u + 1} := sumCongr (Equiv.refl _) (Equiv.Set.singleton _)

@[simp]
/-
**Equiv.Set.insert_symm_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α}
 (H : a ∉ s) (b : s) : (Equiv.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩
参数：· in s；H : a ∉ s；b : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s)
    (b : s) : (Equiv.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩ :=
  rfl

@[simp]
/-
**Equiv.Set.insert_symm_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α}
 (H : a ∉ s) (b : PUnit.{u + 1}) : (Equiv.Set.insert H).symm (Sum.inr b) = ⟨a, O
r.inl rfl⟩
参数：· in s；H : a ∉ s；b : PUnit.{u + 1}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s)
    (b : PUnit.{u + 1}) : (Equiv.Set.insert H).symm (Sum.inr b) = ⟨a, Or.inl rfl⟩ :=
  rfl

@[simp]
/-
**Equiv.Set.insert_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H 
: a ∉ s) : Equiv.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit
参数：· in s；H : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    Equiv.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit :=
  (Equiv.Set.insert H).eq_symm_apply.1 rfl

@[simp]
/-
**Equiv.Set.insert_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H
 : a ∉ s) (b : s) : Equiv.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b
参数：· in s；H : a ∉ s；b : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
    Equiv.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b :=
  (Equiv.Set.insert H).eq_symm_apply.1 rfl

/-- If `s : Set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`.

See also `Equiv.sumCompl`. -/
/-
**Equiv.Set.sumCompl** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → (s : Set α) → [DecidablePred fun x => x ∈ s] → ↑s ⊕ ↑sᶜ ≃
 α
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s : Set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent t
o `α`.

See also `Equiv.sumCompl`.
-/
protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : s ⊕ (sᶜ : Set α) ≃ α :=
  Equiv.sumCompl (· ∈ s)

@[simp]
/-
**Equiv.Set.sumCompl_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· in s)] (x : 
s) : Equiv.Set.sumCompl s (Sum.inl x) = x
参数：s : Set α；· in s；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumCompl s (Sum.inl x) = x :=
  rfl

@[simp]
/-
**Equiv.Set.sumCompl_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· in s)] (x : 
(sᶜ : Set α)) : Equiv.Set.sumCompl s (Sum.inr x) = x
参数：s : Set α；· in s；x : (sᶜ : Set α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
    Equiv.Set.sumCompl s (Sum.inr x) = x :=
  rfl
/-
**Equiv.Set.sumCompl_symm_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· in s
)] {x : α} (hx : x in s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩
参数：· in s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.sumCompl_symm_apply_of_pos`：sumCompl_symm_apply_of_pos {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : p a) : (sumCompl p).symm a = Sum.inl ⟨a,
 h⟩
-/
theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∈ s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ :=
  sumCompl_symm_apply_of_pos hx
/-
**Equiv.Set.sumCompl_symm_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· i
n s)] {x : α} (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩
参数：· in s；hx : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.sumCompl_symm_apply_of_neg`：sumCompl_symm_apply_of_neg {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : ¬p a) : (sumCompl p).symm a = Sum.inr ⟨a
, h⟩
-/
theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ :=
  sumCompl_symm_apply_of_neg hx

@[simp]
/-
**Equiv.Set.sumCompl_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· in s)] (x : 
s) : (Equiv.Set.sumCompl s).symm x = Sum.inl x
参数：· in s；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.sumCompl_symm_apply_pos`：sumCompl_symm_apply_pos {α} {p : α -> Pro
p} [DecidablePred p] (x : {x // p x}) : (sumCompl p).symm x = Sum.inl x
-/
theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] (x : s) :
    (Equiv.Set.sumCompl s).symm x = Sum.inl x :=
  sumCompl_symm_apply_pos x

@[simp]
/-
**Equiv.Set.sumCompl_symm_apply_compl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· in s)]
 (x : (sᶜ : Set α)) : (Equiv.Set.sumCompl s).symm x = Sum.inr x
参数：· in s；x : (sᶜ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.sumCompl_symm_apply_neg`：sumCompl_symm_apply_neg {α} {p : α -> Pro
p} [DecidablePred p] (x : {x // ¬ p x}) : (sumCompl p).symm x = Sum.inr x
-/
theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
    (x : (sᶜ : Set α)) : (Equiv.Set.sumCompl s).symm x = Sum.inr x :=
  sumCompl_symm_apply_neg x

/-- `sumDiffSubset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
/-
**Equiv.Set.sumDiffSubset** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {s t : Set α} → s ⊆ t → [DecidablePred fun x => x ∈ s] → 
↑s ⊕ ↑(t \ s) ≃ ↑t
参数：t \ s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`sumDiffSubset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets.
-/
protected def sumDiffSubset {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] :
    s ⊕ (t \ s : Set α) ≃ t :=
  calc
    s ⊕ (t \ s : Set α) ≃ (s ∪ t \ s : Set α) :=
      (Equiv.Set.union disjoint_sdiff_self_right).symm
    _ ≃ t := Equiv.setCongr (by simp [union_sdiff_self, union_eq_self_of_subset_left h])

@[simp]
/-
**Equiv.Set.sumDiffSubset_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumDiffSubset_apply_inl {α} {s t : Set α} (h : s subseteq t) [DecidablePre
d (· in s)] (x : s) : Equiv.Set.sumDiffSubset h (Sum.inl x) = inclusion h x
参数：h : s subseteq t；· in s；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumDiffSubset_apply_inl {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumDiffSubset h (Sum.inl x) = inclusion h x :=
  rfl

@[simp]
/-
**Equiv.Set.sumDiffSubset_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：sumDiffSubset_apply_inr {α} {s t : Set α} (h : s subseteq t) [DecidablePre
d (· in s)] (x : (t \ s : Set α)) : Equiv.Set.sumDiffSubset h (Sum.inr x) = incl
usion sdiff_subset x
参数：h : s subseteq t；· in s；x : (t \ s : Set α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumDiffSubset_apply_inr {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    (x : (t \ s : Set α)) : Equiv.Set.sumDiffSubset h (Sum.inr x) = inclusion sdiff_subset x :=
  rfl
/-
**Equiv.Set.sumDiffSubset_symm_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set
`。
形式化陈述：sumDiffSubset_symm_apply_of_mem {α} {s t : Set α} (h : s subseteq t) [Deci
dablePred (· in s)] {x : t} (hx : x.1 in s) : (Equiv.Set.sumDiffSubset h).symm x
 = Sum.inl ⟨x, hx⟩
参数：h : s subseteq t；· in s；hx : x.1 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumDiffSubset_symm_apply_of_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    {x : t} (hx : x.1 ∈ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inl ⟨x, hx⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inl, Set.inclusion_mk]
/-
**Equiv.Set.sumDiffSubset_symm_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Set`。
形式化陈述：sumDiffSubset_symm_apply_of_notMem {α} {s t : Set α} (h : s subseteq t) [D
ecidablePred (· in s)] {x : t} (hx : x.1 ∉ s) : (Equiv.Set.sumDiffSubset h).symm
 x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩
参数：h : s subseteq t；· in s；hx : x.1 ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumDiffSubset_symm_apply_of_notMem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    {x : t} (hx : x.1 ∉ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inr]

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
/-
**Equiv.Set.unionSumInter** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u} → (s t : Set α) → [DecidablePred fun x => x ∈ s] → ↑(s ∪ t) ⊕
 ↑(s ∩ t) ≃ ↑s ⊕ ↑t
参数：s t : Set α；s ∪ t；s ∩ t。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` i
s equivalent
to `s ⊕ t`.
-/
protected def unionSumInter {α : Type u} (s t : Set α) [DecidablePred (· ∈ s)] :
    (s ∪ t : Set α) ⊕ (s ∩ t : Set α) ≃ s ⊕ t :=
  calc
    (s ∪ t : Set α) ⊕ (s ∩ t : Set α)
      ≃ (s ∪ t \ s : Set α) ⊕ (s ∩ t : Set α) := by rw [union_sdiff_self]
    _ ≃ (s ⊕ (t \ s : Set α)) ⊕ (s ∩ t : Set α) :=
      sumCongr (Set.union disjoint_sdiff_self_right) (Equiv.refl _)
    _ ≃ s ⊕ ((t \ s : Set α) ⊕ (s ∩ t : Set α)) := sumAssoc _ _ _
    _ ≃ s ⊕ (t \ s ∪ s ∩ t : Set α) :=
      sumCongr (Equiv.refl _)
        (by
          refine (Set.union' (· ∉ s) ?_ ?_).symm
          exacts [fun x hx => hx.2, fun x hx => not_not_intro hx.1])
    _ ≃ s ⊕ t := by
      { rw [(_ : t \ s ∪ s ∩ t = t)]
        rw [union_comm, inter_comm, inter_union_sdiff] }

set_option backward.isDefEq.respectTransparency false in
/-- Given an equivalence `e₀` between sets `s : Set α` and `t : Set β`, the set of equivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set of equivalences
between `sᶜ` and `tᶜ`. -/
/-
**Equiv.Set.compl** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u} →   {β : Type v} →     {s : Set α} →       {t : Set β} →     
    [DecidablePred fun x => x ∈ s] →           [DecidablePred fun x => x ∈ t] → 
(e₀ : ↑s ≃ ↑t) → { e // ∀ (x : ↑s), e ↑x = ↑(e₀ x) } ≃ (↑sᶜ ≃ ↑tᶜ)
参数：e₀ : ↑s ≃ ↑t；x : ↑s；e₀ x；↑sᶜ ≃ ↑tᶜ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an equivalence `e₀` between sets `s : Set α` and `t : Set β`, the set of e
quivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set
 of equivalences
between `sᶜ` and `tᶜ`.
-/
protected def compl {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] (e₀ : s ≃ t) :
    { e : α ≃ β // ∀ x : s, e x = e₀ x } ≃ ((sᶜ : Set α) ≃ (tᶜ : Set β)) where
  toFun e :=
    subtypeEquiv e fun _ =>
      not_congr <|
        Iff.symm <|
          MapsTo.mem_iff (mapsTo_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.mapsTo_compl
              (surjOn_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.surjective, e.2⟩)
              e.1.injective)
  invFun e₁ :=
    Subtype.mk
      (calc
        α ≃ s ⊕ (sᶜ : Set α) := (Set.sumCompl s).symm
        _ ≃ t ⊕ (tᶜ : Set β) := e₀.sumCongr e₁
        _ ≃ β := Set.sumCompl t)
      fun x => by
      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
        Set.sumCompl_symm_apply, Trans.trans]
  left_inv e := by
    ext x
    by_cases hx : x ∈ s
    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
        trans_apply, Set.sumCompl_apply_inl, Trans.trans]
    · simp only [Set.sumCompl_symm_apply_of_notMem hx, Sum.map_inr, subtypeEquiv_apply,
        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Trans.trans]
  right_inv e :=
    Equiv.ext fun x => by
      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
        sumCongr_apply, Equiv.coe_trans, Subtype.coe_eta, Trans.trans,
        Set.sumCompl_symm_apply_compl]

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
/-
**Equiv.Set.prod** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {β : Type u_4} → (s : Set α) → (t : Set β) → ↑(s ×ˢ t) ≃ 
↑s × ↑t
参数：s : Set α；t : Set β；s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set product of two sets is equivalent to the type product of their coercions
 to types.
-/
protected def prod {α β} (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ s × t :=
  @subtypeProdEquivProd α β (· ∈ s) (· ∈ t)

/-- The set `Set.pi Set.univ s` is equivalent to `Π a, s a`. -/
@[simps]
/-
**Equiv.Set.univPi** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {β : α → Type u_4} → (s : (a : α) → Set (β a)) → ↑(Set.un
iv.pi s) ≃ ((a : α) → ↑(s a))
参数：s : (a : α) → Set (β a)；Set.univ.pi s；(a : α) → ↑(s a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `Set.pi Set.univ s` is equivalent to `Π a, s a`.
-/
protected def univPi {α : Type*} {β : α → Type*} (s : ∀ a, Set (β a)) :
    pi univ s ≃ ∀ a, s a where
  toFun f a := ⟨(f : ∀ a, β a) a, f.2 a (mem_univ a)⟩
  invFun f := ⟨fun a => f a, fun a _ => (f a).2⟩

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
/-
**Equiv.Set.imageOfInjOn** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {β : Type u_4} → (f : α → β) → (s : Set α) → Set.InjOn f 
s → ↑s ≃ ↑(f '' s)
参数：f : α → β；s : Set α；f '' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`.
-/
protected noncomputable def imageOfInjOn {α β} (f : α → β) (s : Set α) (H : InjOn f s) :
    s ≃ f '' s :=
  ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p =>
    ⟨Classical.choose p.2, (Classical.choose_spec p.2).1⟩, fun ⟨_, h⟩ =>
    Subtype.ext
      (H (Classical.choose_spec (mem_image_of_mem f h)).1 h
        (Classical.choose_spec (mem_image_of_mem f h)).2),
    fun ⟨_, h⟩ => Subtype.ext (Classical.choose_spec h).2⟩

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simps! apply]
/-
**Equiv.Set.image** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {β : Type u_4} → (f : α → β) → (s : Set α) → Function.Inj
ective f → ↑s ≃ ↑(f '' s)
参数：f : α → β；s : Set α；f '' s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
If `f` is an injective function, then `s` is equivalent to `f '' s`.
-/
protected noncomputable def image {α β} (f : α → β) (s : Set α) (H : Injective f) : s ≃ f '' s :=
  Equiv.Set.imageOfInjOn f s H.injOn

@[simp]
/-
**Equiv.Set.image_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (f : α → β) (s : Set α) (H : Function.Inje
ctive f) (x : α) (h : f x ∈ f '' s),   (Equiv.Set.image f s H).symm ⟨f x, h⟩ = ⟨
x, ⋯⟩
参数：f : α → β；s : Set α；H : Function.Injective f；x : α；h : f x ∈ f '' s；Equiv.Set
.image f s H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
protected theorem image_symm_apply {α β} (f : α → β) (s : Set α) (H : Injective f) (x : α)
    (h : f x ∈ f '' s) : (Set.image f s H).symm ⟨f x, h⟩ = ⟨x, H.mem_set_image.1 h⟩ :=
  (Equiv.symm_apply_eq _).2 rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Set.image_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：image_symm_preimage {α β} {f : α -> β} (hf : Injective f) (u s : Set α) : 
(fun x => (Set.image f s hf).symm x : f '' s -> α) ⁻¹' u = Subtype.val ⁻¹' f '' 
u
参数：hf : Injective f；u s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Equiv.Set.image_symm_apply`：∀ {α : Type u_3} {β : Type u_4} (f : α → β) 
(s : Set α) (H : Function.Injective f) (x : α) (h : f x ∈ f '' s),   (Equiv.Set.
image f s H).sym…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_symm_preimage {α β} {f : α → β} (hf : Injective f) (u s : Set α) :
    (fun x => (Set.image f s hf).symm x : f '' s → α) ⁻¹' u = Subtype.val ⁻¹' f '' u := by
  ext ⟨b, a, has, rfl⟩
  simp [hf.eq_iff]

/-- If `α` is equivalent to `β`, then `Set α` is equivalent to `Set β`. -/
@[simps]
/-
**Equiv.Set.congr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → {β : Type u_4} → α ≃ β → Set α ≃ Set β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s

--- 原说明 ---
If `α` is equivalent to `β`, then `Set α` is equivalent to `Set β`.
-/
protected def congr {α β : Type*} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
/-
**Equiv.Set.sep** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u} → (s : Set α) → (t : α → Prop) → ↑{x | x ∈ s ∧ t x} ≃ ↑{x | t
 ↑x}
参数：s : Set α；t : α → Prop。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`.
-/
protected def sep {α : Type u} (s : Set α) (t : α → Prop) :
    ({ x ∈ s | t x } : Set α) ≃ { x : s | t x } :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) t).symm

/-- The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `Set S`. -/
/-
**Equiv.Set.powerset** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：{α : Type u_3} → (S : Set α) → ↑(𝒫 S) ≃ Set ↑S
参数：S : Set α；𝒫 S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `Set S`.
-/
protected def powerset {α} (S : Set α) :
    𝒫 S ≃ Set S where
  toFun := fun x : 𝒫 S => Subtype.val ⁻¹' (x : Set α)
  invFun := fun x : Set S => ⟨Subtype.val '' x, by rintro _ ⟨a : S, _, rfl⟩; exact a.2⟩
  left_inv x := by ext y; exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩
  right_inv x := by ext; simp

/-- If `s` is a set in `range f`,
then its image under `rangeSplitting f` is in bijection (via `f`) with `s`.
-/
@[simps]
/-
**Equiv.Set.rangeSplittingImageEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：rangeSplittingImageEquiv {α β : Type*} (f : α -> β) (s : Set (range f)) : 
rangeSplitting f '' s ≃ s where toFun x
参数：f : α -> β；s : Set (range f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a set in `range f`,
then its image under `rangeSplitting f` is in bijection (via `f`) with `s`.
-/
noncomputable def rangeSplittingImageEquiv {α β : Type*} (f : α → β) (s : Set (range f)) :
    rangeSplitting f '' s ≃ s where
  toFun x :=
    ⟨⟨f x, by simp⟩, by
      rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
      simpa [apply_rangeSplitting f] using m⟩
  invFun x := ⟨rangeSplitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩
  left_inv x := by
    rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
    simp [apply_rangeSplitting f]
  right_inv x := by simp [apply_rangeSplitting f]

/-- Equivalence between the range of `Sum.inl : α → α ⊕ β` and `α`. -/
@[simps symm_apply_coe]
/-
**Equiv.Set.rangeInl** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：rangeInl (α β : Type*) : Set.range (Sum.inl : α -> α oplus β) ≃ α where to
Fun | ⟨.inl x, _⟩ => x | ⟨.inr _, h⟩ => False.elim by rcases h with ⟨x, h'⟩; cas
es h' invFun x
参数：α β : Type*。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the range of `Sum.inl : α → α ⊕ β` and `α`.
-/
def rangeInl (α β : Type*) : Set.range (Sum.inl : α → α ⊕ β) ≃ α where
  toFun
  | ⟨.inl x, _⟩ => x
  | ⟨.inr _, h⟩ => False.elim <| by rcases h with ⟨x, h'⟩; cases h'
  invFun x := ⟨.inl x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
/-
**Equiv.Set.rangeInl_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：∀ {α : Type u_3} (β : Type u_4) (x : α), (Equiv.Set.rangeInl α β) ⟨Sum.inl
 x, ⋯⟩ = x
参数：β : Type u_4；x : α；Equiv.Set.rangeInl α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
@[simp] lemma rangeInl_apply_inl {α : Type*} (β : Type*) (x : α) :
    (rangeInl α β) ⟨.inl x, mem_range_self _⟩ = x :=
  rfl

/-- Equivalence between the range of `Sum.inr : β → α ⊕ β` and `β`. -/
@[simps symm_apply_coe]
/-
**Equiv.Set.rangeInr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Set`。
形式化陈述：rangeInr (α β : Type*) : Set.range (Sum.inr : β -> α oplus β) ≃ β where to
Fun | ⟨.inl _, h⟩ => False.elim by rcases h with ⟨x, h'⟩; cases h' | ⟨.inr x, _⟩
 => x invFun x
参数：α β : Type*。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the range of `Sum.inr : β → α ⊕ β` and `β`.
-/
def rangeInr (α β : Type*) : Set.range (Sum.inr : β → α ⊕ β) ≃ β where
  toFun
  | ⟨.inl _, h⟩ => False.elim <| by rcases h with ⟨x, h'⟩; cases h'
  | ⟨.inr x, _⟩ => x
  invFun x := ⟨.inr x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
/-
**Equiv.Set.rangeInr_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Set`。
形式化陈述：∀ (α : Type u_3) {β : Type u_4} (x : β), (Equiv.Set.rangeInr α β) ⟨Sum.inr
 x, ⋯⟩ = x
参数：α : Type u_3；x : β；Equiv.Set.rangeInr α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
@[simp] lemma rangeInr_apply_inr (α : Type*) {β : Type*} (x : β) :
    (rangeInr α β) ⟨.inr x, mem_range_self _⟩ = x :=
  rfl

end Set

/-- If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably equivalent to the
range of `f`.

While awkward, the `Nonempty α` hypothesis on `f_inv` and `hf` allows this to be used when `α` is
empty too. This hypothesis is absent on analogous definitions on stronger `Equiv`s like
`LinearEquiv.ofLeftInverse` and `RingEquiv.ofLeftInverse` as their typeclass assumptions
are already sufficient to ensure non-emptiness. -/
@[simps]
/-
**Equiv.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofLeftInverse {α β : Sort _} (f : α -> β) (f_inv : Nonempty α -> β -> α) (
hf : forall h : Nonempty α, LeftInverse (f_inv h) f) : α ≃ range f where toFun a
参数：f : α -> β；f_inv : Nonempty α -> β -> α；hf : forall h : Nonempty α, LeftInver
se (f_inv h) f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably e
quivalent to the
range of `f`.

While awkward, the `Nonempty α` hypothesis on `f_inv` and `hf` allows this to be
 used when `α` is
empty too. This hypothesis is absent on analogous definitions on stronger `Equiv
`s like
`LinearEquiv.ofLeftInverse` and `RingEquiv.ofLeftInverse` as their typeclass ass
umptions
are already sufficient to ensure non-emptiness.
-/
def ofLeftInverse {α β : Sort _} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    α ≃ range f where
  toFun a := ⟨f a, a, rfl⟩
  invFun b := f_inv b.2.nonempty b
  left_inv a := hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ =>
    Subtype.ext <| show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha

/-- If `f : α → β` has a left-inverse, then `α` is computably equivalent to the range of `f`.

Note that if `α` is empty, no such `f_inv` exists and so this definition can't be used, unlike
the stronger but less convenient `ofLeftInverse`. -/
/-
**Equiv.ofLeftInverse'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv`。
形式化陈述：ofLeftInverse' {α β : Sort _} (f : α -> β) (f_inv : β -> α) (hf : LeftInve
rse f_inv f) : α ≃ range f
参数：f : α -> β；f_inv : β -> α；hf : LeftInverse f_inv f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → β` has a left-inverse, then `α` is computably equivalent to the rang
e of `f`.

Note that if `α` is empty, no such `f_inv` exists and so this definition can't b
e used, unlike
the stronger but less convenient `ofLeftInverse`.
-/
abbrev ofLeftInverse' {α β : Sort _} (f : α → β) (f_inv : β → α) (hf : LeftInverse f_inv f) :
    α ≃ range f :=
  ofLeftInverse f (fun _ => f_inv) fun _ => hf

/-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
@[simps! apply]
/-
**Equiv.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofInjective {α β} (f : α -> β) (hf : Injective f) : α ≃ range f
参数：f : α -> β；hf : Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f

--- 原说明 ---
If `f : α → β` is an injective function, then domain `α` is equivalent to the ra
nge of `f`.
-/
noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
  Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf
/-
**Equiv.apply_ofInjective_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：apply_ofInjective_symm {α β} {f : α -> β} (hf : Injective f) (b : range f)
 : f ((ofInjective f hf).symm b) = b
参数：hf : Injective f；b : range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_ofInjective_symm {α β} {f : α → β} (hf : Injective f) (b : range f) :
    f ((ofInjective f hf).symm b) = b :=
  Subtype.ext_iff.1 <| (ofInjective f hf).apply_symm_apply b

@[simp]
/-
**Equiv.ofInjective_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：ofInjective_symm_apply {α β} {f : α -> β} (hf : Injective f) (a : α) : (of
Injective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
参数：hf : Injective f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
  apply (ofInjective f hf).injective
  simp
/-
**Equiv.coe_ofInjective_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_ofInjective_symm {α β} {f : α -> β} (hf : Injective f) : ((ofInjective
 f hf).symm : range f -> α) = rangeSplitting f
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.ofInjective_symm_apply`：ofInjective_symm_apply {α β} {f : α -> β} 
(hf : Injective f) (a : α) : (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
    ((ofInjective f hf).symm : range f → α) = rangeSplitting f := by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [apply_rangeSplitting f]

@[simp]
/-
**Equiv.self_comp_ofInjective_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：self_comp_ofInjective_symm {α β} {f : α -> β} (hf : Injective f) : f ∘ (of
Injective f hf).symm = Subtype.val
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_ofInjective_symm`：apply_ofInjective_symm {α β} {f : α -> β} 
(hf : Injective f) (b : range f) : f ((ofInjective f hf).symm b) = b
-/
theorem self_comp_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
    f ∘ (ofInjective f hf).symm = Subtype.val :=
  funext fun x => apply_ofInjective_symm hf x
/-
**Equiv.ofLeftInverse_eq_ofInjective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：ofLeftInverse_eq_ofInjective {α β : Type*} (f : α -> β) (f_inv : Nonempty 
α -> β -> α) (hf : forall h : Nonempty α, LeftInverse (f_inv h) f) : ofLeftInver
se f f_inv hf = ofInjective f ((isEmpty_or_nonempty α).elim (fun _ _ _ _ => Subs
ingleton.elim _ _) (fun h => (hf h).injective))
参数：f : α -> β；f_inv : Nonempty α -> β -> α；hf : forall h : Nonempty α, LeftInver
se (f_inv h) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.ofLeftInverse_apply_coe`：∀ {α : Sort u_3} {β : Type u_4} (f : α → 
β) (f_inv : Nonempty α → β → α)   (hf : ∀ (h : Nonempty α), Function.LeftInverse
 (f_inv h) f) (a : …
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLeftInverse_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    ofLeftInverse f f_inv hf =
      ofInjective f ((isEmpty_or_nonempty α).elim (fun _ _ _ _ => Subsingleton.elim _ _)
        (fun h => (hf h).injective)) := by
  ext
  simp
/-
**Equiv.ofLeftInverse'_eq_ofInjective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (f : α → β) (f_inv : β → α) (hf : Function
.LeftInverse f_inv f),   Equiv.ofLeftInverse' f f_inv hf = Equiv.ofInjective f ⋯
参数：f : α → β；f_inv : β → α；hf : Function.LeftInverse f_inv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.ofLeftInverse_apply_coe`：∀ {α : Sort u_3} {β : Type u_4} (f : α → 
β) (f_inv : Nonempty α → β → α)   (hf : ∀ (h : Nonempty α), Function.LeftInverse
 (f_inv h) f) (a : …
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLeftInverse'_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : β → α)
    (hf : LeftInverse f_inv f) : ofLeftInverse' f f_inv hf = ofInjective f hf.injective := by
  ext
  simp
/-
**Equiv.set_forall_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) {p : Set α → Prop}, (∀ (a : Se
t α), p a) ↔ ∀ (a : Set β), p (⇑e ⁻¹' a)
参数：e : α ≃ β；∀ (a : Set α), p a；a : Set β；⇑e ⁻¹' a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Injective.preimage_surjective`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β}, Function.Injective f → Function.Surjective (Set.preimage f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem set_forall_iff {α β} (e : α ≃ β) {p : Set α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (e ⁻¹' a) :=
  e.injective.preimage_surjective.forall
/-
**Equiv.preimage_piEquivPiSubtypeProd_symm_pi** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：preimage_piEquivPiSubtypeProd_symm_pi {α : Type*} {β : α -> Type*} (p : α 
-> Prop) [DecidablePred p] (s : forall i, Set (β i)) : (piEquivPiSubtypeProd p β
).symm ⁻¹' pi univ s = (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : 
{ i // ¬p i } => s i
参数：p : α -> Prop；s : forall i, Set (β i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Equiv.piEquivPiSubtypeProd_symm_apply`：∀ {α : Type u_9} (p : α → Prop) (
β : α → Type u_10) [inst : DecidablePred p]   (f : ((i : { x // p x }) → β ↑i) ×
 ((i : { x // ¬p x }) → β ↑…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem preimage_piEquivPiSubtypeProd_symm_pi {α : Type*} {β : α → Type*} (p : α → Prop)
    [DecidablePred p] (s : ∀ i, Set (β i)) :
    (piEquivPiSubtypeProd p β).symm ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i := by
  ext ⟨f, g⟩
  simp only [mem_preimage, mem_univ_pi, prodMk_mem_set_prod_eq, Subtype.forall, ← forall_and]
  refine forall_congr' fun i => ?_
  by_cases hi : p i <;> simp [hi]

-- See also `Equiv.sigmaFiberEquiv`.
/-- `sigmaPreimageEquiv f` for `f : α → β` is the natural equivalence between
the type of all preimages of points under `f` and the total space `α`. -/
@[simps!]
/-
**Equiv.sigmaPreimageEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaPreimageEquiv {α β} (f : α -> β) : (Σ b, f ⁻¹' {b}) ≃ α
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sigmaPreimageEquiv f` for `f : α → β` is the natural equivalence between
the type of all preimages of points under `f` and the total space `α`.
-/
def sigmaPreimageEquiv {α β} (f : α → β) : (Σ b, f ⁻¹' {b}) ≃ α :=
  sigmaFiberEquiv f

-- See also `Equiv.ofFiberEquiv`.
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A family of equivalences between preimages of points gives an equivalence between domains. -/
@[simps!]
/-
**Equiv.ofPreimageEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofPreimageEquiv {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, f ⁻¹' {c}
 ≃ g ⁻¹' {c}) : α ≃ β
参数：e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of equivalences between preimages of points gives an equivalence betwee
n domains.
-/
def ofPreimageEquiv {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c}) : α ≃ β :=
  Equiv.ofFiberEquiv e
/-
**Equiv.ofPreimageEquiv_map** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：ofPreimageEquiv_map {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, f ⁻¹'
 {c} ≃ g ⁻¹' {c}) (a : α) : g (ofPreimageEquiv e a) = f a
参数：e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c}；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ofFiberEquiv_map`：ofFiberEquiv_map {α β γ} {f : α -> γ} {g : β -> 
γ} (e : forall c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv
 e a) = f a
-/
theorem ofPreimageEquiv_map {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c})
    (a : α) : g (ofPreimageEquiv e a) = f a :=
  Equiv.ofFiberEquiv_map e a

end Equiv

/-- If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the types `↥s` and `↥t`. -/
/-
**Set.BijOn.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.BijOn.equiv {α : Type*} {β : Type*} {s : Set α} {t : Set β} (f : α -> 
β) (h : BijOn f s t) : s ≃ t
参数：f : α -> β；h : BijOn f s t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.BijOn.bijective`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Se
t β} {f : α → β} (h : Set.BijOn f s t),   Function.Bijective (Set.MapsTo.restric
t f s t ⋯…

--- 原说明 ---
If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the types `↥s` and `↥t`.
-/
noncomputable def Set.BijOn.equiv {α : Type*} {β : Type*} {s : Set α} {t : Set β} (f : α → β)
    (h : BijOn f s t) : s ≃ t :=
  Equiv.ofBijective _ h.bijective

/-- The composition of an updated function with an equiv on a subtype can be expressed as an
updated function. -/
/-
**dite_comp_equiv_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_comp_equiv_update {α E : Type*} {β γ : Sort*} {p : α -> Prop} [EquivL
ike E {x // p x} β] (e : E) (v : β -> γ) (w : α -> γ) (j : β) (x : γ) [Decidable
Eq β] [DecidableEq α] [forall j, Decidable (p j)] : (fun i : α => if h : p i the
n (update v j x) (e ⟨i, h⟩) else w i) = update (fun i : α => if h : p i then v (
e ⟨i, h⟩) else w i) (EquivLike.inv e j) x
参数：e : E；v : β -> γ；w : α -> γ；j : β；x : γ；p j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `EquivLike.inv_apply_apply`：inv_apply_apply (e : E) (a : α) : inv e (e a)
 = a

--- 原说明 ---
The composition of an updated function with an equiv on a subtype can be express
ed as an
updated function.
-/
theorem dite_comp_equiv_update
    {α E : Type*} {β γ : Sort*} {p : α → Prop} [EquivLike E {x // p x} β]
    (e : E) (v : β → γ) (w : α → γ) (j : β) (x : γ)
    [DecidableEq β] [DecidableEq α] [∀ j, Decidable (p j)] :
    (fun i : α => if h : p i then (update v j x) (e ⟨i, h⟩) else w i) =
      update (fun i : α => if h : p i then v (e ⟨i, h⟩) else w i) (EquivLike.inv e j) x := by
  ext i
  by_cases h : p i
  · simp only [h, update_apply]
    aesop
  · grind

section Swap

variable {α : Type*} [DecidableEq α] {a b : α} {s : Set α}

/-
**Equiv.swap_bijOn_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.swap_bijOn_self (hs : a in s ↔ b in s) : BijOn (Equiv.swap a b) s s
参数：hs : a in s ↔ b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equiv.swap_bijOn_self (hs : a ∈ s ↔ b ∈ s) : BijOn (Equiv.swap a b) s s := by
  grind [Equiv.bijOn]
/-
**Equiv.swap_bijOn_exchange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.swap_bijOn_exchange (ha : a in s) (hb : b ∉ s) : BijOn (Equiv.swap a
 b) s (insert b (s \ {a}))
参数：ha : a in s；hb : b ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equiv.swap_bijOn_exchange (ha : a ∈ s) (hb : b ∉ s) :
    BijOn (Equiv.swap a b) s (insert b (s \ {a})) := by
  grind [Equiv.bijOn]

end Swap

