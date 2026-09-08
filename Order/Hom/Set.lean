/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.MinImports

/-!
# Order homomorphisms and sets
-/

@[expose] public section


open OrderDual Set

variable {α β γ : Type*}

namespace Set

set_option backward.isDefEq.respectTransparency false in
/-- Sets on sum types are order-equivalent to pairs of sets on each summand. -/
@[simps apply]
/-
**Set.sumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：sumEquiv : Set (α oplus β) ≃o Set α × Set β where toFun s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_inl_union_image_preimage_inr`：image_preimage_inl_unio
n_image_preimage_inr (s : Set (α oplus β)) : Sum.inl '' Sum.inl ⁻¹' s union Sum.
inr '' Sum.inr ⁻¹' s = s

--- 原说明 ---
Sets on sum types are order-equivalent to pairs of sets on each summand.
-/
def sumEquiv : Set (α ⊕ β) ≃o Set α × Set β where
  toFun s := (Sum.inl ⁻¹' s, Sum.inr ⁻¹' s)
  invFun s := Sum.inl '' s.1 ∪ Sum.inr '' s.2
  left_inv s := image_preimage_inl_union_image_preimage_inr s
  right_inv s := by
    simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
  map_rel_iff' := by simp [subset_def]

@[simp]
/-
**Set.sumEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sumEquiv_symm_apply {s : Set α × Set β} : sumEquiv.symm s = Sum.inl '' s.1
 union Sum.inr '' s.2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumEquiv_symm_apply {s : Set α × Set β} :
    sumEquiv.symm s = Sum.inl '' s.1 ∪ Sum.inr '' s.2 := rfl
/-
**Set.MapsTo.sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → γ} {g : β → γ} {s 
: Set α × Set β} {t : Set γ},   Set.MapsTo f s.1 t → Set.MapsTo g s.2 t → Set.Ma
psTo (Sum.elim f g) (Set.sumEquiv.symm s) t
参数：Sum.elim f g；Set.sumEquiv.symm s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem MapsTo.sumElim {f : α → γ} {g : β → γ} {s : Set α × Set β} {t : Set γ}
    (hf : Set.MapsTo f s.1 t) (hg : Set.MapsTo g s.2 t) :
    Set.MapsTo (Sum.elim f g) (Set.sumEquiv.symm s) t := by
  rintro (a | b) <;> aesop
/-
**Set.InjOn.sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → γ} {g : β → γ} {s 
: Set α × Set β},   Set.InjOn f s.1 → Set.InjOn g s.2 → (∀ a ∈ s.1, ∀ b ∈ s.2, f
 a ≠ g b) → Set.InjOn (Sum.elim f g) (Set.sumEquiv.symm s)
参数：∀ a ∈ s.1, ∀ b ∈ s.2, f a ≠ g b；Sum.elim f g；Set.sumEquiv.symm s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem InjOn.sumElim {f : α → γ} {g : β → γ} {s : Set α × Set β}
    (hf : Set.InjOn f s.1) (hg : Set.InjOn g s.2) (hfg : ∀ᵉ (a ∈ s.1) (b ∈ s.2), f a ≠ g b) :
    Set.InjOn (Sum.elim f g) (Set.sumEquiv.symm s) := by
  rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ heq <;> aesop

end Set

namespace OrderIso

section LE

variable [LE α] [LE β]

/-
**OrderIso.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：range_eq (e : α ≃o β) : Set.range e = Set.univ
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
-/
theorem range_eq (e : α ≃o β) : Set.range e = Set.univ :=
  e.surjective.range_eq

@[simp]
/-
**OrderIso.symm_image_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' e '' s = s
参数：e : α ≃o β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' e '' s = s :=
  e.toEquiv.symm_image_image s

@[simp]
/-
**OrderIso.image_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_symm_image (e : α ≃o β) (s : Set β) : e '' e.symm '' s = s
参数：e : α ≃o β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
-/
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' e.symm '' s = s :=
  e.toEquiv.image_symm_image s
/-
**OrderIso.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_eq_preimage_symm (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s
参数：e : α ≃o β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_eq_preimage_symm (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

@[simp]
/-
**OrderIso.preimage_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' e.symm ⁻¹' s = s
参数：e : α ≃o β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.preimage_symm_preimage`：preimage_symm_preimage {α β} (e : α ≃ β) (
s : Set α) : e ⁻¹' e.symm ⁻¹' s = s
-/
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' e.symm ⁻¹' s = s :=
  e.toEquiv.preimage_symm_preimage s

@[simp]
/-
**OrderIso.symm_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
参数：e : α ≃o β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_preimage_preimage`：symm_preimage_preimage {α β} (e : α ≃ β) (
s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
-/
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s :=
  e.toEquiv.symm_preimage_preimage s

@[simp]
/-
**OrderIso.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_preimage (e : α ≃o β) (s : Set β) : e '' e ⁻¹' s = s
参数：e : α ≃o β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
-/
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' e ⁻¹' s = s :=
  e.toEquiv.image_preimage s

@[simp]
/-
**OrderIso.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' e '' s = s
参数：e : α ≃o β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
-/
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' e '' s = s :=
  e.toEquiv.preimage_image s

end LE

open Set

variable [Preorder α]

/-- Order isomorphism between two equal sets. -/
@[simps! apply symm_apply]
/-
**OrderIso.setCongr** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：setCongr (s t : Set α) (h : s = t) : s ≃o t where toEquiv
参数：s t : Set α；h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between two equal sets.
-/
def setCongr (s t : Set α) (h : s = t) :
    s ≃o t where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl

/-- Order isomorphism between `univ : Set α` and `α`. -/
/-
**OrderIso.Set.univ** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso.Set`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → ↑Set.univ ≃o α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between `univ : Set α` and `α`.
-/
def Set.univ : (Set.univ : Set α) ≃o α where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' := Iff.rfl

end OrderIso

/-- We can regard an order embedding as an order isomorphism to its range. -/
@[simps! apply]
/-
**OrderEmbedding.orderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderEmbedding.orderIso [LE α] [LE β] {f : α ↪o β} : α ≃o Set.range f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can regard an order embedding as an order isomorphism to its range.
-/
noncomputable def OrderEmbedding.orderIso [LE α] [LE β] {f : α ↪o β} :
    α ≃o Set.range f :=
  { Equiv.ofInjective _ f.injective with
    map_rel_iff' := f.map_rel_iff }

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
/-
**StrictMonoOn.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `StrictMonoOn`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : LinearOrder α] → [inst_1 :
 Preorder β] → (f : α → β) → (s : Set α) → StrictMonoOn f s → ↑s ≃o ↑(f '' s)
参数：f : α → β；s : Set α；f '' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` is strictly monotone on a set `s`, then it defines an order is
omorphism
between `s` and its image.
-/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α → β)
    (s : Set α) (hf : StrictMonoOn f s) :
    s ≃o f '' s where
  toEquiv := hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)

namespace StrictMono

variable [LinearOrder α] [Preorder β]
variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps! apply]
/-
**StrictMono.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `StrictMono`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : LinearOrder α] → [inst_1 : Pre
order β] → (f : α → β) → StrictMono f → α ≃o ↑(Set.range f)
参数：f : α → β；Set.range f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b

--- 原说明 ---
A strictly monotone function from a linear order is an order isomorphism between
 its domain and
its range.
-/
protected noncomputable def orderIso :
    α ≃o Set.range f where
  toEquiv := Equiv.ofInjective f h_mono.injective
  map_rel_iff' := h_mono.le_iff_le

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
/-
**StrictMono.orderIsoOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `StrictMono`。
形式化陈述：orderIsoOfSurjective : α ≃o β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ

--- 原说明 ---
A strictly monotone surjective function from a linear order is an order isomorph
ism.
-/
noncomputable def orderIsoOfSurjective : α ≃o β :=
  (h_mono.orderIso f).trans <|
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

@[simp]
/-
**StrictMono.coe_orderIsoOfSurjective** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α -> β)
 = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α → β) = f :=
  rfl

@[simp]
/-
**StrictMono.orderIsoOfSurjective_symm_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Str
ictMono`。
形式化陈述：orderIsoOfSurjective_symm_apply_self (a : α) : (orderIsoOfSurjective f h_m
ono h_surj).symm (f a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem orderIsoOfSurjective_symm_apply_self (a : α) :
    (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _
/-
**StrictMono.orderIsoOfSurjective_self_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Str
ictMono`。
形式化陈述：orderIsoOfSurjective_self_symm_apply (b : β) : f ((orderIsoOfSurjective f 
h_mono h_surj).symm b) = b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
theorem orderIsoOfSurjective_self_symm_apply (b : β) :
    f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _

end StrictMono

/-- Two order embeddings on a well-order are equal provided that their ranges are equal. -/
/-
**OrderEmbedding.range_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrderEmbedding.range_inj [LinearOrder α] [WellFoundedLT α] [Preorder β] {f
 g : α ↪o β} : Set.range f = Set.range g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.range_inj`：StrictMono.range_inj [WellFoundedLT β] {f g : β ->
 γ} (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two order embeddings on a well-order are equal provided that their ranges are eq
ual.
-/
lemma OrderEmbedding.range_inj [LinearOrder α] [WellFoundedLT α] [Preorder β] {f g : α ↪o β} :
    Set.range f = Set.range g ↔ f = g := by
  rw [f.strictMono.range_inj g.strictMono, DFunLike.coe_fn_eq]

namespace OrderIso

-- These results are also true whenever β is well-founded instead of α.
-- You can use `RelEmbedding.isWellFounded` to transfer the instance over.

/-
**OrderIso.subsingleton_of_wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
形式化陈述：subsingleton_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] [Preorder 
β] : Subsingleton (α ≃o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.ext_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 
: LE β] {f g : α ≃o β}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.coe_toOrderEmbedding`：coe_toOrderEmbedding (e : α ≃o β) : ⇑e.to
OrderEmbedding = e
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用引理 `OrderEmbedding.range_inj`：OrderEmbedding.range_inj [LinearOrder α] [Well
FoundedLT α] [Preorder β] {f g : α ↪o β} : Set.range f = Set.range g ↔ f = g
· 使用定理 `OrderIso.range_eq`：range_eq (e : α ≃o β) : Set.range e = Set.univ
-/
instance subsingleton_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] [Preorder β] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  rw [OrderIso.ext_iff, ← coe_toOrderEmbedding, ← coe_toOrderEmbedding, DFunLike.coe_fn_eq,
    ← OrderEmbedding.range_inj, coe_toOrderEmbedding, coe_toOrderEmbedding, range_eq, range_eq]
/-
**OrderIso.subsingleton_of_wellFoundedLT'** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
形式化陈述：subsingleton_of_wellFoundedLT' [LinearOrder β] [WellFoundedLT β] [Preorder
 α] : Subsingleton (α ≃o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance subsingleton_of_wellFoundedLT' [LinearOrder β] [WellFoundedLT β] [Preorder α] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  change f.symm.symm = g.symm.symm
  rw [Subsingleton.elim f.symm]
/-
**OrderIso.unique_of_wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
形式化陈述：unique_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] : Unique (α ≃o α
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] : Unique (α ≃o α) := Unique.mk' _
/-
**OrderIso.subsingleton_of_wellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
形式化陈述：subsingleton_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] [Preorder 
β] : Subsingleton (α ≃o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
instance subsingleton_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] [Preorder β] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]
/-
**OrderIso.subsingleton_of_wellFoundedGT'** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
形式化陈述：subsingleton_of_wellFoundedGT' [LinearOrder β] [WellFoundedGT β] [Preorder
 α] : Subsingleton (α ≃o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
instance subsingleton_of_wellFoundedGT' [LinearOrder β] [WellFoundedGT β] [Preorder α] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]
/-
**OrderIso.unique_of_wellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
形式化陈述：unique_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] : Unique (α ≃o α
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] : Unique (α ≃o α) := Unique.mk' _

set_option backward.isDefEq.respectTransparency false in
/-- An order isomorphism between lattices induces an order isomorphism between corresponding
interval sublattices. -/
/-
**OrderIso.Iic** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : Lattice α] → [inst_1 : Lattice
 β] → (e : α ≃o β) → (x : α) → ↑(Set.Iic x) ≃o ↑(Set.Iic (e x))
参数：e : α ≃o β；x : α；Set.Iic x；Set.Iic (e x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism between lattices induces an order isomorphism between corre
sponding
interval sublattices.
-/
protected def Iic [Lattice α] [Lattice β] (e : α ≃o β) (x : α) :
    Iic x ≃o Iic (e x) where
  toFun y := ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.symm_apply_le.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/-- An order isomorphism between lattices induces an order isomorphism between corresponding
interval sublattices. -/
/-
**OrderIso.Ici** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : Lattice α] → [inst_1 : Lattice
 β] → (e : α ≃o β) → (x : α) → ↑(Set.Ici x) ≃o ↑(Set.Ici (e x))
参数：e : α ≃o β；x : α；Set.Ici x；Set.Ici (e x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism between lattices induces an order isomorphism between corre
sponding
interval sublattices.
-/
protected def Ici [Lattice α] [Lattice β] (e : α ≃o β) (x : α) :
    Ici x ≃o Ici (e x) where
  toFun y := ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.le_symm_apply.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/-- An order isomorphism between lattices induces an order isomorphism between corresponding
interval sublattices. -/
/-
**OrderIso.Icc** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : Lattice α] → [inst_1 : Lat
tice β] → (e : α ≃o β) → (x y : α) → ↑(Set.Icc x y) ≃o ↑(Set.Icc (e x) (e y))
参数：e : α ≃o β；x y : α；Set.Icc x y；Set.Icc (e x) (e y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism between lattices induces an order isomorphism between corre
sponding
interval sublattices.
-/
protected def Icc [Lattice α] [Lattice β] (e : α ≃o β) (x y : α) :
    Icc x y ≃o Icc (e x) (e y) where
  toFun z := ⟨e z, by simp only [mem_Icc, map_le_map_iff]; exact z.property⟩
  invFun z := ⟨e.symm z, by simp only [mem_Icc, e.le_symm_apply, e.symm_apply_le]; exact z.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

end OrderIso

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

/-- Taking complements as an order isomorphism to the order dual. -/
@[simps!]
/-
**OrderIso.compl** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.compl : α ≃o αᵒᵈ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `compl_le_compl_iff_le`：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y

--- 原说明 ---
Taking complements as an order isomorphism to the order dual.
-/
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ Compl.compl
  invFun := Compl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le
/-
**compl_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_strictAnti : StrictAnti (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem compl_strictAnti : StrictAnti (compl : α → α) :=
  (OrderIso.compl α).strictMono
/-
**compl_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_antitone : Antitone (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
theorem compl_antitone : Antitone (compl : α → α) :=
  (OrderIso.compl α).monotone

end BooleanAlgebra

