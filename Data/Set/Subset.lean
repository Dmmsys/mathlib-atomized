/-
Copyright (c) 2024 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel Marco
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Functor

/-!
# Sets in subtypes

This file is about sets in `Set A` when `A` is a set.

It defines notation `↓∩` for sets in a type pulled down to sets in a subtype, as an inverse
operation to the coercion that lifts sets in a subtype up to sets in the ambient type.

This module also provides lemmas for `↓∩` and this coercion.

## Notation

Let `α` be a `Type`, `A B : Set α` two sets in `α`, and `C : Set A` a set in the subtype `↑A`.

- `A ↓∩ B` denotes `(Subtype.val ⁻¹' B : Set A)` (that is, `{x : ↑A | ↑x ∈ B}`).
- `↑C` denotes `Subtype.val '' C` (that is, `{x : α | ∃ y ∈ C, ↑y = x}`).

This notation, (together with the `↑` notation for `Set.CoeHead`)
is defined in `Mathlib/Data/Set/Notation.lean` and is scoped to the `Set.Notation` namespace.
To enable it, use `open Set.Notation`.


## Naming conventions

Theorem names refer to `↓∩` as `preimage_val`.

## Tags

subsets
-/

public section

open Set

variable {ι : Sort*} {α : Type*} {A B C : Set α} {D E : Set A}
variable {S : Set (Set α)} {T : Set (Set A)} {s : ι → Set α} {t : ι → Set A}

namespace Set

open Notation

/-
**Set.preimage_val_eq_univ_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_val_eq_univ_of_subset (h : A subseteq B) : A ↓inter B = univ
参数：h : A subseteq B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
lemma preimage_val_eq_univ_of_subset (h : A ⊆ B) : A ↓∩ B = univ := by
  rw [eq_univ_iff_forall, Subtype.forall]
  exact h
/-
**Set.preimage_val_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_val_sUnion : A ↓inter (⋃₀ S) = ⋃₀ { (A ↓inter B) | B in S }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_val_sUnion : A ↓∩ (⋃₀ S) = ⋃₀ { (A ↓∩ B) | B ∈ S } := by
  rw [← Set.image, sUnion_image]
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]

@[simp]
/-
**Set.preimage_val_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_val_iInter : A ↓inter (⋂ i, s i) = ⋂ i, A ↓inter s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
-/
lemma preimage_val_iInter : A ↓∩ (⋂ i, s i) = ⋂ i, A ↓∩ s i := preimage_iInter
/-
**Set.preimage_val_sInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_val_sInter : A ↓inter (⋂₀ S) = ⋂₀ { (A ↓inter B) | B in S }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_val_sInter : A ↓∩ (⋂₀ S) = ⋂₀ { (A ↓∩ B) | B ∈ S } := by
  rw [← Set.image, sInter_image]
  simp_rw [sInter_eq_biInter, preimage_iInter]
/-
**Set.preimage_val_sInter_eq_sInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_val_sInter_eq_sInter : A ↓inter (⋂₀ S) = ⋂₀ ((A ↓inter ·) '' S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_sInter`：preimage_sInter {f : α -> β} {s : Set (Set β)} : f 
⁻¹' ⋂₀ s = ⋂ t in s, f ⁻¹' t
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_val_sInter_eq_sInter : A ↓∩ (⋂₀ S) = ⋂₀ ((A ↓∩ ·) '' S) := by
  simp only [preimage_sInter, sInter_image]
/-
**Set.eq_of_preimage_val_eq_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_preimage_val_eq_of_subset (hB : B subseteq A) (hC : C subseteq A) (h
 : A ↓inter B = A ↓inter C) : B = C
参数：hB : B subseteq A；hC : C subseteq A；h : A ↓inter B = A ↓inter C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma eq_of_preimage_val_eq_of_subset (hB : B ⊆ A) (hC : C ⊆ A) (h : A ↓∩ B = A ↓∩ C) : B = C := by
  simp only [← inter_eq_right] at hB hC
  simp only [Subtype.preimage_val_eq_preimage_val_iff, hB, hC] at h
  exact h

/-!
The following simp lemmas try to transform operations in the subtype into operations in the ambient
type, if possible.
-/

@[simp]
/-
**Set.image_val_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_union : (↑(D union E) : Set α) = ↑D union ↑E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t

--- 原说明 ---
The following simp lemmas try to transform operations in the subtype into operat
ions in the ambient
type, if possible.
-/
lemma image_val_union : (↑(D ∪ E) : Set α) = ↑D ∪ ↑E := image_union _ _ _

@[simp]
/-
**Set.image_val_inter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_inter : (↑(D inter E) : Set α) = ↑D inter ↑E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_inter : (↑(D ∩ E) : Set α) = ↑D ∩ ↑E := image_inter Subtype.val_injective

@[simp]
/-
**Set.image_val_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_sdiff : (↑(D \ E) : Set α) = ↑D \ ↑E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_sdiff : (↑(D \ E) : Set α) = ↑D \ ↑E := image_sdiff Subtype.val_injective _ _

@[deprecated (since := "2026-06-03")] alias image_val_diff := image_val_sdiff

@[simp]
/-
**Set.image_val_compl** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_compl : ↑(Dᶜ) = A \ ↑D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用引理 `Set.image_val_sdiff`：image_val_sdiff : (↑(D \ E) : Set α) = ↑D \ ↑E
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
-/
lemma image_val_compl : ↑(Dᶜ) = A \ ↑D := by
  rw [compl_eq_univ_sdiff, image_val_sdiff, image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]

@[simp]
/-
**Set.image_val_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_sUnion : ↑(⋃₀ T) = ⋃₀ { (B : Set α) | B in T}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sUnion`：image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀
 s) = ⋃₀ (image f '' s)
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
-/
lemma image_val_sUnion : ↑(⋃₀ T) = ⋃₀ { (B : Set α) | B ∈ T} := by
  rw [image_sUnion, image]

@[simp]
/-
**Set.image_val_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_iUnion : ↑(⋃ i, t i) = ⋃ i, (t i : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
-/
lemma image_val_iUnion : ↑(⋃ i, t i) = ⋃ i, (t i : Set α) := image_iUnion

@[simp]
/-
**Set.image_val_sInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_sInter (hT : T.Nonempty) : (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α)
 | B in T }
参数：hT : T.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.InjOn.image_biInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_
5} {p : ι → Prop} {s : (i : ι) → p i → Set α},   (∃ i, p i) →     ∀ {f : α → β},
       Set.InjOn…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_sInter (hT : T.Nonempty) : (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α) | B ∈ T } := by
  rw [← Set.image, sInter_image, sInter_eq_biInter, Subtype.val_injective.injOn.image_biInter_eq hT]

@[simp]
/-
**Set.image_val_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_iInter [Nonempty ι] : (↑(⋂ i, t i) : Set α) = ⋂ i, (↑(t i) : Set
 α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_iInter [Nonempty ι] : (↑(⋂ i, t i) : Set α) = ⋂ i, (↑(t i) : Set α) :=
  Subtype.val_injective.injOn.image_iInter_eq

@[simp]
/-
**Set.image_val_union_self_right_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_union_self_right_eq : A union ↑D = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_left`：union_eq_left {s t : Set α} : s union t = s ↔ t subse
teq s
· 使用定理 `Set.image_val_subset`：image_val_subset : (γ : Set α) subseteq β
-/
lemma image_val_union_self_right_eq : A ∪ ↑D = A :=
  union_eq_left.2 image_val_subset

@[simp]
/-
**Set.image_val_union_self_left_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_union_self_left_eq : ↑D union A = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Set.image_val_subset`：image_val_subset : (γ : Set α) subseteq β
-/
lemma image_val_union_self_left_eq : ↑D ∪ A = A :=
  union_eq_right.2 image_val_subset

@[simp]
/-
**Set.image_val_inter_self_right_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_inter_self_right_eq_coe : A inter ↑D = ↑D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.image_val_subset`：image_val_subset : (γ : Set α) subseteq β
-/
lemma image_val_inter_self_right_eq_coe : A ∩ ↑D = ↑D :=
  inter_eq_right.2 image_val_subset

@[simp]
/-
**Set.image_val_inter_self_left_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_inter_self_left_eq_coe : ↑D inter A = ↑D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.image_val_subset`：image_val_subset : (γ : Set α) subseteq β
-/
lemma image_val_inter_self_left_eq_coe : ↑D ∩ A = ↑D :=
  inter_eq_left.2 image_val_subset
/-
**Set.subset_preimage_val_image_val_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_preimage_val_image_val_iff : D subseteq A ↓inter ↑E ↔ D subseteq E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma subset_preimage_val_image_val_iff : D ⊆ A ↓∩ ↑E ↔ D ⊆ E := by
  rw [preimage_image_eq _ Subtype.val_injective]

@[simp]
/-
**Set.image_val_inj** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_inj : (D : Set α) = ↑E ↔ D = E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_inj : (D : Set α) = ↑E ↔ D = E := Subtype.val_injective.image_injective.eq_iff
/-
**Set.image_val_injective** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_injective : Function.Injective ((↑) : Set A -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_injective : Function.Injective ((↑) : Set A → Set α) :=
  Subtype.val_injective.image_injective
/-
**Set.subset_of_image_val_subset_image_val** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_of_image_val_subset_image_val (h : (↑D : Set α) subseteq ↑E) : D su
bseteq E
参数：h : (↑D : Set α) subseteq ↑E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma subset_of_image_val_subset_image_val (h : (↑D : Set α) ⊆ ↑E) : D ⊆ E :=
  (image_subset_image_iff Subtype.val_injective).1 h

@[gcongr, mono]
/-
**Set.image_val_mono** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_mono (h : D subseteq E) : (↑D : Set α) subseteq ↑E
参数：h : D subseteq E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma image_val_mono (h : D ⊆ E) : (↑D : Set α) ⊆ ↑E :=
  (image_subset_image_iff Subtype.val_injective).2 h

/-!
Relations between restriction and coercion.
-/

/-
**Set.image_val_preimage_val_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_val_preimage_val_subset_self : ↑(A ↓inter B) subseteq B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s

--- 原说明 ---
Relations between restriction and coercion.
-/
lemma image_val_preimage_val_subset_self : ↑(A ↓∩ B) ⊆ B :=
  image_preimage_subset _ _
/-
**Set.preimage_val_image_val_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_val_image_val_eq_self : A ↓inter ↑D = D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma preimage_val_image_val_eq_self : A ↓∩ ↑D = D :=
  Function.Injective.preimage_image Subtype.val_injective _

end Set

