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
/--
theorem `range_eq_univ` / 定理 `range_eq_univ`

English:
theorem range_eq_univ
  given: {α : Type*} {β : Type*} {E : Type*} [EquivLike E α β] (e : E)
  proof: eq_univ_of_forall (EquivLike.toEquiv e).surjective

中文:
定理 range_eq_univ
  条件: {α : 类型} {β : 类型} {E : 类型} [EquivLike E α β] (e : E)
  证明: eq_univ_of_forall (EquivLike.toEquiv e).surjective

Depends on / 依赖: EquivLike, EquivLike.toEquiv, eq_univ_of_forall, surjective, toEquiv
-/
theorem range_eq_univ {α : Type*} {β : Type*} {E : Type*} [EquivLike E α β] (e : E) :
    range e = univ :=
  eq_univ_of_forall (EquivLike.toEquiv e).surjective

end EquivLike

namespace Equiv
variable {α β : Type*}

/--
theorem `range_eq_univ` / 定理 `range_eq_univ`

English:
theorem range_eq_univ
  given: (e : α ≃ β)
  statement: range e = univ
  proof: EquivLike.range_eq_univ e

中文:
定理 range_eq_univ
  条件: (e : α ≃ β)
  结论: range e = univ
  证明: EquivLike.range_eq_univ e

Depends on / 依赖: EquivLike, EquivLike.range_eq_univ, range_eq_univ
-/
theorem range_eq_univ (e : α ≃ β) : range e = univ := EquivLike.range_eq_univ e

/--
lemma `image_symm_eq_preimage` / 引理 `image_symm_eq_preimage`

English:
lemma image_symm_eq_preimage
  given: (e : α ≃ β) (s : Set β)
  statement: e.symm '' s = e ⁻¹' s
  proof: by
  ext; exact mem_image_iff_of_inverse e.right_inv e.left_inv

中文:
引理 image_symm_eq_preimage
  条件: (e : α ≃ β) (s : Set β)
  结论: e.symm '' s = e ⁻¹' s
  证明: by
  ext; exact mem_image_iff_of_inverse e.right_inv e.left_inv

Depends on / 依赖: e.left_inv, e.right_inv, left_inv, mem_image_iff_of_inverse, right_inv
-/
lemma image_symm_eq_preimage (e : α ≃ β) (s : Set β) : e.symm '' s = e ⁻¹' s := by
  ext; exact mem_image_iff_of_inverse e.right_inv e.left_inv

/--
lemma `image_eq_preimage_symm` / 引理 `image_eq_preimage_symm`

English:
lemma image_eq_preimage_symm
  given: (e : α ≃ β) (s : Set α)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.symm.image_symm_eq_preimage _

@[simp 1001]

中文:
引理 image_eq_preimage_symm
  条件: (e : α ≃ β) (s : Set α)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.symm.image_symm_eq_preimage _

@[simp 1001]

Depends on / 依赖: e.symm.image_symm_eq_preimage, image_symm_eq_preimage
-/
lemma image_eq_preimage_symm (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.symm.image_symm_eq_preimage _

@[simp 1001]
/--
theorem `_root_.Set.mem_image_equiv` / 定理 `_root_.Set.mem_image_equiv`

English:
theorem _root_.Set.mem_image_equiv
  given: {α β} {S : Set α} {f : α ≃ β} {x : β}
  proof: Set.ext_iff.mp (image_eq_preimage_symm ..) x

中文:
定理 _root_.Set.mem_image_equiv
  条件: {α β} {S : Set α} {f : α ≃ β} {x : β}
  证明: Set.ext_iff.mp (image_eq_preimage_symm ..) x

Depends on / 依赖: Set.ext_iff.mp, ext_iff, image_eq_preimage_symm
-/
theorem _root_.Set.mem_image_equiv {α β} {S : Set α} {f : α ≃ β} {x : β} :
    x in f '' S ↔ f.symm x in S :=
  Set.ext_iff.mp (image_eq_preimage_symm ..) x

-- Increased priority so this fires before `image_subset_iff`
@[simp high]
/--
theorem `symm_image_subset` / 定理 `symm_image_subset`

English:
theorem symm_image_subset
  given: {α β} (e : α ≃ β) (s : Set α) (t : Set β)
  proof: by rw [image_subset_iff, image_eq_preimage_symm]

中文:
定理 symm_image_subset
  条件: {α β} (e : α ≃ β) (s : Set α) (t : Set β)
  证明: by rw [image_subset_iff, image_eq_preimage_symm]
-/
protected theorem symm_image_subset {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    e.symm '' t subseteq s ↔ t subseteq e '' s := by rw [image_subset_iff, image_eq_preimage_symm]

-- Increased priority so this fires before `image_subset_iff`
@[simp high]
/--
theorem `subset_symm_image` / 定理 `subset_symm_image`

English:
theorem subset_symm_image
  given: {α β} (e : α ≃ β) (s : Set α) (t : Set β)
  proof: calc
    s subseteq e.symm '' t ↔ e.symm.symm '' s subseteq t := by rw [e.symm.symm_image_subset]
    _ ↔ e '' s subseteq t := by rw [e.symm_symm]

@[simp]

中文:
定理 subset_symm_image
  条件: {α β} (e : α ≃ β) (s : Set α) (t : Set β)
  证明: calc
    s subseteq e.symm '' t ↔ e.symm.symm '' s subseteq t := by rw [e.symm.symm_image_subset]
    _ ↔ e '' s subseteq t := by rw [e.symm_symm]

@[simp]
-/
protected theorem subset_symm_image {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    s subseteq e.symm '' t ↔ e '' s subseteq t :=
  calc
    s subseteq e.symm '' t ↔ e.symm.symm '' s subseteq t := by rw [e.symm.symm_image_subset]
    _ ↔ e '' s subseteq t := by rw [e.symm_symm]

@[simp]
/--
theorem `symm_image_image` / 定理 `symm_image_image`

English:
theorem symm_image_image
  given: {α β} (e : α ≃ β) (s : Set α)
  statement: e.symm '' e '' s = s
  proof: e.leftInverse_symm.image_image s

中文:
定理 symm_image_image
  条件: {α β} (e : α ≃ β) (s : Set α)
  结论: e.symm '' e '' s = s
  证明: e.leftInverse_symm.image_image s

Depends on / 依赖: e.leftInverse_symm.image_image, image_image, leftInverse_symm
-/
theorem symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' e '' s = s :=
  e.leftInverse_symm.image_image s

/--
theorem `eq_image_iff_symm_image_eq` / 定理 `eq_image_iff_symm_image_eq`

English:
theorem eq_image_iff_symm_image_eq
  given: {α β} (e : α ≃ β) (s : Set α) (t : Set β)
  proof: (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp]

中文:
定理 eq_image_iff_symm_image_eq
  条件: {α β} (e : α ≃ β) (s : Set α) (t : Set β)
  证明: (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp]

Depends on / 依赖: e.symm.injective.image_injective.eq_iff, e.symm_image_image, eq_iff, image_injective, injective, symm_image_image
-/
theorem eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    t = e '' s ↔ e.symm '' t = s :=
  (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp]
/--
theorem `image_symm_image` / 定理 `image_symm_image`

English:
theorem image_symm_image
  given: {α β} (e : α ≃ β) (s : Set β)
  statement: e '' e.symm '' s = s
  proof: e.symm.symm_image_image s

@[simp]

中文:
定理 image_symm_image
  条件: {α β} (e : α ≃ β) (s : Set β)
  结论: e '' e.symm '' s = s
  证明: e.symm.symm_image_image s

@[simp]

Depends on / 依赖: e.symm.symm_image_image, symm_image_image
-/
theorem image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp]
/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  given: {α β} (e : α ≃ β) (s : Set β)
  statement: e '' e ⁻¹' s = s
  proof: e.surjective.image_preimage s

@[simp]

中文:
定理 image_preimage
  条件: {α β} (e : α ≃ β) (s : Set β)
  结论: e '' e ⁻¹' s = s
  证明: e.surjective.image_preimage s

@[simp]

Depends on / 依赖: e.surjective.image_preimage, image_preimage, surjective
-/
theorem image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' e ⁻¹' s = s :=
  e.surjective.image_preimage s

@[simp]
/--
theorem `preimage_image` / 定理 `preimage_image`

English:
theorem preimage_image
  given: {α β} (e : α ≃ β) (s : Set α)
  statement: e ⁻¹' e '' s = s
  proof: e.injective.preimage_image s

中文:
定理 preimage_image
  条件: {α β} (e : α ≃ β) (s : Set α)
  结论: e ⁻¹' e '' s = s
  证明: e.injective.preimage_image s

Depends on / 依赖: e.injective.preimage_image, injective, preimage_image
-/
theorem preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' e '' s = s :=
  e.injective.preimage_image s

/--
theorem `image_compl` / 定理 `image_compl`

English:
theorem image_compl
  given: {α β} (f : Equiv α β) (s : Set α)
  statement: f '' sᶜ = (f '' s)ᶜ
  proof: image_compl_eq f.bijective

@[simp]

中文:
定理 image_compl
  条件: {α β} (f : Equiv α β) (s : Set α)
  结论: f '' sᶜ = (f '' s)ᶜ
  证明: image_compl_eq f.bijective

@[simp]
-/
protected theorem image_compl {α β} (f : Equiv α β) (s : Set α) : f '' sᶜ = (f '' s)ᶜ :=
  image_compl_eq f.bijective

@[simp]
/--
theorem `symm_preimage_preimage` / 定理 `symm_preimage_preimage`

English:
theorem symm_preimage_preimage
  given: {α β} (e : α ≃ β) (s : Set β)
  statement: e.symm ⁻¹' e ⁻¹' s = s
  proof: e.rightInverse_symm.preimage_preimage s

@[simp]

中文:
定理 symm_preimage_preimage
  条件: {α β} (e : α ≃ β) (s : Set β)
  结论: e.symm ⁻¹' e ⁻¹' s = s
  证明: e.rightInverse_symm.preimage_preimage s

@[simp]

Depends on / 依赖: e.rightInverse_symm.preimage_preimage, preimage_preimage, rightInverse_symm
-/
theorem symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s :=
  e.rightInverse_symm.preimage_preimage s

@[simp]
/--
theorem `preimage_symm_preimage` / 定理 `preimage_symm_preimage`

English:
theorem preimage_symm_preimage
  given: {α β} (e : α ≃ β) (s : Set α)
  statement: e ⁻¹' e.symm ⁻¹' s = s
  proof: e.leftInverse_symm.preimage_preimage s

中文:
定理 preimage_symm_preimage
  条件: {α β} (e : α ≃ β) (s : Set α)
  结论: e ⁻¹' e.symm ⁻¹' s = s
  证明: e.leftInverse_symm.preimage_preimage s

Depends on / 依赖: e.leftInverse_symm.preimage_preimage, leftInverse_symm, preimage_preimage
-/
theorem preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' e.symm ⁻¹' s = s :=
  e.leftInverse_symm.preimage_preimage s

/--
theorem `preimage_subset` / 定理 `preimage_subset`

English:
theorem preimage_subset
  given: {α β} (e : α ≃ β) (s t : Set β)
  statement: e ⁻¹' s subseteq e ⁻¹' t ↔ s subseteq t
  proof: e.surjective.preimage_subset_preimage_iff

中文:
定理 preimage_subset
  条件: {α β} (e : α ≃ β) (s t : Set β)
  结论: e ⁻¹' s subseteq e ⁻¹' t ↔ s subseteq t
  证明: e.surjective.preimage_subset_preimage_iff

Depends on / 依赖: e.surjective.preimage_subset_preimage_iff, preimage_subset_preimage_iff, surjective
-/
theorem preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s subseteq e ⁻¹' t ↔ s subseteq t :=
  e.surjective.preimage_subset_preimage_iff

/--
theorem `image_subset` / 定理 `image_subset`

English:
theorem image_subset
  given: {α β} (e : α ≃ β) (s t : Set α)
  statement: e '' s subseteq e '' t ↔ s subseteq t
  proof: image_subset_image_iff e.injective

@[simp]

中文:
定理 image_subset
  条件: {α β} (e : α ≃ β) (s t : Set α)
  结论: e '' s subseteq e '' t ↔ s subseteq t
  证明: image_subset_image_iff e.injective

@[simp]

Depends on / 依赖: e.injective, image_subset_image_iff, injective
-/
theorem image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s subseteq e '' t ↔ s subseteq t :=
  image_subset_image_iff e.injective

@[simp]
/--
theorem `image_eq_iff_eq` / 定理 `image_eq_iff_eq`

English:
theorem image_eq_iff_eq
  given: {α β} (e : α ≃ β) (s t : Set α)
  statement: e '' s = e '' t ↔ s = t
  proof: image_eq_image e.injective

中文:
定理 image_eq_iff_eq
  条件: {α β} (e : α ≃ β) (s t : Set α)
  结论: e '' s = e '' t ↔ s = t
  证明: image_eq_image e.injective

Depends on / 依赖: e.injective, image_eq_image, injective
-/
theorem image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t :=
  image_eq_image e.injective

/--
theorem `preimage_eq_iff_eq_image` / 定理 `preimage_eq_iff_eq_image`

English:
theorem preimage_eq_iff_eq_image
  given: {α β} (e : α ≃ β) (s t)
  statement: e ⁻¹' s = t ↔ s = e '' t
  proof: Set.preimage_eq_iff_eq_image e.bijective

中文:
定理 preimage_eq_iff_eq_image
  条件: {α β} (e : α ≃ β) (s t)
  结论: e ⁻¹' s = t ↔ s = e '' t
  证明: Set.preimage_eq_iff_eq_image e.bijective

Depends on / 依赖: Set.preimage_eq_iff_eq_image, bijective, e.bijective, preimage_eq_iff_eq_image
-/
theorem preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' t :=
  Set.preimage_eq_iff_eq_image e.bijective

/--
theorem `eq_preimage_iff_image_eq` / 定理 `eq_preimage_iff_image_eq`

English:
theorem eq_preimage_iff_image_eq
  given: {α β} (e : α ≃ β) (s t)
  statement: s = e ⁻¹' t ↔ e '' s = t
  proof: Set.eq_preimage_iff_image_eq e.bijective

中文:
定理 eq_preimage_iff_image_eq
  条件: {α β} (e : α ≃ β) (s t)
  结论: s = e ⁻¹' t ↔ e '' s = t
  证明: Set.eq_preimage_iff_image_eq e.bijective

Depends on / 依赖: Set.eq_preimage_iff_image_eq, bijective, e.bijective, eq_preimage_iff_image_eq
-/
theorem eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = t :=
  Set.eq_preimage_iff_image_eq e.bijective

/--
lemma `setOfPred_apply_symm_eq_image_setOfPred` / 引理 `setOfPred_apply_symm_eq_image_setOfPred`

English:
lemma setOfPred_apply_symm_eq_image_setOfPred
  given: {α β} (e : α ≃ β) (p : α -> Prop)
  proof: by
  rw [Equiv.image_eq_preimage_symm]; rw [preimage_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_apply_symm_eq_image_setOf := setOfPred_apply_symm_eq_image_setOfPred

@[simp]

中文:
引理 setOfPred_apply_symm_eq_image_setOfPred
  条件: {α β} (e : α ≃ β) (p : α -> 命题)
  证明: by
  rw [Equiv.image_eq_preimage_symm]; rw [preimage_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_apply_symm_eq_image_setOf := setOfPred_apply_symm_eq_image_setOfPred

@[simp]

Depends on / 依赖: Equiv.image_eq_preimage_symm, image_eq_preimage_symm, preimage_ofPred_eq
-/
lemma setOfPred_apply_symm_eq_image_setOfPred {α β} (e : α ≃ β) (p : α -> Prop) :
    {b | p (e.symm b)} = e '' {a | p a} := by
  rw [Equiv.image_eq_preimage_symm]; rw [preimage_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_apply_symm_eq_image_setOf := setOfPred_apply_symm_eq_image_setOfPred

@[simp]
/--
theorem `prod_assoc_preimage` / 定理 `prod_assoc_preimage`

English:
theorem prod_assoc_preimage
  given: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  proof: by
  ext
  simp [and_assoc]

@[simp]

中文:
定理 prod_assoc_preimage
  条件: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  证明: by
  ext
  simp [and_assoc]

@[simp]

Depends on / 依赖: and_assoc
-/
theorem prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  ext
  simp [and_assoc]

@[simp]
/--
theorem `prod_assoc_symm_preimage` / 定理 `prod_assoc_symm_preimage`

English:
theorem prod_assoc_symm_preimage
  given: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  proof: by
  ext
  simp [and_assoc]

中文:
定理 prod_assoc_symm_preimage
  条件: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  证明: by
  ext
  simp [and_assoc]

Depends on / 依赖: and_assoc
-/
theorem prod_assoc_symm_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  ext
  simp [and_assoc]

-- `@[simp]` doesn't like these lemmas, as it uses `Set.image_congr'` to turn `Equiv.prodAssoc`
-- into a lambda expression and then unfold it.
/--
theorem `prod_assoc_image` / 定理 `prod_assoc_image`

English:
theorem prod_assoc_image
  given: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  proof: by
  simpa only [Equiv.image_eq_preimage_symm] using prod_assoc_symm_preimage

中文:
定理 prod_assoc_image
  条件: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  证明: by
  simpa only [Equiv.image_eq_preimage_symm] using prod_assoc_symm_preimage

Depends on / 依赖: Equiv.image_eq_preimage_symm, image_eq_preimage_symm, prod_assoc_symm_preimage
-/
theorem prod_assoc_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ '' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  simpa only [Equiv.image_eq_preimage_symm] using prod_assoc_symm_preimage

/--
theorem `prod_assoc_symm_image` / 定理 `prod_assoc_symm_image`

English:
theorem prod_assoc_symm_image
  given: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  proof: by
  simpa only [Equiv.image_eq_preimage_symm] using! prod_assoc_preimage

中文:
定理 prod_assoc_symm_image
  条件: {α β γ} {s : Set α} {t : Set β} {u : Set γ}
  证明: by
  simpa only [Equiv.image_eq_preimage_symm] using! prod_assoc_preimage

Depends on / 依赖: Equiv.image_eq_preimage_symm, image_eq_preimage_symm, prod_assoc_preimage
-/
theorem prod_assoc_symm_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm '' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  simpa only [Equiv.image_eq_preimage_symm] using! prod_assoc_preimage

/--
Definition of `setProdEquivSigma` / `setProdEquivSigma` 的定义

English:
definition setProdEquivSigma
  signature: {α β : Type*} (s : Set (α × β))
  body: ⟨x.1.1, x.1.2, by simp⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩

中文:
定义 setProdEquivSigma
  签名: {α β : 类型} (s : Set (α × β))
  定义体: ⟨x.1.1, x.1.2, by simp⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
-/
def setProdEquivSigma {α β : Type*} (s : Set (α × β)) :
    s ≃ Σ x : α, { y : β | (x, y) in s } where
  toFun x := ⟨x.1.1, x.1.2, by simp⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩

/-- The subtypes corresponding to equal sets are equivalent. -/
@[simps! apply symm_apply]
/--
Definition of `setCongr` / `setCongr` 的定义

English:
definition setCongr
  signature: {α : Type*} {s t : Set α} (h : s = t)
  body: subtypeEquivProp h ▸ rfl

中文:
定义 setCongr
  签名: {α : 类型} {s t : Set α} (h : s = t)
  定义体: subtypeEquivProp h ▸ rfl

Depends on / 依赖: subtypeEquivProp
-/
def setCongr {α : Type*} {s t : Set α} (h : s = t) : s ≃ t :=
subtypeEquivProp h ▸ rfl

-- We could construct this using `Equiv.Set.image e s e.injective`,
-- but this definition provides an explicit inverse.
/-- A set is equivalent to its image under an equivalence.
-/
@[simps]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: {α β : Type*} (e : α ≃ β) (s : Set α)
  body: ⟨e x.1, by simp⟩
  invFun y :=
    ⟨e.symm y.1, by
      rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
      simpa using m⟩
  left_inv x := by simp
  right_inv y := by simp

中文:
定义 image
  签名: {α β : 类型} (e : α ≃ β) (s : Set α)
  定义体: ⟨e x.1, by simp⟩
  invFun y :=
    ⟨e.symm y.1, by
      rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
      simpa using m⟩
  left_inv x := by simp
  right_inv y := by simp
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

/--
lemma `image_monotone` / 引理 `image_monotone`

English:
lemma image_monotone
  given: (hs : Monotone e)
  statement: Monotone (e.image s)
  proof: hs.comp (Subtype.mono_coe _)

中文:
引理 image_monotone
  条件: (hs : Monotone e)
  结论: Monotone (e.image s)
  证明: hs.comp (Subtype.mono_coe _)

Depends on / 依赖: Subtype, Subtype.mono_coe, hs.comp, mono_coe
-/
lemma image_monotone (hs : Monotone e) : Monotone (e.image s) :=
  hs.comp (Subtype.mono_coe _)

/--
lemma `image_antitone` / 引理 `image_antitone`

English:
lemma image_antitone
  given: (hs : Antitone e)
  statement: Antitone (e.image s)
  proof: hs.comp_monotone (Subtype.mono_coe _)

中文:
引理 image_antitone
  条件: (hs : Antitone e)
  结论: Antitone (e.image s)
  证明: hs.comp_monotone (Subtype.mono_coe _)

Depends on / 依赖: Subtype, Subtype.mono_coe, comp_monotone, hs.comp_monotone, mono_coe
-/
lemma image_antitone (hs : Antitone e) : Antitone (e.image s) :=
  hs.comp_monotone (Subtype.mono_coe _)

/--
lemma `image_strictMono` / 引理 `image_strictMono`

English:
lemma image_strictMono
  given: (hs : StrictMono e)
  statement: StrictMono (e.image s)
  proof: hs.comp (Subtype.strictMono_coe _)

中文:
引理 image_strictMono
  条件: (hs : StrictMono e)
  结论: StrictMono (e.image s)
  证明: hs.comp (Subtype.strictMono_coe _)

Depends on / 依赖: Subtype, Subtype.strictMono_coe, hs.comp, strictMono_coe
-/
lemma image_strictMono (hs : StrictMono e) : StrictMono (e.image s) :=
  hs.comp (Subtype.strictMono_coe _)

/--
lemma `image_strictAnti` / 引理 `image_strictAnti`

English:
lemma image_strictAnti
  given: (hs : StrictAnti e)
  statement: StrictAnti (e.image s)
  proof: hs.comp_strictMono (Subtype.strictMono_coe _)

中文:
引理 image_strictAnti
  条件: (hs : StrictAnti e)
  结论: StrictAnti (e.image s)
  证明: hs.comp_strictMono (Subtype.strictMono_coe _)

Depends on / 依赖: Subtype, Subtype.strictMono_coe, comp_strictMono, hs.comp_strictMono, strictMono_coe
-/
lemma image_strictAnti (hs : StrictAnti e) : StrictAnti (e.image s) :=
  hs.comp_strictMono (Subtype.strictMono_coe _)

end order

namespace Set

/-- `univ α` is equivalent to `α`. -/
@[simps apply symm_apply]
/--
Definition of `univ` / `univ` 的定义

English:
definition univ
  signature: (α)
  body: ⟨Subtype.val, fun a => ⟨a, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩

中文:
定义 univ
  签名: (α)
  定义体: ⟨Subtype.val, fun a => ⟨a, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩
-/
protected def univ (α) : @univ α ≃ α :=
  ⟨Subtype.val, fun a => ⟨a, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: (α)
  body: equivEmpty _

中文:
定义 empty
  签名: (α)
  定义体: equivEmpty _
-/
protected def empty (α) : (∅ : Set α) ≃ Empty :=
  equivEmpty _

/--
Definition of `pempty` / `pempty` 的定义

English:
definition pempty
  signature: (α)
  body: equivPEmpty _

中文:
定义 pempty
  签名: (α)
  定义体: equivPEmpty _
-/
protected def pempty (α) : (∅ : Set α) ≃ PEmpty :=
  equivPEmpty _

/--
Definition of `union'` / `union'` 的定义

English:
definition union'
  signature: {α} {s t : Set α} (p : α -> Prop) [DecidablePred p] (hs : forall x in s, p x)
  body: if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩
    else Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩
  invFun o :=
    match o with
    | Sum.inl x => ⟨x, Or.inl x.2⟩
    | Sum.inr x => ⟨x, Or.inr x.2⟩
  left_inv := fun ⟨x, h'⟩ => by by_cases h : p x <;> simp [h]
  righ

中文:
定义 union'
  签名: {α} {s t : Set α} (p : α -> 命题) [DecidablePred p] (hs : 对任意 x in s, p x)
  定义体: if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩
    else Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩
  invFun o :=
    match o with
    | Sum.inl x => ⟨x, Or.inl x.2⟩
    | Sum.inr x => ⟨x, Or.inr x.2⟩
  left_inv := fun ⟨x, h'⟩ => by by_cases h : p x <;> simp [h]
  righ
-/
protected def union' {α} {s t : Set α} (p : α -> Prop) [DecidablePred p] (hs : forall x in s, p x)
    (ht : forall x in t, ¬p x) : (s union t : Set α) ≃ s oplus t where
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

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  body: Set.union' (fun x => x in s) (fun _ => id) fun _ xt xs => Set.disjoint_left.mp H xs xt

中文:
定义 union
  签名: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  定义体: Set.union' (fun x => x in s) (fun _ => id) fun _ xt xs => Set.disjoint_left.mp H xs xt
-/
protected def union {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t) :
    (s union t : Set α) ≃ s oplus t :=
  Set.union' (fun x => x in s) (fun _ => id) fun _ xt xs => Set.disjoint_left.mp H xs xt

/--
theorem `union_apply_left` / 定理 `union_apply_left`

English:
theorem union_apply_left
  statement: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  proof: dif_pos ha

中文:
定理 union_apply_left
  结论: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  证明: dif_pos ha

Depends on / 依赖: dif_pos
-/
theorem union_apply_left {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
    {a : (s union t : Set α)} (ha : ↑a in s) : Equiv.Set.union H a = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha

/--
theorem `union_apply_right` / 定理 `union_apply_right`

English:
theorem union_apply_right
  statement: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  proof: dif_neg fun h => Set.disjoint_left.mp H h ha

@[simp]

中文:
定理 union_apply_right
  结论: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  证明: dif_neg fun h => Set.disjoint_left.mp H h ha

@[simp]

Depends on / 依赖: Set.disjoint_left.mp, dif_neg, disjoint_left
-/
theorem union_apply_right {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
    {a : (s union t : Set α)} (ha : ↑a in t) : Equiv.Set.union H a = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => Set.disjoint_left.mp H h ha

@[simp]
/--
theorem `union_symm_apply_left` / 定理 `union_symm_apply_left`

English:
theorem union_symm_apply_left
  statement: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  proof: rfl

@[simp]

中文:
定理 union_symm_apply_left
  结论: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  证明: rfl

@[simp]
-/
theorem union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
    (a : s) : (Equiv.Set.union H).symm (Sum.inl a) = ⟨a, by simp⟩ :=
  rfl

@[simp]
/--
theorem `union_symm_apply_right` / 定理 `union_symm_apply_right`

English:
theorem union_symm_apply_right
  statement: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  proof: rfl

中文:
定理 union_symm_apply_right
  结论: {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
  证明: rfl
-/
theorem union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x in s] (H : Disjoint s t)
    (a : t) : (Equiv.Set.union H).symm (Sum.inr a) = ⟨a, by simp⟩ :=
  rfl

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: {α} (a : α)
  body: ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    subst x
    rfl, fun ⟨⟩ => rfl⟩

中文:
定义 singleton
  签名: {α} (a : α)
  定义体: ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    subst x
    rfl, fun ⟨⟩ => rfl⟩
-/
protected def singleton {α} (a : α) : ({a} : Set α) ≃ PUnit.{u} :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    subst x
    rfl, fun ⟨⟩ => rfl⟩

/--
lemma `_root_.Equiv.strictMono_setCongr` / 引理 `_root_.Equiv.strictMono_setCongr`

English:
lemma _root_.Equiv.strictMono_setCongr
  given: {α : Type*} [Preorder α] {S T : Set α} (h : S = T)
  proof: fun _ _ => id

中文:
引理 _root_.Equiv.strictMono_setCongr
  条件: {α : 类型} [Preorder α] {S T : Set α} (h : S = T)
  证明: fun _ _ => id
-/
lemma _root_.Equiv.strictMono_setCongr {α : Type*} [Preorder α] {S T : Set α} (h : S = T) :
    StrictMono (setCongr h) := fun _ _ => id

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Equiv.strictMono_setCongr := Equiv.strictMono_setCongr

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  body: calc
    (insert a s : Set α) ≃ ↥(s union {a}) := Equiv.setCongr (by simp)
_ ≃ s oplus ({a} : Set α) := Equiv.Set.union by simpa
    _ ≃ s oplus PUnit.{u + 1} := sumCongr (Equiv.refl _) (Equiv.Set.singleton _)

@[simp]

中文:
定义 insert
  签名: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  定义体: calc
    (insert a s : Set α) ≃ ↥(s union {a}) := Equiv.setCongr (by simp)
_ ≃ s oplus ({a} : Set α) := Equiv.Set.union by simpa
    _ ≃ s oplus PUnit.{u + 1} := sumCongr (Equiv.refl _) (Equiv.Set.singleton _)

@[simp]
-/
protected def insert {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s) :
    (insert a s : Set α) ≃ s oplus PUnit.{u + 1} :=
  calc
    (insert a s : Set α) ≃ ↥(s union {a}) := Equiv.setCongr (by simp)
_ ≃ s oplus ({a} : Set α) := Equiv.Set.union by simpa
    _ ≃ s oplus PUnit.{u + 1} := sumCongr (Equiv.refl _) (Equiv.Set.singleton _)

@[simp]
/--
theorem `insert_symm_apply_inl` / 定理 `insert_symm_apply_inl`

English:
theorem insert_symm_apply_inl
  statement: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  proof: rfl

@[simp]

中文:
定理 insert_symm_apply_inl
  结论: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  证明: rfl

@[simp]
-/
theorem insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
    (b : s) : (Equiv.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩ :=
  rfl

@[simp]
/--
theorem `insert_symm_apply_inr` / 定理 `insert_symm_apply_inr`

English:
theorem insert_symm_apply_inr
  statement: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  proof: rfl

@[simp]

中文:
定理 insert_symm_apply_inr
  结论: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  证明: rfl

@[simp]
-/
theorem insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
    (b : PUnit.{u + 1}) : (Equiv.Set.insert H).symm (Sum.inr b) = ⟨a, Or.inl rfl⟩ :=
  rfl

@[simp]
/--
theorem `insert_apply_left` / 定理 `insert_apply_left`

English:
theorem insert_apply_left
  given: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  proof: (Equiv.Set.insert H).eq_symm_apply.1 rfl

@[simp]

中文:
定理 insert_apply_left
  条件: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s)
  证明: (Equiv.Set.insert H).eq_symm_apply.1 rfl

@[simp]

Depends on / 依赖: Equiv.Set.insert, eq_symm_apply, insert
-/
theorem insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s) :
    Equiv.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit :=
  (Equiv.Set.insert H).eq_symm_apply.1 rfl

@[simp]
/--
theorem `insert_apply_right` / 定理 `insert_apply_right`

English:
theorem insert_apply_right
  given: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s) (b : s)
  proof: (Equiv.Set.insert H).eq_symm_apply.1 rfl

中文:
定理 insert_apply_right
  条件: {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s) (b : s)
  证明: (Equiv.Set.insert H).eq_symm_apply.1 rfl

Depends on / 依赖: Equiv.Set.insert, eq_symm_apply, insert
-/
theorem insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· in s)] {a : α} (H : a ∉ s) (b : s) :
    Equiv.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b :=
  (Equiv.Set.insert H).eq_symm_apply.1 rfl

/--
Definition of `sumCompl` / `sumCompl` 的定义

English:
definition sumCompl
  signature: {α} (s : Set α) [DecidablePred (· in s)]
  body: Equiv.sumCompl (· in s)

@[simp]

中文:
定义 sumCompl
  签名: {α} (s : Set α) [DecidablePred (· in s)]
  定义体: Equiv.sumCompl (· in s)

@[simp]
-/
protected def sumCompl {α} (s : Set α) [DecidablePred (· in s)] : s oplus (sᶜ : Set α) ≃ α :=
  Equiv.sumCompl (· in s)

@[simp]
/--
theorem `sumCompl_apply_inl` / 定理 `sumCompl_apply_inl`

English:
theorem sumCompl_apply_inl
  given: {α : Type u} (s : Set α) [DecidablePred (· in s)] (x : s)
  proof: rfl

@[simp]

中文:
定理 sumCompl_apply_inl
  条件: {α : 类型u} (s : Set α) [DecidablePred (· in s)] (x : s)
  证明: rfl

@[simp]
-/
theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· in s)] (x : s) :
    Equiv.Set.sumCompl s (Sum.inl x) = x :=
  rfl

@[simp]
/--
theorem `sumCompl_apply_inr` / 定理 `sumCompl_apply_inr`

English:
theorem sumCompl_apply_inr
  given: {α : Type u} (s : Set α) [DecidablePred (· in s)] (x : (sᶜ : Set α))
  proof: rfl

中文:
定理 sumCompl_apply_inr
  条件: {α : 类型u} (s : Set α) [DecidablePred (· in s)] (x : (sᶜ : Set α))
  证明: rfl
-/
theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· in s)] (x : (sᶜ : Set α)) :
    Equiv.Set.sumCompl s (Sum.inr x) = x :=
  rfl

/--
theorem `sumCompl_symm_apply_of_mem` / 定理 `sumCompl_symm_apply_of_mem`

English:
theorem sumCompl_symm_apply_of_mem
  statement: {α : Type u} {s : Set α} [DecidablePred (· in s)] {x : α}
  proof: sumCompl_symm_apply_of_pos hx

中文:
定理 sumCompl_symm_apply_of_mem
  结论: {α : 类型u} {s : Set α} [DecidablePred (· in s)] {x : α}
  证明: sumCompl_symm_apply_of_pos hx

Depends on / 依赖: sumCompl_symm_apply_of_pos
-/
theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· in s)] {x : α}
    (hx : x in s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ :=
  sumCompl_symm_apply_of_pos hx

/--
theorem `sumCompl_symm_apply_of_notMem` / 定理 `sumCompl_symm_apply_of_notMem`

English:
theorem sumCompl_symm_apply_of_notMem
  statement: {α : Type u} {s : Set α} [DecidablePred (· in s)] {x : α}
  proof: sumCompl_symm_apply_of_neg hx

@[simp]

中文:
定理 sumCompl_symm_apply_of_notMem
  结论: {α : 类型u} {s : Set α} [DecidablePred (· in s)] {x : α}
  证明: sumCompl_symm_apply_of_neg hx

@[simp]

Depends on / 依赖: sumCompl_symm_apply_of_neg
-/
theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· in s)] {x : α}
    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ :=
  sumCompl_symm_apply_of_neg hx

@[simp]
/--
theorem `sumCompl_symm_apply` / 定理 `sumCompl_symm_apply`

English:
theorem sumCompl_symm_apply
  given: {α : Type*} {s : Set α} [DecidablePred (· in s)] (x : s)
  proof: sumCompl_symm_apply_pos x

@[simp]

中文:
定理 sumCompl_symm_apply
  条件: {α : 类型} {s : Set α} [DecidablePred (· in s)] (x : s)
  证明: sumCompl_symm_apply_pos x

@[simp]

Depends on / 依赖: sumCompl_symm_apply_pos
-/
theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· in s)] (x : s) :
    (Equiv.Set.sumCompl s).symm x = Sum.inl x :=
  sumCompl_symm_apply_pos x

@[simp]
/--
theorem `sumCompl_symm_apply_compl` / 定理 `sumCompl_symm_apply_compl`

English:
theorem sumCompl_symm_apply_compl
  statement: {α : Type*} {s : Set α} [DecidablePred (· in s)]
  proof: sumCompl_symm_apply_neg x

中文:
定理 sumCompl_symm_apply_compl
  结论: {α : 类型} {s : Set α} [DecidablePred (· in s)]
  证明: sumCompl_symm_apply_neg x

Depends on / 依赖: sumCompl_symm_apply_neg
-/
theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· in s)]
    (x : (sᶜ : Set α)) : (Equiv.Set.sumCompl s).symm x = Sum.inr x :=
  sumCompl_symm_apply_neg x

/--
Definition of `sumDiffSubset` / `sumDiffSubset` 的定义

English:
definition sumDiffSubset
  signature: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  body: calc
    s oplus (t \ s : Set α) ≃ (s union t \ s : Set α) :=
      (Equiv.Set.union disjoint_sdiff_self_right).symm
    _ ≃ t := Equiv.setCongr (by simp [union_sdiff_self, union_eq_self_of_subset_left h])

@[simp]

中文:
定义 sumDiffSubset
  签名: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  定义体: calc
    s oplus (t \ s : Set α) ≃ (s union t \ s : Set α) :=
      (Equiv.Set.union disjoint_sdiff_self_right).symm
    _ ≃ t := Equiv.setCongr (by simp [union_sdiff_self, union_eq_self_of_subset_left h])

@[simp]
-/
protected def sumDiffSubset {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)] :
    s oplus (t \ s : Set α) ≃ t :=
  calc
    s oplus (t \ s : Set α) ≃ (s union t \ s : Set α) :=
      (Equiv.Set.union disjoint_sdiff_self_right).symm
    _ ≃ t := Equiv.setCongr (by simp [union_sdiff_self, union_eq_self_of_subset_left h])

@[simp]
/--
theorem `sumDiffSubset_apply_inl` / 定理 `sumDiffSubset_apply_inl`

English:
theorem sumDiffSubset_apply_inl
  given: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)] (x : s)
  proof: rfl

@[simp]

中文:
定理 sumDiffSubset_apply_inl
  条件: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)] (x : s)
  证明: rfl

@[simp]
-/
theorem sumDiffSubset_apply_inl {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)] (x : s) :
    Equiv.Set.sumDiffSubset h (Sum.inl x) = inclusion h x :=
  rfl

@[simp]
/--
theorem `sumDiffSubset_apply_inr` / 定理 `sumDiffSubset_apply_inr`

English:
theorem sumDiffSubset_apply_inr
  statement: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  proof: rfl

中文:
定理 sumDiffSubset_apply_inr
  结论: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  证明: rfl
-/
theorem sumDiffSubset_apply_inr {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
    (x : (t \ s : Set α)) : Equiv.Set.sumDiffSubset h (Sum.inr x) = inclusion sdiff_subset x :=
  rfl

/--
theorem `sumDiffSubset_symm_apply_of_mem` / 定理 `sumDiffSubset_symm_apply_of_mem`

English:
theorem sumDiffSubset_symm_apply_of_mem
  statement: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  proof: by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inl, Set.inclusion_mk]

中文:
定理 sumDiffSubset_symm_apply_of_mem
  结论: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  证明: by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inl, Set.inclusion_mk]

Depends on / 依赖: Equiv.Set.sumDiffSubset, Set.inclusion_mk, apply_symm_apply, inclusion_mk, injective, sumDiffSubset, sumDiffSubset_apply_inl
-/
theorem sumDiffSubset_symm_apply_of_mem {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
    {x : t} (hx : x.1 in s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inl ⟨x, hx⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inl, Set.inclusion_mk]

/--
theorem `sumDiffSubset_symm_apply_of_notMem` / 定理 `sumDiffSubset_symm_apply_of_notMem`

English:
theorem sumDiffSubset_symm_apply_of_notMem
  statement: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  proof: by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inr]

中文:
定理 sumDiffSubset_symm_apply_of_notMem
  结论: {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
  证明: by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inr]

Depends on / 依赖: Equiv.Set.sumDiffSubset, apply_symm_apply, injective, sumDiffSubset, sumDiffSubset_apply_inr
-/
theorem sumDiffSubset_symm_apply_of_notMem {α} {s t : Set α} (h : s subseteq t) [DecidablePred (· in s)]
    {x : t} (hx : x.1 ∉ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inr]

/--
Definition of `unionSumInter` / `unionSumInter` 的定义

English:
definition unionSumInter
  signature: {α : Type u} (s t : Set α) [DecidablePred (· in s)]
  body: calc
    (s union t : Set α) oplus (s inter t : Set α)
      ≃ (s union t \ s : Set α) oplus (s inter t : Set α) := by rw [union_sdiff_self]
    _ ≃ (s oplus (t \ s : Set α)) oplus (s inter t : Set α) :=
      sumCongr (Set.union disjoint_sdiff_self_right) (Equiv.refl _)
    _ ≃ s oplus ((t \ s : Se

中文:
定义 unionSumInter
  签名: {α : 类型u} (s t : Set α) [DecidablePred (· in s)]
  定义体: calc
    (s union t : Set α) oplus (s inter t : Set α)
      ≃ (s union t \ s : Set α) oplus (s inter t : Set α) := by rw [union_sdiff_self]
    _ ≃ (s oplus (t \ s : Set α)) oplus (s inter t : Set α) :=
      sumCongr (Set.union disjoint_sdiff_self_right) (Equiv.refl _)
    _ ≃ s oplus ((t \ s : Se
-/
protected def unionSumInter {α : Type u} (s t : Set α) [DecidablePred (· in s)] :
    (s union t : Set α) oplus (s inter t : Set α) ≃ s oplus t :=
  calc
    (s union t : Set α) oplus (s inter t : Set α)
      ≃ (s union t \ s : Set α) oplus (s inter t : Set α) := by rw [union_sdiff_self]
    _ ≃ (s oplus (t \ s : Set α)) oplus (s inter t : Set α) :=
      sumCongr (Set.union disjoint_sdiff_self_right) (Equiv.refl _)
    _ ≃ s oplus ((t \ s : Set α) oplus (s inter t : Set α)) := sumAssoc _ _ _
    _ ≃ s oplus (t \ s union s inter t : Set α) :=
      sumCongr (Equiv.refl _)
        (by
          refine (Set.union' (· ∉ s) ?_ ?_).symm
          exacts [fun x hx => hx.2, fun x hx => not_not_intro hx.1])
    _ ≃ s oplus t := by
      { rw [(_ : t \ s union s inter t = t)]
        rw [union_comm]; rw [inter_comm]; rw [inter_union_sdiff] }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· in s)]
  body: subtypeEquiv e fun _ =>
not_congr
Iff.symm
          MapsTo.mem_iff (mapsTo_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.mapsTo_compl
              (surjOn_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.surjective, e.2⟩)
              e.1.injective)
  invFun e₁ :=
    Subtype.mk
     

中文:
定义 compl
  签名: {α : 类型u} {β : 类型v} {s : Set α} {t : Set β} [DecidablePred (· in s)]
  定义体: subtypeEquiv e fun _ =>
not_congr
Iff.symm
          MapsTo.mem_iff (mapsTo_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.mapsTo_compl
              (surjOn_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.surjective, e.2⟩)
              e.1.injective)
  invFun e₁ :=
    Subtype.mk
     
-/
protected def compl {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· in s)]
    [DecidablePred (· in t)] (e₀ : s ≃ t) :
    { e : α ≃ β // forall x : s, e x = e₀ x } ≃ ((sᶜ : Set α) ≃ (tᶜ : Set β)) where
  toFun e :=
    subtypeEquiv e fun _ =>
not_congr
Iff.symm
          MapsTo.mem_iff (mapsTo_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.mapsTo_compl
              (surjOn_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.surjective, e.2⟩)
              e.1.injective)
  invFun e₁ :=
    Subtype.mk
      (calc
        α ≃ s oplus (sᶜ : Set α) := (Set.sumCompl s).symm
        _ ≃ t oplus (tᶜ : Set β) := e₀.sumCongr e₁
        _ ≃ β := Set.sumCompl t)
      fun x => by
      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
        Set.sumCompl_symm_apply, Trans.trans]
  left_inv e := by
    ext x
    by_cases hx : x in s
    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
        trans_apply, Set.sumCompl_apply_inl, Trans.trans]
    · simp only [Set.sumCompl_symm_apply_of_notMem hx, Sum.map_inr, subtypeEquiv_apply,
        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Trans.trans]
  right_inv e :=
    Equiv.ext fun x => by
      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
        sumCongr_apply, Equiv.coe_trans, Subtype.coe_eta, Trans.trans,
        Set.sumCompl_symm_apply_compl]

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {α β} (s : Set α) (t : Set β)
  body: @subtypeProdEquivProd α β (· in s) (· in t)

中文:
定义 prod
  签名: {α β} (s : Set α) (t : Set β)
  定义体: @subtypeProdEquivProd α β (· in s) (· in t)
-/
protected def prod {α β} (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ s × t :=
  @subtypeProdEquivProd α β (· in s) (· in t)

/-- The set `Set.pi Set.univ s` is equivalent to `Π a, s a`. -/
@[simps]
/--
Definition of `univPi` / `univPi` 的定义

English:
definition univPi
  signature: {α : Type*} {β : α -> Type*} (s : forall a, Set (β a))
  body: ⟨(f : forall a, β a) a, f.2 a (mem_univ a)⟩
  invFun f := ⟨fun a => f a, fun a _ => (f a).2⟩

中文:
定义 univPi
  签名: {α : 类型} {β : α -> 类型} (s : 对任意 a, Set (β a))
  定义体: ⟨(f : forall a, β a) a, f.2 a (mem_univ a)⟩
  invFun f := ⟨fun a => f a, fun a _ => (f a).2⟩
-/
protected def univPi {α : Type*} {β : α -> Type*} (s : forall a, Set (β a)) :
    pi univ s ≃ forall a, s a where
  toFun f a := ⟨(f : forall a, β a) a, f.2 a (mem_univ a)⟩
  invFun f := ⟨fun a => f a, fun a _ => (f a).2⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def imageOfInjOn {α β} (f : α -> β) (s : Set α) (H : InjOn f s)
  body: ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p =>
    ⟨Classical.choose p.2, (Classical.choose_spec p.2).1⟩, fun ⟨_, h⟩ =>
    Subtype.ext
      (H (Classical.choose_spec (mem_image_of_mem f h)).1 h
        (Classical.choose_spec (mem_image_of_mem f h)).2),
    fun ⟨_, h⟩ => Subtype.ext (Classical.c

中文:
定义 noncomputable
  签名: def imageOfInjOn {α β} (f : α -> β) (s : Set α) (H : InjOn f s)
  定义体: ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p =>
    ⟨Classical.choose p.2, (Classical.choose_spec p.2).1⟩, fun ⟨_, h⟩ =>
    Subtype.ext
      (H (Classical.choose_spec (mem_image_of_mem f h)).1 h
        (Classical.choose_spec (mem_image_of_mem f h)).2),
    fun ⟨_, h⟩ => Subtype.ext (Classical.c
-/
protected noncomputable def imageOfInjOn {α β} (f : α -> β) (s : Set α) (H : InjOn f s) :
    s ≃ f '' s :=
  ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p =>
    ⟨Classical.choose p.2, (Classical.choose_spec p.2).1⟩, fun ⟨_, h⟩ =>
    Subtype.ext
      (H (Classical.choose_spec (mem_image_of_mem f h)).1 h
        (Classical.choose_spec (mem_image_of_mem f h)).2),
    fun ⟨_, h⟩ => Subtype.ext (Classical.choose_spec h).2⟩

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simps! apply]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def image {α β} (f : α -> β) (s : Set α) (H : Injective f)
  body: Equiv.Set.imageOfInjOn f s H.injOn

@[simp]

中文:
定义 noncomputable
  签名: def image {α β} (f : α -> β) (s : Set α) (H : Injective f)
  定义体: Equiv.Set.imageOfInjOn f s H.injOn

@[simp]
-/
protected noncomputable def image {α β} (f : α -> β) (s : Set α) (H : Injective f) : s ≃ f '' s :=
  Equiv.Set.imageOfInjOn f s H.injOn

@[simp]
/--
theorem `image_symm_apply` / 定理 `image_symm_apply`

English:
theorem image_symm_apply
  statement: {α β} (f : α -> β) (s : Set α) (H : Injective f) (x : α)
  proof: (Equiv.symm_apply_eq _).2 rfl

中文:
定理 image_symm_apply
  结论: {α β} (f : α -> β) (s : Set α) (H : Injective f) (x : α)
  证明: (Equiv.symm_apply_eq _).2 rfl
-/
protected theorem image_symm_apply {α β} (f : α -> β) (s : Set α) (H : Injective f) (x : α)
    (h : f x in f '' s) : (Set.image f s H).symm ⟨f x, h⟩ = ⟨x, H.mem_set_image.1 h⟩ :=
  (Equiv.symm_apply_eq _).2 rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `image_symm_preimage` / 定理 `image_symm_preimage`

English:
theorem image_symm_preimage
  given: {α β} {f : α -> β} (hf : Injective f) (u s : Set α)
  proof: by
  ext ⟨b, a, has, rfl⟩
  simp [hf.eq_iff]

中文:
定理 image_symm_preimage
  条件: {α β} {f : α -> β} (hf : Injective f) (u s : Set α)
  证明: by
  ext ⟨b, a, has, rfl⟩
  simp [hf.eq_iff]

Depends on / 依赖: eq_iff, hf.eq_iff
-/
theorem image_symm_preimage {α β} {f : α -> β} (hf : Injective f) (u s : Set α) :
    (fun x => (Set.image f s hf).symm x : f '' s -> α) ⁻¹' u = Subtype.val ⁻¹' f '' u := by
  ext ⟨b, a, has, rfl⟩
  simp [hf.eq_iff]

/-- If `α` is equivalent to `β`, then `Set α` is equivalent to `Set β`. -/
@[simps]
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {α β : Type*} (e : α ≃ β)
  body: ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

中文:
定义 congr
  签名: {α β : 类型} (e : α ≃ β)
  定义体: ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩
-/
protected def congr {α β : Type*} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

/--
Definition of `sep` / `sep` 的定义

English:
definition sep
  signature: {α : Type u} (s : Set α) (t : α -> Prop)
  body: (Equiv.subtypeSubtypeEquivSubtypeInter (· in s) t).symm

中文:
定义 sep
  签名: {α : 类型u} (s : Set α) (t : α -> 命题)
  定义体: (Equiv.subtypeSubtypeEquivSubtypeInter (· in s) t).symm
-/
protected def sep {α : Type u} (s : Set α) (t : α -> Prop) :
    ({ x in s | t x } : Set α) ≃ { x : s | t x } :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (· in s) t).symm

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: {α} (S : Set α)
  body: fun x : 𝒫 S => Subtype.val ⁻¹' (x : Set α)
  invFun := fun x : Set S => ⟨Subtype.val '' x, by rintro _ ⟨a : S, _, rfl⟩; exact a.2⟩
  left_inv x := by ext y; exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩
  right_inv x := by ext; simp

中文:
定义 powerset
  签名: {α} (S : Set α)
  定义体: fun x : 𝒫 S => Subtype.val ⁻¹' (x : Set α)
  invFun := fun x : Set S => ⟨Subtype.val '' x, by rintro _ ⟨a : S, _, rfl⟩; exact a.2⟩
  left_inv x := by ext y; exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩
  right_inv x := by ext; simp
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
/--
Definition of `rangeSplittingImageEquiv` / `rangeSplittingImageEquiv` 的定义

English:
definition rangeSplittingImageEquiv
  signature: {α β : Type*} (f : α -> β) (s : Set (range f))
  body: ⟨⟨f x, by simp⟩, by
      rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
      simpa [apply_rangeSplitting f] using m⟩
  invFun x := ⟨rangeSplitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩
  left_inv x := by
    rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
    simp [apply_rangeSplitting f]
  right_inv x := by simp [apply_rangeSplitting f]

中文:
定义 rangeSplittingImageEquiv
  签名: {α β : 类型} (f : α -> β) (s : Set (range f))
  定义体: ⟨⟨f x, by simp⟩, by
      rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
      simpa [apply_rangeSplitting f] using m⟩
  invFun x := ⟨rangeSplitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩
  left_inv x := by
    rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
    simp [apply_rangeSplitting f]
  right_inv x := by simp [apply_rangeSplitting f]

Depends on / 依赖: apply_rangeSplitting, invFun, left_inv, rangeSplitting, right_inv
-/
noncomputable def rangeSplittingImageEquiv {α β : Type*} (f : α -> β) (s : Set (range f)) :
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
/--
Definition of `rangeInl` / `rangeInl` 的定义

English:
definition rangeInl
  signature: (α β : Type*)
  body: ⟨.inl x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl

中文:
定义 rangeInl
  签名: (α β : 类型)
  定义体: ⟨.inl x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl

Depends on / 依赖: mem_range_self
-/
def rangeInl (α β : Type*) : Set.range (Sum.inl : α -> α oplus β) ≃ α where
  toFun
  | ⟨.inl x, _⟩ => x
| ⟨.inr _, h⟩ => False.elim by rcases h with ⟨x, h'⟩; cases h'
  invFun x := ⟨.inl x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl

/--
lemma `rangeInl_apply_inl` / 引理 `rangeInl_apply_inl`

English:
lemma rangeInl_apply_inl
  given: {α : Type*} (β : Type*) (x : α)
  proof: rfl

中文:
引理 rangeInl_apply_inl
  条件: {α : 类型} (β : 类型) (x : α)
  证明: rfl
-/
@[simp] lemma rangeInl_apply_inl {α : Type*} (β : Type*) (x : α) :
    (rangeInl α β) ⟨.inl x, mem_range_self _⟩ = x :=
  rfl

/-- Equivalence between the range of `Sum.inr : β → α ⊕ β` and `β`. -/
@[simps symm_apply_coe]
/--
Definition of `rangeInr` / `rangeInr` 的定义

English:
definition rangeInr
  signature: (α β : Type*)
  body: ⟨.inr x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl

中文:
定义 rangeInr
  签名: (α β : 类型)
  定义体: ⟨.inr x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl

Depends on / 依赖: mem_range_self
-/
def rangeInr (α β : Type*) : Set.range (Sum.inr : β -> α oplus β) ≃ β where
  toFun
| ⟨.inl _, h⟩ => False.elim by rcases h with ⟨x, h'⟩; cases h'
  | ⟨.inr x, _⟩ => x
  invFun x := ⟨.inr x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl

/--
lemma `rangeInr_apply_inr` / 引理 `rangeInr_apply_inr`

English:
lemma rangeInr_apply_inr
  given: (α : Type*) {β : Type*} (x : β)
  proof: rfl

中文:
引理 rangeInr_apply_inr
  条件: (α : 类型) {β : 类型} (x : β)
  证明: rfl
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
/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: {α β : Sort _} (f : α -> β) (f_inv : Nonempty α -> β -> α)
  body: ⟨f a, a, rfl⟩
  invFun b := f_inv b.2.nonempty b
  left_inv a := hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ =>
Subtype.ext show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha

中文:
定义 ofLeftInverse
  签名: {α β : Sort _} (f : α -> β) (f_inv : Nonempty α -> β -> α)
  定义体: ⟨f a, a, rfl⟩
  invFun b := f_inv b.2.nonempty b
  left_inv a := hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ =>
Subtype.ext show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha
-/
def ofLeftInverse {α β : Sort _} (f : α -> β) (f_inv : Nonempty α -> β -> α)
    (hf : forall h : Nonempty α, LeftInverse (f_inv h) f) :
    α ≃ range f where
  toFun a := ⟨f a, a, rfl⟩
  invFun b := f_inv b.2.nonempty b
  left_inv a := hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ =>
Subtype.ext show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha

/--
Definition of `ofLeftInverse'` / `ofLeftInverse'` 的定义

English:
abbreviation ofLeftInverse'
  signature: {α β : Sort _} (f : α -> β) (f_inv : β -> α) (hf : LeftInverse f_inv f)
  body: ofLeftInverse f (fun _ => f_inv) fun _ => hf

中文:
缩写 ofLeftInverse'
  签名: {α β : Sort _} (f : α -> β) (f_inv : β -> α) (hf : LeftInverse f_inv f)
  定义体: ofLeftInverse f (fun _ => f_inv) fun _ => hf

Depends on / 依赖: f_inv, ofLeftInverse
-/
abbrev ofLeftInverse' {α β : Sort _} (f : α -> β) (f_inv : β -> α) (hf : LeftInverse f_inv f) :
    α ≃ range f :=
  ofLeftInverse f (fun _ => f_inv) fun _ => hf

/-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
@[simps! apply]
/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: {α β} (f : α -> β) (hf : Injective f)
  body: Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf

中文:
定义 ofInjective
  签名: {α β} (f : α -> β) (hf : Injective f)
  定义体: Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf

Depends on / 依赖: Equiv.ofLeftInverse, Function, Function.invFun, Function.leftInverse_invFun, invFun, leftInverse_invFun, ofLeftInverse
-/
noncomputable def ofInjective {α β} (f : α -> β) (hf : Injective f) : α ≃ range f :=
  Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf

/--
theorem `apply_ofInjective_symm` / 定理 `apply_ofInjective_symm`

English:
theorem apply_ofInjective_symm
  given: {α β} {f : α -> β} (hf : Injective f) (b : range f)
  proof: Subtype.ext_iff.1 (ofInjective f hf).apply_symm_apply b

@[simp]

中文:
定理 apply_ofInjective_symm
  条件: {α β} {f : α -> β} (hf : Injective f) (b : range f)
  证明: Subtype.ext_iff.1 (ofInjective f hf).apply_symm_apply b

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, apply_symm_apply, ext_iff, ofInjective
-/
theorem apply_ofInjective_symm {α β} {f : α -> β} (hf : Injective f) (b : range f) :
    f ((ofInjective f hf).symm b) = b :=
Subtype.ext_iff.1 (ofInjective f hf).apply_symm_apply b

@[simp]
/--
theorem `ofInjective_symm_apply` / 定理 `ofInjective_symm_apply`

English:
theorem ofInjective_symm_apply
  given: {α β} {f : α -> β} (hf : Injective f) (a : α)
  proof: by
  apply (ofInjective f hf).injective
  simp

中文:
定理 ofInjective_symm_apply
  条件: {α β} {f : α -> β} (hf : Injective f) (a : α)
  证明: by
  apply (ofInjective f hf).injective
  simp

Depends on / 依赖: injective, ofInjective
-/
theorem ofInjective_symm_apply {α β} {f : α -> β} (hf : Injective f) (a : α) :
    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
  apply (ofInjective f hf).injective
  simp

/--
theorem `coe_ofInjective_symm` / 定理 `coe_ofInjective_symm`

English:
theorem coe_ofInjective_symm
  given: {α β} {f : α -> β} (hf : Injective f)
  proof: by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [apply_rangeSplitting f]

@[simp]

中文:
定理 coe_ofInjective_symm
  条件: {α β} {f : α -> β} (hf : Injective f)
  证明: by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [apply_rangeSplitting f]

@[simp]

Depends on / 依赖: apply_rangeSplitting
-/
theorem coe_ofInjective_symm {α β} {f : α -> β} (hf : Injective f) :
    ((ofInjective f hf).symm : range f -> α) = rangeSplitting f := by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [apply_rangeSplitting f]

@[simp]
/--
theorem `self_comp_ofInjective_symm` / 定理 `self_comp_ofInjective_symm`

English:
theorem self_comp_ofInjective_symm
  given: {α β} {f : α -> β} (hf : Injective f)
  proof: funext fun x => apply_ofInjective_symm hf x

中文:
定理 self_comp_ofInjective_symm
  条件: {α β} {f : α -> β} (hf : Injective f)
  证明: funext fun x => apply_ofInjective_symm hf x

Depends on / 依赖: apply_ofInjective_symm
-/
theorem self_comp_ofInjective_symm {α β} {f : α -> β} (hf : Injective f) :
    f ∘ (ofInjective f hf).symm = Subtype.val :=
  funext fun x => apply_ofInjective_symm hf x

/--
theorem `ofLeftInverse_eq_ofInjective` / 定理 `ofLeftInverse_eq_ofInjective`

English:
theorem ofLeftInverse_eq_ofInjective
  statement: {α β : Type*} (f : α -> β) (f_inv : Nonempty α -> β -> α)
  proof: by
  ext
  simp

中文:
定理 ofLeftInverse_eq_ofInjective
  结论: {α β : 类型} (f : α -> β) (f_inv : Nonempty α -> β -> α)
  证明: by
  ext
  simp
-/
theorem ofLeftInverse_eq_ofInjective {α β : Type*} (f : α -> β) (f_inv : Nonempty α -> β -> α)
    (hf : forall h : Nonempty α, LeftInverse (f_inv h) f) :
    ofLeftInverse f f_inv hf =
      ofInjective f ((isEmpty_or_nonempty α).elim (fun _ _ _ _ => Subsingleton.elim _ _)
        (fun h => (hf h).injective)) := by
  ext
  simp

/--
theorem `ofLeftInverse'_eq_ofInjective` / 定理 `ofLeftInverse'_eq_ofInjective`

English:
theorem ofLeftInverse'_eq_ofInjective
  statement: {α β : Type*} (f : α -> β) (f_inv : β -> α)
  proof: by
  ext
  simp

中文:
定理 ofLeftInverse'_eq_ofInjective
  结论: {α β : 类型} (f : α -> β) (f_inv : β -> α)
  证明: by
  ext
  simp
-/
theorem ofLeftInverse'_eq_ofInjective {α β : Type*} (f : α -> β) (f_inv : β -> α)
    (hf : LeftInverse f_inv f) : ofLeftInverse' f f_inv hf = ofInjective f hf.injective := by
  ext
  simp

/--
theorem `set_forall_iff` / 定理 `set_forall_iff`

English:
theorem set_forall_iff
  given: {α β} (e : α ≃ β) {p : Set α -> Prop}
  proof: e.injective.preimage_surjective.forall

中文:
定理 set_forall_iff
  条件: {α β} (e : α ≃ β) {p : Set α -> 命题}
  证明: e.injective.preimage_surjective.forall
-/
protected theorem set_forall_iff {α β} (e : α ≃ β) {p : Set α -> Prop} :
    (forall a, p a) ↔ forall a, p (e ⁻¹' a) :=
  e.injective.preimage_surjective.forall

/--
theorem `preimage_piEquivPiSubtypeProd_symm_pi` / 定理 `preimage_piEquivPiSubtypeProd_symm_pi`

English:
theorem preimage_piEquivPiSubtypeProd_symm_pi
  statement: {α : Type*} {β : α -> Type*} (p : α -> Prop)
  proof: by
  ext ⟨f, g⟩
  simp only [mem_preimage, mem_univ_pi, prodMk_mem_set_prod_eq, Subtype.forall, ← forall_and]
  refine forall_congr' fun i => ?_
  by_cases hi : p i <;> simp [hi]

中文:
定理 preimage_piEquivPiSubtypeProd_symm_pi
  结论: {α : 类型} {β : α -> 类型} (p : α -> 命题)
  证明: by
  ext ⟨f, g⟩
  simp only [mem_preimage, mem_univ_pi, prodMk_mem_set_prod_eq, Subtype.forall, ← forall_and]
  refine forall_congr' fun i => ?_
  by_cases hi : p i <;> simp [hi]

Depends on / 依赖: Subtype, Subtype.forall, forall_and, forall_congr, mem_preimage, mem_univ_pi, prodMk_mem_set_prod_eq
-/
theorem preimage_piEquivPiSubtypeProd_symm_pi {α : Type*} {β : α -> Type*} (p : α -> Prop)
    [DecidablePred p] (s : forall i, Set (β i)) :
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
/--
Definition of `sigmaPreimageEquiv` / `sigmaPreimageEquiv` 的定义

English:
definition sigmaPreimageEquiv
  signature: {α β} (f : α -> β)
  body: sigmaFiberEquiv f

中文:
定义 sigmaPreimageEquiv
  签名: {α β} (f : α -> β)
  定义体: sigmaFiberEquiv f

Depends on / 依赖: sigmaFiberEquiv
-/
def sigmaPreimageEquiv {α β} (f : α -> β) : (Σ b, f ⁻¹' {b}) ≃ α :=
  sigmaFiberEquiv f

-- See also `Equiv.ofFiberEquiv`.
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A family of equivalences between preimages of points gives an equivalence between domains. -/
@[simps!]
/--
Definition of `ofPreimageEquiv` / `ofPreimageEquiv` 的定义

English:
definition ofPreimageEquiv
  signature: {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c})
  body: Equiv.ofFiberEquiv e

中文:
定义 ofPreimageEquiv
  签名: {α β γ} {f : α -> γ} {g : β -> γ} (e : 对任意 c, f ⁻¹' {c} ≃ g ⁻¹' {c})
  定义体: Equiv.ofFiberEquiv e

Depends on / 依赖: Equiv.ofFiberEquiv, ofFiberEquiv
-/
def ofPreimageEquiv {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c}) : α ≃ β :=
  Equiv.ofFiberEquiv e

/--
theorem `ofPreimageEquiv_map` / 定理 `ofPreimageEquiv_map`

English:
theorem ofPreimageEquiv_map
  statement: {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c})
  proof: Equiv.ofFiberEquiv_map e a

中文:
定理 ofPreimageEquiv_map
  结论: {α β γ} {f : α -> γ} {g : β -> γ} (e : 对任意 c, f ⁻¹' {c} ≃ g ⁻¹' {c})
  证明: Equiv.ofFiberEquiv_map e a

Depends on / 依赖: Equiv.ofFiberEquiv_map, ofFiberEquiv_map
-/
theorem ofPreimageEquiv_map {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c})
    (a : α) : g (ofPreimageEquiv e a) = f a :=
  Equiv.ofFiberEquiv_map e a

end Equiv

/--
Definition of `Set.BijOn.equiv` / `Set.BijOn.equiv` 的定义

English:
definition Set.BijOn.equiv
  signature: {α : Type*} {β : Type*} {s : Set α} {t : Set β} (f : α -> β)
  body: Equiv.ofBijective _ h.bijective

中文:
定义 Set.BijOn.equiv
  签名: {α : 类型} {β : 类型} {s : Set α} {t : Set β} (f : α -> β)
  定义体: Equiv.ofBijective _ h.bijective

Depends on / 依赖: Equiv.ofBijective, bijective, h.bijective, ofBijective
-/
noncomputable def Set.BijOn.equiv {α : Type*} {β : Type*} {s : Set α} {t : Set β} (f : α -> β)
    (h : BijOn f s t) : s ≃ t :=
  Equiv.ofBijective _ h.bijective

/--
theorem `dite_comp_equiv_update` / 定理 `dite_comp_equiv_update`

English:
theorem dite_comp_equiv_update
  proof: by
  ext i
  by_cases h : p i
  · simp only [h, update_apply]
    aesop
  · grind

中文:
定理 dite_comp_equiv_update
  证明: by
  ext i
  by_cases h : p i
  · simp only [h, update_apply]
    aesop
  · grind

Depends on / 依赖: update_apply
-/
theorem dite_comp_equiv_update
    {α E : Type*} {β γ : Sort*} {p : α -> Prop} [EquivLike E {x // p x} β]
    (e : E) (v : β -> γ) (w : α -> γ) (j : β) (x : γ)
    [DecidableEq β] [DecidableEq α] [forall j, Decidable (p j)] :
    (fun i : α => if h : p i then (update v j x) (e ⟨i, h⟩) else w i) =
      update (fun i : α => if h : p i then v (e ⟨i, h⟩) else w i) (EquivLike.inv e j) x := by
  ext i
  by_cases h : p i
  · simp only [h, update_apply]
    aesop
  · grind

section Swap

variable {α : Type*} [DecidableEq α] {a b : α} {s : Set α}

/--
theorem `Equiv.swap_bijOn_self` / 定理 `Equiv.swap_bijOn_self`

English:
theorem Equiv.swap_bijOn_self
  given: (hs : a in s ↔ b in s)
  statement: BijOn (Equiv.swap a b) s s
  proof: by
  grind [Equiv.bijOn]

中文:
定理 Equiv.swap_bijOn_self
  条件: (hs : a in s ↔ b in s)
  结论: BijOn (Equiv.swap a b) s s
  证明: by
  grind [Equiv.bijOn]

Depends on / 依赖: Equiv.bijOn
-/
theorem Equiv.swap_bijOn_self (hs : a in s ↔ b in s) : BijOn (Equiv.swap a b) s s := by
  grind [Equiv.bijOn]

/--
theorem `Equiv.swap_bijOn_exchange` / 定理 `Equiv.swap_bijOn_exchange`

English:
theorem Equiv.swap_bijOn_exchange
  given: (ha : a in s) (hb : b ∉ s)
  proof: by
  grind [Equiv.bijOn]

中文:
定理 Equiv.swap_bijOn_exchange
  条件: (ha : a in s) (hb : b ∉ s)
  证明: by
  grind [Equiv.bijOn]

Depends on / 依赖: Equiv.bijOn
-/
theorem Equiv.swap_bijOn_exchange (ha : a in s) (hb : b ∉ s) :
    BijOn (Equiv.swap a b) s (insert b (s \ {a})) := by
  grind [Equiv.bijOn]

end Swap
