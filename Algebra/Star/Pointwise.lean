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
/--
Definition of `star` / `star` 的定义

English:
definition star
  signature: [Star α]
  body: ⟨preimage Star.star⟩

scoped[Pointwise] attribute [instance] Set.star

@[simp]

中文:
定义 star
  签名: [Star α]
  定义体: ⟨preimage Star.star⟩

scoped[Pointwise] attribute [instance] Set.star

@[simp]
-/
protected def star [Star α] : Star (Set α) := ⟨preimage Star.star⟩

scoped[Pointwise] attribute [instance] Set.star

@[simp]
/--
theorem `star_empty` / 定理 `star_empty`

English:
theorem star_empty
  given: [Star α]
  statement: (∅ : Set α)⋆ = ∅
  proof: rfl

@[simp]

中文:
定理 star_empty
  条件: [Star α]
  结论: (∅ : Set α)⋆ = ∅
  证明: rfl

@[simp]
-/
theorem star_empty [Star α] : (∅ : Set α)⋆ = ∅ := rfl

@[simp]
/--
theorem `star_univ` / 定理 `star_univ`

English:
theorem star_univ
  given: [Star α]
  statement: (univ : Set α)⋆ = univ
  proof: rfl

@[simp]

中文:
定理 star_univ
  条件: [Star α]
  结论: (univ : Set α)⋆ = univ
  证明: rfl

@[simp]
-/
theorem star_univ [Star α] : (univ : Set α)⋆ = univ := rfl

@[simp]
/--
theorem `nonempty_star` / 定理 `nonempty_star`

English:
theorem nonempty_star
  given: [InvolutiveStar α] {s : Set α}
  statement: s⋆.Nonempty ↔ s.Nonempty
  proof: star_involutive.surjective.nonempty_preimage

中文:
定理 nonempty_star
  条件: [InvolutiveStar α] {s : Set α}
  结论: s⋆.Nonempty ↔ s.Nonempty
  证明: star_involutive.surjective.nonempty_preimage

Depends on / 依赖: nonempty_preimage, star_involutive, star_involutive.surjective.nonempty_preimage, surjective
-/
theorem nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty :=
  star_involutive.surjective.nonempty_preimage

/--
theorem `Nonempty.star` / 定理 `Nonempty.star`

English:
theorem Nonempty.star
  given: [InvolutiveStar α] {s : Set α} (h : s.Nonempty)
  statement: s⋆.Nonempty
  proof: nonempty_star.2 h

@[simp, push]

中文:
定理 Nonempty.star
  条件: [InvolutiveStar α] {s : Set α} (h : s.Nonempty)
  结论: s⋆.Nonempty
  证明: nonempty_star.2 h

@[simp, push]

Depends on / 依赖: nonempty_star
-/
theorem Nonempty.star [InvolutiveStar α] {s : Set α} (h : s.Nonempty) : s⋆.Nonempty :=
  nonempty_star.2 h

@[simp, push]
/--
theorem `mem_star` / 定理 `mem_star`

English:
theorem mem_star
  given: [Star α]
  statement: a in s⋆ ↔ a⋆ in s
  proof: Iff.rfl

中文:
定理 mem_star
  条件: [Star α]
  结论: a in s⋆ ↔ a⋆ in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_star [Star α] : a in s⋆ ↔ a⋆ in s := Iff.rfl

/--
theorem `star_mem_star` / 定理 `star_mem_star`

English:
theorem star_mem_star
  given: [InvolutiveStar α]
  statement: a⋆ in s⋆ ↔ a in s
  proof: by simp only [mem_star, star_star]

@[simp]

中文:
定理 star_mem_star
  条件: [InvolutiveStar α]
  结论: a⋆ in s⋆ ↔ a in s
  证明: by simp only [mem_star, star_star]

@[simp]

Depends on / 依赖: mem_star, star_star
-/
theorem star_mem_star [InvolutiveStar α] : a⋆ in s⋆ ↔ a in s := by simp only [mem_star, star_star]

@[simp]
/--
theorem `star_preimage` / 定理 `star_preimage`

English:
theorem star_preimage
  given: [Star α]
  statement: Star.star ⁻¹' s = s⋆
  proof: rfl

@[simp]

中文:
定理 star_preimage
  条件: [Star α]
  结论: Star.star ⁻¹' s = s⋆
  证明: rfl

@[simp]
-/
theorem star_preimage [Star α] : Star.star ⁻¹' s = s⋆ := rfl

@[simp]
/--
theorem `image_star` / 定理 `image_star`

English:
theorem image_star
  given: [InvolutiveStar α]
  statement: Star.star '' s = s⋆
  proof: by
  simp only [← star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]

@[simp]

中文:
定理 image_star
  条件: [InvolutiveStar α]
  结论: Star.star '' s = s⋆
  证明: by
  simp only [← star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]

@[simp]

Depends on / 依赖: image_eq_preimage_of_inverse, star_preimage, star_star
-/
theorem image_star [InvolutiveStar α] : Star.star '' s = s⋆ := by
  simp only [← star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]

@[simp]
/--
theorem `inter_star` / 定理 `inter_star`

English:
theorem inter_star
  given: [Star α]
  statement: (s inter t)⋆ = s⋆ inter t⋆
  proof: preimage_inter

@[simp]

中文:
定理 inter_star
  条件: [Star α]
  结论: (s inter t)⋆ = s⋆ inter t⋆
  证明: preimage_inter

@[simp]

Depends on / 依赖: preimage_inter
-/
theorem inter_star [Star α] : (s inter t)⋆ = s⋆ inter t⋆ := preimage_inter

@[simp]
/--
theorem `union_star` / 定理 `union_star`

English:
theorem union_star
  given: [Star α]
  statement: (s union t)⋆ = s⋆ union t⋆
  proof: preimage_union

@[simp]

中文:
定理 union_star
  条件: [Star α]
  结论: (s union t)⋆ = s⋆ union t⋆
  证明: preimage_union

@[simp]

Depends on / 依赖: preimage_union
-/
theorem union_star [Star α] : (s union t)⋆ = s⋆ union t⋆ := preimage_union

@[simp]
/--
theorem `iInter_star` / 定理 `iInter_star`

English:
theorem iInter_star
  given: {ι : Sort*} [Star α] (s : ι -> Set α)
  statement: (⋂ i, s i)⋆ = ⋂ i, (s i)⋆
  proof: preimage_iInter

@[simp]

中文:
定理 iInter_star
  条件: {ι : Sort*} [Star α] (s : ι -> Set α)
  结论: (⋂ i, s i)⋆ = ⋂ i, (s i)⋆
  证明: preimage_iInter

@[simp]

Depends on / 依赖: preimage_iInter
-/
theorem iInter_star {ι : Sort*} [Star α] (s : ι -> Set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ :=
  preimage_iInter

@[simp]
/--
theorem `iUnion_star` / 定理 `iUnion_star`

English:
theorem iUnion_star
  given: {ι : Sort*} [Star α] (s : ι -> Set α)
  statement: (⋃ i, s i)⋆ = ⋃ i, (s i)⋆
  proof: preimage_iUnion

@[simp]

中文:
定理 iUnion_star
  条件: {ι : Sort*} [Star α] (s : ι -> Set α)
  结论: (⋃ i, s i)⋆ = ⋃ i, (s i)⋆
  证明: preimage_iUnion

@[simp]

Depends on / 依赖: preimage_iUnion
-/
theorem iUnion_star {ι : Sort*} [Star α] (s : ι -> Set α) : (⋃ i, s i)⋆ = ⋃ i, (s i)⋆ :=
  preimage_iUnion

@[simp]
/--
theorem `compl_star` / 定理 `compl_star`

English:
theorem compl_star
  given: [Star α]
  statement: sᶜ⋆ = s⋆ᶜ
  proof: preimage_compl

@[simp]

中文:
定理 compl_star
  条件: [Star α]
  结论: sᶜ⋆ = s⋆ᶜ
  证明: preimage_compl

@[simp]

Depends on / 依赖: preimage_compl
-/
theorem compl_star [Star α] : sᶜ⋆ = s⋆ᶜ := preimage_compl

@[simp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: α] : InvolutiveStar (Set α) where
  body: by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

@[simp]

中文:
实例 [InvolutiveStar
  签名: α] : InvolutiveStar (Set α) where
  定义体: by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

@[simp]

Depends on / 依赖: preimage_id, preimage_preimage, star_preimage, star_star
-/
instance [InvolutiveStar α] : InvolutiveStar (Set α) where
  star_involutive s := by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

@[simp]
/--
theorem `star_subset_star` / 定理 `star_subset_star`

English:
theorem star_subset_star
  given: [InvolutiveStar α] {s t : Set α}
  statement: s⋆ subseteq t⋆ ↔ s subseteq t
  proof: Equiv.Perm.star.surjective.preimage_subset_preimage_iff

中文:
定理 star_subset_star
  条件: [InvolutiveStar α] {s t : Set α}
  结论: s⋆ subseteq t⋆ ↔ s subseteq t
  证明: Equiv.Perm.star.surjective.preimage_subset_preimage_iff

Depends on / 依赖: Equiv.Perm.star.surjective.preimage_subset_preimage_iff, preimage_subset_preimage_iff, surjective
-/
theorem star_subset_star [InvolutiveStar α] {s t : Set α} : s⋆ subseteq t⋆ ↔ s subseteq t :=
  Equiv.Perm.star.surjective.preimage_subset_preimage_iff

/--
theorem `star_subset` / 定理 `star_subset`

English:
theorem star_subset
  given: [InvolutiveStar α] {s t : Set α}
  statement: s⋆ subseteq t ↔ s subseteq t⋆
  proof: by
  rw [← star_subset_star]; rw [star_star]

中文:
定理 star_subset
  条件: [InvolutiveStar α] {s t : Set α}
  结论: s⋆ subseteq t ↔ s subseteq t⋆
  证明: by
  rw [← star_subset_star]; rw [star_star]

Depends on / 依赖: star_star, star_subset_star
-/
theorem star_subset [InvolutiveStar α] {s t : Set α} : s⋆ subseteq t ↔ s subseteq t⋆ := by
  rw [← star_subset_star]; rw [star_star]

/--
theorem `Finite.star` / 定理 `Finite.star`

English:
theorem Finite.star
  given: [InvolutiveStar α] {s : Set α} (hs : s.Finite)
  statement: s⋆.Finite
  proof: hs.preimage star_injective.injOn

中文:
定理 Finite.star
  条件: [InvolutiveStar α] {s : Set α} (hs : s.Finite)
  结论: s⋆.Finite
  证明: hs.preimage star_injective.injOn

Depends on / 依赖: hs.preimage, preimage, star_injective, star_injective.injOn
-/
theorem Finite.star [InvolutiveStar α] {s : Set α} (hs : s.Finite) : s⋆.Finite :=
  hs.preimage star_injective.injOn

/--
theorem `star_singleton` / 定理 `star_singleton`

English:
theorem star_singleton
  given: {β : Type*} [InvolutiveStar β] (x : β)
  statement: ({x} : Set β)⋆ = {x⋆}
  proof: by
  ext1 y
  rw [mem_star]; rw [mem_singleton_iff]; rw [mem_singleton_iff]; rw [star_eq_iff_star_eq]; rw [eq_comm]

中文:
定理 star_singleton
  条件: {β : 类型} [InvolutiveStar β] (x : β)
  结论: ({x} : Set β)⋆ = {x⋆}
  证明: by
  ext1 y
  rw [mem_star]; rw [mem_singleton_iff]; rw [mem_singleton_iff]; rw [star_eq_iff_star_eq]; rw [eq_comm]

Depends on / 依赖: eq_comm, mem_singleton_iff, mem_star, star_eq_iff_star_eq
-/
theorem star_singleton {β : Type*} [InvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {x⋆} := by
  ext1 y
  rw [mem_star]; rw [mem_singleton_iff]; rw [mem_singleton_iff]; rw [star_eq_iff_star_eq]; rw [eq_comm]

/--
theorem `star_mul` / 定理 `star_mul`

English:
theorem star_mul
  given: [Mul α] [StarMul α] (s t : Set α)
  statement: (s * t)⋆ = t⋆ * s⋆
  proof: by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]

中文:
定理 star_mul
  条件: [Mul α] [StarMul α] (s t : Set α)
  结论: (s * t)⋆ = t⋆ * s⋆
  证明: by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]
-/
protected theorem star_mul [Mul α] [StarMul α] (s t : Set α) : (s * t)⋆ = t⋆ * s⋆ := by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]

/--
theorem `star_add` / 定理 `star_add`

English:
theorem star_add
  given: [AddMonoid α] [StarAddMonoid α] (s t : Set α)
  statement: (s + t)⋆ = s⋆ + t⋆
  proof: by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]

@[simp]

中文:
定理 star_add
  条件: [AddMonoid α] [StarAddMonoid α] (s t : Set α)
  结论: (s + t)⋆ = s⋆ + t⋆
  证明: by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]

@[simp]
-/
protected theorem star_add [AddMonoid α] [StarAddMonoid α] (s t : Set α) : (s + t)⋆ = s⋆ + t⋆ := by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]

@[simp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: α] [TrivialStar α] : TrivialStar (Set α) where
  body: by
    rw [← star_preimage]
    ext1
    simp [star_trivial]

中文:
实例 [Star
  签名: α] [TrivialStar α] : TrivialStar (Set α) where
  定义体: by
    rw [← star_preimage]
    ext1
    simp [star_trivial]

Depends on / 依赖: star_preimage, star_trivial
-/
instance [Star α] [TrivialStar α] : TrivialStar (Set α) where
  star_trivial s := by
    rw [← star_preimage]
    ext1
    simp [star_trivial]

/--
theorem `star_inv` / 定理 `star_inv`

English:
theorem star_inv
  given: [Group α] [StarMul α] (s : Set α)
  statement: s⁻¹⋆ = s⋆⁻¹
  proof: by
  ext
  simp only [mem_star, mem_inv, star_inv]

中文:
定理 star_inv
  条件: [Group α] [StarMul α] (s : Set α)
  结论: s⁻¹⋆ = s⋆⁻¹
  证明: by
  ext
  simp only [mem_star, mem_inv, star_inv]
-/
protected theorem star_inv [Group α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [mem_star, mem_inv, star_inv]

/--
theorem `star_inv'` / 定理 `star_inv'`

English:
theorem star_inv'
  given: [GroupWithZero α] [StarMul α] (s : Set α)
  statement: s⁻¹⋆ = s⋆⁻¹
  proof: by
  ext
  simp only [mem_star, mem_inv, star_inv₀]

中文:
定理 star_inv'
  条件: [GroupWithZero α] [StarMul α] (s : Set α)
  结论: s⁻¹⋆ = s⋆⁻¹
  证明: by
  ext
  simp only [mem_star, mem_inv, star_inv₀]
-/
protected theorem star_inv' [GroupWithZero α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [mem_star, mem_inv, star_inv₀]

end Set

@[simp]
/--
lemma `StarMemClass.star_coe_eq` / 引理 `StarMemClass.star_coe_eq`

English:
lemma StarMemClass.star_coe_eq
  statement: {S α : Type*} [InvolutiveStar α] [SetLike S α]
  proof: by
  ext
  simpa using star_mem_iff

中文:
引理 StarMemClass.star_coe_eq
  结论: {S α : 类型} [InvolutiveStar α] [SetLike S α]
  证明: by
  ext
  simpa using star_mem_iff

Depends on / 依赖: star_mem_iff
-/
lemma StarMemClass.star_coe_eq {S α : Type*} [InvolutiveStar α] [SetLike S α]
    [StarMemClass S α] (s : S) : star (s : Set α) = s := by
  ext
  simpa using star_mem_iff
