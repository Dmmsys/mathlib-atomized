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

/--
theorem `upperBounds_image` / 定理 `upperBounds_image`

English:
theorem upperBounds_image
  given: {s : Set α}
  statement: upperBounds (f '' s) = f '' upperBounds s
  proof: Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image

中文:
定理 upperBounds_image
  条件: {s : Set α}
  结论: upperBounds (f '' s) = f '' upperBounds s
  证明: Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image

Depends on / 依赖: Subset, Subset.antisymm, antisymm, apply_symm_apply, f.apply_symm_apply, f.le_symm_apply, f.monotone.image_upperBounds_subset_upperBounds_image, f.symm, image_upperBounds_subset_upperBounds_image, le_symm_apply, mem_image_of_mem, monotone
-/
theorem upperBounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s :=
  Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image

/--
theorem `lowerBounds_image` / 定理 `lowerBounds_image`

English:
theorem lowerBounds_image
  given: {s : Set α}
  statement: lowerBounds (f '' s) = f '' lowerBounds s
  proof: @upperBounds_image αᵒᵈ βᵒᵈ _ _ f.dual _

@[simp]

中文:
定理 lowerBounds_image
  条件: {s : Set α}
  结论: lowerBounds (f '' s) = f '' lowerBounds s
  证明: @upperBounds_image αᵒᵈ βᵒᵈ _ _ f.dual _

@[simp]

Depends on / 依赖: f.dual, upperBounds_image
-/
theorem lowerBounds_image {s : Set α} : lowerBounds (f '' s) = f '' lowerBounds s :=
  @upperBounds_image αᵒᵈ βᵒᵈ _ _ f.dual _

@[simp]
/--
theorem `isLUB_image` / 定理 `isLUB_image`

English:
theorem isLUB_image
  given: {s : Set α} {x : β}
  statement: IsLUB (f '' s) x ↔ IsLUB s (f.symm x)
  proof: ⟨fun h => IsLUB.of_image (by simp) ((f.apply_symm_apply x).symm ▸ h), fun h =>
(IsLUB.of_image (by simp)) (f.symm_image_image s).symm ▸ h⟩

中文:
定理 isLUB_image
  条件: {s : Set α} {x : β}
  结论: IsLUB (f '' s) x ↔ IsLUB s (f.symm x)
  证明: ⟨fun h => IsLUB.of_image (by simp) ((f.apply_symm_apply x).symm ▸ h), fun h =>
(IsLUB.of_image (by simp)) (f.symm_image_image s).symm ▸ h⟩

Depends on / 依赖: IsLUB.of_image, apply_symm_apply, f.apply_symm_apply, f.symm_image_image, of_image, symm_image_image
-/
theorem isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x ↔ IsLUB s (f.symm x) :=
  ⟨fun h => IsLUB.of_image (by simp) ((f.apply_symm_apply x).symm ▸ h), fun h =>
(IsLUB.of_image (by simp)) (f.symm_image_image s).symm ▸ h⟩

/--
theorem `isLUB_image'` / 定理 `isLUB_image'`

English:
theorem isLUB_image'
  given: {s : Set α} {x : α}
  statement: IsLUB (f '' s) (f x) ↔ IsLUB s x
  proof: by
  rw [isLUB_image]; rw [f.symm_apply_apply]

@[simp]

中文:
定理 isLUB_image'
  条件: {s : Set α} {x : α}
  结论: IsLUB (f '' s) (f x) ↔ IsLUB s x
  证明: by
  rw [isLUB_image]; rw [f.symm_apply_apply]

@[simp]

Depends on / 依赖: f.symm_apply_apply, isLUB_image, symm_apply_apply
-/
theorem isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s) (f x) ↔ IsLUB s x := by
  rw [isLUB_image]; rw [f.symm_apply_apply]

@[simp]
/--
theorem `isGLB_image` / 定理 `isGLB_image`

English:
theorem isGLB_image
  given: {s : Set α} {x : β}
  statement: IsGLB (f '' s) x ↔ IsGLB s (f.symm x)
  proof: f.dual.isLUB_image

中文:
定理 isGLB_image
  条件: {s : Set α} {x : β}
  结论: IsGLB (f '' s) x ↔ IsGLB s (f.symm x)
  证明: f.dual.isLUB_image

Depends on / 依赖: f.dual.isLUB_image, isLUB_image
-/
theorem isGLB_image {s : Set α} {x : β} : IsGLB (f '' s) x ↔ IsGLB s (f.symm x) :=
  f.dual.isLUB_image

/--
theorem `isGLB_image'` / 定理 `isGLB_image'`

English:
theorem isGLB_image'
  given: {s : Set α} {x : α}
  statement: IsGLB (f '' s) (f x) ↔ IsGLB s x
  proof: f.dual.isLUB_image'

@[simp]

中文:
定理 isGLB_image'
  条件: {s : Set α} {x : α}
  结论: IsGLB (f '' s) (f x) ↔ IsGLB s x
  证明: f.dual.isLUB_image'

@[simp]

Depends on / 依赖: f.dual.isLUB_image, isLUB_image
-/
theorem isGLB_image' {s : Set α} {x : α} : IsGLB (f '' s) (f x) ↔ IsGLB s x :=
  f.dual.isLUB_image'

@[simp]
/--
theorem `isLUB_preimage` / 定理 `isLUB_preimage`

English:
theorem isLUB_preimage
  given: {s : Set β} {x : α}
  statement: IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x)
  proof: by
  rw [← f.symm_symm]; rw [← image_eq_preimage_symm]; rw [isLUB_image]

中文:
定理 isLUB_preimage
  条件: {s : Set β} {x : α}
  结论: IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x)
  证明: by
  rw [← f.symm_symm]; rw [← image_eq_preimage_symm]; rw [isLUB_image]

Depends on / 依赖: f.symm_symm, image_eq_preimage_symm, isLUB_image, symm_symm
-/
theorem isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x) := by
  rw [← f.symm_symm]; rw [← image_eq_preimage_symm]; rw [isLUB_image]

/--
theorem `isLUB_preimage'` / 定理 `isLUB_preimage'`

English:
theorem isLUB_preimage'
  given: {s : Set β} {x : β}
  statement: IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s x
  proof: by
  rw [isLUB_preimage]; rw [f.apply_symm_apply]

@[simp]

中文:
定理 isLUB_preimage'
  条件: {s : Set β} {x : β}
  结论: IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s x
  证明: by
  rw [isLUB_preimage]; rw [f.apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, f.apply_symm_apply, isLUB_preimage
-/
theorem isLUB_preimage' {s : Set β} {x : β} : IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s x := by
  rw [isLUB_preimage]; rw [f.apply_symm_apply]

@[simp]
/--
theorem `isGLB_preimage` / 定理 `isGLB_preimage`

English:
theorem isGLB_preimage
  given: {s : Set β} {x : α}
  statement: IsGLB (f ⁻¹' s) x ↔ IsGLB s (f x)
  proof: f.dual.isLUB_preimage

中文:
定理 isGLB_preimage
  条件: {s : Set β} {x : α}
  结论: IsGLB (f ⁻¹' s) x ↔ IsGLB s (f x)
  证明: f.dual.isLUB_preimage

Depends on / 依赖: f.dual.isLUB_preimage, isLUB_preimage
-/
theorem isGLB_preimage {s : Set β} {x : α} : IsGLB (f ⁻¹' s) x ↔ IsGLB s (f x) :=
  f.dual.isLUB_preimage

/--
theorem `isGLB_preimage'` / 定理 `isGLB_preimage'`

English:
theorem isGLB_preimage'
  given: {s : Set β} {x : β}
  statement: IsGLB (f ⁻¹' s) (f.symm x) ↔ IsGLB s x
  proof: f.dual.isLUB_preimage'

中文:
定理 isGLB_preimage'
  条件: {s : Set β} {x : β}
  结论: IsGLB (f ⁻¹' s) (f.symm x) ↔ IsGLB s x
  证明: f.dual.isLUB_preimage'

Depends on / 依赖: f.dual.isLUB_preimage, isLUB_preimage
-/
theorem isGLB_preimage' {s : Set β} {x : β} : IsGLB (f ⁻¹' s) (f.symm x) ↔ IsGLB s x :=
  f.dual.isLUB_preimage'

end OrderIso
