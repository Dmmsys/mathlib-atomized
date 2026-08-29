/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# The set lattice and (pre)images of functions

This file contains lemmas on the interaction between the indexed union/intersection of sets
and the image and preimage operations: `Set.image`, `Set.preimage`, `Set.image2`, `Set.kernImage`.
It also covers `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`.

In order to accommodate `Set.image2`, the file includes results on union/intersection in products.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

public section

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ : ι -> Sort*}

namespace Set

section GaloisConnection

variable {f : α -> β}

/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  statement: GaloisConnection (image f) (preimage f)
  proof: fun _ _ =>
  image_subset_iff

中文:
定理 image_preimage
  结论: GaloisConnection (像 f) (原像 f)
  证明: fun _ _ =>
  image_subset_iff
-/
protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun _ _ =>
  image_subset_iff

/--
theorem `preimage_kernImage` / 定理 `preimage_kernImage`

English:
theorem preimage_kernImage
  statement: GaloisConnection (preimage f) (kernImage f)
  proof: fun _ _ =>
  subset_kernImage_iff.symm

中文:
定理 preimage_kernImage
  结论: GaloisConnection (原像 f) (kernImage f)
  证明: fun _ _ =>
  subset_kernImage_iff.symm
-/
protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun _ _ =>
  subset_kernImage_iff.symm

end GaloisConnection

section kernImage

variable {f : α -> β}

/--
lemma `kernImage_mono` / 引理 `kernImage_mono`

English:
lemma kernImage_mono
  statement: Monotone (kernImage f)
  proof: Set.preimage_kernImage.monotone_u

中文:
引理 kernImage_mono
  结论: 递增 (kernImage f)
  证明: Set.preimage_kernImage.monotone_u

Depends on / 依赖: Set.preimage_kernImage.monotone_u, monotone_u, preimage_kernImage
-/
lemma kernImage_mono : Monotone (kernImage f) :=
  Set.preimage_kernImage.monotone_u

/--
lemma `kernImage_eq_compl` / 引理 `kernImage_eq_compl`

English:
lemma kernImage_eq_compl
  given: {s : Set α}
  statement: kernImage f s = (f '' sᶜ)ᶜ
  proof: Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t => compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)

中文:
引理 kernImage_eq_compl
  条件: {s : 集合 α}
  结论: kernImage f s = (f '' sᶜ)ᶜ
  证明: Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t => compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)

Depends on / 依赖: Set.image_preimage.compl, Set.preimage_compl, Set.preimage_kernImage.u_unique, compl_compl, image_preimage, preimage_compl, preimage_kernImage, u_unique
-/
lemma kernImage_eq_compl {s : Set α} : kernImage f s = (f '' sᶜ)ᶜ :=
  Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t => compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)

/--
lemma `kernImage_compl` / 引理 `kernImage_compl`

English:
lemma kernImage_compl
  given: {s : Set α}
  statement: kernImage f (sᶜ) = (f '' s)ᶜ
  proof: by
  rw [kernImage_eq_compl]; rw [compl_compl]

中文:
引理 kernImage_compl
  条件: {s : 集合 α}
  结论: kernImage f (sᶜ) = (f '' s)ᶜ
  证明: by
  rw [kernImage_eq_compl]; rw [compl_compl]

Depends on / 依赖: compl_compl, kernImage_eq_compl
-/
lemma kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f '' s)ᶜ := by
  rw [kernImage_eq_compl]; rw [compl_compl]

/--
lemma `kernImage_empty` / 引理 `kernImage_empty`

English:
lemma kernImage_empty
  statement: kernImage f ∅ = (range f)ᶜ
  proof: by
  rw [kernImage_eq_compl]; rw [compl_empty]; rw [image_univ]

中文:
引理 kernImage_empty
  结论: kernImage f ∅ = (range f)ᶜ
  证明: by
  rw [kernImage_eq_compl]; rw [compl_empty]; rw [image_univ]

Depends on / 依赖: compl_empty, image_univ, kernImage_eq_compl
-/
lemma kernImage_empty : kernImage f ∅ = (range f)ᶜ := by
  rw [kernImage_eq_compl]; rw [compl_empty]; rw [image_univ]

/--
lemma `kernImage_preimage_eq_iff` / 引理 `kernImage_preimage_eq_iff`

English:
lemma kernImage_preimage_eq_iff
  given: {s : Set β}
  statement: kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ subseteq s
  proof: by
  rw [kernImage_eq_compl]; rw [← preimage_compl]; rw [compl_eq_comm]; rw [eq_comm]; rw [image_preimage_eq_iff]; rw [compl_subset_comm]

中文:
引理 kernImage_preimage_eq_iff
  条件: {s : 集合 β}
  结论: kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ subseteq s
  证明: by
  rw [kernImage_eq_compl]; rw [← preimage_compl]; rw [compl_eq_comm]; rw [eq_comm]; rw [image_preimage_eq_iff]; rw [compl_subset_comm]

Depends on / 依赖: compl_eq_comm, compl_subset_comm, eq_comm, image_preimage_eq_iff, kernImage_eq_compl, preimage_compl
-/
lemma kernImage_preimage_eq_iff {s : Set β} : kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ subseteq s := by
  rw [kernImage_eq_compl]; rw [← preimage_compl]; rw [compl_eq_comm]; rw [eq_comm]; rw [image_preimage_eq_iff]; rw [compl_subset_comm]

/--
lemma `compl_range_subset_kernImage` / 引理 `compl_range_subset_kernImage`

English:
lemma compl_range_subset_kernImage
  given: {s : Set α}
  statement: (range f)ᶜ subseteq kernImage f s
  proof: by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)

中文:
引理 compl_range_subset_kernImage
  条件: {s : 集合 α}
  结论: (range f)ᶜ subseteq kernImage f s
  证明: by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)

Depends on / 依赖: empty_subset, kernImage_empty, kernImage_mono
-/
lemma compl_range_subset_kernImage {s : Set α} : (range f)ᶜ subseteq kernImage f s := by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)

/--
lemma `kernImage_union_preimage` / 引理 `kernImage_union_preimage`

English:
lemma kernImage_union_preimage
  given: {s : Set α} {t : Set β}
  proof: by
  rw [kernImage_eq_compl]; rw [kernImage_eq_compl]; rw [compl_union]; rw [← preimage_compl]; rw [image_inter_preimage]; rw [compl_inter]; rw [compl_compl]

中文:
引理 kernImage_union_preimage
  条件: {s : 集合 α} {t : 集合 β}
  证明: by
  rw [kernImage_eq_compl]; rw [kernImage_eq_compl]; rw [compl_union]; rw [← preimage_compl]; rw [image_inter_preimage]; rw [compl_inter]; rw [compl_compl]

Depends on / 依赖: compl_compl, compl_inter, compl_union, image_inter_preimage, kernImage_eq_compl, preimage_compl
-/
lemma kernImage_union_preimage {s : Set α} {t : Set β} :
    kernImage f (s union f ⁻¹' t) = kernImage f s union t := by
  rw [kernImage_eq_compl]; rw [kernImage_eq_compl]; rw [compl_union]; rw [← preimage_compl]; rw [image_inter_preimage]; rw [compl_inter]; rw [compl_compl]

/--
lemma `kernImage_preimage_union` / 引理 `kernImage_preimage_union`

English:
lemma kernImage_preimage_union
  given: {s : Set α} {t : Set β}
  proof: by
  rw [union_comm]; rw [kernImage_union_preimage]; rw [union_comm]

中文:
引理 kernImage_preimage_union
  条件: {s : 集合 α} {t : 集合 β}
  证明: by
  rw [union_comm]; rw [kernImage_union_preimage]; rw [union_comm]

Depends on / 依赖: kernImage_union_preimage, union_comm
-/
lemma kernImage_preimage_union {s : Set α} {t : Set β} :
    kernImage f (f ⁻¹' t union s) = t union kernImage f s := by
  rw [union_comm]; rw [kernImage_union_preimage]; rw [union_comm]

end kernImage

/--
theorem `image_projection_prod` / 定理 `image_projection_prod`

English:
theorem image_projection_prod
  statement: {ι : Type*} {α : ι -> Type*} {v : forall i : ι, Set (α i)}
  proof: by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_self i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t in v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩

中文:
定理 image_projection_prod
  结论: {ι : 类型} {α : ι -> 类型} {v : 对任意 i : ι, 集合 (α i)}
  证明: by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_self i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t in v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩

Depends on / 依赖: Function, Function.update, Subset, Subset.antisymm, antisymm, classical, forall_update_iff, iInter_subset, mem_iInter, mem_image, mem_preimage, update, update_self, y_in
-/
theorem image_projection_prod {ι : Type*} {α : ι -> Type*} {v : forall i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : forall i : ι, α i => x i) '' ⋂ k, (fun x : forall j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_self i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t in v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩

/-! ### Bounded unions and intersections -/

section Function

/-! ### Lemmas about `Set.MapsTo` -/

@[simp]
/--
theorem `mapsTo_sUnion` / 定理 `mapsTo_sUnion`

English:
theorem mapsTo_sUnion
  given: {S : Set (Set α)} {t : Set β} {f : α -> β}
  proof: mapsTo_iff_subset_preimage.trans sUnion_subset_iff

@[simp]

中文:
定理 mapsTo_sUnion
  条件: {S : 集合 (集合 α)} {t : 集合 β} {f : α -> β}
  证明: mapsTo_iff_subset_preimage.trans sUnion_subset_iff

@[simp]

Depends on / 依赖: mapsTo_iff_subset_preimage, mapsTo_iff_subset_preimage.trans, sUnion_subset_iff
-/
theorem mapsTo_sUnion {S : Set (Set α)} {t : Set β} {f : α -> β} :
    MapsTo f (⋃₀ S) t ↔ forall s in S, MapsTo f s t :=
  mapsTo_iff_subset_preimage.trans sUnion_subset_iff

@[simp]
/--
theorem `mapsTo_iUnion` / 定理 `mapsTo_iUnion`

English:
theorem mapsTo_iUnion
  given: {s : ι -> Set α} {t : Set β} {f : α -> β}
  proof: mapsTo_iff_subset_preimage.trans iUnion_subset_iff

中文:
定理 mapsTo_iUnion
  条件: {s : ι -> 集合 α} {t : 集合 β} {f : α -> β}
  证明: mapsTo_iff_subset_preimage.trans iUnion_subset_iff

Depends on / 依赖: iUnion_subset_iff, mapsTo_iff_subset_preimage, mapsTo_iff_subset_preimage.trans
-/
theorem mapsTo_iUnion {s : ι -> Set α} {t : Set β} {f : α -> β} :
    MapsTo f (⋃ i, s i) t ↔ forall i, MapsTo f (s i) t :=
  mapsTo_iff_subset_preimage.trans iUnion_subset_iff

/--
theorem `mapsTo_iUnion₂` / 定理 `mapsTo_iUnion₂`

English:
theorem mapsTo_iUnion₂
  given: {s : forall i, κ i -> Set α} {t : Set β} {f : α -> β}
  proof: mapsTo_iff_subset_preimage.trans iUnion₂_subset_iff

中文:
定理 mapsTo_iUnion₂
  条件: {s : 对任意 i, κ i -> 集合 α} {t : 集合 β} {f : α -> β}
  证明: mapsTo_iff_subset_preimage.trans iUnion₂_subset_iff

Depends on / 依赖: mapsTo_iff_subset_preimage, mapsTo_iff_subset_preimage.trans
-/
theorem mapsTo_iUnion₂ {s : forall i, κ i -> Set α} {t : Set β} {f : α -> β} :
    MapsTo f (⋃ (i) (j), s i j) t ↔ forall i j, MapsTo f (s i j) t :=
  mapsTo_iff_subset_preimage.trans iUnion₂_subset_iff

/--
theorem `mapsTo_iUnion_iUnion` / 定理 `mapsTo_iUnion_iUnion`

English:
theorem mapsTo_iUnion_iUnion
  statement: {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
  proof: mapsTo_iUnion.2 fun i => (H i).mono_right (subset_iUnion t i)

中文:
定理 mapsTo_iUnion_iUnion
  结论: {s : ι -> 集合 α} {t : ι -> 集合 β} {f : α -> β}
  证明: mapsTo_iUnion.2 fun i => (H i).mono_right (subset_iUnion t i)

Depends on / 依赖: mapsTo_iUnion, mono_right, subset_iUnion
-/
theorem mapsTo_iUnion_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
    (H : forall i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  mapsTo_iUnion.2 fun i => (H i).mono_right (subset_iUnion t i)

/--
theorem `mapsTo_iUnion₂_iUnion₂` / 定理 `mapsTo_iUnion₂_iUnion₂`

English:
theorem mapsTo_iUnion₂_iUnion₂
  statement: {s : forall i, κ i -> Set α} {t : forall i, κ i -> Set β} {f : α -> β}
  proof: mapsTo_iUnion_iUnion fun i => mapsTo_iUnion_iUnion (H i)

@[simp]

中文:
定理 mapsTo_iUnion₂_iUnion₂
  结论: {s : 对任意 i, κ i -> 集合 α} {t : 对任意 i, κ i -> 集合 β} {f : α -> β}
  证明: mapsTo_iUnion_iUnion fun i => mapsTo_iUnion_iUnion (H i)

@[simp]

Depends on / 依赖: mapsTo_iUnion_iUnion
-/
theorem mapsTo_iUnion₂_iUnion₂ {s : forall i, κ i -> Set α} {t : forall i, κ i -> Set β} {f : α -> β}
    (H : forall i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  mapsTo_iUnion_iUnion fun i => mapsTo_iUnion_iUnion (H i)

@[simp]
/--
theorem `mapsTo_sInter` / 定理 `mapsTo_sInter`

English:
theorem mapsTo_sInter
  given: {s : Set α} {T : Set (Set β)} {f : α -> β}
  proof: forall₂_comm

@[simp]

中文:
定理 mapsTo_s整数er
  条件: {s : 集合 α} {T : 集合 (集合 β)} {f : α -> β}
  证明: forall₂_comm

@[simp]
-/
theorem mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α -> β} :
    MapsTo f s (⋂₀ T) ↔ forall t in T, MapsTo f s t :=
  forall₂_comm

@[simp]
/--
theorem `mapsTo_iInter` / 定理 `mapsTo_iInter`

English:
theorem mapsTo_iInter
  given: {s : Set α} {t : ι -> Set β} {f : α -> β}
  proof: mapsTo_sInter.trans forall_mem_range

中文:
定理 mapsTo_i整数er
  条件: {s : 集合 α} {t : ι -> 集合 β} {f : α -> β}
  证明: mapsTo_sInter.trans forall_mem_range

Depends on / 依赖: forall_mem_range, mapsTo_sInter, mapsTo_sInter.trans
-/
theorem mapsTo_iInter {s : Set α} {t : ι -> Set β} {f : α -> β} :
    MapsTo f s (⋂ i, t i) ↔ forall i, MapsTo f s (t i) :=
  mapsTo_sInter.trans forall_mem_range

/--
theorem `mapsTo_iInter₂` / 定理 `mapsTo_iInter₂`

English:
theorem mapsTo_iInter₂
  given: {s : Set α} {t : forall i, κ i -> Set β} {f : α -> β}
  proof: by
  simp only [mapsTo_iInter]

中文:
定理 mapsTo_i整数er₂
  条件: {s : 集合 α} {t : 对任意 i, κ i -> 集合 β} {f : α -> β}
  证明: by
  simp only [mapsTo_iInter]

Depends on / 依赖: mapsTo_iInter
-/
theorem mapsTo_iInter₂ {s : Set α} {t : forall i, κ i -> Set β} {f : α -> β} :
    MapsTo f s (⋂ (i) (j), t i j) ↔ forall i j, MapsTo f s (t i j) := by
  simp only [mapsTo_iInter]

/--
theorem `mapsTo_iInter_iInter` / 定理 `mapsTo_iInter_iInter`

English:
theorem mapsTo_iInter_iInter
  statement: {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
  proof: mapsTo_iInter.2 fun i => (H i).mono_left (iInter_subset s i)

中文:
定理 mapsTo_i整数er_i整数er
  结论: {s : ι -> 集合 α} {t : ι -> 集合 β} {f : α -> β}
  证明: mapsTo_iInter.2 fun i => (H i).mono_left (iInter_subset s i)

Depends on / 依赖: iInter_subset, mapsTo_iInter, mono_left
-/
theorem mapsTo_iInter_iInter {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
    (H : forall i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  mapsTo_iInter.2 fun i => (H i).mono_left (iInter_subset s i)

/--
theorem `mapsTo_iInter₂_iInter₂` / 定理 `mapsTo_iInter₂_iInter₂`

English:
theorem mapsTo_iInter₂_iInter₂
  statement: {s : forall i, κ i -> Set α} {t : forall i, κ i -> Set β} {f : α -> β}
  proof: mapsTo_iInter_iInter fun i => mapsTo_iInter_iInter (H i)

中文:
定理 mapsTo_i整数er₂_i整数er₂
  结论: {s : 对任意 i, κ i -> 集合 α} {t : 对任意 i, κ i -> 集合 β} {f : α -> β}
  证明: mapsTo_iInter_iInter fun i => mapsTo_iInter_iInter (H i)

Depends on / 依赖: mapsTo_iInter_iInter
-/
theorem mapsTo_iInter₂_iInter₂ {s : forall i, κ i -> Set α} {t : forall i, κ i -> Set β} {f : α -> β}
    (H : forall i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  mapsTo_iInter_iInter fun i => mapsTo_iInter_iInter (H i)

/--
theorem `image_iInter_subset` / 定理 `image_iInter_subset`

English:
theorem image_iInter_subset
  given: (s : ι -> Set α) (f : α -> β)
  statement: (f '' ⋂ i, s i) subseteq ⋂ i, f '' s i
  proof: (mapsTo_iInter_iInter fun i => mapsTo_image f (s i)).image_subset

中文:
定理 image_i整数er_subset
  条件: (s : ι -> 集合 α) (f : α -> β)
  结论: (f '' ⋂ i, s i) subseteq ⋂ i, f '' s i
  证明: (mapsTo_iInter_iInter fun i => mapsTo_image f (s i)).image_subset

Depends on / 依赖: image_subset, mapsTo_iInter_iInter, mapsTo_image
-/
theorem image_iInter_subset (s : ι -> Set α) (f : α -> β) : (f '' ⋂ i, s i) subseteq ⋂ i, f '' s i :=
  (mapsTo_iInter_iInter fun i => mapsTo_image f (s i)).image_subset

/--
theorem `image_iInter₂_subset` / 定理 `image_iInter₂_subset`

English:
theorem image_iInter₂_subset
  given: (s : forall i, κ i -> Set α) (f : α -> β)
  proof: (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset

中文:
定理 image_i整数er₂_subset
  条件: (s : 对任意 i, κ i -> 集合 α) (f : α -> β)
  证明: (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset

Depends on / 依赖: image_subset, mapsTo_image
-/
theorem image_iInter₂_subset (s : forall i, κ i -> Set α) (f : α -> β) :
    (f '' ⋂ (i) (j), s i j) subseteq ⋂ (i) (j), f '' s i j :=
  (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset

/--
theorem `image_sInter_subset` / 定理 `image_sInter_subset`

English:
theorem image_sInter_subset
  given: (S : Set (Set α)) (f : α -> β)
  statement: f '' ⋂₀ S subseteq ⋂ s in S, f '' s
  proof: by
  rw [sInter_eq_biInter]
  apply image_iInter₂_subset

中文:
定理 image_s整数er_subset
  条件: (S : 集合 (集合 α)) (f : α -> β)
  结论: f '' ⋂₀ S subseteq ⋂ s in S, f '' s
  证明: by
  rw [sInter_eq_biInter]
  apply image_iInter₂_subset

Depends on / 依赖: sInter_eq_biInter
-/
theorem image_sInter_subset (S : Set (Set α)) (f : α -> β) : f '' ⋂₀ S subseteq ⋂ s in S, f '' s := by
  rw [sInter_eq_biInter]
  apply image_iInter₂_subset

/--
theorem `image2_sInter_right_subset` / 定理 `image2_sInter_right_subset`

English:
theorem image2_sInter_right_subset
  given: (t : Set α) (S : Set (Set β)) (f : α -> β -> γ)
  proof: by
  aesop

中文:
定理 image2_s整数er_right_subset
  条件: (t : 集合 α) (S : 集合 (集合 β)) (f : α -> β -> γ)
  证明: by
  aesop
-/
theorem image2_sInter_right_subset (t : Set α) (S : Set (Set β)) (f : α -> β -> γ) :
    image2 f t (⋂₀ S) subseteq ⋂ s in S, image2 f t s := by
  aesop

/--
theorem `image2_sInter_left_subset` / 定理 `image2_sInter_left_subset`

English:
theorem image2_sInter_left_subset
  given: (S : Set (Set α)) (t : Set β) (f : α -> β -> γ)
  proof: by
  aesop

中文:
定理 image2_s整数er_left_subset
  条件: (S : 集合 (集合 α)) (t : 集合 β) (f : α -> β -> γ)
  证明: by
  aesop
-/
theorem image2_sInter_left_subset (S : Set (Set α)) (t : Set β) (f : α -> β -> γ) :
    image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f s t := by
  aesop

/-! ### `restrictPreimage` -/


section

open Function

variable {f : α -> β} {U : ι -> Set β} (hU : iUnion U = univ)
include hU

/--
theorem `injective_iff_injective_of_iUnion_eq_univ` / 定理 `injective_iff_injective_of_iUnion_eq_univ`

English:
theorem injective_iff_injective_of_iUnion_eq_univ
  proof: by
  refine ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show f x in Set.iUnion U by rw [hU]; trivial)
  injection @H i ⟨x, hi⟩ ⟨y, show f y in U i from e ▸ hi⟩ (Subtype.ext e)

中文:
定理 injective_iff_injective_of_iUnion_eq_univ
  证明: by
  refine ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show f x in Set.iUnion U by rw [hU]; trivial)
  injection @H i ⟨x, hi⟩ ⟨y, show f y in U i from e ▸ hi⟩ (Subtype.ext e)

Depends on / 依赖: Set.iUnion, Set.mem_iUnion.mp, Subtype, Subtype.ext, iUnion, injection, mem_iUnion, restrictPreimage_injective
-/
theorem injective_iff_injective_of_iUnion_eq_univ :
    Injective f ↔ forall i, Injective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show f x in Set.iUnion U by rw [hU]; trivial)
  injection @H i ⟨x, hi⟩ ⟨y, show f y in U i from e ▸ hi⟩ (Subtype.ext e)

/--
theorem `surjective_iff_surjective_of_iUnion_eq_univ` / 定理 `surjective_iff_surjective_of_iUnion_eq_univ`

English:
theorem surjective_iff_surjective_of_iUnion_eq_univ
  proof: by
  refine ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => ?_⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.mp
      (show x in Set.iUnion U by rw [hU]; trivial)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩

中文:
定理 surjective_iff_surjective_of_iUnion_eq_univ
  证明: by
  refine ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => ?_⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.mp
      (show x in Set.iUnion U by rw [hU]; trivial)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩

Depends on / 依赖: Set.iUnion, Set.mem_iUnion.mp, Subtype, Subtype.val, choose_spec, congr_arg, iUnion, mem_iUnion, restrictPreimage_surjective
-/
theorem surjective_iff_surjective_of_iUnion_eq_univ :
    Surjective f ↔ forall i, Surjective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => ?_⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.mp
      (show x in Set.iUnion U by rw [hU]; trivial)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩

/--
theorem `bijective_iff_bijective_of_iUnion_eq_univ` / 定理 `bijective_iff_bijective_of_iUnion_eq_univ`

English:
theorem bijective_iff_bijective_of_iUnion_eq_univ
  proof: by
  rw [Bijective]; rw [injective_iff_injective_of_iUnion_eq_univ hU]; rw [surjective_iff_surjective_of_iUnion_eq_univ hU]
  simp [Bijective, forall_and]

中文:
定理 bijective_iff_bijective_of_iUnion_eq_univ
  证明: by
  rw [Bijective]; rw [injective_iff_injective_of_iUnion_eq_univ hU]; rw [surjective_iff_surjective_of_iUnion_eq_univ hU]
  simp [Bijective, forall_and]

Depends on / 依赖: Bijective, forall_and, injective_iff_injective_of_iUnion_eq_univ, surjective_iff_surjective_of_iUnion_eq_univ
-/
theorem bijective_iff_bijective_of_iUnion_eq_univ :
    Bijective f ↔ forall i, Bijective ((U i).restrictPreimage f) := by
  rw [Bijective]; rw [injective_iff_injective_of_iUnion_eq_univ hU]; rw [surjective_iff_surjective_of_iUnion_eq_univ hU]
  simp [Bijective, forall_and]

end



/--
theorem `InjOn.image_iInter_eq` / 定理 `InjOn.image_iInter_eq`

English:
theorem InjOn.image_iInter_eq
  given: [Nonempty ι] {s : ι -> Set α} {f : α -> β} (h : InjOn f (⋃ i, s i))
  proof: by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : forall i, x i in ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]

中文:
定理 单射限制.image_i整数er_eq
  条件: [非空 ι] {s : ι -> 集合 α} {f : α -> β} (h : 单射限制 f (⋃ i, s i))
  证明: by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : forall i, x i in ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, image_iInter_subset, inhabit, mem_iInter, mem_image, replace, subset_iUnion
-/
theorem InjOn.image_iInter_eq [Nonempty ι] {s : ι -> Set α} {f : α -> β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : forall i, x i in ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]

/--
theorem `InjOn.image_biInter_eq` / 定理 `InjOn.image_biInter_eq`

English:
theorem InjOn.image_biInter_eq
  statement: {p : ι -> Prop} {s : forall i, p i -> Set α} (hp : exists i, p i)
  proof: by
  simp only [iInter, iInf_subtype']
  have : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_iInter_eq
  simpa only [iUnion, iSup_subtype'] using h

中文:
定理 单射限制.image_bi整数er_eq
  结论: {p : ι -> 命题} {s : 对任意 i, p i -> 集合 α} (hp : 存在 i, p i)
  证明: by
  simp only [iInter, iInf_subtype']
  have : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_iInter_eq
  simpa only [iUnion, iSup_subtype'] using h

Depends on / 依赖: InjOn.image_iInter_eq, Nonempty, iInf_subtype, iInter, iSup_subtype, iUnion, image_iInter_eq, nonempty_subtype
-/
theorem InjOn.image_biInter_eq {p : ι -> Prop} {s : forall i, p i -> Set α} (hp : exists i, p i)
    {f : α -> β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [iInter, iInf_subtype']
  have : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_iInter_eq
  simpa only [iUnion, iSup_subtype'] using h

/--
theorem `image_iInter` / 定理 `image_iInter`

English:
theorem image_iInter
  given: {f : α -> β} (hf : Bijective f) (s : ι -> Set α)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp_rw [iInter_of_empty, image_univ_of_surjective hf.surjective]
  · exact hf.injective.injOn.image_iInter_eq

中文:
定理 image_i整数er
  条件: {f : α -> β} (hf : 双射 f) (s : ι -> 集合 α)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp_rw [iInter_of_empty, image_univ_of_surjective hf.surjective]
  · exact hf.injective.injOn.image_iInter_eq

Depends on / 依赖: hf.injective.injOn.image_iInter_eq, hf.surjective, iInter_of_empty, image_iInter_eq, image_univ_of_surjective, injective, isEmpty_or_nonempty, simp_rw, surjective
-/
theorem image_iInter {f : α -> β} (hf : Bijective f) (s : ι -> Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iInter_of_empty, image_univ_of_surjective hf.surjective]
  · exact hf.injective.injOn.image_iInter_eq

/--
theorem `image_iInter₂` / 定理 `image_iInter₂`

English:
theorem image_iInter₂
  given: {f : α -> β} (hf : Bijective f) (s : forall i, κ i -> Set α)
  proof: by simp_rw [image_iInter hf]

中文:
定理 image_i整数er₂
  条件: {f : α -> β} (hf : 双射 f) (s : 对任意 i, κ i -> 集合 α)
  证明: by simp_rw [image_iInter hf]

Depends on / 依赖: image_iInter, simp_rw
-/
theorem image_iInter₂ {f : α -> β} (hf : Bijective f) (s : forall i, κ i -> Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_iInter hf]

/--
theorem `inj_on_iUnion_of_directed` / 定理 `inj_on_iUnion_of_directed`

English:
theorem inj_on_iUnion_of_directed
  statement: {s : ι -> Set α} (hs : Directed (· subseteq ·) s) {f : α -> β}
  proof: by
  intro x hx y hy hxy
  rcases mem_iUnion.1 hx with ⟨i, hx⟩
  rcases mem_iUnion.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy

中文:
定理 inj_on_iUnion_of_directed
  结论: {s : ι -> 集合 α} (hs : Directed (· subseteq ·) s) {f : α -> β}
  证明: by
  intro x hx y hy hxy
  rcases mem_iUnion.1 hx with ⟨i, hx⟩
  rcases mem_iUnion.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy

Depends on / 依赖: mem_iUnion
-/
theorem inj_on_iUnion_of_directed {s : ι -> Set α} (hs : Directed (· subseteq ·) s) {f : α -> β}
    (hf : forall i, InjOn f (s i)) : InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_iUnion.1 hx with ⟨i, hx⟩
  rcases mem_iUnion.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy



/--
theorem `surjOn_sUnion` / 定理 `surjOn_sUnion`

English:
theorem surjOn_sUnion
  given: {s : Set α} {T : Set (Set β)} {f : α -> β} (H : forall t in T, SurjOn f s t)
  proof: fun _ ⟨t, ht, hx⟩ => H t ht hx

中文:
定理 surjOn_sUnion
  条件: {s : 集合 α} {T : 集合 (集合 β)} {f : α -> β} (H : 对任意 t in T, 满射限制 f s t)
  证明: fun _ ⟨t, ht, hx⟩ => H t ht hx
-/
theorem surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α -> β} (H : forall t in T, SurjOn f s t) :
    SurjOn f s (⋃₀ T) := fun _ ⟨t, ht, hx⟩ => H t ht hx

/--
theorem `surjOn_iUnion` / 定理 `surjOn_iUnion`

English:
theorem surjOn_iUnion
  given: {s : Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, SurjOn f s (t i))
  proof: surjOn_sUnion forall_mem_range.2 H

中文:
定理 surjOn_iUnion
  条件: {s : 集合 α} {t : ι -> 集合 β} {f : α -> β} (H : 对任意 i, 满射限制 f s (t i))
  证明: surjOn_sUnion forall_mem_range.2 H

Depends on / 依赖: forall_mem_range, surjOn_sUnion
-/
theorem surjOn_iUnion {s : Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
surjOn_sUnion forall_mem_range.2 H

/--
theorem `surjOn_iUnion_iUnion` / 定理 `surjOn_iUnion_iUnion`

English:
theorem surjOn_iUnion_iUnion
  statement: {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
  proof: surjOn_iUnion fun i => (H i).mono (subset_iUnion _ _) (Subset.refl _)

中文:
定理 surjOn_iUnion_iUnion
  结论: {s : ι -> 集合 α} {t : ι -> 集合 β} {f : α -> β}
  证明: surjOn_iUnion fun i => (H i).mono (subset_iUnion _ _) (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, subset_iUnion, surjOn_iUnion
-/
theorem surjOn_iUnion_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
    (H : forall i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surjOn_iUnion fun i => (H i).mono (subset_iUnion _ _) (Subset.refl _)

/--
theorem `surjOn_iUnion₂` / 定理 `surjOn_iUnion₂`

English:
theorem surjOn_iUnion₂
  statement: {s : Set α} {t : forall i, κ i -> Set β} {f : α -> β}
  proof: surjOn_iUnion fun i => surjOn_iUnion (H i)

中文:
定理 surjOn_iUnion₂
  结论: {s : 集合 α} {t : 对任意 i, κ i -> 集合 β} {f : α -> β}
  证明: surjOn_iUnion fun i => surjOn_iUnion (H i)

Depends on / 依赖: surjOn_iUnion
-/
theorem surjOn_iUnion₂ {s : Set α} {t : forall i, κ i -> Set β} {f : α -> β}
    (H : forall i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surjOn_iUnion fun i => surjOn_iUnion (H i)

/--
theorem `surjOn_iUnion₂_iUnion₂` / 定理 `surjOn_iUnion₂_iUnion₂`

English:
theorem surjOn_iUnion₂_iUnion₂
  statement: {s : forall i, κ i -> Set α} {t : forall i, κ i -> Set β} {f : α -> β}
  proof: surjOn_iUnion_iUnion fun i => surjOn_iUnion_iUnion (H i)

中文:
定理 surjOn_iUnion₂_iUnion₂
  结论: {s : 对任意 i, κ i -> 集合 α} {t : 对任意 i, κ i -> 集合 β} {f : α -> β}
  证明: surjOn_iUnion_iUnion fun i => surjOn_iUnion_iUnion (H i)

Depends on / 依赖: surjOn_iUnion_iUnion
-/
theorem surjOn_iUnion₂_iUnion₂ {s : forall i, κ i -> Set α} {t : forall i, κ i -> Set β} {f : α -> β}
    (H : forall i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surjOn_iUnion_iUnion fun i => surjOn_iUnion_iUnion (H i)

/--
theorem `surjOn_iInter` / 定理 `surjOn_iInter`

English:
theorem surjOn_iInter
  statement: [Nonempty ι] {s : ι -> Set α} {t : Set β} {f : α -> β}
  proof: by
  intro y hy
  rw [Hinj.image_iInter_eq]; rw [mem_iInter]
  exact fun i => H i hy

中文:
定理 surjOn_i整数er
  结论: [非空 ι] {s : ι -> 集合 α} {t : 集合 β} {f : α -> β}
  证明: by
  intro y hy
  rw [Hinj.image_iInter_eq]; rw [mem_iInter]
  exact fun i => H i hy

Depends on / 依赖: Hinj.image_iInter_eq, image_iInter_eq, mem_iInter
-/
theorem surjOn_iInter [Nonempty ι] {s : ι -> Set α} {t : Set β} {f : α -> β}
    (H : forall i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_iInter_eq]; rw [mem_iInter]
  exact fun i => H i hy

/--
theorem `surjOn_iInter_iInter` / 定理 `surjOn_iInter_iInter`

English:
theorem surjOn_iInter_iInter
  statement: [Nonempty ι] {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
  proof: surjOn_iInter (fun i => (H i).mono (Subset.refl _) (iInter_subset _ _)) Hinj

中文:
定理 surjOn_i整数er_i整数er
  结论: [非空 ι] {s : ι -> 集合 α} {t : ι -> 集合 β} {f : α -> β}
  证明: surjOn_iInter (fun i => (H i).mono (Subset.refl _) (iInter_subset _ _)) Hinj

Depends on / 依赖: Subset, Subset.refl, iInter_subset, surjOn_iInter
-/
theorem surjOn_iInter_iInter [Nonempty ι] {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
    (H : forall i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surjOn_iInter (fun i => (H i).mono (Subset.refl _) (iInter_subset _ _)) Hinj



/--
theorem `bijOn_iUnion` / 定理 `bijOn_iUnion`

English:
theorem bijOn_iUnion
  statement: {s : ι -> Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, BijOn f (s i) (t i))
  proof: ⟨mapsTo_iUnion_iUnion fun i => (H i).mapsTo, Hinj, surjOn_iUnion_iUnion fun i => (H i).surjOn⟩

中文:
定理 bijOn_iUnion
  结论: {s : ι -> 集合 α} {t : ι -> 集合 β} {f : α -> β} (H : 对任意 i, 双射限制 f (s i) (t i))
  证明: ⟨mapsTo_iUnion_iUnion fun i => (H i).mapsTo, Hinj, surjOn_iUnion_iUnion fun i => (H i).surjOn⟩

Depends on / 依赖: mapsTo, mapsTo_iUnion_iUnion, surjOn, surjOn_iUnion_iUnion
-/
theorem bijOn_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨mapsTo_iUnion_iUnion fun i => (H i).mapsTo, Hinj, surjOn_iUnion_iUnion fun i => (H i).surjOn⟩

/--
theorem `bijOn_iInter` / 定理 `bijOn_iInter`

English:
theorem bijOn_iInter
  statement: [hi : Nonempty ι] {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
  proof: ⟨mapsTo_iInter_iInter fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (iInter_subset _ _),
    surjOn_iInter_iInter (fun i => (H i).surjOn) Hinj⟩

中文:
定理 bijOn_i整数er
  结论: [hi : 非空 ι] {s : ι -> 集合 α} {t : ι -> 集合 β} {f : α -> β}
  证明: ⟨mapsTo_iInter_iInter fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (iInter_subset _ _),
    surjOn_iInter_iInter (fun i => (H i).surjOn) Hinj⟩

Depends on / 依赖: hi.elim, iInter_subset, injOn.mono, mapsTo, mapsTo_iInter_iInter, surjOn, surjOn_iInter_iInter
-/
theorem bijOn_iInter [hi : Nonempty ι] {s : ι -> Set α} {t : ι -> Set β} {f : α -> β}
    (H : forall i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨mapsTo_iInter_iInter fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (iInter_subset _ _),
    surjOn_iInter_iInter (fun i => (H i).surjOn) Hinj⟩

/--
theorem `bijOn_iUnion_of_directed` / 定理 `bijOn_iUnion_of_directed`

English:
theorem bijOn_iUnion_of_directed
  statement: {s : ι -> Set α} (hs : Directed (· subseteq ·) s) {t : ι -> Set β}
  proof: bijOn_iUnion H inj_on_iUnion_of_directed hs fun i => (H i).injOn

中文:
定理 bijOn_iUnion_of_directed
  结论: {s : ι -> 集合 α} (hs : Directed (· subseteq ·) s) {t : ι -> 集合 β}
  证明: bijOn_iUnion H inj_on_iUnion_of_directed hs fun i => (H i).injOn

Depends on / 依赖: bijOn_iUnion, inj_on_iUnion_of_directed
-/
theorem bijOn_iUnion_of_directed {s : ι -> Set α} (hs : Directed (· subseteq ·) s) {t : ι -> Set β}
    {f : α -> β} (H : forall i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
bijOn_iUnion H inj_on_iUnion_of_directed hs fun i => (H i).injOn

/--
theorem `bijOn_iInter_of_directed` / 定理 `bijOn_iInter_of_directed`

English:
theorem bijOn_iInter_of_directed
  statement: [Nonempty ι] {s : ι -> Set α} (hs : Directed (· subseteq ·) s)
  proof: bijOn_iInter H inj_on_iUnion_of_directed hs fun i => (H i).injOn

中文:
定理 bijOn_i整数er_of_directed
  结论: [非空 ι] {s : ι -> 集合 α} (hs : Directed (· subseteq ·) s)
  证明: bijOn_iInter H inj_on_iUnion_of_directed hs fun i => (H i).injOn

Depends on / 依赖: bijOn_iInter, inj_on_iUnion_of_directed
-/
theorem bijOn_iInter_of_directed [Nonempty ι] {s : ι -> Set α} (hs : Directed (· subseteq ·) s)
    {t : ι -> Set β} {f : α -> β} (H : forall i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
bijOn_iInter H inj_on_iUnion_of_directed hs fun i => (H i).injOn

end Function

/-! ### `image`, `preimage` -/


section Image

/--
theorem `image_iUnion` / 定理 `image_iUnion`

English:
theorem image_iUnion
  given: {f : α -> β} {s : ι -> Set α}
  statement: (f '' ⋃ i, s i) = ⋃ i, f '' s i
  proof: by
  ext1 x
  simp only [mem_image, mem_iUnion, ← exists_and_right, exists_comm (α := α)]

中文:
定理 image_iUnion
  条件: {f : α -> β} {s : ι -> 集合 α}
  结论: (f '' ⋃ i, s i) = ⋃ i, f '' s i
  证明: by
  ext1 x
  simp only [mem_image, mem_iUnion, ← exists_and_right, exists_comm (α := α)]

Depends on / 依赖: exists_and_right, exists_comm, mem_iUnion, mem_image
-/
theorem image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp only [mem_image, mem_iUnion, ← exists_and_right, exists_comm (α := α)]

/--
theorem `image_iUnion₂` / 定理 `image_iUnion₂`

English:
theorem image_iUnion₂
  given: (f : α -> β) (s : forall i, κ i -> Set α)
  proof: by simp_rw [image_iUnion]

中文:
定理 image_iUnion₂
  条件: (f : α -> β) (s : 对任意 i, κ i -> 集合 α)
  证明: by simp_rw [image_iUnion]

Depends on / 依赖: image_iUnion, simp_rw
-/
theorem image_iUnion₂ (f : α -> β) (s : forall i, κ i -> Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_iUnion]

/--
theorem `univ_subtype` / 定理 `univ_subtype`

English:
theorem univ_subtype
  given: {p : α -> Prop}
  statement: (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩}
  proof: Set.ext fun ⟨x, h⟩ => by simp [h]

中文:
定理 univ_subtype
  条件: {p : α -> 命题}
  结论: (univ : 集合 (子类型 p)) = ⋃ (x) (h : p x), {⟨x, h⟩}
  证明: Set.ext fun ⟨x, h⟩ => by simp [h]

Depends on / 依赖: Set.ext
-/
theorem univ_subtype {p : α -> Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]

/--
theorem `range_eq_iUnion` / 定理 `range_eq_iUnion`

English:
theorem range_eq_iUnion
  given: {ι} (f : ι -> α)
  statement: range f = ⋃ i, {f i}
  proof: Set.ext fun a => by simp [@eq_comm α a]

中文:
定理 range_eq_iUnion
  条件: {ι} (f : ι -> α)
  结论: range f = ⋃ i, {f i}
  证明: Set.ext fun a => by simp [@eq_comm α a]

Depends on / 依赖: Set.ext, eq_comm
-/
theorem range_eq_iUnion {ι} (f : ι -> α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]

/--
theorem `image_eq_iUnion` / 定理 `image_eq_iUnion`

English:
theorem image_eq_iUnion
  given: (f : α -> β) (s : Set α)
  statement: f '' s = ⋃ i in s, {f i}
  proof: Set.ext fun b => by simp [@eq_comm β b]

中文:
定理 image_eq_iUnion
  条件: (f : α -> β) (s : 集合 α)
  结论: f '' s = ⋃ i in s, {f i}
  证明: Set.ext fun b => by simp [@eq_comm β b]

Depends on / 依赖: Set.ext, eq_comm
-/
theorem image_eq_iUnion (f : α -> β) (s : Set α) : f '' s = ⋃ i in s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]

/--
theorem `biUnion_range` / 定理 `biUnion_range`

English:
theorem biUnion_range
  given: {f : ι -> α} {g : α -> Set β}
  statement: ⋃ x in range f, g x = ⋃ y, g (f y)
  proof: iSup_range

@[simp]

中文:
定理 biUnion_range
  条件: {f : ι -> α} {g : α -> 集合 β}
  结论: ⋃ x in range f, g x = ⋃ y, g (f y)
  证明: iSup_range

@[simp]

Depends on / 依赖: iSup_range
-/
theorem biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in range f, g x = ⋃ y, g (f y) :=
  iSup_range

@[simp]
/--
theorem `iUnion_iUnion_eq'` / 定理 `iUnion_iUnion_eq'`

English:
theorem iUnion_iUnion_eq'
  given: {f : ι -> α} {g : α -> Set β}
  proof: by simpa using biUnion_range

中文:
定理 iUnion_iUnion_eq'
  条件: {f : ι -> α} {g : α -> 集合 β}
  证明: by simpa using biUnion_range

Depends on / 依赖: biUnion_range
-/
theorem iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
    ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y) := by simpa using biUnion_range

/--
theorem `biInter_range` / 定理 `biInter_range`

English:
theorem biInter_range
  given: {f : ι -> α} {g : α -> Set β}
  statement: ⋂ x in range f, g x = ⋂ y, g (f y)
  proof: iInf_range

@[simp]

中文:
定理 bi整数er_range
  条件: {f : ι -> α} {g : α -> 集合 β}
  结论: ⋂ x in range f, g x = ⋂ y, g (f y)
  证明: iInf_range

@[simp]

Depends on / 依赖: iInf_range
-/
theorem biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in range f, g x = ⋂ y, g (f y) :=
  iInf_range

@[simp]
/--
theorem `iInter_iInter_eq'` / 定理 `iInter_iInter_eq'`

English:
theorem iInter_iInter_eq'
  given: {f : ι -> α} {g : α -> Set β}
  proof: by simpa using biInter_range

中文:
定理 i整数er_i整数er_eq'
  条件: {f : ι -> α} {g : α -> 集合 β}
  证明: by simpa using biInter_range

Depends on / 依赖: biInter_range
-/
theorem iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
    ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y) := by simpa using biInter_range

variable {s : Set γ} {f : γ -> α} {g : α -> Set β}

/--
theorem `biUnion_image` / 定理 `biUnion_image`

English:
theorem biUnion_image
  statement: ⋃ x in f '' s, g x = ⋃ y in s, g (f y)
  proof: iSup_image

中文:
定理 biUnion_image
  结论: ⋃ x in f '' s, g x = ⋃ y in s, g (f y)
  证明: iSup_image

Depends on / 依赖: iSup_image
-/
theorem biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y) :=
  iSup_image

/--
theorem `biInter_image` / 定理 `biInter_image`

English:
theorem biInter_image
  statement: ⋂ x in f '' s, g x = ⋂ y in s, g (f y)
  proof: iInf_image

中文:
定理 bi整数er_image
  结论: ⋂ x in f '' s, g x = ⋂ y in s, g (f y)
  证明: iInf_image

Depends on / 依赖: iInf_image
-/
theorem biInter_image : ⋂ x in f '' s, g x = ⋂ y in s, g (f y) :=
  iInf_image

/--
lemma `biUnion_image2` / 引理 `biUnion_image2`

English:
lemma biUnion_image2
  given: (s : Set α) (t : Set β) (f : α -> β -> γ) (g : γ -> Set δ)
  proof: iSup_image2 ..

中文:
引理 biUnion_image2
  条件: (s : 集合 α) (t : 集合 β) (f : α -> β -> γ) (g : γ -> 集合 δ)
  证明: iSup_image2 ..

Depends on / 依赖: iSup_image2
-/
lemma biUnion_image2 (s : Set α) (t : Set β) (f : α -> β -> γ) (g : γ -> Set δ) :
    ⋃ c in image2 f s t, g c = ⋃ a in s, ⋃ b in t, g (f a b) := iSup_image2 ..

/--
lemma `biInter_image2` / 引理 `biInter_image2`

English:
lemma biInter_image2
  given: (s : Set α) (t : Set β) (f : α -> β -> γ) (g : γ -> Set δ)
  proof: iInf_image2 ..

中文:
引理 bi整数er_image2
  条件: (s : 集合 α) (t : 集合 β) (f : α -> β -> γ) (g : γ -> 集合 δ)
  证明: iInf_image2 ..

Depends on / 依赖: iInf_image2
-/
lemma biInter_image2 (s : Set α) (t : Set β) (f : α -> β -> γ) (g : γ -> Set δ) :
    ⋂ c in image2 f s t, g c = ⋂ a in s, ⋂ b in t, g (f a b) := iInf_image2 ..

/--
lemma `iUnion_inter_iUnion` / 引理 `iUnion_inter_iUnion`

English:
lemma iUnion_inter_iUnion
  given: {ι κ : Sort*} (f : ι -> Set α) (g : κ -> Set α)
  proof: by simp_rw [iUnion_inter, inter_iUnion]

中文:
引理 iUnion_inter_iUnion
  条件: {ι κ : 类型层*} (f : ι -> 集合 α) (g : κ -> 集合 α)
  证明: by simp_rw [iUnion_inter, inter_iUnion]

Depends on / 依赖: iUnion_inter, inter_iUnion, simp_rw
-/
lemma iUnion_inter_iUnion {ι κ : Sort*} (f : ι -> Set α) (g : κ -> Set α) :
    (⋃ i, f i) inter ⋃ j, g j = ⋃ i, ⋃ j, f i inter g j := by simp_rw [iUnion_inter, inter_iUnion]

/--
lemma `iInter_union_iInter` / 引理 `iInter_union_iInter`

English:
lemma iInter_union_iInter
  given: {ι κ : Sort*} (f : ι -> Set α) (g : κ -> Set α)
  proof: by simp_rw [iInter_union, union_iInter]

中文:
引理 i整数er_union_i整数er
  条件: {ι κ : 类型层*} (f : ι -> 集合 α) (g : κ -> 集合 α)
  证明: by simp_rw [iInter_union, union_iInter]

Depends on / 依赖: iInter_union, simp_rw, union_iInter
-/
lemma iInter_union_iInter {ι κ : Sort*} (f : ι -> Set α) (g : κ -> Set α) :
    (⋂ i, f i) union ⋂ j, g j = ⋂ i, ⋂ j, f i union g j := by simp_rw [iInter_union, union_iInter]

/--
lemma `iUnion₂_inter_iUnion₂` / 引理 `iUnion₂_inter_iUnion₂`

English:
lemma iUnion₂_inter_iUnion₂
  statement: {ι₁ κ₁ : Sort*} {ι₂ : ι₁ -> Sort*} {k₂ : κ₁ -> Sort*}
  proof: by
  simp_rw [iUnion_inter, inter_iUnion]

中文:
引理 iUnion₂_inter_iUnion₂
  结论: {ι₁ κ₁ : 类型层*} {ι₂ : ι₁ -> 类型层*} {k₂ : κ₁ -> 类型层*}
  证明: by
  simp_rw [iUnion_inter, inter_iUnion]

Depends on / 依赖: iUnion_inter, inter_iUnion, simp_rw
-/
lemma iUnion₂_inter_iUnion₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ -> Sort*} {k₂ : κ₁ -> Sort*}
    (f : forall i₁, ι₂ i₁ -> Set α) (g : forall j₁, k₂ j₁ -> Set α) :
    (⋃ i₁, ⋃ i₂, f i₁ i₂) inter ⋃ j₁, ⋃ j₂, g j₁ j₂ = ⋃ i₁, ⋃ i₂, ⋃ j₁, ⋃ j₂, f i₁ i₂ inter g j₁ j₂ := by
  simp_rw [iUnion_inter, inter_iUnion]

/--
lemma `iInter₂_union_iInter₂` / 引理 `iInter₂_union_iInter₂`

English:
lemma iInter₂_union_iInter₂
  statement: {ι₁ κ₁ : Sort*} {ι₂ : ι₁ -> Sort*} {k₂ : κ₁ -> Sort*}
  proof: by
  simp_rw [iInter_union, union_iInter]

中文:
引理 i整数er₂_union_i整数er₂
  结论: {ι₁ κ₁ : 类型层*} {ι₂ : ι₁ -> 类型层*} {k₂ : κ₁ -> 类型层*}
  证明: by
  simp_rw [iInter_union, union_iInter]

Depends on / 依赖: iInter_union, simp_rw, union_iInter
-/
lemma iInter₂_union_iInter₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ -> Sort*} {k₂ : κ₁ -> Sort*}
    (f : forall i₁, ι₂ i₁ -> Set α) (g : forall j₁, k₂ j₁ -> Set α) :
    (⋂ i₁, ⋂ i₂, f i₁ i₂) union ⋂ j₁, ⋂ j₂, g j₁ j₂ = ⋂ i₁, ⋂ i₂, ⋂ j₁, ⋂ j₂, f i₁ i₂ union g j₁ j₂ := by
  simp_rw [iInter_union, union_iInter]

/--
theorem `biUnion_inter_of_pairwise_disjoint` / 定理 `biUnion_inter_of_pairwise_disjoint`

English:
theorem biUnion_inter_of_pairwise_disjoint
  statement: {ι : Type*} {f : ι -> Set α}
  proof: biSup_inter_of_pairwise_disjoint h s t

中文:
定理 biUnion_inter_of_pairwise_disjoint
  结论: {ι : 类型} {f : ι -> 集合 α}
  证明: biSup_inter_of_pairwise_disjoint h s t

Depends on / 依赖: biSup_inter_of_pairwise_disjoint
-/
theorem biUnion_inter_of_pairwise_disjoint {ι : Type*} {f : ι -> Set α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⋃ i in (s inter t), f i) = (⋃ i in s, f i) inter (⋃ i in t, f i) :=
  biSup_inter_of_pairwise_disjoint h s t

/--
theorem `biUnion_iInter_of_pairwise_disjoint` / 定理 `biUnion_iInter_of_pairwise_disjoint`

English:
theorem biUnion_iInter_of_pairwise_disjoint
  statement: {ι κ : Type*}
  proof: biSup_iInter_of_pairwise_disjoint h s

中文:
定理 biUnion_i整数er_of_pairwise_disjoint
  结论: {ι κ : 类型}
  证明: biSup_iInter_of_pairwise_disjoint h s

Depends on / 依赖: biSup_iInter_of_pairwise_disjoint
-/
theorem biUnion_iInter_of_pairwise_disjoint {ι κ : Type*}
    [hκ : Nonempty κ] {f : ι -> Set α} (h : Pairwise (Disjoint on f)) (s : κ -> Set ι) :
    (⋃ i in (⋂ j, s j), f i) = ⋂ j, (⋃ i in s j, f i) :=
  biSup_iInter_of_pairwise_disjoint h s

end Image

section Preimage

/--
theorem `monotone_preimage` / 定理 `monotone_preimage`

English:
theorem monotone_preimage
  given: {f : α -> β}
  statement: Monotone (preimage f)
  proof: fun _ _ h => preimage_mono h

@[simp]

中文:
定理 monotone_preimage
  条件: {f : α -> β}
  结论: 递增 (原像 f)
  证明: fun _ _ h => preimage_mono h

@[simp]

Depends on / 依赖: preimage_mono
-/
theorem monotone_preimage {f : α -> β} : Monotone (preimage f) := fun _ _ h => preimage_mono h

@[simp]
/--
theorem `preimage_iUnion` / 定理 `preimage_iUnion`

English:
theorem preimage_iUnion
  given: {f : α -> β} {s : ι -> Set β}
  statement: (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
  proof: Set.ext by simp [preimage]

中文:
定理 preimage_iUnion
  条件: {f : α -> β} {s : ι -> 集合 β}
  结论: (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
  证明: Set.ext by simp [preimage]

Depends on / 依赖: Set.ext, preimage
-/
theorem preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
Set.ext by simp [preimage]

/--
theorem `preimage_iUnion₂` / 定理 `preimage_iUnion₂`

English:
theorem preimage_iUnion₂
  given: {f : α -> β} {s : forall i, κ i -> Set β}
  proof: by simp_rw [preimage_iUnion]

中文:
定理 preimage_iUnion₂
  条件: {f : α -> β} {s : 对任意 i, κ i -> 集合 β}
  证明: by simp_rw [preimage_iUnion]

Depends on / 依赖: preimage_iUnion, simp_rw
-/
theorem preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -> Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iUnion]

/--
theorem `image_sUnion` / 定理 `image_sUnion`

English:
theorem image_sUnion
  given: {f : α -> β} {s : Set (Set α)}
  statement: (f '' ⋃₀ s) = ⋃₀ (image f '' s)
  proof: by
  ext
  simp only [Set.mem_iUnion, Set.sUnion_image]
  grind

@[simp]

中文:
定理 image_sUnion
  条件: {f : α -> β} {s : 集合 (集合 α)}
  结论: (f '' ⋃₀ s) = ⋃₀ (像 f '' s)
  证明: by
  ext
  simp only [Set.mem_iUnion, Set.sUnion_image]
  grind

@[simp]

Depends on / 依赖: Set.mem_iUnion, Set.sUnion_image, mem_iUnion, sUnion_image
-/
theorem image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀ s) = ⋃₀ (image f '' s) := by
  ext
  simp only [Set.mem_iUnion, Set.sUnion_image]
  grind

@[simp]
/--
theorem `preimage_sUnion` / 定理 `preimage_sUnion`

English:
theorem preimage_sUnion
  given: {f : α -> β} {s : Set (Set β)}
  statement: f ⁻¹' ⋃₀ s = ⋃ t in s, f ⁻¹' t
  proof: by
  rw [sUnion_eq_biUnion]; rw [preimage_iUnion₂]

中文:
定理 preimage_sUnion
  条件: {f : α -> β} {s : 集合 (集合 β)}
  结论: f ⁻¹' ⋃₀ s = ⋃ t in s, f ⁻¹' t
  证明: by
  rw [sUnion_eq_biUnion]; rw [preimage_iUnion₂]

Depends on / 依赖: sUnion_eq_biUnion
-/
theorem preimage_sUnion {f : α -> β} {s : Set (Set β)} : f ⁻¹' ⋃₀ s = ⋃ t in s, f ⁻¹' t := by
  rw [sUnion_eq_biUnion]; rw [preimage_iUnion₂]

/--
theorem `preimage_iInter` / 定理 `preimage_iInter`

English:
theorem preimage_iInter
  given: {f : α -> β} {s : ι -> Set β}
  statement: (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
  proof: by
  ext; simp

中文:
定理 preimage_i整数er
  条件: {f : α -> β} {s : ι -> 集合 β}
  结论: (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
  证明: by
  ext; simp
-/
theorem preimage_iInter {f : α -> β} {s : ι -> Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext; simp

/--
theorem `preimage_iInter₂` / 定理 `preimage_iInter₂`

English:
theorem preimage_iInter₂
  given: {f : α -> β} {s : forall i, κ i -> Set β}
  proof: by simp_rw [preimage_iInter]

@[simp]

中文:
定理 preimage_i整数er₂
  条件: {f : α -> β} {s : 对任意 i, κ i -> 集合 β}
  证明: by simp_rw [preimage_iInter]

@[simp]

Depends on / 依赖: preimage_iInter, simp_rw
-/
theorem preimage_iInter₂ {f : α -> β} {s : forall i, κ i -> Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iInter]

@[simp]
/--
theorem `preimage_sInter` / 定理 `preimage_sInter`

English:
theorem preimage_sInter
  given: {f : α -> β} {s : Set (Set β)}
  statement: f ⁻¹' ⋂₀ s = ⋂ t in s, f ⁻¹' t
  proof: by
  rw [sInter_eq_biInter]; rw [preimage_iInter₂]

@[simp]

中文:
定理 preimage_s整数er
  条件: {f : α -> β} {s : 集合 (集合 β)}
  结论: f ⁻¹' ⋂₀ s = ⋂ t in s, f ⁻¹' t
  证明: by
  rw [sInter_eq_biInter]; rw [preimage_iInter₂]

@[simp]

Depends on / 依赖: sInter_eq_biInter
-/
theorem preimage_sInter {f : α -> β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t in s, f ⁻¹' t := by
  rw [sInter_eq_biInter]; rw [preimage_iInter₂]

@[simp]
/--
theorem `biUnion_preimage_singleton` / 定理 `biUnion_preimage_singleton`

English:
theorem biUnion_preimage_singleton
  given: (f : α -> β) (s : Set β)
  statement: ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
  proof: by
  rw [← preimage_iUnion₂]; rw [biUnion_of_singleton]

中文:
定理 biUnion_preimage_singleton
  条件: (f : α -> β) (s : 集合 β)
  结论: ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
  证明: by
  rw [← preimage_iUnion₂]; rw [biUnion_of_singleton]

Depends on / 依赖: biUnion_of_singleton
-/
theorem biUnion_preimage_singleton (f : α -> β) (s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s := by
  rw [← preimage_iUnion₂]; rw [biUnion_of_singleton]

/--
theorem `biUnion_range_preimage_singleton` / 定理 `biUnion_range_preimage_singleton`

English:
theorem biUnion_range_preimage_singleton
  given: (f : α -> β)
  statement: ⋃ y in range f, f ⁻¹' {y} = univ
  proof: by
  rw [biUnion_preimage_singleton]; rw [preimage_range]

中文:
定理 biUnion_range_preimage_singleton
  条件: (f : α -> β)
  结论: ⋃ y in range f, f ⁻¹' {y} = univ
  证明: by
  rw [biUnion_preimage_singleton]; rw [preimage_range]

Depends on / 依赖: biUnion_preimage_singleton, preimage_range
-/
theorem biUnion_range_preimage_singleton (f : α -> β) : ⋃ y in range f, f ⁻¹' {y} = univ := by
  rw [biUnion_preimage_singleton]; rw [preimage_range]

end Preimage

section Prod

/--
theorem `prod_iUnion` / 定理 `prod_iUnion`

English:
theorem prod_iUnion
  given: {s : Set α} {t : ι -> Set β}
  statement: (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i
  proof: by
  ext
  simp

中文:
定理 prod_iUnion
  条件: {s : 集合 α} {t : ι -> 集合 β}
  结论: (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i
  证明: by
  ext
  simp
-/
theorem prod_iUnion {s : Set α} {t : ι -> Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp

/--
theorem `prod_iUnion₂` / 定理 `prod_iUnion₂`

English:
theorem prod_iUnion₂
  given: {s : Set α} {t : forall i, κ i -> Set β}
  proof: by simp_rw [prod_iUnion]

中文:
定理 prod_iUnion₂
  条件: {s : 集合 α} {t : 对任意 i, κ i -> 集合 β}
  证明: by simp_rw [prod_iUnion]

Depends on / 依赖: prod_iUnion, simp_rw
-/
theorem prod_iUnion₂ {s : Set α} {t : forall i, κ i -> Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_iUnion]

/--
theorem `prod_sUnion` / 定理 `prod_sUnion`

English:
theorem prod_sUnion
  given: {s : Set α} {C : Set (Set β)}
  statement: s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ t) '' C)
  proof: by
  simp_rw [sUnion_eq_biUnion, biUnion_image, prod_iUnion₂]

中文:
定理 prod_sUnion
  条件: {s : 集合 α} {C : 集合 (集合 β)}
  结论: s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ t) '' C)
  证明: by
  simp_rw [sUnion_eq_biUnion, biUnion_image, prod_iUnion₂]

Depends on / 依赖: biUnion_image, sUnion_eq_biUnion, simp_rw
-/
theorem prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_biUnion, biUnion_image, prod_iUnion₂]

/--
theorem `iUnion_prod_const` / 定理 `iUnion_prod_const`

English:
theorem iUnion_prod_const
  given: {s : ι -> Set α} {t : Set β}
  statement: (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t
  proof: by
  ext
  simp

中文:
定理 iUnion_prod_const
  条件: {s : ι -> 集合 α} {t : 集合 β}
  结论: (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t
  证明: by
  ext
  simp
-/
theorem iUnion_prod_const {s : ι -> Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp

/--
theorem `iUnion₂_prod_const` / 定理 `iUnion₂_prod_const`

English:
theorem iUnion₂_prod_const
  given: {s : forall i, κ i -> Set α} {t : Set β}
  proof: by simp_rw [iUnion_prod_const]

中文:
定理 iUnion₂_prod_const
  条件: {s : 对任意 i, κ i -> 集合 α} {t : 集合 β}
  证明: by simp_rw [iUnion_prod_const]

Depends on / 依赖: iUnion_prod_const, simp_rw
-/
theorem iUnion₂_prod_const {s : forall i, κ i -> Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [iUnion_prod_const]

/--
theorem `sUnion_prod_const` / 定理 `sUnion_prod_const`

English:
theorem sUnion_prod_const
  given: {C : Set (Set α)} {t : Set β}
  proof: by
  simp only [sUnion_eq_biUnion, iUnion₂_prod_const, biUnion_image]

中文:
定理 sUnion_prod_const
  条件: {C : 集合 (集合 α)} {t : 集合 β}
  证明: by
  simp only [sUnion_eq_biUnion, iUnion₂_prod_const, biUnion_image]

Depends on / 依赖: biUnion_image, sUnion_eq_biUnion
-/
theorem sUnion_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀ C ×ˢ t = ⋃₀ ((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [sUnion_eq_biUnion, iUnion₂_prod_const, biUnion_image]

/--
theorem `iUnion_prod` / 定理 `iUnion_prod`

English:
theorem iUnion_prod
  given: {ι ι' α β} (s : ι -> Set α) (t : ι' -> Set β)
  proof: by
  ext
  simp

中文:
定理 iUnion_prod
  条件: {ι ι' α β} (s : ι -> 集合 α) (t : ι' -> 集合 β)
  证明: by
  ext
  simp
-/
theorem iUnion_prod {ι ι' α β} (s : ι -> Set α) (t : ι' -> Set β) :
    ⋃ x : ι × ι', s x.1 ×ˢ t x.2 = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp

/--
lemma `iUnion_prod'` / 引理 `iUnion_prod'`

English:
lemma iUnion_prod'
  given: (f : β × γ -> Set α)
  statement: ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), f (i, j)
  proof: iSup_prod

中文:
引理 iUnion_prod'
  条件: (f : β × γ -> 集合 α)
  结论: ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), f (i, j)
  证明: iSup_prod

Depends on / 依赖: iSup_prod
-/
lemma iUnion_prod' (f : β × γ -> Set α) : ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), f (i, j) :=
  iSup_prod

/--
theorem `iUnion_prod_of_monotone` / 定理 `iUnion_prod_of_monotone`

English:
theorem iUnion_prod_of_monotone
  statement: [SemilatticeSup α] {s : α -> Set β} {t : α -> Set γ} (hs : Monotone s)
  proof: by
  ext ⟨z, w⟩; simp only [mem_prod, mem_iUnion, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩

中文:
定理 iUnion_prod_of_monotone
  结论: [SemilatticeSup α] {s : α -> 集合 β} {t : α -> 集合 γ} (hs : 递增 s)
  证明: by
  ext ⟨z, w⟩; simp only [mem_prod, mem_iUnion, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩

Depends on / 依赖: and_imp, exists_imp, iff_def, le_sup_left, le_sup_right, mem_iUnion, mem_prod
-/
theorem iUnion_prod_of_monotone [SemilatticeSup α] {s : α -> Set β} {t : α -> Set γ} (hs : Monotone s)
    (ht : Monotone t) : ⋃ x, s x ×ˢ t x = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩; simp only [mem_prod, mem_iUnion, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩

/--
lemma `biUnion_prod` / 引理 `biUnion_prod`

English:
lemma biUnion_prod
  given: {α β γ} (s : Set α) (t : Set β) (f : α -> Set γ) (g : β -> Set δ)
  proof: by
  ext ⟨_, _⟩
  simp only [mem_iUnion, mem_prod, exists_prop, Prod.exists]; tauto

中文:
引理 biUnion_prod
  条件: {α β γ} (s : 集合 α) (t : 集合 β) (f : α -> 集合 γ) (g : β -> 集合 δ)
  证明: by
  ext ⟨_, _⟩
  simp only [mem_iUnion, mem_prod, exists_prop, Prod.exists]; tauto

Depends on / 依赖: Prod.exists, exists_prop, mem_iUnion, mem_prod
-/
lemma biUnion_prod {α β γ} (s : Set α) (t : Set β) (f : α -> Set γ) (g : β -> Set δ) :
    ⋃ x in s ×ˢ t, f x.1 ×ˢ g x.2 = (⋃ x in s, f x) ×ˢ (⋃ x in t, g x) := by
  ext ⟨_, _⟩
  simp only [mem_iUnion, mem_prod, exists_prop, Prod.exists]; tauto

/--
lemma `biUnion_prod'` / 引理 `biUnion_prod'`

English:
lemma biUnion_prod'
  given: (s : Set β) (t : Set γ) (f : β × γ -> Set α)
  proof: biSup_prod

中文:
引理 biUnion_prod'
  条件: (s : 集合 β) (t : 集合 γ) (f : β × γ -> 集合 α)
  证明: biSup_prod

Depends on / 依赖: biSup_prod
-/
lemma biUnion_prod' (s : Set β) (t : Set γ) (f : β × γ -> Set α) :
    ⋃ x in s ×ˢ t, f x = ⋃ (i in s) (j in t), f (i, j) :=
  biSup_prod

/--
theorem `sInter_prod_sInter_subset` / 定理 `sInter_prod_sInter_subset`

English:
theorem sInter_prod_sInter_subset
  given: (S : Set (Set α)) (T : Set (Set β))
  proof: subset_iInter₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩

中文:
定理 s整数er_prod_s整数er_subset
  条件: (S : 集合 (集合 α)) (T : 集合 (集合 β))
  证明: subset_iInter₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩
-/
theorem sInter_prod_sInter_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T subseteq ⋂ r in S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_iInter₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩

/--
theorem `sInter_prod_sInter` / 定理 `sInter_prod_sInter`

English:
theorem sInter_prod_sInter
  given: {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty)
  proof: by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => ?_
  rw [mem_iInter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩

中文:
定理 s整数er_prod_s整数er
  条件: {S : 集合 (集合 α)} {T : 集合 (集合 β)} (hS : S.非空) (hT : T.非空)
  证明: by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => ?_
  rw [mem_iInter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩

Depends on / 依赖: Set.Subset.antisymm, Subset, antisymm, sInter_prod_sInter_subset
-/
theorem sInter_prod_sInter {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r in S ×ˢ T, r.1 ×ˢ r.2 := by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => ?_
  rw [mem_iInter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩

/--
theorem `sInter_prod` / 定理 `sInter_prod`

English:
theorem sInter_prod
  given: {S : Set (Set α)} (hS : S.Nonempty) (t : Set β)
  proof: by
  rw [← sInter_singleton t]; rw [sInter_prod_sInter hS (singleton_nonempty t)]; rw [sInter_singleton]
  simp_rw [prod_singleton, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

中文:
定理 s整数er_prod
  条件: {S : 集合 (集合 α)} (hS : S.非空) (t : 集合 β)
  证明: by
  rw [← sInter_singleton t]; rw [sInter_prod_sInter hS (singleton_nonempty t)]; rw [sInter_singleton]
  simp_rw [prod_singleton, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

Depends on / 依赖: biInter_and, iInter_exists, iInter_iInter_eq_right, mem_image, prod_singleton, sInter_prod_sInter, sInter_singleton, simp_rw, singleton_nonempty
-/
theorem sInter_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) :
    ⋂₀ S ×ˢ t = ⋂ s in S, s ×ˢ t := by
  rw [← sInter_singleton t]; rw [sInter_prod_sInter hS (singleton_nonempty t)]; rw [sInter_singleton]
  simp_rw [prod_singleton, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

/--
theorem `prod_sInter` / 定理 `prod_sInter`

English:
theorem prod_sInter
  given: {T : Set (Set β)} (hT : T.Nonempty) (s : Set α)
  proof: by
  rw [← sInter_singleton s]; rw [sInter_prod_sInter (singleton_nonempty s) hT]; rw [sInter_singleton]
  simp_rw [singleton_prod, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

中文:
定理 prod_s整数er
  条件: {T : 集合 (集合 β)} (hT : T.非空) (s : 集合 α)
  证明: by
  rw [← sInter_singleton s]; rw [sInter_prod_sInter (singleton_nonempty s) hT]; rw [sInter_singleton]
  simp_rw [singleton_prod, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

Depends on / 依赖: biInter_and, iInter_exists, iInter_iInter_eq_right, mem_image, sInter_prod_sInter, sInter_singleton, simp_rw, singleton_nonempty, singleton_prod
-/
theorem prod_sInter {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) :
    s ×ˢ ⋂₀ T = ⋂ t in T, s ×ˢ t := by
  rw [← sInter_singleton s]; rw [sInter_prod_sInter (singleton_nonempty s) hT]; rw [sInter_singleton]
  simp_rw [singleton_prod, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

/--
theorem `prod_iInter` / 定理 `prod_iInter`

English:
theorem prod_iInter
  given: {s : Set α} {t : ι -> Set β} [hι : Nonempty ι]
  proof: by
  ext x
  simp only [mem_prod, mem_iInter]
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩

中文:
定理 prod_i整数er
  条件: {s : 集合 α} {t : ι -> 集合 β} [hι : 非空 ι]
  证明: by
  ext x
  simp only [mem_prod, mem_iInter]
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩

Depends on / 依赖: mem_iInter, mem_prod
-/
theorem prod_iInter {s : Set α} {t : ι -> Set β} [hι : Nonempty ι] :
    (s ×ˢ ⋂ i, t i) = ⋂ i, s ×ˢ t i := by
  ext x
  simp only [mem_prod, mem_iInter]
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩

end Prod

section Image2

variable (f : α -> β -> γ) {s : Set α} {t : Set β}

/--
theorem `image2_eq_iUnion` / 定理 `image2_eq_iUnion`

English:
theorem image2_eq_iUnion
  given: (s : Set α) (t : Set β)
  statement: image2 f s t = ⋃ (i in s) (j in t), {f i j}
  proof: by
  ext; simp [eq_comm]

中文:
定理 image2_eq_iUnion
  条件: (s : 集合 α) (t : 集合 β)
  结论: image2 f s t = ⋃ (i in s) (j in t), {f i j}
  证明: by
  ext; simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem image2_eq_iUnion (s : Set α) (t : Set β) : image2 f s t = ⋃ (i in s) (j in t), {f i j} := by
  ext; simp [eq_comm]

/--
theorem `iUnion_image_left` / 定理 `iUnion_image_left`

English:
theorem iUnion_image_left
  statement: ⋃ a in s, f a '' t = image2 f s t
  proof: by
  simp only [image2_eq_iUnion, image_eq_iUnion]

中文:
定理 iUnion_image_left
  结论: ⋃ a in s, f a '' t = image2 f s t
  证明: by
  simp only [image2_eq_iUnion, image_eq_iUnion]

Depends on / 依赖: image2_eq_iUnion, image_eq_iUnion
-/
theorem iUnion_image_left : ⋃ a in s, f a '' t = image2 f s t := by
  simp only [image2_eq_iUnion, image_eq_iUnion]

/--
theorem `iUnion_image_right` / 定理 `iUnion_image_right`

English:
theorem iUnion_image_right
  statement: ⋃ b in t, (f · b) '' s = image2 f s t
  proof: by
  rw [image2_swap]; rw [iUnion_image_left]

中文:
定理 iUnion_image_right
  结论: ⋃ b in t, (f · b) '' s = image2 f s t
  证明: by
  rw [image2_swap]; rw [iUnion_image_left]

Depends on / 依赖: iUnion_image_left, image2_swap
-/
theorem iUnion_image_right : ⋃ b in t, (f · b) '' s = image2 f s t := by
  rw [image2_swap]; rw [iUnion_image_left]

/--
theorem `image2_iUnion_left` / 定理 `image2_iUnion_left`

English:
theorem image2_iUnion_left
  given: (s : ι -> Set α) (t : Set β)
  proof: by
  simp only [← image_prod, iUnion_prod_const, image_iUnion]

中文:
定理 image2_iUnion_left
  条件: (s : ι -> 集合 α) (t : 集合 β)
  证明: by
  simp only [← image_prod, iUnion_prod_const, image_iUnion]

Depends on / 依赖: iUnion_prod_const, image_iUnion, image_prod
-/
theorem image2_iUnion_left (s : ι -> Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, iUnion_prod_const, image_iUnion]

/--
theorem `image2_iUnion_right` / 定理 `image2_iUnion_right`

English:
theorem image2_iUnion_right
  given: (s : Set α) (t : ι -> Set β)
  proof: by
  simp only [← image_prod, prod_iUnion, image_iUnion]

中文:
定理 image2_iUnion_right
  条件: (s : 集合 α) (t : ι -> 集合 β)
  证明: by
  simp only [← image_prod, prod_iUnion, image_iUnion]

Depends on / 依赖: image_iUnion, image_prod, prod_iUnion
-/
theorem image2_iUnion_right (s : Set α) (t : ι -> Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_iUnion, image_iUnion]

/--
theorem `image2_sUnion_left` / 定理 `image2_sUnion_left`

English:
theorem image2_sUnion_left
  given: (S : Set (Set α)) (t : Set β)
  proof: by
  aesop

中文:
定理 image2_sUnion_left
  条件: (S : 集合 (集合 α)) (t : 集合 β)
  证明: by
  aesop
-/
theorem image2_sUnion_left (S : Set (Set α)) (t : Set β) :
    image2 f (⋃₀ S) t = ⋃ s in S, image2 f s t := by
  aesop

/--
theorem `image2_sUnion_right` / 定理 `image2_sUnion_right`

English:
theorem image2_sUnion_right
  given: (s : Set α) (T : Set (Set β))
  proof: by
  aesop

中文:
定理 image2_sUnion_right
  条件: (s : 集合 α) (T : 集合 (集合 β))
  证明: by
  aesop
-/
theorem image2_sUnion_right (s : Set α) (T : Set (Set β)) :
    image2 f s (⋃₀ T) = ⋃ t in T, image2 f s t := by
  aesop

/--
theorem `image2_iUnion₂_left` / 定理 `image2_iUnion₂_left`

English:
theorem image2_iUnion₂_left
  given: (s : forall i, κ i -> Set α) (t : Set β)
  proof: by simp_rw [image2_iUnion_left]

中文:
定理 image2_iUnion₂_left
  条件: (s : 对任意 i, κ i -> 集合 α) (t : 集合 β)
  证明: by simp_rw [image2_iUnion_left]

Depends on / 依赖: image2_iUnion_left, simp_rw
-/
theorem image2_iUnion₂_left (s : forall i, κ i -> Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_iUnion_left]

/--
theorem `image2_iUnion₂_right` / 定理 `image2_iUnion₂_right`

English:
theorem image2_iUnion₂_right
  given: (s : Set α) (t : forall i, κ i -> Set β)
  proof: by
  simp_rw [image2_iUnion_right]

中文:
定理 image2_iUnion₂_right
  条件: (s : 集合 α) (t : 对任意 i, κ i -> 集合 β)
  证明: by
  simp_rw [image2_iUnion_right]

Depends on / 依赖: image2_iUnion_right, simp_rw
-/
theorem image2_iUnion₂_right (s : Set α) (t : forall i, κ i -> Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_iUnion_right]

/--
theorem `image2_iInter_subset_left` / 定理 `image2_iInter_subset_left`

English:
theorem image2_iInter_subset_left
  given: (s : ι -> Set α) (t : Set β)
  proof: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy

中文:
定理 image2_i整数er_subset_left
  条件: (s : ι -> 集合 α) (t : 集合 β)
  证明: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy

Depends on / 依赖: image2_subset_iff, mem_iInter, mem_image2_of_mem, simp_rw
-/
theorem image2_iInter_subset_left (s : ι -> Set α) (t : Set β) :
    image2 f (⋂ i, s i) t subseteq ⋂ i, image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy

/--
theorem `image2_iInter_subset_right` / 定理 `image2_iInter_subset_right`

English:
theorem image2_iInter_subset_right
  given: (s : Set α) (t : ι -> Set β)
  proof: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)

中文:
定理 image2_i整数er_subset_right
  条件: (s : 集合 α) (t : ι -> 集合 β)
  证明: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)

Depends on / 依赖: image2_subset_iff, mem_iInter, mem_image2_of_mem, simp_rw
-/
theorem image2_iInter_subset_right (s : Set α) (t : ι -> Set β) :
    image2 f s (⋂ i, t i) subseteq ⋂ i, image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)

/--
theorem `image2_iInter₂_subset_left` / 定理 `image2_iInter₂_subset_left`

English:
theorem image2_iInter₂_subset_left
  given: (s : forall i, κ i -> Set α) (t : Set β)
  proof: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy

中文:
定理 image2_i整数er₂_subset_left
  条件: (s : 对任意 i, κ i -> 集合 α) (t : 集合 β)
  证明: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy

Depends on / 依赖: image2_subset_iff, mem_iInter, mem_image2_of_mem, simp_rw
-/
theorem image2_iInter₂_subset_left (s : forall i, κ i -> Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t subseteq ⋂ (i) (j), image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy

/--
theorem `image2_iInter₂_subset_right` / 定理 `image2_iInter₂_subset_right`

English:
theorem image2_iInter₂_subset_right
  given: (s : Set α) (t : forall i, κ i -> Set β)
  proof: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)

中文:
定理 image2_i整数er₂_subset_right
  条件: (s : 集合 α) (t : 对任意 i, κ i -> 集合 β)
  证明: by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)

Depends on / 依赖: image2_subset_iff, mem_iInter, mem_image2_of_mem, simp_rw
-/
theorem image2_iInter₂_subset_right (s : Set α) (t : forall i, κ i -> Set β) :
    image2 f s (⋂ (i) (j), t i j) subseteq ⋂ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)

/--
theorem `image2_sInter_subset_left` / 定理 `image2_sInter_subset_left`

English:
theorem image2_sInter_subset_left
  given: (S : Set (Set α)) (t : Set β)
  proof: by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_left ..

中文:
定理 image2_s整数er_subset_left
  条件: (S : 集合 (集合 α)) (t : 集合 β)
  证明: by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_left ..

Depends on / 依赖: sInter_eq_biInter
-/
theorem image2_sInter_subset_left (S : Set (Set α)) (t : Set β) :
    image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f s t := by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_left ..

/--
theorem `image2_sInter_subset_right` / 定理 `image2_sInter_subset_right`

English:
theorem image2_sInter_subset_right
  given: (s : Set α) (T : Set (Set β))
  proof: by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_right ..

中文:
定理 image2_s整数er_subset_right
  条件: (s : 集合 α) (T : 集合 (集合 β))
  证明: by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_right ..

Depends on / 依赖: sInter_eq_biInter
-/
theorem image2_sInter_subset_right (s : Set α) (T : Set (Set β)) :
    image2 f s (⋂₀ T) subseteq ⋂ t in T, image2 f s t := by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_right ..

/--
theorem `prod_eq_biUnion_left` / 定理 `prod_eq_biUnion_left`

English:
theorem prod_eq_biUnion_left
  statement: s ×ˢ t = ⋃ a in s, (fun b => (a, b)) '' t
  proof: by
  rw [iUnion_image_left]; rw [image2_mk_eq_prod]

中文:
定理 prod_eq_biUnion_left
  结论: s ×ˢ t = ⋃ a in s, (fun b => (a, b)) '' t
  证明: by
  rw [iUnion_image_left]; rw [image2_mk_eq_prod]

Depends on / 依赖: iUnion_image_left, image2_mk_eq_prod
-/
theorem prod_eq_biUnion_left : s ×ˢ t = ⋃ a in s, (fun b => (a, b)) '' t := by
  rw [iUnion_image_left]; rw [image2_mk_eq_prod]

/--
theorem `prod_eq_biUnion_right` / 定理 `prod_eq_biUnion_right`

English:
theorem prod_eq_biUnion_right
  statement: s ×ˢ t = ⋃ b in t, (fun a => (a, b)) '' s
  proof: by
  rw [iUnion_image_right]; rw [image2_mk_eq_prod]

中文:
定理 prod_eq_biUnion_right
  结论: s ×ˢ t = ⋃ b in t, (fun a => (a, b)) '' s
  证明: by
  rw [iUnion_image_right]; rw [image2_mk_eq_prod]

Depends on / 依赖: iUnion_image_right, image2_mk_eq_prod
-/
theorem prod_eq_biUnion_right : s ×ˢ t = ⋃ b in t, (fun a => (a, b)) '' s := by
  rw [iUnion_image_right]; rw [image2_mk_eq_prod]

end Image2

section Seq

/--
theorem `seq_def` / 定理 `seq_def`

English:
theorem seq_def
  given: {s : Set (α -> β)} {t : Set α}
  statement: seq s t = ⋃ f in s, f '' t
  proof: by
  rw [seq_eq_image2]; rw [iUnion_image_left]

中文:
定理 seq_def
  条件: {s : 集合 (α -> β)} {t : 集合 α}
  结论: seq s t = ⋃ f in s, f '' t
  证明: by
  rw [seq_eq_image2]; rw [iUnion_image_left]

Depends on / 依赖: iUnion_image_left, seq_eq_image2
-/
theorem seq_def {s : Set (α -> β)} {t : Set α} : seq s t = ⋃ f in s, f '' t := by
  rw [seq_eq_image2]; rw [iUnion_image_left]

/--
theorem `seq_subset` / 定理 `seq_subset`

English:
theorem seq_subset
  given: {s : Set (α -> β)} {t : Set α} {u : Set β}
  proof: image2_subset_iff

@[gcongr, mono]

中文:
定理 seq_subset
  条件: {s : 集合 (α -> β)} {t : 集合 α} {u : 集合 β}
  证明: image2_subset_iff

@[gcongr, mono]

Depends on / 依赖: image2_subset_iff
-/
theorem seq_subset {s : Set (α -> β)} {t : Set α} {u : Set β} :
    seq s t subseteq u ↔ forall f in s, forall a in t, (f : α -> β) a in u :=
  image2_subset_iff

@[gcongr, mono]
/--
theorem `seq_mono` / 定理 `seq_mono`

English:
theorem seq_mono
  given: {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ subseteq s₁) (ht : t₀ subseteq t₁)
  proof: image2_subset hs ht

中文:
定理 seq_mono
  条件: {s₀ s₁ : 集合 (α -> β)} {t₀ t₁ : 集合 α} (hs : s₀ subseteq s₁) (ht : t₀ subseteq t₁)
  证明: image2_subset hs ht

Depends on / 依赖: image2_subset
-/
theorem seq_mono {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ subseteq s₁) (ht : t₀ subseteq t₁) :
    seq s₀ t₀ subseteq seq s₁ t₁ := image2_subset hs ht

/--
theorem `singleton_seq` / 定理 `singleton_seq`

English:
theorem singleton_seq
  given: {f : α -> β} {t : Set α}
  statement: Set.seq ({f} : Set (α -> β)) t = f '' t
  proof: image2_singleton_left

中文:
定理 singleton_seq
  条件: {f : α -> β} {t : 集合 α}
  结论: 集合.seq ({f} : 集合 (α -> β)) t = f '' t
  证明: image2_singleton_left

Depends on / 依赖: image2_singleton_left
-/
theorem singleton_seq {f : α -> β} {t : Set α} : Set.seq ({f} : Set (α -> β)) t = f '' t :=
  image2_singleton_left

/--
theorem `seq_singleton` / 定理 `seq_singleton`

English:
theorem seq_singleton
  given: {s : Set (α -> β)} {a : α}
  statement: Set.seq s {a} = (fun f : α -> β => f a) '' s
  proof: image2_singleton_right

中文:
定理 seq_singleton
  条件: {s : 集合 (α -> β)} {a : α}
  结论: 集合.seq s {a} = (fun f : α -> β => f a) '' s
  证明: image2_singleton_right

Depends on / 依赖: image2_singleton_right
-/
theorem seq_singleton {s : Set (α -> β)} {a : α} : Set.seq s {a} = (fun f : α -> β => f a) '' s :=
  image2_singleton_right

/--
theorem `seq_seq` / 定理 `seq_seq`

English:
theorem seq_seq
  given: {s : Set (β -> γ)} {t : Set (α -> β)} {u : Set α}
  proof: by
  simp only [seq_eq_image2, image2_image_left]
exact .symm image2_assoc fun _ _ _ => rfl

中文:
定理 seq_seq
  条件: {s : 集合 (β -> γ)} {t : 集合 (α -> β)} {u : 集合 α}
  证明: by
  simp only [seq_eq_image2, image2_image_left]
exact .symm image2_assoc fun _ _ _ => rfl

Depends on / 依赖: image2_assoc, image2_image_left, seq_eq_image2
-/
theorem seq_seq {s : Set (β -> γ)} {t : Set (α -> β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u := by
  simp only [seq_eq_image2, image2_image_left]
exact .symm image2_assoc fun _ _ _ => rfl

/--
theorem `image_seq` / 定理 `image_seq`

English:
theorem image_seq
  given: {f : β -> γ} {s : Set (α -> β)} {t : Set α}
  proof: by
  simp only [seq, image_image2, image2_image_left, comp_apply]

中文:
定理 image_seq
  条件: {f : β -> γ} {s : 集合 (α -> β)} {t : 集合 α}
  证明: by
  simp only [seq, image_image2, image2_image_left, comp_apply]

Depends on / 依赖: comp_apply, image2_image_left, image_image2
-/
theorem image_seq {f : β -> γ} {s : Set (α -> β)} {t : Set α} :
    f '' seq s t = seq ((f ∘ ·) '' s) t := by
  simp only [seq, image_image2, image2_image_left, comp_apply]

/--
theorem `prod_eq_seq` / 定理 `prod_eq_seq`

English:
theorem prod_eq_seq
  given: {s : Set α} {t : Set β}
  statement: s ×ˢ t = (Prod.mk '' s).seq t
  proof: by
  rw [seq_eq_image2]; rw [image2_image_left]; rw [image2_mk_eq_prod]

中文:
定理 prod_eq_seq
  条件: {s : 集合 α} {t : 集合 β}
  结论: s ×ˢ t = (积类型.mk '' s).seq t
  证明: by
  rw [seq_eq_image2]; rw [image2_image_left]; rw [image2_mk_eq_prod]

Depends on / 依赖: image2_image_left, image2_mk_eq_prod, seq_eq_image2
-/
theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  rw [seq_eq_image2]; rw [image2_image_left]; rw [image2_mk_eq_prod]

/--
theorem `prod_image_seq_comm` / 定理 `prod_image_seq_comm`

English:
theorem prod_image_seq_comm
  given: (s : Set α) (t : Set β)
  proof: by
  rw [← prod_eq_seq]; rw [← image_swap_prod]; rw [prod_eq_seq]; rw [image_seq]; rw [← image_comp]; rfl

中文:
定理 prod_image_seq_comm
  条件: (s : 集合 α) (t : 集合 β)
  证明: by
  rw [← prod_eq_seq]; rw [← image_swap_prod]; rw [prod_eq_seq]; rw [image_seq]; rw [← image_comp]; rfl

Depends on / 依赖: image_comp, image_seq, image_swap_prod, prod_eq_seq
-/
theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq]; rw [← image_swap_prod]; rw [prod_eq_seq]; rw [image_seq]; rw [← image_comp]; rfl

/--
theorem `image2_eq_seq` / 定理 `image2_eq_seq`

English:
theorem image2_eq_seq
  given: (f : α -> β -> γ) (s : Set α) (t : Set β)
  statement: image2 f s t = seq (f '' s) t
  proof: by
  rw [seq_eq_image2]; rw [image2_image_left]

中文:
定理 image2_eq_seq
  条件: (f : α -> β -> γ) (s : 集合 α) (t : 集合 β)
  结论: image2 f s t = seq (f '' s) t
  证明: by
  rw [seq_eq_image2]; rw [image2_image_left]

Depends on / 依赖: image2_image_left, seq_eq_image2
-/
theorem image2_eq_seq (f : α -> β -> γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t := by
  rw [seq_eq_image2]; rw [image2_image_left]

end Seq

end Set
