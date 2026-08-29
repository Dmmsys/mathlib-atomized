/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Set.Finite.Basic

/-!
# Preimage of a `Finset` under an injective map.
-/

@[expose] public section

assert_not_exists Finset.sum

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (s : Finset β) (f : α -> β) (hf : Set.InjOn f (f ⁻¹' ↑s))
  body: (s.finite_toSet.preimage hf).toFinset

@[simp]

中文:
定义 preimage
  签名: (s : Finset β) (f : α -> β) (hf : Set.InjOn f (f ⁻¹' ↑s))
  定义体: (s.finite_toSet.preimage hf).toFinset

@[simp]

Depends on / 依赖: finite_toSet, preimage, s.finite_toSet.preimage, toFinset
-/
noncomputable def preimage (s : Finset β) (f : α -> β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_toSet.preimage hf).toFinset

@[simp]
/--
theorem `mem_preimage` / 定理 `mem_preimage`

English:
theorem mem_preimage
  given: {f : α -> β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α}
  proof: Set.Finite.mem_toFinset _

@[simp, norm_cast]

中文:
定理 mem_preimage
  条件: {f : α -> β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α}
  证明: Set.Finite.mem_toFinset _

@[simp, norm_cast]

Depends on / 依赖: Finite, Set.Finite.mem_toFinset, mem_toFinset
-/
theorem mem_preimage {f : α -> β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α} :
    x in preimage s f hf ↔ f x in s :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
/--
theorem `coe_preimage` / 定理 `coe_preimage`

English:
theorem coe_preimage
  given: {f : α -> β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s))
  proof: Set.Finite.coe_toFinset _

@[simp]

中文:
定理 coe_preimage
  条件: {f : α -> β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s))
  证明: Set.Finite.coe_toFinset _

@[simp]

Depends on / 依赖: Finite, Set.Finite.coe_toFinset, coe_toFinset
-/
theorem coe_preimage {f : α -> β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) :
    (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s :=
  Set.Finite.coe_toFinset _

@[simp]
/--
theorem `preimage_empty` / 定理 `preimage_empty`

English:
theorem preimage_empty
  given: {f : α -> β}
  statement: preimage ∅ f (by simp [InjOn]) = ∅
  proof: Finset.coe_injective (by simp)

@[simp]

中文:
定理 preimage_empty
  条件: {f : α -> β}
  结论: preimage ∅ f (by simp [InjOn]) = ∅
  证明: Finset.coe_injective (by simp)

@[simp]

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem preimage_empty {f : α -> β} : preimage ∅ f (by simp [InjOn]) = ∅ :=
  Finset.coe_injective (by simp)

@[simp]
/--
theorem `preimage_univ` / 定理 `preimage_univ`

English:
theorem preimage_univ
  given: {f : α -> β} [Fintype α] [Fintype β] (hf)
  statement: preimage univ f hf = univ
  proof: Finset.coe_injective (by simp)

@[simp]

中文:
定理 preimage_univ
  条件: {f : α -> β} [Fintype α] [Fintype β] (hf)
  结论: preimage univ f hf = univ
  证明: Finset.coe_injective (by simp)

@[simp]

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem preimage_univ {f : α -> β} [Fintype α] [Fintype β] (hf) : preimage univ f hf = univ :=
  Finset.coe_injective (by simp)

@[simp]
/--
theorem `disjoint_preimage` / 定理 `disjoint_preimage`

English:
theorem disjoint_preimage
  statement: {f : α -> β} {s t : Finset β}
  proof: by
  grind [not_disjoint_iff, mem_preimage]

中文:
定理 disjoint_preimage
  结论: {f : α -> β} {s t : Finset β}
  证明: by
  grind [not_disjoint_iff, mem_preimage]

Depends on / 依赖: mem_preimage, not_disjoint_iff
-/
theorem disjoint_preimage {f : α -> β} {s t : Finset β}
    {hs : Set.InjOn f (f ⁻¹' ↑s)} {ht : Set.InjOn f (f ⁻¹' ↑t)} (hd : Disjoint s t) :
    Disjoint (s.preimage f hs) (t.preimage f ht) := by
  grind [not_disjoint_iff, mem_preimage]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `preimage_inter` / 定理 `preimage_inter`

English:
theorem preimage_inter
  statement: [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset β}
  proof: Finset.coe_injective (by simp)

中文:
定理 preimage_inter
  结论: [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset β}
  证明: Finset.coe_injective (by simp)

Depends on / 依赖: Finset, Finset.coe_injective, PosNum, coe_injective
-/
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s inter t) f fun _ hx₁ _ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs inter preimage t f ht :=
  Finset.coe_injective (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `preimage_union` / 定理 `preimage_union`

English:
theorem preimage_union
  given: [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset β} (hst)
  proof: Finset.coe_injective (by simp)

@[simp]

中文:
定理 preimage_union
  条件: [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset β} (hst)
  证明: Finset.coe_injective (by simp)

@[simp]

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset β} (hst) :
    preimage (s union t) f hst =
      (preimage s f fun _ hx₁ _ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) union
        preimage t f fun _ hx₁ _ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective (by simp)

@[simp]
/--
theorem `preimage_compl'` / 定理 `preimage_compl'`

English:
theorem preimage_compl'
  statement: [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α -> β}
  proof: Finset.coe_injective (by simp)

中文:
定理 preimage_compl'
  结论: [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α -> β}
  证明: Finset.coe_injective (by simp)

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem preimage_compl' [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α -> β}
    (s : Finset β) (hfc : InjOn f (f ⁻¹' ↑sᶜ)) (hf : InjOn f (f ⁻¹' ↑s)) :
    preimage sᶜ f hfc = (preimage s f hf)ᶜ :=
  Finset.coe_injective (by simp)

-- Not `@[simp]` since `simp` can't figure out `hf`; `simp`-normal form is `preimage_compl'`.
/--
theorem `preimage_compl` / 定理 `preimage_compl`

English:
theorem preimage_compl
  statement: [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α -> β}
  proof: preimage_compl' _ _ _

@[simp]

中文:
定理 preimage_compl
  结论: [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α -> β}
  证明: preimage_compl' _ _ _

@[simp]

Depends on / 依赖: CoeHTCT, PosNum, posNumCoe, preimage_compl
-/
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α -> β}
    (s : Finset β) (hf : Function.Injective f) :
    preimage sᶜ f hf.injOn = (preimage s f hf.injOn)ᶜ :=
  preimage_compl' _ _ _

@[simp]
/--
lemma `preimage_map` / 引理 `preimage_map`

English:
lemma preimage_map
  given: (f : α ↪ β) (s : Finset α)
  statement: (s.map f).preimage f f.injective.injOn = s
  proof: coe_injective by simp only [coe_preimage, coe_map, Set.preimage_image_eq _ f.injective]

中文:
引理 preimage_map
  条件: (f : α ↪ β) (s : Finset α)
  结论: (s.map f).preimage f f.injective.injOn = s
  证明: coe_injective by simp only [coe_preimage, coe_map, Set.preimage_image_eq _ f.injective]

Depends on / 依赖: CoeHTCT, Set.preimage_image_eq, coe_injective, coe_map, coe_preimage, f.injective, injective, numNatCoe, preimage_image_eq
-/
lemma preimage_map (f : α ↪ β) (s : Finset α) : (s.map f).preimage f f.injective.injOn = s :=
coe_injective by simp only [coe_preimage, coe_map, Set.preimage_image_eq _ f.injective]

/--
theorem `monotone_preimage` / 定理 `monotone_preimage`

English:
theorem monotone_preimage
  given: {f : α -> β} (h : Injective f)
  proof: fun _ _ H _ hx =>
  mem_preimage.2 (H <| mem_preimage.1 hx)

中文:
定理 monotone_preimage
  条件: {f : α -> β} (h : Injective f)
  证明: fun _ _ H _ hx =>
  mem_preimage.2 (H <| mem_preimage.1 hx)
-/
theorem monotone_preimage {f : α -> β} (h : Injective f) :
    Monotone fun s => preimage s f h.injOn := fun _ _ H _ hx =>
  mem_preimage.2 (H <| mem_preimage.1 hx)

/--
theorem `image_subset_iff_subset_preimage` / 定理 `image_subset_iff_subset_preimage`

English:
theorem image_subset_iff_subset_preimage
  statement: [DecidableEq β] {f : α -> β} {s : Finset α} {t : Finset β}
  proof: image_subset_iff.trans by simp only [subset_iff, mem_preimage]

中文:
定理 image_subset_iff_subset_preimage
  结论: [DecidableEq β] {f : α -> β} {s : Finset α} {t : Finset β}
  证明: image_subset_iff.trans by simp only [subset_iff, mem_preimage]

Depends on / 依赖: image_subset_iff, image_subset_iff.trans, mem_preimage, subset_iff
-/
theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α -> β} {s : Finset α} {t : Finset β}
    (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f subseteq t ↔ s subseteq t.preimage f hf :=
image_subset_iff.trans by simp only [subset_iff, mem_preimage]

/--
theorem `map_subset_iff_subset_preimage` / 定理 `map_subset_iff_subset_preimage`

English:
theorem map_subset_iff_subset_preimage
  given: {f : α ↪ β} {s : Finset α} {t : Finset β}
  proof: by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]

中文:
定理 map_subset_iff_subset_preimage
  条件: {f : α ↪ β} {s : Finset α} {t : Finset β}
  证明: by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]

Depends on / 依赖: classical, image_subset_iff_subset_preimage, map_eq_image
-/
theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
    s.map f subseteq t ↔ s subseteq t.preimage f f.injective.injOn := by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]

/--
lemma `card_preimage` / 引理 `card_preimage`

English:
lemma card_preimage
  given: (s : Finset β) (f : α -> β) (hf) [DecidablePred (· in Set.range f)]
  proof: card_nbij f (by simp [Set.MapsTo]) (by simpa) (fun b hb => by aesop)

中文:
引理 card_preimage
  条件: (s : Finset β) (f : α -> β) (hf) [DecidablePred (· in Set.range f)]
  证明: card_nbij f (by simp [Set.MapsTo]) (by simpa) (fun b hb => by aesop)

Depends on / 依赖: MapsTo, Set.MapsTo, card_nbij
-/
lemma card_preimage (s : Finset β) (f : α -> β) (hf) [DecidablePred (· in Set.range f)] :
    (s.preimage f hf).card = {x in s | x in Set.range f}.card :=
  card_nbij f (by simp [Set.MapsTo]) (by simpa) (fun b hb => by aesop)

/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  statement: [DecidableEq β] (f : α -> β) (s : Finset β) [forall x, Decidable (x in Set.range f)]
  proof: Finset.coe_inj.1 by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl

中文:
定理 image_preimage
  结论: [DecidableEq β] (f : α -> β) (s : Finset β) [对任意 x, Decidable (x in Set.range f)]
  证明: Finset.coe_inj.1 by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl

Depends on / 依赖: Finset, Finset.coe_inj, Set.image_preimage_eq_inter_range, Set.sep_mem_eq, coe_filter, coe_image, coe_inj, coe_preimage, image_preimage_eq_inter_range, sep_mem_eq
-/
theorem image_preimage [DecidableEq β] (f : α -> β) (s : Finset β) [forall x, Decidable (x in Set.range f)]
    (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f hf) = {x in s | x in Set.range f} :=
Finset.coe_inj.1 by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl

/--
theorem `image_eq_preimage_of_leftInvOn_injOn` / 定理 `image_eq_preimage_of_leftInvOn_injOn`

English:
theorem image_eq_preimage_of_leftInvOn_injOn
  statement: {α β : Type*} [DecidableEq β] {f : α -> β}
  proof: by
  simp only [SetLike.ext'_iff, coe_preimage, coe_image]
  rw [Set.image_eq_preimage_of_leftInvOn_injOn hgf ginj]

中文:
定理 image_eq_preimage_of_leftInvOn_injOn
  结论: {α β : 类型} [DecidableEq β] {f : α -> β}
  证明: by
  simp only [SetLike.ext'_iff, coe_preimage, coe_image]
  rw [Set.image_eq_preimage_of_leftInvOn_injOn hgf ginj]

Depends on / 依赖: Set.image_eq_preimage_of_leftInvOn_injOn, SetLike, SetLike.ext, _iff, coe_image, coe_preimage, image_eq_preimage_of_leftInvOn_injOn
-/
theorem image_eq_preimage_of_leftInvOn_injOn {α β : Type*} [DecidableEq β] {f : α -> β}
    {g : β -> α} {s : Finset α} (hgf : Set.LeftInvOn g f s) (ginj : Set.InjOn g (g ⁻¹' s)) :
    s.image f = s.preimage g ginj := by
  simp only [SetLike.ext'_iff, coe_preimage, coe_image]
  rw [Set.image_eq_preimage_of_leftInvOn_injOn hgf ginj]

/--
theorem `image_preimage_of_bij` / 定理 `image_preimage_of_bij`

English:
theorem image_preimage_of_bij
  statement: [DecidableEq β] (f : α -> β) (s : Finset β)
  proof: Finset.coe_inj.1 by simpa using hf.image_eq

中文:
定理 image_preimage_of_bij
  结论: [DecidableEq β] (f : α -> β) (s : Finset β)
  证明: Finset.coe_inj.1 by simpa using hf.image_eq

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj, hf.image_eq, image_eq
-/
theorem image_preimage_of_bij [DecidableEq β] (f : α -> β) (s : Finset β)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.injOn) = s :=
Finset.coe_inj.1 by simpa using hf.image_eq

/--
theorem `image_preimage_of_bijective` / 定理 `image_preimage_of_bijective`

English:
theorem image_preimage_of_bijective
  statement: [DecidableEq β] {f : α -> β} (s : Finset β)
  proof: image_preimage_of_bij f s hf.bijOn_preimage

中文:
定理 image_preimage_of_bijective
  结论: [DecidableEq β] {f : α -> β} (s : Finset β)
  证明: image_preimage_of_bij f s hf.bijOn_preimage

Depends on / 依赖: bijOn_preimage, hf.bijOn_preimage, image_preimage_of_bij
-/
theorem image_preimage_of_bijective [DecidableEq β] {f : α -> β} (s : Finset β)
    (hf : Bijective f) : image f (preimage s f (hf.injective.injOn)) = s :=
  image_preimage_of_bij f s hf.bijOn_preimage

/--
lemma `preimage_subset_of_subset_image` / 引理 `preimage_subset_of_subset_image`

English:
lemma preimage_subset_of_subset_image
  statement: [DecidableEq β] {f : α -> β} {s : Finset β} {t : Finset α}
  proof: by
  rw [← coe_subset]; rw [coe_preimage]; exact Set.preimage_subset (mod_cast hs) hf

中文:
引理 preimage_subset_of_subset_image
  结论: [DecidableEq β] {f : α -> β} {s : Finset β} {t : Finset α}
  证明: by
  rw [← coe_subset]; rw [coe_preimage]; exact Set.preimage_subset (mod_cast hs) hf

Depends on / 依赖: Set.preimage_subset, coe_preimage, coe_subset, mod_cast, preimage_subset
-/
lemma preimage_subset_of_subset_image [DecidableEq β] {f : α -> β} {s : Finset β} {t : Finset α}
    (hs : s subseteq t.image f) {hf} : s.preimage f hf subseteq t := by
  rw [← coe_subset]; rw [coe_preimage]; exact Set.preimage_subset (mod_cast hs) hf

/--
theorem `preimage_subset` / 定理 `preimage_subset`

English:
theorem preimage_subset
  given: {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s subseteq t.map f)
  proof: fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))

中文:
定理 preimage_subset
  条件: {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s subseteq t.map f)
  证明: fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))

Depends on / 依赖: mem_map, mem_preimage
-/
theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s subseteq t.map f) :
    s.preimage f f.injective.injOn subseteq t := fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))

/--
theorem `subset_map_iff` / 定理 `subset_map_iff`

English:
theorem subset_map_iff
  given: {f : α ↪ β} {s : Finset β} {t : Finset α}
  proof: by
  classical
  simp_rw [map_eq_image, subset_image_iff, eq_comm]

中文:
定理 subset_map_iff
  条件: {f : α ↪ β} {s : Finset β} {t : Finset α}
  证明: by
  classical
  simp_rw [map_eq_image, subset_image_iff, eq_comm]

Depends on / 依赖: classical, eq_comm, map_eq_image, simp_rw, subset_image_iff
-/
theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} :
    s subseteq t.map f ↔ exists u subseteq t, s = u.map f := by
  classical
  simp_rw [map_eq_image, subset_image_iff, eq_comm]

/--
theorem `image_eq_iff_eq_preimage` / 定理 `image_eq_iff_eq_preimage`

English:
theorem image_eq_iff_eq_preimage
  statement: [DecidableEq β] {s : Finset α} {t : Finset β}
  proof: by
  rw [← image_inj hf.injective]; rw [t.image_preimage_of_bijective hf]

@[simp]

中文:
定理 image_eq_iff_eq_preimage
  结论: [DecidableEq β] {s : Finset α} {t : Finset β}
  证明: by
  rw [← image_inj hf.injective]; rw [t.image_preimage_of_bijective hf]

@[simp]

Depends on / 依赖: hf.injective, image_inj, image_preimage_of_bijective, injective, t.image_preimage_of_bijective
-/
theorem image_eq_iff_eq_preimage [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α -> β} (hf : Bijective f) :
    s.image f = t ↔ s = t.preimage f hf.injective.injOn := by
  rw [← image_inj hf.injective]; rw [t.image_preimage_of_bijective hf]

@[simp]
/--
theorem `sup_preimage_self` / 定理 `sup_preimage_self`

English:
theorem sup_preimage_self
  statement: {α β : Type*} [Nonempty α] [SemilatticeSup β] [OrderBot β]
  proof: by
  classical
  have hfinvs : forall x in s, (f ∘ invFunOn f (f ⁻¹' ↑s)) x = id x := hf.invOn_invFunOn.2
  rw [← sup_congr (Eq.refl s) hfinvs]; rw [← sup_image]
  congr
  exact (image_eq_preimage_of_leftInvOn_injOn hf.invOn_invFunOn.2 hf.2.1).symm

中文:
定理 sup_preimage_self
  结论: {α β : 类型} [Nonempty α] [SemilatticeSup β] [OrderBot β]
  证明: by
  classical
  have hfinvs : forall x in s, (f ∘ invFunOn f (f ⁻¹' ↑s)) x = id x := hf.invOn_invFunOn.2
  rw [← sup_congr (Eq.refl s) hfinvs]; rw [← sup_image]
  congr
  exact (image_eq_preimage_of_leftInvOn_injOn hf.invOn_invFunOn.2 hf.2.1).symm

Depends on / 依赖: Eq.refl, classical, hf.invOn_invFunOn, hfinvs, image_eq_preimage_of_leftInvOn_injOn, invFunOn, invOn_invFunOn, sup_congr, sup_image
-/
theorem sup_preimage_self {α β : Type*} [Nonempty α] [SemilatticeSup β] [OrderBot β]
    {s : Finset β} {f : α -> β} (hf : Set.BijOn f (f ⁻¹' ↑s) s) :
    (preimage s f hf.2.1).sup f = s.sup id := by
  classical
  have hfinvs : forall x in s, (f ∘ invFunOn f (f ⁻¹' ↑s)) x = id x := hf.invOn_invFunOn.2
  rw [← sup_congr (Eq.refl s) hfinvs]; rw [← sup_image]
  congr
  exact (image_eq_preimage_of_leftInvOn_injOn hf.invOn_invFunOn.2 hf.2.1).symm

/--
lemma `sup_preimage_val_id` / 引理 `sup_preimage_val_id`

English:
lemma sup_preimage_val_id
  statement: [Lattice α] [OrderBot α] {P : α -> Prop}
  proof: Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.preimage Subtype.val Subtype.val_injective.injOn).sup id =
      (⟨t.sup id, sup_induction Pbot (fun _ h _ => Psup h) ht⟩ : Subtype P) := by
  let : OrderBot (Subtype P) := Subtype.orderBot Pbot
  ext
  simp only [sup_coe, id_eq]
 

中文:
引理 sup_preimage_val_id
  结论: [Lattice α] [OrderBot α] {P : α -> 命题}
  证明: Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.preimage Subtype.val Subtype.val_injective.injOn).sup id =
      (⟨t.sup id, sup_induction Pbot (fun _ h _ => Psup h) ht⟩ : Subtype P) := by
  let : OrderBot (Subtype P) := Subtype.orderBot Pbot
  ext
  simp only [sup_coe, id_eq]
 

Depends on / 依赖: Subtype, Subtype.semilatticeSup, semilatticeSup
-/
lemma sup_preimage_val_id [Lattice α] [OrderBot α] {P : α -> Prop}
    (Psup : forall ⦃s t : α⦄, P s -> P t -> P (s ⊔ t)) (Pbot : P ⊥) {t : Finset α}
    (ht : forall x in t, P x) :
    letI := Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.preimage Subtype.val Subtype.val_injective.injOn).sup id =
      (⟨t.sup id, sup_induction Pbot (fun _ h _ => Psup h) ht⟩ : Subtype P) := by
  let : OrderBot (Subtype P) := Subtype.orderBot Pbot
  ext
  simp only [sup_coe, id_eq]
  apply sup_preimage_self
  refine ⟨mapsTo_preimage _ _, injOn_of_injective Subtype.val_injective, ?_⟩
  intro x hx; simpa using ⟨hx, ht x hx⟩

/--
theorem `sigma_preimage_mk` / 定理 `sigma_preimage_mk`

English:
theorem sigma_preimage_mk
  given: {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a)) (t : Finset α)
  proof: by
  ext x
  simp [and_comm]

中文:
定理 sigma_preimage_mk
  条件: {β : α -> 类型} [DecidableEq α] (s : Finset (Σ a, β a)) (t : Finset α)
  证明: by
  ext x
  simp [and_comm]

Depends on / 依赖: and_comm
-/
theorem sigma_preimage_mk {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a)) (t : Finset α) :
    t.sigma (fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = {a in s | a.1 in t} := by
  ext x
  simp [and_comm]

/--
theorem `sigma_preimage_mk_of_subset` / 定理 `sigma_preimage_mk_of_subset`

English:
theorem sigma_preimage_mk_of_subset
  statement: {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a))
  proof: by
  rw [sigma_preimage_mk]; rw [filter_true_of_mem <| image_subset_iff.1 ht]

中文:
定理 sigma_preimage_mk_of_subset
  结论: {β : α -> 类型} [DecidableEq α] (s : Finset (Σ a, β a))
  证明: by
  rw [sigma_preimage_mk]; rw [filter_true_of_mem <| image_subset_iff.1 ht]

Depends on / 依赖: filter_true_of_mem, image_subset_iff, sigma_preimage_mk
-/
theorem sigma_preimage_mk_of_subset {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a))
    {t : Finset α} (ht : s.image Sigma.fst subseteq t) :
    (t.sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = s := by
  rw [sigma_preimage_mk]; rw [filter_true_of_mem <| image_subset_iff.1 ht]

/--
theorem `sigma_image_fst_preimage_mk` / 定理 `sigma_image_fst_preimage_mk`

English:
theorem sigma_image_fst_preimage_mk
  given: {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a))
  proof: s.sigma_preimage_mk_of_subset (Subset.refl _)

中文:
定理 sigma_image_fst_preimage_mk
  条件: {β : α -> 类型} [DecidableEq α] (s : Finset (Σ a, β a))
  证明: s.sigma_preimage_mk_of_subset (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, s.sigma_preimage_mk_of_subset, sigma_preimage_mk_of_subset
-/
theorem sigma_image_fst_preimage_mk {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a)) :
    ((s.image Sigma.fst).sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) =
      s :=
  s.sigma_preimage_mk_of_subset (Subset.refl _)

/--
lemma `preimage_inl` / 引理 `preimage_inl`

English:
lemma preimage_inl
  given: (s : Finset (α oplus β))
  proof: by
  ext x; simp

中文:
引理 preimage_inl
  条件: (s : Finset (α oplus β))
  证明: by
  ext x; simp
-/
@[simp] lemma preimage_inl (s : Finset (α oplus β)) :
    s.preimage Sum.inl Sum.inl_injective.injOn = s.toLeft := by
  ext x; simp

/--
lemma `preimage_inr` / 引理 `preimage_inr`

English:
lemma preimage_inr
  given: (s : Finset (α oplus β))
  proof: by
  ext x; simp

中文:
引理 preimage_inr
  条件: (s : Finset (α oplus β))
  证明: by
  ext x; simp
-/
@[simp] lemma preimage_inr (s : Finset (α oplus β)) :
    s.preimage Sum.inr Sum.inr_injective.injOn = s.toRight := by
  ext x; simp

end Preimage
end Finset

namespace Equiv

/-- Given an equivalence `e : α ≃ β` and `s : Finset β`, restrict `e` to an equivalence
from `e ⁻¹' s` to `s`. -/
@[simps]
/--
Definition of `restrictPreimageFinset` / `restrictPreimageFinset` 的定义

English:
definition restrictPreimageFinset
  signature: (e : α ≃ β) (s : Finset β)
  body: ⟨e a, Finset.mem_preimage.1 a.2⟩
  invFun b := ⟨e.symm b, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 restrictPreimageFinset
  签名: (e : α ≃ β) (s : Finset β)
  定义体: ⟨e a, Finset.mem_preimage.1 a.2⟩
  invFun b := ⟨e.symm b, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: Finset, Finset.mem_preimage, mem_preimage
-/
def restrictPreimageFinset (e : α ≃ β) (s : Finset β) : (s.preimage e e.injective.injOn) ≃ s where
  toFun a := ⟨e a, Finset.mem_preimage.1 a.2⟩
  invFun b := ⟨e.symm b, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp

/--
lemma `image_symm_eq_preimage_of_finset` / 引理 `image_symm_eq_preimage_of_finset`

English:
lemma image_symm_eq_preimage_of_finset
  given: [DecidableEq α] (e : α ≃ β) (s : Finset β)
  proof: by
  grind [Finset.mem_preimage]

中文:
引理 image_symm_eq_preimage_of_finset
  条件: [DecidableEq α] (e : α ≃ β) (s : Finset β)
  证明: by
  grind [Finset.mem_preimage]

Depends on / 依赖: Finset, Finset.mem_preimage, mem_preimage
-/
lemma image_symm_eq_preimage_of_finset [DecidableEq α] (e : α ≃ β) (s : Finset β) :
    s.image e.symm = s.preimage e e.injective.injOn := by
  grind [Finset.mem_preimage]

/--
lemma `image_eq_preimage_symm_of_finset` / 引理 `image_eq_preimage_symm_of_finset`

English:
lemma image_eq_preimage_symm_of_finset
  given: [DecidableEq β] (e : α ≃ β) (s : Finset α)
  proof: e.symm.image_symm_eq_preimage_of_finset s

中文:
引理 image_eq_preimage_symm_of_finset
  条件: [DecidableEq β] (e : α ≃ β) (s : Finset α)
  证明: e.symm.image_symm_eq_preimage_of_finset s

Depends on / 依赖: e.symm.image_symm_eq_preimage_of_finset, image_symm_eq_preimage_of_finset
-/
lemma image_eq_preimage_symm_of_finset [DecidableEq β] (e : α ≃ β) (s : Finset α) :
    s.image e = s.preimage e.symm e.symm.injective.injOn :=
  e.symm.image_symm_eq_preimage_of_finset s

end Equiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Finset.restrict_comp_piCongrLeft` / 引理 `Finset.restrict_comp_piCongrLeft`

English:
lemma Finset.restrict_comp_piCongrLeft
  given: {π : β -> Type*} (s : Finset β) (e : α ≃ β)
  proof: by
  ext x b
  simp only [comp_apply, restrict, Equiv.piCongrLeft_apply_eq_cast,
    Equiv.restrictPreimageFinset_symm_apply_coe]

中文:
引理 Finset.restrict_comp_piCongrLeft
  条件: {π : β -> 类型} (s : Finset β) (e : α ≃ β)
  证明: by
  ext x b
  simp only [comp_apply, restrict, Equiv.piCongrLeft_apply_eq_cast,
    Equiv.restrictPreimageFinset_symm_apply_coe]

Depends on / 依赖: Equiv.piCongrLeft_apply_eq_cast, Equiv.restrictPreimageFinset_symm_apply_coe, comp_apply, piCongrLeft_apply_eq_cast, restrict, restrictPreimageFinset_symm_apply_coe
-/
lemma Finset.restrict_comp_piCongrLeft {π : β -> Type*} (s : Finset β) (e : α ≃ β) :
    s.restrict ∘ ⇑(e.piCongrLeft π) =
    ⇑((e.restrictPreimageFinset s).piCongrLeft (fun b : s => (π b))) ∘
    (s.preimage e e.injective.injOn).restrict := by
  ext x b
  simp only [comp_apply, restrict, Equiv.piCongrLeft_apply_eq_cast,
    Equiv.restrictPreimageFinset_symm_apply_coe]
