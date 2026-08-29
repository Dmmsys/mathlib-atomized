/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Set.Prod

/-!
# N-ary images of sets

This file defines `Set.image2`, the binary image of sets.
This is mostly useful to define pointwise operations and `Set.seq`.

## Notes

This file is very similar to `Mathlib/Data/Finset/NAry.lean`, `Mathlib/Order/Filter/NAry.lean`, and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.
-/

public section

open Function

namespace Set
variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*} {f f' : α -> β -> γ}
variable {s s' : Set α} {t t' : Set β} {u : Set γ} {v : Set δ} {a : α} {b : β}

/--
theorem `mem_image2_iff` / 定理 `mem_image2_iff`

English:
theorem mem_image2_iff
  given: (hf : Injective2 f)
  statement: f a b in image2 f s t ↔ a in s ∧ b in t
  proof: ⟨by
    rintro ⟨a', ha', b', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

中文:
定理 mem_image2_iff
  条件: (hf : Injective2 f)
  结论: f a b in image2 f s t ↔ a in s ∧ b in t
  证明: ⟨by
    rintro ⟨a', ha', b', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

Depends on / 依赖: mem_image2_of_mem
-/
theorem mem_image2_iff (hf : Injective2 f) : f a b in image2 f s t ↔ a in s ∧ b in t :=
  ⟨by
    rintro ⟨a', ha', b', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
@[gcongr]
/--
theorem `image2_subset` / 定理 `image2_subset`

English:
theorem image2_subset
  given: (hs : s subseteq s') (ht : t subseteq t')
  statement: image2 f s t subseteq image2 f s' t'
  proof: by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)

中文:
定理 image2_subset
  条件: (hs : s subseteq s') (ht : t subseteq t')
  结论: image2 f s t subseteq image2 f s' t'
  证明: by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)

Depends on / 依赖: mem_image2_of_mem
-/
theorem image2_subset (hs : s subseteq s') (ht : t subseteq t') : image2 f s t subseteq image2 f s' t' := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)

/--
theorem `image2_subset_left` / 定理 `image2_subset_left`

English:
theorem image2_subset_left
  given: (ht : t subseteq t')
  statement: image2 f s t subseteq image2 f s t'
  proof: image2_subset Subset.rfl ht

中文:
定理 image2_subset_left
  条件: (ht : t subseteq t')
  结论: image2 f s t subseteq image2 f s t'
  证明: image2_subset Subset.rfl ht

Depends on / 依赖: Subset, Subset.rfl, image2_subset
-/
theorem image2_subset_left (ht : t subseteq t') : image2 f s t subseteq image2 f s t' :=
  image2_subset Subset.rfl ht

/--
theorem `image2_subset_right` / 定理 `image2_subset_right`

English:
theorem image2_subset_right
  given: (hs : s subseteq s')
  statement: image2 f s t subseteq image2 f s' t
  proof: image2_subset hs Subset.rfl

中文:
定理 image2_subset_right
  条件: (hs : s subseteq s')
  结论: image2 f s t subseteq image2 f s' t
  证明: image2_subset hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, image2_subset
-/
theorem image2_subset_right (hs : s subseteq s') : image2 f s t subseteq image2 f s' t :=
  image2_subset hs Subset.rfl

/--
theorem `image_subset_image2_left` / 定理 `image_subset_image2_left`

English:
theorem image_subset_image2_left
  given: (hb : b in t)
  statement: (fun a => f a b) '' s subseteq image2 f s t
  proof: forall_mem_image.2 fun _ ha => mem_image2_of_mem ha hb

中文:
定理 image_subset_image2_left
  条件: (hb : b in t)
  结论: (fun a => f a b) '' s subseteq image2 f s t
  证明: forall_mem_image.2 fun _ ha => mem_image2_of_mem ha hb

Depends on / 依赖: forall_mem_image, mem_image2_of_mem
-/
theorem image_subset_image2_left (hb : b in t) : (fun a => f a b) '' s subseteq image2 f s t :=
  forall_mem_image.2 fun _ ha => mem_image2_of_mem ha hb

/--
theorem `image_subset_image2_right` / 定理 `image_subset_image2_right`

English:
theorem image_subset_image2_right
  given: (ha : a in s)
  statement: f a '' t subseteq image2 f s t
  proof: forall_mem_image.2 fun _ => mem_image2_of_mem ha

中文:
定理 image_subset_image2_right
  条件: (ha : a in s)
  结论: f a '' t subseteq image2 f s t
  证明: forall_mem_image.2 fun _ => mem_image2_of_mem ha

Depends on / 依赖: forall_mem_image, mem_image2_of_mem
-/
theorem image_subset_image2_right (ha : a in s) : f a '' t subseteq image2 f s t :=
  forall_mem_image.2 fun _ => mem_image2_of_mem ha

/--
lemma `forall_mem_image2` / 引理 `forall_mem_image2`

English:
lemma forall_mem_image2
  given: {p : γ -> Prop}
  proof: by grind

中文:
引理 对任意_mem_image2
  条件: {p : γ -> 命题}
  证明: by grind
-/
lemma forall_mem_image2 {p : γ -> Prop} :
    (forall z in image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y) := by grind

/--
lemma `exists_mem_image2` / 引理 `exists_mem_image2`

English:
lemma exists_mem_image2
  given: {p : γ -> Prop}
  proof: by grind

@[simp]

中文:
引理 存在_mem_image2
  条件: {p : γ -> 命题}
  证明: by grind

@[simp]
-/
lemma exists_mem_image2 {p : γ -> Prop} :
    (exists z in image2 f s t, p z) ↔ exists x in s, exists y in t, p (f x y) := by grind

@[simp]
/--
theorem `image2_subset_iff` / 定理 `image2_subset_iff`

English:
theorem image2_subset_iff
  given: {u : Set γ}
  statement: image2 f s t subseteq u ↔ forall x in s, forall y in t, f x y in u
  proof: forall_mem_image2

中文:
定理 image2_subset_iff
  条件: {u : 集合 γ}
  结论: image2 f s t subseteq u ↔ 对任意 x in s, 对任意 y in t, f x y in u
  证明: forall_mem_image2

Depends on / 依赖: forall_mem_image2
-/
theorem image2_subset_iff {u : Set γ} : image2 f s t subseteq u ↔ forall x in s, forall y in t, f x y in u :=
  forall_mem_image2

/--
theorem `image2_subset_iff_left` / 定理 `image2_subset_iff_left`

English:
theorem image2_subset_iff_left
  statement: image2 f s t subseteq u ↔ forall a in s, (fun b => f a b) '' t subseteq u
  proof: by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]

中文:
定理 image2_subset_iff_left
  结论: image2 f s t subseteq u ↔ 对任意 a in s, (fun b => f a b) '' t subseteq u
  证明: by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]

Depends on / 依赖: image2_subset_iff, image_subset_iff, infer_instance, invApp, mem_preimage, simp_rw, subset_def
-/
theorem image2_subset_iff_left : image2 f s t subseteq u ↔ forall a in s, (fun b => f a b) '' t subseteq u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]

/--
theorem `image2_subset_iff_right` / 定理 `image2_subset_iff_right`

English:
theorem image2_subset_iff_right
  statement: image2 f s t subseteq u ↔ forall b in t, (fun a => f a b) '' s subseteq u
  proof: by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage, @forall₂_comm α]

中文:
定理 image2_subset_iff_right
  结论: image2 f s t subseteq u ↔ 对任意 b in t, (fun a => f a b) '' s subseteq u
  证明: by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage, @forall₂_comm α]

Depends on / 依赖: image2_subset_iff, image_subset_iff, mem_preimage, simp_rw, subset_def
-/
theorem image2_subset_iff_right : image2 f s t subseteq u ↔ forall b in t, (fun a => f a b) '' s subseteq u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage, @forall₂_comm α]

variable (f)

@[simp]
/--
lemma `image_prod` / 引理 `image_prod`

English:
lemma image_prod
  statement: (fun x : α × β => f x.1 x.2) '' s ×ˢ t = image2 f s t
  proof: ext fun _ => by simp [and_assoc]

中文:
引理 image_prod
  结论: (fun x : α × β => f x.1 x.2) '' s ×ˢ t = image2 f s t
  证明: ext fun _ => by simp [and_assoc]

Depends on / 依赖: and_assoc
-/
lemma image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = image2 f s t :=
  ext fun _ => by simp [and_assoc]

/--
lemma `image_uncurry_prod` / 引理 `image_uncurry_prod`

English:
lemma image_uncurry_prod
  given: (s : Set α) (t : Set β)
  statement: uncurry f '' s ×ˢ t = image2 f s t
  proof: image_prod _

中文:
引理 image_uncurry_prod
  条件: (s : 集合 α) (t : 集合 β)
  结论: uncurry f '' s ×ˢ t = image2 f s t
  证明: image_prod _
-/
@[simp] lemma image_uncurry_prod (s : Set α) (t : Set β) : uncurry f '' s ×ˢ t = image2 f s t :=
  image_prod _

/--
lemma `image2_mk_eq_prod` / 引理 `image2_mk_eq_prod`

English:
lemma image2_mk_eq_prod
  statement: image2 Prod.mk s t = s ×ˢ t
  proof: ext by simp

中文:
引理 image2_mk_eq_prod
  结论: image2 积类型.mk s t = s ×ˢ t
  证明: ext by simp
-/
@[simp] lemma image2_mk_eq_prod : image2 Prod.mk s t = s ×ˢ t := ext by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `image2_curry` / 引理 `image2_curry`

English:
lemma image2_curry
  given: (f : α × β -> γ) (s : Set α) (t : Set β)
  proof: by
  simp [← image_uncurry_prod, uncurry]

中文:
引理 image2_curry
  条件: (f : α × β -> γ) (s : 集合 α) (t : 集合 β)
  证明: by
  simp [← image_uncurry_prod, uncurry]

Depends on / 依赖: image_uncurry_prod, uncurry
-/
lemma image2_curry (f : α × β -> γ) (s : Set α) (t : Set β) :
    image2 (fun a b => f (a, b)) s t = f '' s ×ˢ t := by
  simp [← image_uncurry_prod, uncurry]

/--
theorem `image2_swap` / 定理 `image2_swap`

English:
theorem image2_swap
  given: (s : Set α) (t : Set β)
  statement: image2 f s t = image2 (fun a b => f b a) t s
  proof: by
  grind

中文:
定理 image2_swap
  条件: (s : 集合 α) (t : 集合 β)
  结论: image2 f s t = image2 (fun a b => f b a) t s
  证明: by
  grind

Depends on / 依赖: PresheafedSpace, ofIsIso
-/
theorem image2_swap (s : Set α) (t : Set β) : image2 f s t = image2 (fun a b => f b a) t s := by
  grind

variable {f}

/--
theorem `image2_union_left` / 定理 `image2_union_left`

English:
theorem image2_union_left
  statement: image2 f (s union s') t = image2 f s t union image2 f s' t
  proof: by
  simp_rw [← image_prod, union_prod, image_union]

中文:
定理 image2_union_left
  结论: image2 f (s union s') t = image2 f s t union image2 f s' t
  证明: by
  simp_rw [← image_prod, union_prod, image_union]

Depends on / 依赖: image_prod, image_union, simp_rw, union_prod
-/
theorem image2_union_left : image2 f (s union s') t = image2 f s t union image2 f s' t := by
  simp_rw [← image_prod, union_prod, image_union]

/--
theorem `image2_union_right` / 定理 `image2_union_right`

English:
theorem image2_union_right
  statement: image2 f s (t union t') = image2 f s t union image2 f s t'
  proof: by
  rw [← image2_swap]; rw [image2_union_left]; rw [image2_swap f]; rw [image2_swap f]

中文:
定理 image2_union_right
  结论: image2 f s (t union t') = image2 f s t union image2 f s t'
  证明: by
  rw [← image2_swap]; rw [image2_union_left]; rw [image2_swap f]; rw [image2_swap f]

Depends on / 依赖: image2_swap, image2_union_left
-/
theorem image2_union_right : image2 f s (t union t') = image2 f s t union image2 f s t' := by
  rw [← image2_swap]; rw [image2_union_left]; rw [image2_swap f]; rw [image2_swap f]

/--
lemma `image2_inter_left` / 引理 `image2_inter_left`

English:
lemma image2_inter_left
  given: (hf : Injective2 f)
  proof: by
  simp_rw [← image_uncurry_prod, inter_prod, image_inter hf.uncurry]

中文:
引理 image2_inter_left
  条件: (hf : Injective2 f)
  证明: by
  simp_rw [← image_uncurry_prod, inter_prod, image_inter hf.uncurry]

Depends on / 依赖: hf.uncurry, image_inter, image_uncurry_prod, inter_prod, simp_rw, uncurry
-/
lemma image2_inter_left (hf : Injective2 f) :
    image2 f (s inter s') t = image2 f s t inter image2 f s' t := by
  simp_rw [← image_uncurry_prod, inter_prod, image_inter hf.uncurry]

/--
lemma `image2_inter_right` / 引理 `image2_inter_right`

English:
lemma image2_inter_right
  given: (hf : Injective2 f)
  proof: by
  simp_rw [← image_uncurry_prod, prod_inter, image_inter hf.uncurry]

@[simp]

中文:
引理 image2_inter_right
  条件: (hf : Injective2 f)
  证明: by
  simp_rw [← image_uncurry_prod, prod_inter, image_inter hf.uncurry]

@[simp]

Depends on / 依赖: hf.uncurry, image_inter, image_uncurry_prod, prod_inter, simp_rw, uncurry
-/
lemma image2_inter_right (hf : Injective2 f) :
    image2 f s (t inter t') = image2 f s t inter image2 f s t' := by
  simp_rw [← image_uncurry_prod, prod_inter, image_inter hf.uncurry]

@[simp]
/--
theorem `image2_empty_left` / 定理 `image2_empty_left`

English:
theorem image2_empty_left
  statement: image2 f ∅ t = ∅
  proof: ext by simp

@[simp]

中文:
定理 image2_empty_left
  结论: image2 f ∅ t = ∅
  证明: ext by simp

@[simp]
-/
theorem image2_empty_left : image2 f ∅ t = ∅ :=
ext by simp

@[simp]
/--
theorem `image2_empty_right` / 定理 `image2_empty_right`

English:
theorem image2_empty_right
  statement: image2 f s ∅ = ∅
  proof: ext by simp

中文:
定理 image2_empty_right
  结论: image2 f s ∅ = ∅
  证明: ext by simp
-/
theorem image2_empty_right : image2 f s ∅ = ∅ :=
ext by simp

/--
theorem `Nonempty.image2` / 定理 `Nonempty.image2`

English:
theorem Nonempty.image2
  statement: s.Nonempty -> t.Nonempty -> (image2 f s t).Nonempty
  proof: fun ⟨_, ha⟩ ⟨_, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩

@[simp]

中文:
定理 非空.image2
  结论: s.非空 -> t.非空 -> (image2 f s t).非空
  证明: fun ⟨_, ha⟩ ⟨_, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩

@[simp]

Depends on / 依赖: mem_image2_of_mem
-/
theorem Nonempty.image2 : s.Nonempty -> t.Nonempty -> (image2 f s t).Nonempty :=
  fun ⟨_, ha⟩ ⟨_, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩

@[simp]
/--
theorem `image2_nonempty_iff` / 定理 `image2_nonempty_iff`

English:
theorem image2_nonempty_iff
  statement: (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: ⟨fun ⟨_, a, ha, b, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩

中文:
定理 image2_nonempty_iff
  结论: (image2 f s t).非空 ↔ s.非空 ∧ t.非空
  证明: ⟨fun ⟨_, a, ha, b, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩

Depends on / 依赖: image2
-/
theorem image2_nonempty_iff : (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun ⟨_, a, ha, b, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩

/--
theorem `Nonempty.of_image2_left` / 定理 `Nonempty.of_image2_left`

English:
theorem Nonempty.of_image2_left
  given: (h : (Set.image2 f s t).Nonempty)
  statement: s.Nonempty
  proof: (image2_nonempty_iff.1 h).1

中文:
定理 非空.of_image2_left
  条件: (h : (集合.image2 f s t).非空)
  结论: s.非空
  证明: (image2_nonempty_iff.1 h).1

Depends on / 依赖: image2_nonempty_iff
-/
theorem Nonempty.of_image2_left (h : (Set.image2 f s t).Nonempty) : s.Nonempty :=
  (image2_nonempty_iff.1 h).1

/--
theorem `Nonempty.of_image2_right` / 定理 `Nonempty.of_image2_right`

English:
theorem Nonempty.of_image2_right
  given: (h : (Set.image2 f s t).Nonempty)
  statement: t.Nonempty
  proof: (image2_nonempty_iff.1 h).2

@[simp]

中文:
定理 非空.of_image2_right
  条件: (h : (集合.image2 f s t).非空)
  结论: t.非空
  证明: (image2_nonempty_iff.1 h).2

@[simp]

Depends on / 依赖: image2_nonempty_iff
-/
theorem Nonempty.of_image2_right (h : (Set.image2 f s t).Nonempty) : t.Nonempty :=
  (image2_nonempty_iff.1 h).2

@[simp]
/--
theorem `image2_eq_empty_iff` / 定理 `image2_eq_empty_iff`

English:
theorem image2_eq_empty_iff
  statement: image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: by
  rw [← not_nonempty_iff_eq_empty]; rw [image2_nonempty_iff]; rw [not_and_or]
  simp [not_nonempty_iff_eq_empty]

中文:
定理 image2_eq_empty_iff
  结论: image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: by
  rw [← not_nonempty_iff_eq_empty]; rw [image2_nonempty_iff]; rw [not_and_or]
  simp [not_nonempty_iff_eq_empty]

Depends on / 依赖: image2_nonempty_iff, not_and_or, not_nonempty_iff_eq_empty
-/
theorem image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty]; rw [image2_nonempty_iff]; rw [not_and_or]
  simp [not_nonempty_iff_eq_empty]

/--
theorem `Subsingleton.image2` / 定理 `Subsingleton.image2`

English:
theorem Subsingleton.image2
  given: (hs : s.Subsingleton) (ht : t.Subsingleton) (f : α -> β -> γ)
  proof: by
  rw [← image_prod]
  apply (hs.prod ht).image

中文:
定理 子单例.image2
  条件: (hs : s.子单例) (ht : t.子单例) (f : α -> β -> γ)
  证明: by
  rw [← image_prod]
  apply (hs.prod ht).image

Depends on / 依赖: hs.prod, image_prod
-/
theorem Subsingleton.image2 (hs : s.Subsingleton) (ht : t.Subsingleton) (f : α -> β -> γ) :
    (image2 f s t).Subsingleton := by
  rw [← image_prod]
  apply (hs.prod ht).image

/--
theorem `image2_inter_subset_left` / 定理 `image2_inter_subset_left`

English:
theorem image2_inter_subset_left
  statement: image2 f (s inter s') t subseteq image2 f s t inter image2 f s' t
  proof: Monotone.map_inf_le (fun _ _ => image2_subset_right) s s'

中文:
定理 image2_inter_subset_left
  结论: image2 f (s inter s') t subseteq image2 f s t inter image2 f s' t
  证明: Monotone.map_inf_le (fun _ _ => image2_subset_right) s s'

Depends on / 依赖: Monotone, Monotone.map_inf_le, image2_subset_right, map_inf_le
-/
theorem image2_inter_subset_left : image2 f (s inter s') t subseteq image2 f s t inter image2 f s' t :=
  Monotone.map_inf_le (fun _ _ => image2_subset_right) s s'

/--
theorem `image2_inter_subset_right` / 定理 `image2_inter_subset_right`

English:
theorem image2_inter_subset_right
  statement: image2 f s (t inter t') subseteq image2 f s t inter image2 f s t'
  proof: Monotone.map_inf_le (fun _ _ => image2_subset_left) t t'

中文:
定理 image2_inter_subset_right
  结论: image2 f s (t inter t') subseteq image2 f s t inter image2 f s t'
  证明: Monotone.map_inf_le (fun _ _ => image2_subset_left) t t'

Depends on / 依赖: Monotone, Monotone.map_inf_le, image2_subset_left, map_inf_le
-/
theorem image2_inter_subset_right : image2 f s (t inter t') subseteq image2 f s t inter image2 f s t' :=
  Monotone.map_inf_le (fun _ _ => image2_subset_left) t t'

/--
theorem `subset_image2_sdiff_left` / 定理 `subset_image2_sdiff_left`

English:
theorem subset_image2_sdiff_left
  proof: by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ⟨ha, fun ha' => h ⟨_, ha', _, hb, rfl⟩⟩, _, hb, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_left := subset_image2_sdiff_left

中文:
定理 subset_image2_sdiff_left
  证明: by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ⟨ha, fun ha' => h ⟨_, ha', _, hb, rfl⟩⟩, _, hb, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_left := subset_image2_sdiff_left
-/
theorem subset_image2_sdiff_left :
    image2 f s t \ image2 f s' t subseteq image2 f (s \ s') t := by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ⟨ha, fun ha' => h ⟨_, ha', _, hb, rfl⟩⟩, _, hb, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_left := subset_image2_sdiff_left

/--
theorem `subset_image2_sdiff_right` / 定理 `subset_image2_sdiff_right`

English:
theorem subset_image2_sdiff_right
  proof: by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ha, _, ⟨hb, fun hb' => h ⟨_, ha, _, hb', rfl⟩⟩, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_right := subset_image2_sdiff_right

@[simp]

中文:
定理 subset_image2_sdiff_right
  证明: by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ha, _, ⟨hb, fun hb' => h ⟨_, ha, _, hb', rfl⟩⟩, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_right := subset_image2_sdiff_right

@[simp]
-/
theorem subset_image2_sdiff_right :
    image2 f s t \ image2 f s t' subseteq image2 f s (t \ t') := by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ha, _, ⟨hb, fun hb' => h ⟨_, ha, _, hb', rfl⟩⟩, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_right := subset_image2_sdiff_right

@[simp]
/--
theorem `image2_singleton_left` / 定理 `image2_singleton_left`

English:
theorem image2_singleton_left
  statement: image2 f {a} t = f a '' t
  proof: ext fun x => by simp

@[simp]

中文:
定理 image2_singleton_left
  结论: image2 f {a} t = f a '' t
  证明: ext fun x => by simp

@[simp]
-/
theorem image2_singleton_left : image2 f {a} t = f a '' t :=
  ext fun x => by simp

@[simp]
/--
theorem `image2_singleton_right` / 定理 `image2_singleton_right`

English:
theorem image2_singleton_right
  statement: image2 f s {b} = (fun a => f a b) '' s
  proof: ext fun x => by simp

中文:
定理 image2_singleton_right
  结论: image2 f s {b} = (fun a => f a b) '' s
  证明: ext fun x => by simp
-/
theorem image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s :=
  ext fun x => by simp

/--
theorem `image2_singleton` / 定理 `image2_singleton`

English:
theorem image2_singleton
  statement: image2 f {a} {b} = {f a b}
  proof: by simp

@[simp]

中文:
定理 image2_singleton
  结论: image2 f {a} {b} = {f a b}
  证明: by simp

@[simp]
-/
theorem image2_singleton : image2 f {a} {b} = {f a b} := by simp

@[simp]
/--
theorem `image2_insert_left` / 定理 `image2_insert_left`

English:
theorem image2_insert_left
  statement: image2 f (insert a s) t = (fun b => f a b) '' t union image2 f s t
  proof: by
  rw [insert_eq]; rw [image2_union_left]; rw [image2_singleton_left]

@[simp]

中文:
定理 image2_insert_left
  结论: image2 f (insert a s) t = (fun b => f a b) '' t union image2 f s t
  证明: by
  rw [insert_eq]; rw [image2_union_left]; rw [image2_singleton_left]

@[simp]

Depends on / 依赖: image2_singleton_left, image2_union_left, insert_eq
-/
theorem image2_insert_left : image2 f (insert a s) t = (fun b => f a b) '' t union image2 f s t := by
  rw [insert_eq]; rw [image2_union_left]; rw [image2_singleton_left]

@[simp]
/--
theorem `image2_insert_right` / 定理 `image2_insert_right`

English:
theorem image2_insert_right
  statement: image2 f s (insert b t) = (fun a => f a b) '' s union image2 f s t
  proof: by
  rw [insert_eq]; rw [image2_union_right]; rw [image2_singleton_right]

@[congr]

中文:
定理 image2_insert_right
  结论: image2 f s (insert b t) = (fun a => f a b) '' s union image2 f s t
  证明: by
  rw [insert_eq]; rw [image2_union_right]; rw [image2_singleton_right]

@[congr]

Depends on / 依赖: image2_singleton_right, image2_union_right, insert_eq
-/
theorem image2_insert_right : image2 f s (insert b t) = (fun a => f a b) '' s union image2 f s t := by
  rw [insert_eq]; rw [image2_union_right]; rw [image2_singleton_right]

@[congr]
/--
theorem `image2_congr` / 定理 `image2_congr`

English:
theorem image2_congr
  given: (h : forall a in s, forall b in t, f a b = f' a b)
  statement: image2 f s t = image2 f' s t
  proof: by
  grind

中文:
定理 image2_congr
  条件: (h : 对任意 a in s, 对任意 b in t, f a b = f' a b)
  结论: image2 f s t = image2 f' s t
  证明: by
  grind
-/
theorem image2_congr (h : forall a in s, forall b in t, f a b = f' a b) : image2 f s t = image2 f' s t := by
  grind

/--
theorem `image2_congr'` / 定理 `image2_congr'`

English:
theorem image2_congr'
  given: (h : forall a b, f a b = f' a b)
  statement: image2 f s t = image2 f' s t
  proof: image2_congr fun a _ b _ => h a b

中文:
定理 image2_congr'
  条件: (h : 对任意 a b, f a b = f' a b)
  结论: image2 f s t = image2 f' s t
  证明: image2_congr fun a _ b _ => h a b

Depends on / 依赖: image2_congr
-/
theorem image2_congr' (h : forall a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
  image2_congr fun a _ b _ => h a b

/--
theorem `image_image2` / 定理 `image_image2`

English:
theorem image_image2
  given: (f : α -> β -> γ) (g : γ -> δ)
  proof: by
  simp only [← image_prod, image_image]

中文:
定理 image_image2
  条件: (f : α -> β -> γ) (g : γ -> δ)
  证明: by
  simp only [← image_prod, image_image]

Depends on / 依赖: image_image, image_prod
-/
theorem image_image2 (f : α -> β -> γ) (g : γ -> δ) :
    g '' image2 f s t = image2 (fun a b => g (f a b)) s t := by
  simp only [← image_prod, image_image]

/--
theorem `image2_image_left` / 定理 `image2_image_left`

English:
theorem image2_image_left
  given: (f : γ -> β -> δ) (g : α -> γ)
  proof: by
  ext; simp

中文:
定理 image2_image_left
  条件: (f : γ -> β -> δ) (g : α -> γ)
  证明: by
  ext; simp
-/
theorem image2_image_left (f : γ -> β -> δ) (g : α -> γ) :
    image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t := by
  ext; simp

/--
theorem `image2_image_right` / 定理 `image2_image_right`

English:
theorem image2_image_right
  given: (f : α -> γ -> δ) (g : β -> γ)
  proof: by
  ext; simp

@[simp]

中文:
定理 image2_image_right
  条件: (f : α -> γ -> δ) (g : β -> γ)
  证明: by
  ext; simp

@[simp]
-/
theorem image2_image_right (f : α -> γ -> δ) (g : β -> γ) :
    image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t := by
  ext; simp

@[simp]
/--
theorem `image2_left` / 定理 `image2_left`

English:
theorem image2_left
  given: (h : t.Nonempty)
  statement: image2 (fun x _ => x) s t = s
  proof: by
  simp [nonempty_def.mp h, Set.ext_iff]

@[simp]

中文:
定理 image2_left
  条件: (h : t.非空)
  结论: image2 (fun x _ => x) s t = s
  证明: by
  simp [nonempty_def.mp h, Set.ext_iff]

@[simp]

Depends on / 依赖: Set.ext_iff, ext_iff, nonempty_def, nonempty_def.mp
-/
theorem image2_left (h : t.Nonempty) : image2 (fun x _ => x) s t = s := by
  simp [nonempty_def.mp h, Set.ext_iff]

@[simp]
/--
theorem `image2_right` / 定理 `image2_right`

English:
theorem image2_right
  given: (h : s.Nonempty)
  statement: image2 (fun _ y => y) s t = t
  proof: by
  simp [nonempty_def.mp h, Set.ext_iff]

中文:
定理 image2_right
  条件: (h : s.非空)
  结论: image2 (fun _ y => y) s t = t
  证明: by
  simp [nonempty_def.mp h, Set.ext_iff]

Depends on / 依赖: Set.ext_iff, ext_iff, nonempty_def, nonempty_def.mp
-/
theorem image2_right (h : s.Nonempty) : image2 (fun _ y => y) s t = t := by
  simp [nonempty_def.mp h, Set.ext_iff]

/--
lemma `image2_range` / 引理 `image2_range`

English:
lemma image2_range
  given: (f : α' -> β' -> γ) (g : α -> α') (h : β -> β')
  proof: by
  simp_rw [← image_univ, image2_image_left, image2_image_right, ← image_prod, univ_prod_univ]

中文:
引理 image2_range
  条件: (f : α' -> β' -> γ) (g : α -> α') (h : β -> β')
  证明: by
  simp_rw [← image_univ, image2_image_left, image2_image_right, ← image_prod, univ_prod_univ]

Depends on / 依赖: image2_image_left, image2_image_right, image_prod, image_univ, simp_rw, univ_prod_univ
-/
lemma image2_range (f : α' -> β' -> γ) (g : α -> α') (h : β -> β') :
    image2 f (range g) (range h) = range fun x : α × β => f (g x.1) (h x.2) := by
  simp_rw [← image_univ, image2_image_left, image2_image_right, ← image_prod, univ_prod_univ]

/--
theorem `image2_assoc` / 定理 `image2_assoc`

English:
theorem image2_assoc
  statement: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}
  proof: eq_of_forall_subset_iff fun _ => by simp only [image2_subset_iff, forall_mem_image2, h_assoc]

中文:
定理 image2_assoc
  结论: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}
  证明: eq_of_forall_subset_iff fun _ => by simp only [image2_subset_iff, forall_mem_image2, h_assoc]

Depends on / 依赖: eq_of_forall_subset_iff, forall_mem_image2, h_assoc, image2_subset_iff
-/
theorem image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}
    (h_assoc : forall a b c, f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
  eq_of_forall_subset_iff fun _ => by simp only [image2_subset_iff, forall_mem_image2, h_assoc]

/--
theorem `image2_comm` / 定理 `image2_comm`

English:
theorem image2_comm
  given: {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a)
  statement: image2 f s t = image2 g t s
  proof: (image2_swap _ _ _).trans by simp_rw [h_comm]

中文:
定理 image2_comm
  条件: {g : β -> α -> γ} (h_comm : 对任意 a b, f a b = g b a)
  结论: image2 f s t = image2 g t s
  证明: (image2_swap _ _ _).trans by simp_rw [h_comm]

Depends on / 依赖: h_comm, image2_swap, simp_rw
-/
theorem image2_comm {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a) : image2 f s t = image2 g t s :=
(image2_swap _ _ _).trans by simp_rw [h_comm]

/--
theorem `image2_left_comm` / 定理 `image2_left_comm`

English:
theorem image2_left_comm
  statement: {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}
  proof: by
  rw [image2_swap f']; rw [image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _

中文:
定理 image2_left_comm
  结论: {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}
  证明: by
  rw [image2_swap f']; rw [image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _

Depends on / 依赖: h_left_comm, image2_assoc, image2_swap
-/
theorem image2_left_comm {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}
    (h_left_comm : forall a b c, f a (g b c) = g' b (f' a c)) :
    image2 f s (image2 g t u) = image2 g' t (image2 f' s u) := by
  rw [image2_swap f']; rw [image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _

/--
theorem `image2_right_comm` / 定理 `image2_right_comm`

English:
theorem image2_right_comm
  statement: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}
  proof: by
  rw [image2_swap g]; rw [image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _

中文:
定理 image2_right_comm
  结论: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}
  证明: by
  rw [image2_swap g]; rw [image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _

Depends on / 依赖: h_right_comm, image2_assoc, image2_swap
-/
theorem image2_right_comm {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}
    (h_right_comm : forall a b c, f (g a b) c = g' (f' a c) b) :
    image2 f (image2 g s t) u = image2 g' (image2 f' s u) t := by
  rw [image2_swap g]; rw [image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _

/--
theorem `image2_image2_image2_comm` / 定理 `image2_image2_image2_comm`

English:
theorem image2_image2_image2_comm
  statement: {f : ε -> ζ -> ν} {g : α -> β -> ε} {h : γ -> δ -> ζ} {f' : ε' -> ζ' -> ν}
  proof: by
  grind

中文:
定理 image2_image2_image2_comm
  结论: {f : ε -> ζ -> ν} {g : α -> β -> ε} {h : γ -> δ -> ζ} {f' : ε' -> ζ' -> ν}
  证明: by
  grind
-/
theorem image2_image2_image2_comm {f : ε -> ζ -> ν} {g : α -> β -> ε} {h : γ -> δ -> ζ} {f' : ε' -> ζ' -> ν}
    {g' : α -> γ -> ε'} {h' : β -> δ -> ζ'}
    (h_comm : forall a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image2 f (image2 g s t) (image2 h u v) = image2 f' (image2 g' s u) (image2 h' t v) := by
  grind

/--
theorem `image_image2_distrib` / 定理 `image_image2_distrib`

English:
theorem image_image2_distrib
  statement: {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
  proof: by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

中文:
定理 image_image2_distrib
  结论: {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
  证明: by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

Depends on / 依赖: h_distrib, image2_image_left, image2_image_right, image_image2, simp_rw
-/
theorem image_image2_distrib {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
    (h_distrib : forall a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image2 f s t).image g = image2 f' (s.image g₁) (t.image g₂) := by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

/--
theorem `image_image2_distrib_left` / 定理 `image_image2_distrib_left`

English:
theorem image_image2_distrib_left
  statement: {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
  proof: (image_image2_distrib h_distrib).trans by rw [image_id']

中文:
定理 image_image2_distrib_left
  结论: {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
  证明: (image_image2_distrib h_distrib).trans by rw [image_id']

Depends on / 依赖: h_distrib, image_id, image_image2_distrib
-/
theorem image_image2_distrib_left {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
    (h_distrib : forall a b, g (f a b) = f' (g' a) b) :
    (image2 f s t).image g = image2 f' (s.image g') t :=
(image_image2_distrib h_distrib).trans by rw [image_id']

/--
theorem `image_image2_distrib_right` / 定理 `image_image2_distrib_right`

English:
theorem image_image2_distrib_right
  statement: {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
  proof: (image_image2_distrib h_distrib).trans by rw [image_id']

中文:
定理 image_image2_distrib_right
  结论: {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
  证明: (image_image2_distrib h_distrib).trans by rw [image_id']

Depends on / 依赖: h_distrib, image_id, image_image2_distrib
-/
theorem image_image2_distrib_right {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
    (h_distrib : forall a b, g (f a b) = f' a (g' b)) :
    (image2 f s t).image g = image2 f' s (t.image g') :=
(image_image2_distrib h_distrib).trans by rw [image_id']

/--
theorem `image2_image_left_comm` / 定理 `image2_image_left_comm`

English:
theorem image2_image_left_comm
  statement: {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
  proof: (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm

中文:
定理 image2_image_left_comm
  结论: {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
  证明: (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm

Depends on / 依赖: h_left_comm, image_image2_distrib_left
-/
theorem image2_image_left_comm {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
    (h_left_comm : forall a b, f (g a) b = g' (f' a b)) :
    image2 f (s.image g) t = (image2 f' s t).image g' :=
  (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm

/--
theorem `image_image2_right_comm` / 定理 `image_image2_right_comm`

English:
theorem image_image2_right_comm
  statement: {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
  proof: (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm

中文:
定理 image_image2_right_comm
  结论: {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
  证明: (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm

Depends on / 依赖: SheafedSpace, h_right_comm, image_image2_distrib_right, of_isIso
-/
theorem image_image2_right_comm {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
    (h_right_comm : forall a b, f a (g b) = g' (f' a b)) :
    image2 f s (t.image g) = (image2 f' s t).image g' :=
  (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm

/--
theorem `image2_distrib_subset_left` / 定理 `image2_distrib_subset_left`

English:
theorem image2_distrib_subset_left
  statement: {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'}
  proof: by
  grind

中文:
定理 image2_distrib_subset_left
  结论: {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'}
  证明: by
  grind
-/
theorem image2_distrib_subset_left {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'}
    {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε} (h_distrib : forall a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image2 f s (image2 g t u) subseteq image2 g' (image2 f₁ s t) (image2 f₂ s u) := by
  grind

/--
theorem `image2_distrib_subset_right` / 定理 `image2_distrib_subset_right`

English:
theorem image2_distrib_subset_right
  statement: {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'}
  proof: by
  grind

中文:
定理 image2_distrib_subset_right
  结论: {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'}
  证明: by
  grind
-/
theorem image2_distrib_subset_right {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'}
    {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε} (h_distrib : forall a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image2 f (image2 g s t) u subseteq image2 g' (image2 f₁ s u) (image2 f₂ t u) := by
  grind

/--
theorem `image_image2_antidistrib` / 定理 `image_image2_antidistrib`

English:
theorem image_image2_antidistrib
  statement: {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
  proof: by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _

中文:
定理 image_image2_antidistrib
  结论: {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
  证明: by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _

Depends on / 依赖: h_antidistrib, image2_swap, image_image2_distrib
-/
theorem image_image2_antidistrib {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
    (h_antidistrib : forall a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image2 f s t).image g = image2 f' (t.image g₁) (s.image g₂) := by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _

/--
theorem `image_image2_antidistrib_left` / 定理 `image_image2_antidistrib_left`

English:
theorem image_image2_antidistrib_left
  statement: {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
  proof: (image_image2_antidistrib h_antidistrib).trans by rw [image_id']

中文:
定理 image_image2_antidistrib_left
  结论: {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
  证明: (image_image2_antidistrib h_antidistrib).trans by rw [image_id']

Depends on / 依赖: h_antidistrib, image_id, image_image2_antidistrib
-/
theorem image_image2_antidistrib_left {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
    (h_antidistrib : forall a b, g (f a b) = f' (g' b) a) :
    (image2 f s t).image g = image2 f' (t.image g') s :=
(image_image2_antidistrib h_antidistrib).trans by rw [image_id']

/--
theorem `image_image2_antidistrib_right` / 定理 `image_image2_antidistrib_right`

English:
theorem image_image2_antidistrib_right
  statement: {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
  proof: (image_image2_antidistrib h_antidistrib).trans by rw [image_id']

中文:
定理 image_image2_antidistrib_right
  结论: {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
  证明: (image_image2_antidistrib h_antidistrib).trans by rw [image_id']

Depends on / 依赖: h_antidistrib, image_id, image_image2_antidistrib
-/
theorem image_image2_antidistrib_right {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
    (h_antidistrib : forall a b, g (f a b) = f' b (g' a)) :
    (image2 f s t).image g = image2 f' t (s.image g') :=
(image_image2_antidistrib h_antidistrib).trans by rw [image_id']

/--
theorem `image2_image_left_anticomm` / 定理 `image2_image_left_anticomm`

English:
theorem image2_image_left_anticomm
  statement: {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
  proof: (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

中文:
定理 image2_image_left_anticomm
  结论: {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
  证明: (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

Depends on / 依赖: h_left_anticomm, image_image2_antidistrib_left
-/
theorem image2_image_left_anticomm {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
    (h_left_anticomm : forall a b, f (g a) b = g' (f' b a)) :
    image2 f (s.image g) t = (image2 f' t s).image g' :=
  (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/--
theorem `image_image2_right_anticomm` / 定理 `image_image2_right_anticomm`

English:
theorem image_image2_right_anticomm
  statement: {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
  proof: (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

中文:
定理 image_image2_right_anticomm
  结论: {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
  证明: (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

Depends on / 依赖: h_right_anticomm, image_image2_antidistrib_right
-/
theorem image_image2_right_anticomm {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
    (h_right_anticomm : forall a b, f a (g b) = g' (f' b a)) :
    image2 f s (t.image g) = (image2 f' t s).image g' :=
  (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/--
lemma `image2_left_identity` / 引理 `image2_left_identity`

English:
lemma image2_left_identity
  given: {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (t : Set β)
  proof: by
  rw [image2_singleton_left]; rw [show f a = id from funext h]; rw [image_id]

中文:
引理 image2_left_identity
  条件: {f : α -> β -> β} {a : α} (h : 对任意 b, f a b = b) (t : 集合 β)
  证明: by
  rw [image2_singleton_left]; rw [show f a = id from funext h]; rw [image_id]

Depends on / 依赖: image2_singleton_left, image_id
-/
lemma image2_left_identity {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (t : Set β) :
    image2 f {a} t = t := by
  rw [image2_singleton_left]; rw [show f a = id from funext h]; rw [image_id]

/--
lemma `image2_right_identity` / 引理 `image2_right_identity`

English:
lemma image2_right_identity
  given: {f : α -> β -> α} {b : β} (h : forall a, f a b = a) (s : Set α)
  proof: by
  rw [image2_singleton_right]; rw [funext h]; rw [image_id']

中文:
引理 image2_right_identity
  条件: {f : α -> β -> α} {b : β} (h : 对任意 a, f a b = a) (s : 集合 α)
  证明: by
  rw [image2_singleton_right]; rw [funext h]; rw [image_id']

Depends on / 依赖: image2_singleton_right, image_id
-/
lemma image2_right_identity {f : α -> β -> α} {b : β} (h : forall a, f a b = a) (s : Set α) :
    image2 f s {b} = s := by
  rw [image2_singleton_right]; rw [funext h]; rw [image_id']

/--
theorem `image2_inter_union_subset_union` / 定理 `image2_inter_union_subset_union`

English:
theorem image2_inter_union_subset_union
  proof: by
  rw [image2_union_right]
  nth_grw 1 [inter_subset_left, inter_subset_right]

中文:
定理 image2_inter_union_subset_union
  证明: by
  rw [image2_union_right]
  nth_grw 1 [inter_subset_left, inter_subset_right]

Depends on / 依赖: image2_union_right, inter_subset_left, inter_subset_right, nth_grw
-/
theorem image2_inter_union_subset_union :
    image2 f (s inter s') (t union t') subseteq image2 f s t union image2 f s' t' := by
  rw [image2_union_right]
  nth_grw 1 [inter_subset_left, inter_subset_right]

/--
theorem `image2_union_inter_subset_union` / 定理 `image2_union_inter_subset_union`

English:
theorem image2_union_inter_subset_union
  proof: by
  rw [image2_union_left]
  nth_grw 1 [inter_subset_left, inter_subset_right]

中文:
定理 image2_union_inter_subset_union
  证明: by
  rw [image2_union_left]
  nth_grw 1 [inter_subset_left, inter_subset_right]

Depends on / 依赖: image2_union_left, inter_subset_left, inter_subset_right, nth_grw
-/
theorem image2_union_inter_subset_union :
    image2 f (s union s') (t inter t') subseteq image2 f s t union image2 f s' t' := by
  rw [image2_union_left]
  nth_grw 1 [inter_subset_left, inter_subset_right]

/--
theorem `image2_inter_union_subset` / 定理 `image2_inter_union_subset`

English:
theorem image2_inter_union_subset
  given: {f : α -> α -> β} {s t : Set α} (hf : forall a b, f a b = f b a)
  proof: by
  grw [inter_comm, image2_inter_union_subset_union, image2_comm hf, union_self]

中文:
定理 image2_inter_union_subset
  条件: {f : α -> α -> β} {s t : 集合 α} (hf : 对任意 a b, f a b = f b a)
  证明: by
  grw [inter_comm, image2_inter_union_subset_union, image2_comm hf, union_self]

Depends on / 依赖: image2_comm, image2_inter_union_subset_union, inter_comm, union_self
-/
theorem image2_inter_union_subset {f : α -> α -> β} {s t : Set α} (hf : forall a b, f a b = f b a) :
    image2 f (s inter t) (s union t) subseteq image2 f s t := by
  grw [inter_comm, image2_inter_union_subset_union, image2_comm hf, union_self]

/--
theorem `image2_union_inter_subset` / 定理 `image2_union_inter_subset`

English:
theorem image2_union_inter_subset
  given: {f : α -> α -> β} {s t : Set α} (hf : forall a b, f a b = f b a)
  proof: by
  rw [image2_comm hf]
  exact image2_inter_union_subset hf

中文:
定理 image2_union_inter_subset
  条件: {f : α -> α -> β} {s t : 集合 α} (hf : 对任意 a b, f a b = f b a)
  证明: by
  rw [image2_comm hf]
  exact image2_inter_union_subset hf

Depends on / 依赖: image2_comm, image2_inter_union_subset
-/
theorem image2_union_inter_subset {f : α -> α -> β} {s t : Set α} (hf : forall a b, f a b = f b a) :
    image2 f (s union t) (s inter t) subseteq image2 f s t := by
  rw [image2_comm hf]
  exact image2_inter_union_subset hf

end Set
