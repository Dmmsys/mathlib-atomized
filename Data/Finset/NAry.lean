/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Lattice.Image

/-!
# N-ary images of finsets

This file defines `Finset.image₂`, the binary image of finsets. This is the finset version of
`Set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to `Mathlib/Data/Set/NAry.lean`, `Mathlib/Order/Filter/NAry.lean` and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.

We do not define `Finset.image₃` as its only purpose would be to prove properties of `Finset.image₂`
and `Set.image2` already fulfills this task.
-/

@[expose] public section

open Function Set

variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*}

namespace Finset

variable [DecidableEq α'] [DecidableEq β'] [DecidableEq γ] [DecidableEq γ']
  [DecidableEq δ'] [DecidableEq ε] [DecidableEq ε'] {f f' : α -> β -> γ} {g g' : α -> β -> γ -> δ}
  {s s' : Finset α} {t t' : Finset β} {u u' : Finset γ} {a a' : α} {b b' : β} {c : γ}

/--
Definition of `image₂` / `image₂` 的定义

English:
definition image₂
  signature: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  body: (s ×ˢ t).image uncurry f

@[simp]

中文:
定义 image₂
  签名: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  定义体: (s ×ˢ t).image uncurry f

@[simp]

Depends on / 依赖: uncurry
-/
def image₂ (f : α -> β -> γ) (s : Finset α) (t : Finset β) : Finset γ :=
(s ×ˢ t).image uncurry f

@[simp]
/--
theorem `mem_image₂` / 定理 `mem_image₂`

English:
theorem mem_image₂
  statement: c in image₂ f s t ↔ exists a in s, exists b in t, f a b = c
  proof: by
  simp [image₂, and_assoc]

@[simp, norm_cast]

中文:
定理 mem_image₂
  结论: c in image₂ f s t ↔ 存在 a in s, 存在 b in t, f a b = c
  证明: by
  simp [image₂, and_assoc]

@[simp, norm_cast]

Depends on / 依赖: and_assoc
-/
theorem mem_image₂ : c in image₂ f s t ↔ exists a in s, exists b in t, f a b = c := by
  simp [image₂, and_assoc]

@[simp, norm_cast]
/--
theorem `coe_image₂` / 定理 `coe_image₂`

English:
theorem coe_image₂
  given: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  proof: Set.ext fun _ => mem_image₂

中文:
定理 coe_image₂
  条件: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  证明: Set.ext fun _ => mem_image₂

Depends on / 依赖: Set.ext
-/
theorem coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Finset β) :
    (image₂ f s t : Set γ) = Set.image2 f s t :=
  Set.ext fun _ => mem_image₂

/--
theorem `card_image₂_le` / 定理 `card_image₂_le`

English:
theorem card_image₂_le
  given: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  proof: card_image_le.trans_eq card_product _ _

中文:
定理 card_image₂_le
  条件: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  证明: card_image_le.trans_eq card_product _ _

Depends on / 依赖: card_image_le, card_image_le.trans_eq, card_product, trans_eq
-/
theorem card_image₂_le (f : α -> β -> γ) (s : Finset α) (t : Finset β) :
    #(image₂ f s t) <= #s * #t :=
card_image_le.trans_eq card_product _ _

/--
theorem `card_image₂_iff` / 定理 `card_image₂_iff`

English:
theorem card_image₂_iff
  proof: by
  rw [← card_product]; rw [← coe_product]
  exact card_image_iff

中文:
定理 card_image₂_iff
  证明: by
  rw [← card_product]; rw [← coe_product]
  exact card_image_iff

Depends on / 依赖: card_image_iff, card_product, coe_product
-/
theorem card_image₂_iff :
    #(image₂ f s t) = #s * #t ↔ (s ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2 := by
  rw [← card_product]; rw [← coe_product]
  exact card_image_iff

/--
theorem `card_image₂` / 定理 `card_image₂`

English:
theorem card_image₂
  given: (hf : Injective2 f) (s : Finset α) (t : Finset β)
  proof: (card_image_of_injective _ hf.uncurry).trans card_product _ _

中文:
定理 card_image₂
  条件: (hf : Injective2 f) (s : Finset α) (t : Finset β)
  证明: (card_image_of_injective _ hf.uncurry).trans card_product _ _

Depends on / 依赖: card_image_of_injective, card_product, hf.uncurry, uncurry
-/
theorem card_image₂ (hf : Injective2 f) (s : Finset α) (t : Finset β) :
    #(image₂ f s t) = #s * #t :=
(card_image_of_injective _ hf.uncurry).trans card_product _ _

/--
theorem `mem_image₂_of_mem` / 定理 `mem_image₂_of_mem`

English:
theorem mem_image₂_of_mem
  given: (ha : a in s) (hb : b in t)
  statement: f a b in image₂ f s t
  proof: mem_image₂.2 ⟨a, ha, b, hb, rfl⟩

中文:
定理 mem_image₂_of_mem
  条件: (ha : a in s) (hb : b in t)
  结论: f a b in image₂ f s t
  证明: mem_image₂.2 ⟨a, ha, b, hb, rfl⟩
-/
theorem mem_image₂_of_mem (ha : a in s) (hb : b in t) : f a b in image₂ f s t :=
  mem_image₂.2 ⟨a, ha, b, hb, rfl⟩

/--
theorem `mem_image₂_iff` / 定理 `mem_image₂_iff`

English:
theorem mem_image₂_iff
  given: (hf : Injective2 f)
  statement: f a b in image₂ f s t ↔ a in s ∧ b in t
  proof: by
  rw [← mem_coe]; rw [coe_image₂]; rw [mem_image2_iff hf]; rw [mem_coe]; rw [mem_coe]

@[gcongr]

中文:
定理 mem_image₂_iff
  条件: (hf : Injective2 f)
  结论: f a b in image₂ f s t ↔ a in s ∧ b in t
  证明: by
  rw [← mem_coe]; rw [coe_image₂]; rw [mem_image2_iff hf]; rw [mem_coe]; rw [mem_coe]

@[gcongr]

Depends on / 依赖: mem_coe, mem_image2_iff
-/
theorem mem_image₂_iff (hf : Injective2 f) : f a b in image₂ f s t ↔ a in s ∧ b in t := by
  rw [← mem_coe]; rw [coe_image₂]; rw [mem_image2_iff hf]; rw [mem_coe]; rw [mem_coe]

@[gcongr]
/--
theorem `image₂_subset` / 定理 `image₂_subset`

English:
theorem image₂_subset
  given: (hs : s subseteq s') (ht : t subseteq t')
  statement: image₂ f s t subseteq image₂ f s' t'
  proof: by
  rw [← coe_subset]; rw [coe_image₂]; rw [coe_image₂]
  exact image2_subset hs ht

中文:
定理 image₂_subset
  条件: (hs : s subseteq s') (ht : t subseteq t')
  结论: image₂ f s t subseteq image₂ f s' t'
  证明: by
  rw [← coe_subset]; rw [coe_image₂]; rw [coe_image₂]
  exact image2_subset hs ht

Depends on / 依赖: coe_subset, image2_subset
-/
theorem image₂_subset (hs : s subseteq s') (ht : t subseteq t') : image₂ f s t subseteq image₂ f s' t' := by
  rw [← coe_subset]; rw [coe_image₂]; rw [coe_image₂]
  exact image2_subset hs ht

/--
theorem `image₂_subset_left` / 定理 `image₂_subset_left`

English:
theorem image₂_subset_left
  given: (ht : t subseteq t')
  statement: image₂ f s t subseteq image₂ f s t'
  proof: image₂_subset Subset.rfl ht

中文:
定理 image₂_subset_left
  条件: (ht : t subseteq t')
  结论: image₂ f s t subseteq image₂ f s t'
  证明: image₂_subset Subset.rfl ht

Depends on / 依赖: Or.rec, Subset, Subset.rfl, coprime_iff_not_dvd, dvd_of_dvd_mul_left, h.mul_left, h.mul_right, mul_left, mul_right, or_iff_not_imp_left, pp.coprime_iff_not_dvd
-/
theorem image₂_subset_left (ht : t subseteq t') : image₂ f s t subseteq image₂ f s t' :=
  image₂_subset Subset.rfl ht

/--
theorem `image₂_subset_right` / 定理 `image₂_subset_right`

English:
theorem image₂_subset_right
  given: (hs : s subseteq s')
  statement: image₂ f s t subseteq image₂ f s' t
  proof: image₂_subset hs Subset.rfl

中文:
定理 image₂_subset_right
  条件: (hs : s subseteq s')
  结论: image₂ f s t subseteq image₂ f s' t
  证明: image₂_subset hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl
-/
theorem image₂_subset_right (hs : s subseteq s') : image₂ f s t subseteq image₂ f s' t :=
  image₂_subset hs Subset.rfl

/--
theorem `image_subset_image₂_left` / 定理 `image_subset_image₂_left`

English:
theorem image_subset_image₂_left
  given: (hb : b in t)
  statement: s.image (fun a => f a b) subseteq image₂ f s t
  proof: image_subset_iff.2 fun _ ha => mem_image₂_of_mem ha hb

中文:
定理 image_subset_image₂_left
  条件: (hb : b in t)
  结论: s.image (fun a => f a b) subseteq image₂ f s t
  证明: image_subset_iff.2 fun _ ha => mem_image₂_of_mem ha hb

Depends on / 依赖: image_subset_iff
-/
theorem image_subset_image₂_left (hb : b in t) : s.image (fun a => f a b) subseteq image₂ f s t :=
  image_subset_iff.2 fun _ ha => mem_image₂_of_mem ha hb

/--
theorem `image_subset_image₂_right` / 定理 `image_subset_image₂_right`

English:
theorem image_subset_image₂_right
  given: (ha : a in s)
  statement: t.image (fun b => f a b) subseteq image₂ f s t
  proof: image_subset_iff.2 fun _ => mem_image₂_of_mem ha

中文:
定理 image_subset_image₂_right
  条件: (ha : a in s)
  结论: t.image (fun b => f a b) subseteq image₂ f s t
  证明: image_subset_iff.2 fun _ => mem_image₂_of_mem ha

Depends on / 依赖: image_subset_iff
-/
theorem image_subset_image₂_right (ha : a in s) : t.image (fun b => f a b) subseteq image₂ f s t :=
  image_subset_iff.2 fun _ => mem_image₂_of_mem ha

/--
lemma `forall_mem_image₂` / 引理 `forall_mem_image₂`

English:
lemma forall_mem_image₂
  given: {p : γ -> Prop}
  proof: by
  simp_rw [← mem_coe, coe_image₂, forall_mem_image2]

中文:
引理 forall_mem_image₂
  条件: {p : γ -> 命题}
  证明: by
  simp_rw [← mem_coe, coe_image₂, forall_mem_image2]

Depends on / 依赖: forall_mem_image2, mem_coe, simp_rw
-/
lemma forall_mem_image₂ {p : γ -> Prop} :
    (forall z in image₂ f s t, p z) ↔ forall x in s, forall y in t, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, forall_mem_image2]

/--
lemma `exists_mem_image₂` / 引理 `exists_mem_image₂`

English:
lemma exists_mem_image₂
  given: {p : γ -> Prop}
  proof: by
  simp_rw [← mem_coe, coe_image₂, exists_mem_image2]

@[simp]

中文:
引理 exists_mem_image₂
  条件: {p : γ -> 命题}
  证明: by
  simp_rw [← mem_coe, coe_image₂, exists_mem_image2]

@[simp]

Depends on / 依赖: exists_mem_image2, mem_coe, simp_rw
-/
lemma exists_mem_image₂ {p : γ -> Prop} :
    (exists z in image₂ f s t, p z) ↔ exists x in s, exists y in t, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, exists_mem_image2]

@[simp]
/--
theorem `image₂_subset_iff` / 定理 `image₂_subset_iff`

English:
theorem image₂_subset_iff
  statement: image₂ f s t subseteq u ↔ forall x in s, forall y in t, f x y in u
  proof: forall_mem_image₂

中文:
定理 image₂_subset_iff
  结论: image₂ f s t subseteq u ↔ 对任意 x in s, 对任意 y in t, f x y in u
  证明: forall_mem_image₂
-/
theorem image₂_subset_iff : image₂ f s t subseteq u ↔ forall x in s, forall y in t, f x y in u :=
  forall_mem_image₂

/--
theorem `image₂_subset_iff_left` / 定理 `image₂_subset_iff_left`

English:
theorem image₂_subset_iff_left
  statement: image₂ f s t subseteq u ↔ forall a in s, (t.image fun b => f a b) subseteq u
  proof: by
  simp_rw [image₂_subset_iff, image_subset_iff]

中文:
定理 image₂_subset_iff_left
  结论: image₂ f s t subseteq u ↔ 对任意 a in s, (t.image fun b => f a b) subseteq u
  证明: by
  simp_rw [image₂_subset_iff, image_subset_iff]

Depends on / 依赖: image_subset_iff, simp_rw
-/
theorem image₂_subset_iff_left : image₂ f s t subseteq u ↔ forall a in s, (t.image fun b => f a b) subseteq u := by
  simp_rw [image₂_subset_iff, image_subset_iff]

/--
theorem `image₂_subset_iff_right` / 定理 `image₂_subset_iff_right`

English:
theorem image₂_subset_iff_right
  statement: image₂ f s t subseteq u ↔ forall b in t, (s.image fun a => f a b) subseteq u
  proof: by
  simp_rw [image₂_subset_iff, image_subset_iff, @forall₂_comm α]

@[simp]

中文:
定理 image₂_subset_iff_right
  结论: image₂ f s t subseteq u ↔ 对任意 b in t, (s.image fun a => f a b) subseteq u
  证明: by
  simp_rw [image₂_subset_iff, image_subset_iff, @forall₂_comm α]

@[simp]

Depends on / 依赖: image_subset_iff, simp_rw
-/
theorem image₂_subset_iff_right : image₂ f s t subseteq u ↔ forall b in t, (s.image fun a => f a b) subseteq u := by
  simp_rw [image₂_subset_iff, image_subset_iff, @forall₂_comm α]

@[simp]
/--
theorem `image₂_nonempty_iff` / 定理 `image₂_nonempty_iff`

English:
theorem image₂_nonempty_iff
  statement: (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: by
  rw [← coe_nonempty]; rw [coe_image₂]
  exact image2_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 image₂_nonempty_iff
  结论: (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: by
  rw [← coe_nonempty]; rw [coe_image₂]
  exact image2_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: coe_nonempty, image2_nonempty_iff
-/
theorem image₂_nonempty_iff : (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  rw [← coe_nonempty]; rw [coe_image₂]
  exact image2_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.image₂` / 定理 `Nonempty.image₂`

English:
theorem Nonempty.image₂
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  statement: (image₂ f s t).Nonempty
  proof: image₂_nonempty_iff.2 ⟨hs, ht⟩

中文:
定理 Nonempty.image₂
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  结论: (image₂ f s t).Nonempty
  证明: image₂_nonempty_iff.2 ⟨hs, ht⟩
-/
theorem Nonempty.image₂ (hs : s.Nonempty) (ht : t.Nonempty) : (image₂ f s t).Nonempty :=
  image₂_nonempty_iff.2 ⟨hs, ht⟩

/--
theorem `Nonempty.of_image₂_left` / 定理 `Nonempty.of_image₂_left`

English:
theorem Nonempty.of_image₂_left
  given: (h : (s.image₂ f t).Nonempty)
  statement: s.Nonempty
  proof: (image₂_nonempty_iff.1 h).1

中文:
定理 Nonempty.of_image₂_left
  条件: (h : (s.image₂ f t).Nonempty)
  结论: s.Nonempty
  证明: (image₂_nonempty_iff.1 h).1
-/
theorem Nonempty.of_image₂_left (h : (s.image₂ f t).Nonempty) : s.Nonempty :=
  (image₂_nonempty_iff.1 h).1

/--
theorem `Nonempty.of_image₂_right` / 定理 `Nonempty.of_image₂_right`

English:
theorem Nonempty.of_image₂_right
  given: (h : (s.image₂ f t).Nonempty)
  statement: t.Nonempty
  proof: (image₂_nonempty_iff.1 h).2

@[simp]

中文:
定理 Nonempty.of_image₂_right
  条件: (h : (s.image₂ f t).Nonempty)
  结论: t.Nonempty
  证明: (image₂_nonempty_iff.1 h).2

@[simp]
-/
theorem Nonempty.of_image₂_right (h : (s.image₂ f t).Nonempty) : t.Nonempty :=
  (image₂_nonempty_iff.1 h).2

@[simp]
/--
theorem `image₂_empty_left` / 定理 `image₂_empty_left`

English:
theorem image₂_empty_left
  statement: image₂ f ∅ t = ∅
  proof: coe_injective by simp

@[simp]

中文:
定理 image₂_empty_left
  结论: image₂ f ∅ t = ∅
  证明: coe_injective by simp

@[simp]

Depends on / 依赖: coe_injective
-/
theorem image₂_empty_left : image₂ f ∅ t = ∅ :=
coe_injective by simp

@[simp]
/--
theorem `image₂_empty_right` / 定理 `image₂_empty_right`

English:
theorem image₂_empty_right
  statement: image₂ f s ∅ = ∅
  proof: coe_injective by simp

@[simp]

中文:
定理 image₂_empty_right
  结论: image₂ f s ∅ = ∅
  证明: coe_injective by simp

@[simp]

Depends on / 依赖: coe_injective
-/
theorem image₂_empty_right : image₂ f s ∅ = ∅ :=
coe_injective by simp

@[simp]
/--
theorem `image₂_eq_empty_iff` / 定理 `image₂_eq_empty_iff`

English:
theorem image₂_eq_empty_iff
  statement: image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: by
  contrapose!; exact image₂_nonempty_iff

@[simp]

中文:
定理 image₂_eq_empty_iff
  结论: image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: by
  contrapose!; exact image₂_nonempty_iff

@[simp]

Depends on / 依赖: contrapose
-/
theorem image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  contrapose!; exact image₂_nonempty_iff

@[simp]
/--
theorem `image₂_singleton_left` / 定理 `image₂_singleton_left`

English:
theorem image₂_singleton_left
  statement: image₂ f {a} t = t.image fun b => f a b
  proof: ext fun x => by simp

@[simp]

中文:
定理 image₂_singleton_left
  结论: image₂ f {a} t = t.image fun b => f a b
  证明: ext fun x => by simp

@[simp]
-/
theorem image₂_singleton_left : image₂ f {a} t = t.image fun b => f a b :=
  ext fun x => by simp

@[simp]
/--
theorem `image₂_singleton_right` / 定理 `image₂_singleton_right`

English:
theorem image₂_singleton_right
  statement: image₂ f s {b} = s.image fun a => f a b
  proof: ext fun x => by simp

中文:
定理 image₂_singleton_right
  结论: image₂ f s {b} = s.image fun a => f a b
  证明: ext fun x => by simp
-/
theorem image₂_singleton_right : image₂ f s {b} = s.image fun a => f a b :=
  ext fun x => by simp

/--
theorem `image₂_singleton_left'` / 定理 `image₂_singleton_left'`

English:
theorem image₂_singleton_left'
  statement: image₂ f {a} t = t.image (f a)
  proof: image₂_singleton_left

中文:
定理 image₂_singleton_left'
  结论: image₂ f {a} t = t.image (f a)
  证明: image₂_singleton_left
-/
theorem image₂_singleton_left' : image₂ f {a} t = t.image (f a) :=
  image₂_singleton_left

/--
theorem `image₂_singleton` / 定理 `image₂_singleton`

English:
theorem image₂_singleton
  statement: image₂ f {a} {b} = {f a b}
  proof: by simp

中文:
定理 image₂_singleton
  结论: image₂ f {a} {b} = {f a b}
  证明: by simp
-/
theorem image₂_singleton : image₂ f {a} {b} = {f a b} := by simp

/--
theorem `image₂_union_left` / 定理 `image₂_union_left`

English:
theorem image₂_union_left
  given: [DecidableEq α]
  statement: image₂ f (s union s') t = image₂ f s t union image₂ f s' t
  proof: coe_injective by
    push_cast
    exact image2_union_left

中文:
定理 image₂_union_left
  条件: [DecidableEq α]
  结论: image₂ f (s union s') t = image₂ f s t union image₂ f s' t
  证明: coe_injective by
    push_cast
    exact image2_union_left

Depends on / 依赖: coe_injective, image2_union_left
-/
theorem image₂_union_left [DecidableEq α] : image₂ f (s union s') t = image₂ f s t union image₂ f s' t :=
coe_injective by
    push_cast
    exact image2_union_left

/--
theorem `image₂_union_right` / 定理 `image₂_union_right`

English:
theorem image₂_union_right
  given: [DecidableEq β]
  statement: image₂ f s (t union t') = image₂ f s t union image₂ f s t'
  proof: coe_injective by
    push_cast
    exact image2_union_right

@[simp]

中文:
定理 image₂_union_right
  条件: [DecidableEq β]
  结论: image₂ f s (t union t') = image₂ f s t union image₂ f s t'
  证明: coe_injective by
    push_cast
    exact image2_union_right

@[simp]

Depends on / 依赖: coe_injective, image2_union_right
-/
theorem image₂_union_right [DecidableEq β] : image₂ f s (t union t') = image₂ f s t union image₂ f s t' :=
coe_injective by
    push_cast
    exact image2_union_right

@[simp]
/--
theorem `image₂_insert_left` / 定理 `image₂_insert_left`

English:
theorem image₂_insert_left
  given: [DecidableEq α]
  proof: coe_injective by
    push_cast
    exact image2_insert_left

@[simp]

中文:
定理 image₂_insert_left
  条件: [DecidableEq α]
  证明: coe_injective by
    push_cast
    exact image2_insert_left

@[simp]

Depends on / 依赖: coe_injective, image2_insert_left
-/
theorem image₂_insert_left [DecidableEq α] :
    image₂ f (insert a s) t = (t.image fun b => f a b) union image₂ f s t :=
coe_injective by
    push_cast
    exact image2_insert_left

@[simp]
/--
theorem `image₂_insert_right` / 定理 `image₂_insert_right`

English:
theorem image₂_insert_right
  given: [DecidableEq β]
  proof: coe_injective by
    push_cast
    exact image2_insert_right

中文:
定理 image₂_insert_right
  条件: [DecidableEq β]
  证明: coe_injective by
    push_cast
    exact image2_insert_right

Depends on / 依赖: coe_injective, image2_insert_right
-/
theorem image₂_insert_right [DecidableEq β] :
    image₂ f s (insert b t) = (s.image fun a => f a b) union image₂ f s t :=
coe_injective by
    push_cast
    exact image2_insert_right

/--
theorem `image₂_inter_left` / 定理 `image₂_inter_left`

English:
theorem image₂_inter_left
  given: [DecidableEq α] (hf : Injective2 f)
  proof: coe_injective by
    push_cast
    exact image2_inter_left hf

中文:
定理 image₂_inter_left
  条件: [DecidableEq α] (hf : Injective2 f)
  证明: coe_injective by
    push_cast
    exact image2_inter_left hf

Depends on / 依赖: coe_injective, image2_inter_left
-/
theorem image₂_inter_left [DecidableEq α] (hf : Injective2 f) :
    image₂ f (s inter s') t = image₂ f s t inter image₂ f s' t :=
coe_injective by
    push_cast
    exact image2_inter_left hf

/--
theorem `image₂_inter_right` / 定理 `image₂_inter_right`

English:
theorem image₂_inter_right
  given: [DecidableEq β] (hf : Injective2 f)
  proof: coe_injective by
    push_cast
    exact image2_inter_right hf

中文:
定理 image₂_inter_right
  条件: [DecidableEq β] (hf : Injective2 f)
  证明: coe_injective by
    push_cast
    exact image2_inter_right hf

Depends on / 依赖: coe_injective, image2_inter_right
-/
theorem image₂_inter_right [DecidableEq β] (hf : Injective2 f) :
    image₂ f s (t inter t') = image₂ f s t inter image₂ f s t' :=
coe_injective by
    push_cast
    exact image2_inter_right hf

/--
theorem `image₂_inter_subset_left` / 定理 `image₂_inter_subset_left`

English:
theorem image₂_inter_subset_left
  given: [DecidableEq α]
  proof: coe_subset.1 by
    push_cast
    exact image2_inter_subset_left

中文:
定理 image₂_inter_subset_left
  条件: [DecidableEq α]
  证明: coe_subset.1 by
    push_cast
    exact image2_inter_subset_left

Depends on / 依赖: coe_subset, image2_inter_subset_left
-/
theorem image₂_inter_subset_left [DecidableEq α] :
    image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t :=
coe_subset.1 by
    push_cast
    exact image2_inter_subset_left

/--
theorem `image₂_inter_subset_right` / 定理 `image₂_inter_subset_right`

English:
theorem image₂_inter_subset_right
  given: [DecidableEq β]
  proof: coe_subset.1 by
    push_cast
    exact image2_inter_subset_right

中文:
定理 image₂_inter_subset_right
  条件: [DecidableEq β]
  证明: coe_subset.1 by
    push_cast
    exact image2_inter_subset_right

Depends on / 依赖: coe_subset, image2_inter_subset_right
-/
theorem image₂_inter_subset_right [DecidableEq β] :
    image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t' :=
coe_subset.1 by
    push_cast
    exact image2_inter_subset_right

/--
theorem `image₂_congr` / 定理 `image₂_congr`

English:
theorem image₂_congr
  given: (h : forall a in s, forall b in t, f a b = f' a b)
  statement: image₂ f s t = image₂ f' s t
  proof: coe_injective by
    push_cast
    exact image2_congr h

中文:
定理 image₂_congr
  条件: (h : 对任意 a in s, 对任意 b in t, f a b = f' a b)
  结论: image₂ f s t = image₂ f' s t
  证明: coe_injective by
    push_cast
    exact image2_congr h

Depends on / 依赖: coe_injective, image2_congr
-/
theorem image₂_congr (h : forall a in s, forall b in t, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
coe_injective by
    push_cast
    exact image2_congr h

/--
theorem `image₂_congr'` / 定理 `image₂_congr'`

English:
theorem image₂_congr'
  given: (h : forall a b, f a b = f' a b)
  statement: image₂ f s t = image₂ f' s t
  proof: image₂_congr fun a _ b _ => h a b

中文:
定理 image₂_congr'
  条件: (h : 对任意 a b, f a b = f' a b)
  结论: image₂ f s t = image₂ f' s t
  证明: image₂_congr fun a _ b _ => h a b
-/
theorem image₂_congr' (h : forall a b, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  image₂_congr fun a _ b _ => h a b

variable (s t)

/--
theorem `card_image₂_singleton_left` / 定理 `card_image₂_singleton_left`

English:
theorem card_image₂_singleton_left
  given: (hf : Injective (f a))
  statement: #(image₂ f {a} t) = #t
  proof: by
  rw [image₂_singleton_left]; rw [card_image_of_injective _ hf]

中文:
定理 card_image₂_singleton_left
  条件: (hf : Injective (f a))
  结论: #(image₂ f {a} t) = #t
  证明: by
  rw [image₂_singleton_left]; rw [card_image_of_injective _ hf]

Depends on / 依赖: card_image_of_injective
-/
theorem card_image₂_singleton_left (hf : Injective (f a)) : #(image₂ f {a} t) = #t := by
  rw [image₂_singleton_left]; rw [card_image_of_injective _ hf]

/--
theorem `card_image₂_singleton_right` / 定理 `card_image₂_singleton_right`

English:
theorem card_image₂_singleton_right
  given: (hf : Injective fun a => f a b)
  proof: by rw [image₂_singleton_right, card_image_of_injective _ hf]

中文:
定理 card_image₂_singleton_right
  条件: (hf : Injective fun a => f a b)
  证明: by rw [image₂_singleton_right, card_image_of_injective _ hf]

Depends on / 依赖: card_image_of_injective
-/
theorem card_image₂_singleton_right (hf : Injective fun a => f a b) :
    #(image₂ f s {b}) = #s := by rw [image₂_singleton_right, card_image_of_injective _ hf]

/--
theorem `image₂_singleton_inter` / 定理 `image₂_singleton_inter`

English:
theorem image₂_singleton_inter
  given: [DecidableEq β] (t₁ t₂ : Finset β) (hf : Injective (f a))
  proof: by
  simp_rw [image₂_singleton_left, image_inter _ _ hf]

中文:
定理 image₂_singleton_inter
  条件: [DecidableEq β] (t₁ t₂ : Finset β) (hf : Injective (f a))
  证明: by
  simp_rw [image₂_singleton_left, image_inter _ _ hf]

Depends on / 依赖: image_inter, simp_rw
-/
theorem image₂_singleton_inter [DecidableEq β] (t₁ t₂ : Finset β) (hf : Injective (f a)) :
    image₂ f {a} (t₁ inter t₂) = image₂ f {a} t₁ inter image₂ f {a} t₂ := by
  simp_rw [image₂_singleton_left, image_inter _ _ hf]

/--
theorem `image₂_inter_singleton` / 定理 `image₂_inter_singleton`

English:
theorem image₂_inter_singleton
  given: [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective fun a => f a b)
  proof: by
  simp_rw [image₂_singleton_right, image_inter _ _ hf]

中文:
定理 image₂_inter_singleton
  条件: [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective fun a => f a b)
  证明: by
  simp_rw [image₂_singleton_right, image_inter _ _ hf]

Depends on / 依赖: image_inter, simp_rw
-/
theorem image₂_inter_singleton [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective fun a => f a b) :
    image₂ f (s₁ inter s₂) {b} = image₂ f s₁ {b} inter image₂ f s₂ {b} := by
  simp_rw [image₂_singleton_right, image_inter _ _ hf]

/--
theorem `card_le_card_image₂_left` / 定理 `card_le_card_image₂_left`

English:
theorem card_le_card_image₂_left
  given: {s : Finset α} (ha : a in s) (hf : Injective (f a))
  proof: card_le_card_of_injOn (f a) (fun _ hb => mem_image₂_of_mem ha hb) hf.injOn

中文:
定理 card_le_card_image₂_left
  条件: {s : Finset α} (ha : a in s) (hf : Injective (f a))
  证明: card_le_card_of_injOn (f a) (fun _ hb => mem_image₂_of_mem ha hb) hf.injOn

Depends on / 依赖: card_le_card_of_injOn, hf.injOn
-/
theorem card_le_card_image₂_left {s : Finset α} (ha : a in s) (hf : Injective (f a)) :
    #t <= #(image₂ f s t) :=
  card_le_card_of_injOn (f a) (fun _ hb => mem_image₂_of_mem ha hb) hf.injOn

/--
theorem `card_le_card_image₂_right` / 定理 `card_le_card_image₂_right`

English:
theorem card_le_card_image₂_right
  given: {t : Finset β} (hb : b in t) (hf : Injective (f · b))
  proof: card_le_card_of_injOn (f · b) (fun _ ha => mem_image₂_of_mem ha hb) hf.injOn

中文:
定理 card_le_card_image₂_right
  条件: {t : Finset β} (hb : b in t) (hf : Injective (f · b))
  证明: card_le_card_of_injOn (f · b) (fun _ ha => mem_image₂_of_mem ha hb) hf.injOn

Depends on / 依赖: card_le_card_of_injOn, hf.injOn
-/
theorem card_le_card_image₂_right {t : Finset β} (hb : b in t) (hf : Injective (f · b)) :
    #s <= #(image₂ f s t) :=
  card_le_card_of_injOn (f · b) (fun _ ha => mem_image₂_of_mem ha hb) hf.injOn

variable {s t}

/--
theorem `biUnion_image_left` / 定理 `biUnion_image_left`

English:
theorem biUnion_image_left
  statement: (s.biUnion fun a => t.image <| f a) = image₂ f s t
  proof: coe_injective by
    push_cast
    exact Set.iUnion_image_left _

中文:
定理 biUnion_image_left
  结论: (s.biUnion fun a => t.image <| f a) = image₂ f s t
  证明: coe_injective by
    push_cast
    exact Set.iUnion_image_left _

Depends on / 依赖: Set.iUnion_image_left, coe_injective, iUnion_image_left
-/
theorem biUnion_image_left : (s.biUnion fun a => t.image <| f a) = image₂ f s t :=
coe_injective by
    push_cast
    exact Set.iUnion_image_left _

/--
theorem `biUnion_image_right` / 定理 `biUnion_image_right`

English:
theorem biUnion_image_right
  statement: (t.biUnion fun b => s.image fun a => f a b) = image₂ f s t
  proof: coe_injective by
    push_cast
    exact Set.iUnion_image_right _

中文:
定理 biUnion_image_right
  结论: (t.biUnion fun b => s.image fun a => f a b) = image₂ f s t
  证明: coe_injective by
    push_cast
    exact Set.iUnion_image_right _

Depends on / 依赖: Set.iUnion_image_right, coe_injective, iUnion_image_right
-/
theorem biUnion_image_right : (t.biUnion fun b => s.image fun a => f a b) = image₂ f s t :=
coe_injective by
    push_cast
    exact Set.iUnion_image_right _

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Finset.image₂` of those operations.

The proof pattern is `image₂_lemma operation_lemma`. For example, `image₂_comm mul_comm` proves that
`image₂ (*) f g = image₂ (*) g f` in a `CommSemigroup`.
-/

section
variable [DecidableEq δ]

/--
theorem `image_image₂` / 定理 `image_image₂`

English:
theorem image_image₂
  given: (f : α -> β -> γ) (g : γ -> δ)
  proof: coe_injective by
    push_cast
    exact image_image2 _ _

中文:
定理 image_image₂
  条件: (f : α -> β -> γ) (g : γ -> δ)
  证明: coe_injective by
    push_cast
    exact image_image2 _ _

Depends on / 依赖: coe_injective, image_image2
-/
theorem image_image₂ (f : α -> β -> γ) (g : γ -> δ) :
    (image₂ f s t).image g = image₂ (fun a b => g (f a b)) s t :=
coe_injective by
    push_cast
    exact image_image2 _ _

/--
theorem `image₂_image_left` / 定理 `image₂_image_left`

English:
theorem image₂_image_left
  given: (f : γ -> β -> δ) (g : α -> γ)
  proof: coe_injective by
    push_cast
    exact image2_image_left _ _

中文:
定理 image₂_image_left
  条件: (f : γ -> β -> δ) (g : α -> γ)
  证明: coe_injective by
    push_cast
    exact image2_image_left _ _

Depends on / 依赖: coe_injective, image2_image_left
-/
theorem image₂_image_left (f : γ -> β -> δ) (g : α -> γ) :
    image₂ f (s.image g) t = image₂ (fun a b => f (g a) b) s t :=
coe_injective by
    push_cast
    exact image2_image_left _ _

/--
theorem `image₂_image_right` / 定理 `image₂_image_right`

English:
theorem image₂_image_right
  given: (f : α -> γ -> δ) (g : β -> γ)
  proof: coe_injective by
    push_cast
    exact image2_image_right _ _

@[simp]

中文:
定理 image₂_image_right
  条件: (f : α -> γ -> δ) (g : β -> γ)
  证明: coe_injective by
    push_cast
    exact image2_image_right _ _

@[simp]

Depends on / 依赖: coe_injective, image2_image_right
-/
theorem image₂_image_right (f : α -> γ -> δ) (g : β -> γ) :
    image₂ f s (t.image g) = image₂ (fun a b => f a (g b)) s t :=
coe_injective by
    push_cast
    exact image2_image_right _ _

@[simp]
/--
theorem `image₂_mk_eq_product` / 定理 `image₂_mk_eq_product`

English:
theorem image₂_mk_eq_product
  given: [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β)
  proof: by ext; simp [Prod.ext_iff]

@[simp]

中文:
定理 image₂_mk_eq_product
  条件: [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β)
  证明: by ext; simp [Prod.ext_iff]

@[simp]

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
theorem image₂_mk_eq_product [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    image₂ Prod.mk s t = s ×ˢ t := by ext; simp [Prod.ext_iff]

@[simp]
/--
theorem `image₂_curry` / 定理 `image₂_curry`

English:
theorem image₂_curry
  given: (f : α × β -> γ) (s : Finset α) (t : Finset β)
  proof: rfl

@[simp]

中文:
定理 image₂_curry
  条件: (f : α × β -> γ) (s : Finset α) (t : Finset β)
  证明: rfl

@[simp]
-/
theorem image₂_curry (f : α × β -> γ) (s : Finset α) (t : Finset β) :
    image₂ (curry f) s t = (s ×ˢ t).image f := rfl

@[simp]
/--
theorem `image_uncurry_product` / 定理 `image_uncurry_product`

English:
theorem image_uncurry_product
  given: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  proof: rfl

中文:
定理 image_uncurry_product
  条件: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  证明: rfl
-/
theorem image_uncurry_product (f : α -> β -> γ) (s : Finset α) (t : Finset β) :
    (s ×ˢ t).image (uncurry f) = image₂ f s t := rfl

/--
theorem `image₂_swap` / 定理 `image₂_swap`

English:
theorem image₂_swap
  given: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  proof: coe_injective by
    push_cast
    exact image2_swap _ _ _

@[simp]

中文:
定理 image₂_swap
  条件: (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  证明: coe_injective by
    push_cast
    exact image2_swap _ _ _

@[simp]

Depends on / 依赖: coe_injective, image2_swap
-/
theorem image₂_swap (f : α -> β -> γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = image₂ (fun a b => f b a) t s :=
coe_injective by
    push_cast
    exact image2_swap _ _ _

@[simp]
/--
theorem `image₂_left` / 定理 `image₂_left`

English:
theorem image₂_left
  given: [DecidableEq α] (h : t.Nonempty)
  statement: image₂ (fun x _ => x) s t = s
  proof: coe_injective by
    push_cast
    exact image2_left h

@[simp]

中文:
定理 image₂_left
  条件: [DecidableEq α] (h : t.Nonempty)
  结论: image₂ (fun x _ => x) s t = s
  证明: coe_injective by
    push_cast
    exact image2_left h

@[simp]

Depends on / 依赖: coe_injective, image2_left
-/
theorem image₂_left [DecidableEq α] (h : t.Nonempty) : image₂ (fun x _ => x) s t = s :=
coe_injective by
    push_cast
    exact image2_left h

@[simp]
/--
theorem `image₂_right` / 定理 `image₂_right`

English:
theorem image₂_right
  given: [DecidableEq β] (h : s.Nonempty)
  statement: image₂ (fun _ y => y) s t = t
  proof: coe_injective by
    push_cast
    exact image2_right h

中文:
定理 image₂_right
  条件: [DecidableEq β] (h : s.Nonempty)
  结论: image₂ (fun _ y => y) s t = t
  证明: coe_injective by
    push_cast
    exact image2_right h

Depends on / 依赖: coe_injective, image2_right
-/
theorem image₂_right [DecidableEq β] (h : s.Nonempty) : image₂ (fun _ y => y) s t = t :=
coe_injective by
    push_cast
    exact image2_right h

/--
theorem `image₂_assoc` / 定理 `image₂_assoc`

English:
theorem image₂_assoc
  statement: {γ : Type*} {u : Finset γ}
  proof: coe_injective by
    push_cast
    exact image2_assoc h_assoc

中文:
定理 image₂_assoc
  结论: {γ : 类型} {u : Finset γ}
  证明: coe_injective by
    push_cast
    exact image2_assoc h_assoc

Depends on / 依赖: coe_injective, h_assoc, image2_assoc
-/
theorem image₂_assoc {γ : Type*} {u : Finset γ}
    {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε}
    {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (g' b c)) :
    image₂ f (image₂ g s t) u = image₂ f' s (image₂ g' t u) :=
coe_injective by
    push_cast
    exact image2_assoc h_assoc

/--
theorem `image₂_comm` / 定理 `image₂_comm`

English:
theorem image₂_comm
  given: {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a)
  statement: image₂ f s t = image₂ g t s
  proof: (image₂_swap _ _ _).trans by simp_rw [h_comm]

中文:
定理 image₂_comm
  条件: {g : β -> α -> γ} (h_comm : 对任意 a b, f a b = g b a)
  结论: image₂ f s t = image₂ g t s
  证明: (image₂_swap _ _ _).trans by simp_rw [h_comm]

Depends on / 依赖: h_comm, simp_rw
-/
theorem image₂_comm {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a) : image₂ f s t = image₂ g t s :=
(image₂_swap _ _ _).trans by simp_rw [h_comm]

/--
theorem `image₂_left_comm` / 定理 `image₂_left_comm`

English:
theorem image₂_left_comm
  statement: {γ : Type*} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ}
  proof: coe_injective by
    push_cast
    exact image2_left_comm h_left_comm

中文:
定理 image₂_left_comm
  结论: {γ : 类型} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ}
  证明: coe_injective by
    push_cast
    exact image2_left_comm h_left_comm

Depends on / 依赖: coe_injective, h_left_comm, image2_left_comm
-/
theorem image₂_left_comm {γ : Type*} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ}
    {f' : α -> γ -> δ'} {g' : β -> δ' -> ε} (h_left_comm : forall a b c, f a (g b c) = g' b (f' a c)) :
    image₂ f s (image₂ g t u) = image₂ g' t (image₂ f' s u) :=
coe_injective by
    push_cast
    exact image2_left_comm h_left_comm

/--
theorem `image₂_right_comm` / 定理 `image₂_right_comm`

English:
theorem image₂_right_comm
  statement: {γ : Type*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ}
  proof: coe_injective by
    push_cast
    exact image2_right_comm h_right_comm

中文:
定理 image₂_right_comm
  结论: {γ : 类型} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ}
  证明: coe_injective by
    push_cast
    exact image2_right_comm h_right_comm

Depends on / 依赖: coe_injective, h_right_comm, image2_right_comm
-/
theorem image₂_right_comm {γ : Type*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ}
    {f' : α -> γ -> δ'} {g' : δ' -> β -> ε} (h_right_comm : forall a b c, f (g a b) c = g' (f' a c) b) :
    image₂ f (image₂ g s t) u = image₂ g' (image₂ f' s u) t :=
coe_injective by
    push_cast
    exact image2_right_comm h_right_comm

/--
theorem `image₂_image₂_image₂_comm` / 定理 `image₂_image₂_image₂_comm`

English:
theorem image₂_image₂_image₂_comm
  statement: {γ δ : Type*} {u : Finset γ} {v : Finset δ} [DecidableEq ζ]
  proof: coe_injective by
    push_cast
    exact image2_image2_image2_comm h_comm

中文:
定理 image₂_image₂_image₂_comm
  结论: {γ δ : 类型} {u : Finset γ} {v : Finset δ} [DecidableEq ζ]
  证明: coe_injective by
    push_cast
    exact image2_image2_image2_comm h_comm

Depends on / 依赖: coe_injective, h_comm, image2_image2_image2_comm
-/
theorem image₂_image₂_image₂_comm {γ δ : Type*} {u : Finset γ} {v : Finset δ} [DecidableEq ζ]
    [DecidableEq ζ'] [DecidableEq ν] {f : ε -> ζ -> ν} {g : α -> β -> ε} {h : γ -> δ -> ζ}
    {f' : ε' -> ζ' -> ν} {g' : α -> γ -> ε'} {h' : β -> δ -> ζ'}
    (h_comm : forall a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image₂ f (image₂ g s t) (image₂ h u v) = image₂ f' (image₂ g' s u) (image₂ h' t v) :=
coe_injective by
    push_cast
    exact image2_image2_image2_comm h_comm

/--
theorem `image_image₂_distrib` / 定理 `image_image₂_distrib`

English:
theorem image_image₂_distrib
  statement: {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
  proof: coe_injective by
    push_cast
    exact image_image2_distrib h_distrib

中文:
定理 image_image₂_distrib
  结论: {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
  证明: coe_injective by
    push_cast
    exact image_image2_distrib h_distrib

Depends on / 依赖: coe_injective, h_distrib, image_image2_distrib
-/
theorem image_image₂_distrib {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
    (h_distrib : forall a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image₂ f s t).image g = image₂ f' (s.image g₁) (t.image g₂) :=
coe_injective by
    push_cast
    exact image_image2_distrib h_distrib

/--
theorem `image_image₂_distrib_left` / 定理 `image_image₂_distrib_left`

English:
theorem image_image₂_distrib_left
  statement: {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
  proof: coe_injective by
    push_cast
    exact image_image2_distrib_left h_distrib

中文:
定理 image_image₂_distrib_left
  结论: {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
  证明: coe_injective by
    push_cast
    exact image_image2_distrib_left h_distrib

Depends on / 依赖: coe_injective, h_distrib, image_image2_distrib_left
-/
theorem image_image₂_distrib_left {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
    (h_distrib : forall a b, g (f a b) = f' (g' a) b) :
    (image₂ f s t).image g = image₂ f' (s.image g') t :=
coe_injective by
    push_cast
    exact image_image2_distrib_left h_distrib

/--
theorem `image_image₂_distrib_right` / 定理 `image_image₂_distrib_right`

English:
theorem image_image₂_distrib_right
  statement: {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
  proof: coe_injective by
    push_cast
    exact image_image2_distrib_right h_distrib

中文:
定理 image_image₂_distrib_right
  结论: {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
  证明: coe_injective by
    push_cast
    exact image_image2_distrib_right h_distrib

Depends on / 依赖: coe_injective, h_distrib, image_image2_distrib_right
-/
theorem image_image₂_distrib_right {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
    (h_distrib : forall a b, g (f a b) = f' a (g' b)) :
    (image₂ f s t).image g = image₂ f' s (t.image g') :=
coe_injective by
    push_cast
    exact image_image2_distrib_right h_distrib

/--
theorem `image₂_image_left_comm` / 定理 `image₂_image_left_comm`

English:
theorem image₂_image_left_comm
  statement: {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
  proof: (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm

中文:
定理 image₂_image_left_comm
  结论: {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
  证明: (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm

Depends on / 依赖: h_left_comm
-/
theorem image₂_image_left_comm {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
    (h_left_comm : forall a b, f (g a) b = g' (f' a b)) :
    image₂ f (s.image g) t = (image₂ f' s t).image g' :=
  (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm

/--
theorem `image_image₂_right_comm` / 定理 `image_image₂_right_comm`

English:
theorem image_image₂_right_comm
  statement: {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
  proof: (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm

中文:
定理 image_image₂_right_comm
  结论: {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
  证明: (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm

Depends on / 依赖: h_right_comm
-/
theorem image_image₂_right_comm {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
    (h_right_comm : forall a b, f a (g b) = g' (f' a b)) :
    image₂ f s (t.image g) = (image₂ f' s t).image g' :=
  (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm

/--
theorem `image₂_distrib_subset_left` / 定理 `image₂_distrib_subset_left`

English:
theorem image₂_distrib_subset_left
  statement: {γ : Type*} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ}
  proof: coe_subset.1 by
    push_cast
    exact Set.image2_distrib_subset_left h_distrib

中文:
定理 image₂_distrib_subset_left
  结论: {γ : 类型} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ}
  证明: coe_subset.1 by
    push_cast
    exact Set.image2_distrib_subset_left h_distrib

Depends on / 依赖: Set.image2_distrib_subset_left, coe_subset, h_distrib, image2_distrib_subset_left
-/
theorem image₂_distrib_subset_left {γ : Type*} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ}
    {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε}
    (h_distrib : forall a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image₂ f s (image₂ g t u) subseteq image₂ g' (image₂ f₁ s t) (image₂ f₂ s u) :=
coe_subset.1 by
    push_cast
    exact Set.image2_distrib_subset_left h_distrib

/--
theorem `image₂_distrib_subset_right` / 定理 `image₂_distrib_subset_right`

English:
theorem image₂_distrib_subset_right
  statement: {γ : Type*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ}
  proof: coe_subset.1 by
    push_cast
    exact Set.image2_distrib_subset_right h_distrib

中文:
定理 image₂_distrib_subset_right
  结论: {γ : 类型} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ}
  证明: coe_subset.1 by
    push_cast
    exact Set.image2_distrib_subset_right h_distrib

Depends on / 依赖: Set.image2_distrib_subset_right, coe_subset, h_distrib, image2_distrib_subset_right
-/
theorem image₂_distrib_subset_right {γ : Type*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ}
    {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε}
    (h_distrib : forall a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image₂ f (image₂ g s t) u subseteq image₂ g' (image₂ f₁ s u) (image₂ f₂ t u) :=
coe_subset.1 by
    push_cast
    exact Set.image2_distrib_subset_right h_distrib

/--
theorem `image_image₂_antidistrib` / 定理 `image_image₂_antidistrib`

English:
theorem image_image₂_antidistrib
  statement: {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
  proof: by
  rw [image₂_swap f]
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _

中文:
定理 image_image₂_antidistrib
  结论: {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
  证明: by
  rw [image₂_swap f]
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _

Depends on / 依赖: h_antidistrib
-/
theorem image_image₂_antidistrib {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
    (h_antidistrib : forall a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image₂ f s t).image g = image₂ f' (t.image g₁) (s.image g₂) := by
  rw [image₂_swap f]
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _

/--
theorem `image_image₂_antidistrib_left` / 定理 `image_image₂_antidistrib_left`

English:
theorem image_image₂_antidistrib_left
  statement: {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
  proof: coe_injective by
    push_cast
    exact image_image2_antidistrib_left h_antidistrib

中文:
定理 image_image₂_antidistrib_left
  结论: {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
  证明: coe_injective by
    push_cast
    exact image_image2_antidistrib_left h_antidistrib

Depends on / 依赖: coe_injective, h_antidistrib, image_image2_antidistrib_left
-/
theorem image_image₂_antidistrib_left {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
    (h_antidistrib : forall a b, g (f a b) = f' (g' b) a) :
    (image₂ f s t).image g = image₂ f' (t.image g') s :=
coe_injective by
    push_cast
    exact image_image2_antidistrib_left h_antidistrib

/--
theorem `image_image₂_antidistrib_right` / 定理 `image_image₂_antidistrib_right`

English:
theorem image_image₂_antidistrib_right
  statement: {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
  proof: coe_injective by
    push_cast
    exact image_image2_antidistrib_right h_antidistrib

中文:
定理 image_image₂_antidistrib_right
  结论: {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
  证明: coe_injective by
    push_cast
    exact image_image2_antidistrib_right h_antidistrib

Depends on / 依赖: coe_injective, h_antidistrib, image_image2_antidistrib_right
-/
theorem image_image₂_antidistrib_right {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
    (h_antidistrib : forall a b, g (f a b) = f' b (g' a)) :
    (image₂ f s t).image g = image₂ f' t (s.image g') :=
coe_injective by
    push_cast
    exact image_image2_antidistrib_right h_antidistrib

/--
theorem `image₂_image_left_anticomm` / 定理 `image₂_image_left_anticomm`

English:
theorem image₂_image_left_anticomm
  statement: {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
  proof: (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

中文:
定理 image₂_image_left_anticomm
  结论: {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
  证明: (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

Depends on / 依赖: h_left_anticomm
-/
theorem image₂_image_left_anticomm {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
    (h_left_anticomm : forall a b, f (g a) b = g' (f' b a)) :
    image₂ f (s.image g) t = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/--
theorem `image_image₂_right_anticomm` / 定理 `image_image₂_right_anticomm`

English:
theorem image_image₂_right_anticomm
  statement: {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
  proof: (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

中文:
定理 image_image₂_right_anticomm
  结论: {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
  证明: (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

Depends on / 依赖: h_right_anticomm
-/
theorem image_image₂_right_anticomm {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
    (h_right_anticomm : forall a b, f a (g b) = g' (f' b a)) :
    image₂ f s (t.image g) = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/--
theorem `image₂_left_identity` / 定理 `image₂_left_identity`

English:
theorem image₂_left_identity
  given: {f : α -> γ -> γ} {a : α} (h : forall b, f a b = b) (t : Finset γ)
  proof: coe_injective by rw [coe_image₂, coe_singleton, Set.image2_left_identity h]

中文:
定理 image₂_left_identity
  条件: {f : α -> γ -> γ} {a : α} (h : 对任意 b, f a b = b) (t : Finset γ)
  证明: coe_injective by rw [coe_image₂, coe_singleton, Set.image2_left_identity h]

Depends on / 依赖: Set.image2_left_identity, coe_injective, coe_singleton, image2_left_identity
-/
theorem image₂_left_identity {f : α -> γ -> γ} {a : α} (h : forall b, f a b = b) (t : Finset γ) :
    image₂ f {a} t = t :=
coe_injective by rw [coe_image₂, coe_singleton, Set.image2_left_identity h]

/--
theorem `image₂_right_identity` / 定理 `image₂_right_identity`

English:
theorem image₂_right_identity
  given: {f : γ -> β -> γ} {b : β} (h : forall a, f a b = a) (s : Finset γ)
  proof: by rw [image₂_singleton_right, funext h, image_id']

中文:
定理 image₂_right_identity
  条件: {f : γ -> β -> γ} {b : β} (h : 对任意 a, f a b = a) (s : Finset γ)
  证明: by rw [image₂_singleton_right, funext h, image_id']

Depends on / 依赖: image_id
-/
theorem image₂_right_identity {f : γ -> β -> γ} {b : β} (h : forall a, f a b = a) (s : Finset γ) :
    image₂ f s {b} = s := by rw [image₂_singleton_right, funext h, image_id']

/--
theorem `card_dvd_card_image₂_right` / 定理 `card_dvd_card_image₂_right`

English:
theorem card_dvd_card_image₂_right
  statement: (hf : forall a in s, Injective (f a))
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s _ ih => ?_
  specialize ih (forall_of_forall_insert hf)
    (hs.subset <| Set.image_mono <| coe_subset.2 <| subset_insert _ _)
  rw [image₂_insert_left]
  by_cases h : Disjoint (image (f a) t) (image₂ f s t)
  

中文:
定理 card_dvd_card_image₂_right
  结论: (hf : 对任意 a in s, Injective (f a))
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s _ ih => ?_
  specialize ih (forall_of_forall_insert hf)
    (hs.subset <| Set.image_mono <| coe_subset.2 <| subset_insert _ _)
  rw [image₂_insert_left]
  by_cases h : Disjoint (image (f a) t) (image₂ f s t)
  

Depends on / 依赖: Disjoint, Finset, Finset.induction, Nat.dvd_add, Set.image_mono, biUnion_image_left, card_image_of_injective, card_union_of_disjoint, classical, coe_subset, disjoint_biUnion_right, dvd_add, forall_of_forall_insert, hs.subset, image_mono, insert, mem_insert_self, not_forall, simp_rw, specialize
-/
theorem card_dvd_card_image₂_right (hf : forall a in s, Injective (f a))
    (hs : ((fun a => t.image <| f a) '' s).PairwiseDisjoint id) : #t ∣ #(image₂ f s t) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s _ ih => ?_
  specialize ih (forall_of_forall_insert hf)
    (hs.subset <| Set.image_mono <| coe_subset.2 <| subset_insert _ _)
  rw [image₂_insert_left]
  by_cases h : Disjoint (image (f a) t) (image₂ f s t)
  · rw [card_union_of_disjoint h]
    exact Nat.dvd_add (card_image_of_injective _ <| hf _ <| mem_insert_self _ _).symm.dvd ih
  simp_rw [← biUnion_image_left, disjoint_biUnion_right, not_forall] at h
  obtain ⟨b, hb, h⟩ := h
  rwa [union_eq_right.2]
  exact (hs.eq (Set.mem_image_of_mem _ <| mem_insert_self _ _)
      (Set.mem_image_of_mem _ <| mem_insert_of_mem hb) h).trans_subset
    (image_subset_image₂_right hb)

/--
theorem `card_dvd_card_image₂_left` / 定理 `card_dvd_card_image₂_left`

English:
theorem card_dvd_card_image₂_left
  statement: (hf : forall b in t, Injective fun a => f a b)
  proof: by rw [← image₂_swap]; exact card_dvd_card_image₂_right hf ht

中文:
定理 card_dvd_card_image₂_left
  结论: (hf : 对任意 b in t, Injective fun a => f a b)
  证明: by rw [← image₂_swap]; exact card_dvd_card_image₂_right hf ht
-/
theorem card_dvd_card_image₂_left (hf : forall b in t, Injective fun a => f a b)
    (ht : ((fun b => s.image fun a => f a b) '' t).PairwiseDisjoint id) :
    #s ∣ #(image₂ f s t) := by rw [← image₂_swap]; exact card_dvd_card_image₂_right hf ht

/--
theorem `subset_set_image₂` / 定理 `subset_set_image₂`

English:
theorem subset_set_image₂
  given: {s : Set α} {t : Set β} (hu : ↑u subseteq image2 f s t)
  proof: by
  rw [← Set.image_prod]; rw [subset_set_image_iff] at hu
  rcases hu with ⟨u, hu, rfl⟩
  classical
  use u.image Prod.fst, u.image Prod.snd
  simp only [coe_image, Set.image_subset_iff, image₂_image_left, image₂_image_right,
    image_subset_iff]
  exact ⟨fun _ h => (hu h).1, fun _ h => (hu h).2,

中文:
定理 subset_set_image₂
  条件: {s : Set α} {t : Set β} (hu : ↑u subseteq image2 f s t)
  证明: by
  rw [← Set.image_prod]; rw [subset_set_image_iff] at hu
  rcases hu with ⟨u, hu, rfl⟩
  classical
  use u.image Prod.fst, u.image Prod.snd
  simp only [coe_image, Set.image_subset_iff, image₂_image_left, image₂_image_right,
    image_subset_iff]
  exact ⟨fun _ h => (hu h).1, fun _ h => (hu h).2,

Depends on / 依赖: Prod.fst, Prod.snd, Set.image_prod, Set.image_subset_iff, classical, coe_image, image_prod, image_subset_iff, subset_set_image_iff, u.image
-/
theorem subset_set_image₂ {s : Set α} {t : Set β} (hu : ↑u subseteq image2 f s t) :
    exists (s' : Finset α) (t' : Finset β), ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq image₂ f s' t' := by
  rw [← Set.image_prod]; rw [subset_set_image_iff] at hu
  rcases hu with ⟨u, hu, rfl⟩
  classical
  use u.image Prod.fst, u.image Prod.snd
  simp only [coe_image, Set.image_subset_iff, image₂_image_left, image₂_image_right,
    image_subset_iff]
  exact ⟨fun _ h => (hu h).1, fun _ h => (hu h).2, fun x hx => mem_image₂_of_mem hx hx⟩

end
section UnionInter

variable [DecidableEq α] [DecidableEq β]

/--
theorem `image₂_inter_union_subset_union` / 定理 `image₂_inter_union_subset_union`

English:
theorem image₂_inter_union_subset_union
  proof: coe_subset.1 by
    push_cast
    exact Set.image2_inter_union_subset_union

中文:
定理 image₂_inter_union_subset_union
  证明: coe_subset.1 by
    push_cast
    exact Set.image2_inter_union_subset_union

Depends on / 依赖: Set.image2_inter_union_subset_union, coe_subset, image2_inter_union_subset_union
-/
theorem image₂_inter_union_subset_union :
    image₂ f (s inter s') (t union t') subseteq image₂ f s t union image₂ f s' t' :=
coe_subset.1 by
    push_cast
    exact Set.image2_inter_union_subset_union

/--
theorem `image₂_union_inter_subset_union` / 定理 `image₂_union_inter_subset_union`

English:
theorem image₂_union_inter_subset_union
  proof: coe_subset.1 by
    push_cast
    exact Set.image2_union_inter_subset_union

中文:
定理 image₂_union_inter_subset_union
  证明: coe_subset.1 by
    push_cast
    exact Set.image2_union_inter_subset_union

Depends on / 依赖: Set.image2_union_inter_subset_union, coe_subset, image2_union_inter_subset_union
-/
theorem image₂_union_inter_subset_union :
    image₂ f (s union s') (t inter t') subseteq image₂ f s t union image₂ f s' t' :=
coe_subset.1 by
    push_cast
    exact Set.image2_union_inter_subset_union

/--
theorem `image₂_inter_union_subset` / 定理 `image₂_inter_union_subset`

English:
theorem image₂_inter_union_subset
  given: {f : α -> α -> β} {s t : Finset α} (hf : forall a b, f a b = f b a)
  proof: coe_subset.1 by
    push_cast
    exact image2_inter_union_subset hf

中文:
定理 image₂_inter_union_subset
  条件: {f : α -> α -> β} {s t : Finset α} (hf : 对任意 a b, f a b = f b a)
  证明: coe_subset.1 by
    push_cast
    exact image2_inter_union_subset hf

Depends on / 依赖: coe_subset, image2_inter_union_subset
-/
theorem image₂_inter_union_subset {f : α -> α -> β} {s t : Finset α} (hf : forall a b, f a b = f b a) :
    image₂ f (s inter t) (s union t) subseteq image₂ f s t :=
coe_subset.1 by
    push_cast
    exact image2_inter_union_subset hf

/--
theorem `image₂_union_inter_subset` / 定理 `image₂_union_inter_subset`

English:
theorem image₂_union_inter_subset
  given: {f : α -> α -> β} {s t : Finset α} (hf : forall a b, f a b = f b a)
  proof: coe_subset.1 by
    push_cast
    exact image2_union_inter_subset hf

中文:
定理 image₂_union_inter_subset
  条件: {f : α -> α -> β} {s t : Finset α} (hf : 对任意 a b, f a b = f b a)
  证明: coe_subset.1 by
    push_cast
    exact image2_union_inter_subset hf

Depends on / 依赖: coe_subset, image2_union_inter_subset
-/
theorem image₂_union_inter_subset {f : α -> α -> β} {s t : Finset α} (hf : forall a b, f a b = f b a) :
    image₂ f (s union t) (s inter t) subseteq image₂ f s t :=
coe_subset.1 by
    push_cast
    exact image2_union_inter_subset hf

end UnionInter

section SemilatticeSup

variable [SemilatticeSup δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
/--
lemma `sup'_image₂_le` / 引理 `sup'_image₂_le`

English:
lemma sup'_image₂_le
  given: {g : γ -> δ} {a : δ} (h : (image₂ f s t).Nonempty)
  proof: by
  rw [sup'_le_iff]; rw [forall_mem_image₂]

中文:
引理 sup'_image₂_le
  条件: {g : γ -> δ} {a : δ} (h : (image₂ f s t).Nonempty)
  证明: by
  rw [sup'_le_iff]; rw [forall_mem_image₂]
-/
lemma sup'_image₂_le {g : γ -> δ} {a : δ} (h : (image₂ f s t).Nonempty) :
    sup' (image₂ f s t) h g <= a ↔ forall x in s, forall y in t, g (f x y) <= a := by
  rw [sup'_le_iff]; rw [forall_mem_image₂]

/--
lemma `sup'_image₂_left` / 引理 `sup'_image₂_left`

English:
lemma sup'_image₂_left
  given: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  proof: by
  simp only [image₂, sup'_image, sup'_product_left]; rfl

中文:
引理 sup'_image₂_left
  条件: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  证明: by
  simp only [image₂, sup'_image, sup'_product_left]; rfl
-/
lemma sup'_image₂_left (g : γ -> δ) (h : (image₂ f s t).Nonempty) :
    sup' (image₂ f s t) h g =
      sup' s h.of_image₂_left fun x => sup' t h.of_image₂_right (g <| f x ·) := by
  simp only [image₂, sup'_image, sup'_product_left]; rfl

/--
lemma `sup'_image₂_right` / 引理 `sup'_image₂_right`

English:
lemma sup'_image₂_right
  given: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  proof: by
  simp only [image₂, sup'_image, sup'_product_right]; rfl

中文:
引理 sup'_image₂_right
  条件: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  证明: by
  simp only [image₂, sup'_image, sup'_product_right]; rfl
-/
lemma sup'_image₂_right (g : γ -> δ) (h : (image₂ f s t).Nonempty) :
    sup' (image₂ f s t) h g =
      sup' t h.of_image₂_right fun y => sup' s h.of_image₂_left (g <| f · y) := by
  simp only [image₂, sup'_image, sup'_product_right]; rfl

variable [OrderBot δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
/--
lemma `sup_image₂_le` / 引理 `sup_image₂_le`

English:
lemma sup_image₂_le
  given: {g : γ -> δ} {a : δ}
  proof: by
  rw [Finset.sup_le_iff]; rw [forall_mem_image₂]

中文:
引理 sup_image₂_le
  条件: {g : γ -> δ} {a : δ}
  证明: by
  rw [Finset.sup_le_iff]; rw [forall_mem_image₂]

Depends on / 依赖: Finset, Finset.sup_le_iff, sup_le_iff
-/
lemma sup_image₂_le {g : γ -> δ} {a : δ} :
    sup (image₂ f s t) g <= a ↔ forall x in s, forall y in t, g (f x y) <= a := by
  rw [Finset.sup_le_iff]; rw [forall_mem_image₂]

variable (s t)

/--
lemma `sup_image₂_left` / 引理 `sup_image₂_left`

English:
lemma sup_image₂_left
  given: (g : γ -> δ)
  statement: sup (image₂ f s t) g = sup s fun x => sup t (g <| f x ·)
  proof: by
  simp only [image₂, sup_image, sup_product_left]; rfl

中文:
引理 sup_image₂_left
  条件: (g : γ -> δ)
  结论: sup (image₂ f s t) g = sup s fun x => sup t (g <| f x ·)
  证明: by
  simp only [image₂, sup_image, sup_product_left]; rfl

Depends on / 依赖: sup_image, sup_product_left
-/
lemma sup_image₂_left (g : γ -> δ) : sup (image₂ f s t) g = sup s fun x => sup t (g <| f x ·) := by
  simp only [image₂, sup_image, sup_product_left]; rfl

/--
lemma `sup_image₂_right` / 引理 `sup_image₂_right`

English:
lemma sup_image₂_right
  given: (g : γ -> δ)
  statement: sup (image₂ f s t) g = sup t fun y => sup s (g <| f · y)
  proof: by
  simp only [image₂, sup_image, sup_product_right]; rfl

中文:
引理 sup_image₂_right
  条件: (g : γ -> δ)
  结论: sup (image₂ f s t) g = sup t fun y => sup s (g <| f · y)
  证明: by
  simp only [image₂, sup_image, sup_product_right]; rfl

Depends on / 依赖: sup_image, sup_product_right
-/
lemma sup_image₂_right (g : γ -> δ) : sup (image₂ f s t) g = sup t fun y => sup s (g <| f · y) := by
  simp only [image₂, sup_image, sup_product_right]; rfl

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
/--
lemma `le_inf'_image₂` / 引理 `le_inf'_image₂`

English:
lemma le_inf'_image₂
  given: {g : γ -> δ} {a : δ} (h : (image₂ f s t).Nonempty)
  proof: by
  rw [le_inf'_iff]; rw [forall_mem_image₂]

中文:
引理 le_inf'_image₂
  条件: {g : γ -> δ} {a : δ} (h : (image₂ f s t).Nonempty)
  证明: by
  rw [le_inf'_iff]; rw [forall_mem_image₂]

Depends on / 依赖: _iff, le_inf
-/
lemma le_inf'_image₂ {g : γ -> δ} {a : δ} (h : (image₂ f s t).Nonempty) :
    a <= inf' (image₂ f s t) h g ↔ forall x in s, forall y in t, a <= g (f x y) := by
  rw [le_inf'_iff]; rw [forall_mem_image₂]

/--
lemma `inf'_image₂_left` / 引理 `inf'_image₂_left`

English:
lemma inf'_image₂_left
  given: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  proof: sup'_image₂_left (δ := δᵒᵈ) g h

中文:
引理 inf'_image₂_left
  条件: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  证明: sup'_image₂_left (δ := δᵒᵈ) g h
-/
lemma inf'_image₂_left (g : γ -> δ) (h : (image₂ f s t).Nonempty) :
    inf' (image₂ f s t) h g =
      inf' s h.of_image₂_left fun x => inf' t h.of_image₂_right (g <| f x ·) :=
  sup'_image₂_left (δ := δᵒᵈ) g h

/--
lemma `inf'_image₂_right` / 引理 `inf'_image₂_right`

English:
lemma inf'_image₂_right
  given: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  proof: sup'_image₂_right (δ := δᵒᵈ) g h

中文:
引理 inf'_image₂_right
  条件: (g : γ -> δ) (h : (image₂ f s t).Nonempty)
  证明: sup'_image₂_right (δ := δᵒᵈ) g h
-/
lemma inf'_image₂_right (g : γ -> δ) (h : (image₂ f s t).Nonempty) :
    inf' (image₂ f s t) h g =
      inf' t h.of_image₂_right fun y => inf' s h.of_image₂_left (g <| f · y) :=
  sup'_image₂_right (δ := δᵒᵈ) g h

variable [OrderTop δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
/--
lemma `le_inf_image₂` / 引理 `le_inf_image₂`

English:
lemma le_inf_image₂
  given: {g : γ -> δ} {a : δ}
  proof: sup_image₂_le (δ := δᵒᵈ)

中文:
引理 le_inf_image₂
  条件: {g : γ -> δ} {a : δ}
  证明: sup_image₂_le (δ := δᵒᵈ)
-/
lemma le_inf_image₂ {g : γ -> δ} {a : δ} :
    a <= inf (image₂ f s t) g ↔ forall x in s, forall y in t, a <= g (f x y) :=
  sup_image₂_le (δ := δᵒᵈ)

variable (s t)

/--
lemma `inf_image₂_left` / 引理 `inf_image₂_left`

English:
lemma inf_image₂_left
  given: (g : γ -> δ)
  statement: inf (image₂ f s t) g = inf s fun x => inf t (g ∘ f x)
  proof: sup_image₂_left (δ := δᵒᵈ) ..

中文:
引理 inf_image₂_left
  条件: (g : γ -> δ)
  结论: inf (image₂ f s t) g = inf s fun x => inf t (g ∘ f x)
  证明: sup_image₂_left (δ := δᵒᵈ) ..
-/
lemma inf_image₂_left (g : γ -> δ) : inf (image₂ f s t) g = inf s fun x => inf t (g ∘ f x) :=
  sup_image₂_left (δ := δᵒᵈ) ..

/--
lemma `inf_image₂_right` / 引理 `inf_image₂_right`

English:
lemma inf_image₂_right
  given: (g : γ -> δ)
  statement: inf (image₂ f s t) g = inf t fun y => inf s (g <| f · y)
  proof: sup_image₂_right (δ := δᵒᵈ) ..

中文:
引理 inf_image₂_right
  条件: (g : γ -> δ)
  结论: inf (image₂ f s t) g = inf t fun y => inf s (g <| f · y)
  证明: sup_image₂_right (δ := δᵒᵈ) ..
-/
lemma inf_image₂_right (g : γ -> δ) : inf (image₂ f s t) g = inf t fun y => inf s (g <| f · y) :=
  sup_image₂_right (δ := δᵒᵈ) ..

end SemilatticeInf

end Finset

open Finset

namespace Fintype
variable {ι : Type*} {α β γ : ι -> Type*} [DecidableEq ι] [Fintype ι] [forall i, DecidableEq (γ i)]

/--
lemma `piFinset_image₂` / 引理 `piFinset_image₂`

English:
lemma piFinset_image₂
  given: (f : forall i, α i -> β i -> γ i) (s : forall i, Finset (α i)) (t : forall i, Finset (β i))
  proof: by
  ext; simp only [mem_piFinset, mem_image₂, Classical.skolem, forall_and, funext_iff]

中文:
引理 piFinset_image₂
  条件: (f : 对任意 i, α i -> β i -> γ i) (s : 对任意 i, Finset (α i)) (t : 对任意 i, Finset (β i))
  证明: by
  ext; simp only [mem_piFinset, mem_image₂, Classical.skolem, forall_and, funext_iff]

Depends on / 依赖: Classical, Classical.skolem, forall_and, funext_iff, mem_piFinset, skolem
-/
lemma piFinset_image₂ (f : forall i, α i -> β i -> γ i) (s : forall i, Finset (α i)) (t : forall i, Finset (β i)) :
    piFinset (fun i => image₂ (f i) (s i) (t i)) =
      image₂ (fun a b i => f _ (a i) (b i)) (piFinset s) (piFinset t) := by
  ext; simp only [mem_piFinset, mem_image₂, Classical.skolem, forall_and, funext_iff]

end Fintype

namespace Set

variable [DecidableEq γ] {s : Set α} {t : Set β}

@[simp]
/--
theorem `toFinset_image2` / 定理 `toFinset_image2`

English:
theorem toFinset_image2
  statement: (f : α -> β -> γ) (s : Set α) (t : Set β) [Fintype s] [Fintype t]
  proof: Finset.coe_injective by simp

中文:
定理 toFinset_image2
  结论: (f : α -> β -> γ) (s : Set α) (t : Set β) [Fintype s] [Fintype t]
  证明: Finset.coe_injective by simp

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem toFinset_image2 (f : α -> β -> γ) (s : Set α) (t : Set β) [Fintype s] [Fintype t]
    [Fintype (image2 f s t)] : (image2 f s t).toFinset = Finset.image₂ f s.toFinset t.toFinset :=
Finset.coe_injective by simp

/--
theorem `Finite.toFinset_image2` / 定理 `Finite.toFinset_image2`

English:
theorem Finite.toFinset_image2
  statement: (f : α -> β -> γ) (hs : s.Finite) (ht : t.Finite)
  proof: Finset.coe_injective by simp

中文:
定理 Finite.toFinset_image2
  结论: (f : α -> β -> γ) (hs : s.Finite) (ht : t.Finite)
  证明: Finset.coe_injective by simp

Depends on / 依赖: Finset, Finset.image, hf.toFinset, hs.image2, hs.toFinset, ht.toFinset, image2, toFinset
-/
theorem Finite.toFinset_image2 (f : α -> β -> γ) (hs : s.Finite) (ht : t.Finite)
    (hf := hs.image2 f ht) : hf.toFinset = Finset.image₂ f hs.toFinset ht.toFinset :=
Finset.coe_injective by simp

end Set
