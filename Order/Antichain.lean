/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.Adj` for `G : SimpleGraph α`, this corresponds to independent sets of `G`.

## Definitions

* `IsAntichain r s`: Any two elements of `s : Set α` are unrelated by `r : α → α → Prop`.
* `IsStrongAntichain r s`: Any two elements of `s : Set α` are not related by `r : α → α → Prop`
  to a common element.
* `IsMaxAntichain r s`: An antichain such that no antichain strictly including `s` exists.
-/

@[expose] public section

assert_not_exists CompleteLattice

open Function Set Set.Notation

section General

variable {α β : Type*} {r r₁ r₂ : α -> α -> Prop} {r' : β -> β -> Prop} {s t : Set α} {a b : α}

/--
Instance `Std.Symm.compl` / 实例 `Std.Symm.compl`

English:
instance Std.Symm.compl
  signature: [Std.Symm r]
  body: hr symm b a hr'

@[deprecated (since := "2026-06-10")] alias Symmetric.compl := Std.Symm.compl

中文:
实例 Std.Symm.compl
  签名: [Std.Symm r]
  定义体: hr symm b a hr'

@[deprecated (since := "2026-06-10")] alias Symmetric.compl := Std.Symm.compl
-/
protected instance Std.Symm.compl [Std.Symm r] : Std.Symm rᶜ where
symm a b hr hr' := hr symm b a hr'

@[deprecated (since := "2026-06-10")] alias Symmetric.compl := Std.Symm.compl

/--
Definition of `IsAntichain` / `IsAntichain` 的定义

English:
definition IsAntichain
  signature: (r : α -> α -> Prop) (s : Set α)
  body: s.Pairwise rᶜ

中文:
定义 IsAntichain
  签名: (r : α -> α -> 命题) (s : 集合 α)
  定义体: s.Pairwise rᶜ

Depends on / 依赖: Pairwise, s.Pairwise
-/
def IsAntichain (r : α -> α -> Prop) (s : Set α) : Prop :=
  s.Pairwise rᶜ

namespace IsAntichain

/--
theorem `empty` / 定理 `empty`

English:
theorem empty
  statement: IsAntichain r ∅
  proof: pairwise_empty _

中文:
定理 empty
  结论: IsAntichain r ∅
  证明: pairwise_empty _
-/
@[simp] protected theorem empty : IsAntichain r ∅ :=
  pairwise_empty _

/--
theorem `singleton` / 定理 `singleton`

English:
theorem singleton
  statement: IsAntichain r {a}
  proof: pairwise_singleton _ _

中文:
定理 singleton
  结论: IsAntichain r {a}
  证明: pairwise_singleton _ _
-/
@[simp] protected theorem singleton : IsAntichain r {a} :=
  pairwise_singleton _ _

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (hs : IsAntichain r s) (h : t subseteq s)
  statement: IsAntichain r t
  proof: hs.mono h

中文:
定理 subset
  条件: (hs : IsAntichain r s) (h : t subseteq s)
  结论: IsAntichain r t
  证明: hs.mono h
-/
protected theorem subset (hs : IsAntichain r s) (h : t subseteq s) : IsAntichain r t :=
  hs.mono h

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hs : IsAntichain r₁ s) (h : r₂ <= r₁)
  statement: IsAntichain r₂ s
  proof: hs.mono' compl_le_compl h

中文:
定理 mono
  条件: (hs : IsAntichain r₁ s) (h : r₂ <= r₁)
  结论: IsAntichain r₂ s
  证明: hs.mono' compl_le_compl h

Depends on / 依赖: compl_le_compl, hs.mono
-/
theorem mono (hs : IsAntichain r₁ s) (h : r₂ <= r₁) : IsAntichain r₂ s :=
hs.mono' compl_le_compl h

/--
theorem `mono_on` / 定理 `mono_on`

English:
theorem mono_on
  given: (hs : IsAntichain r₁ s) (h : s.Pairwise fun ⦃a b⦄ => r₂ a b -> r₁ a b)
  proof: hs.imp_on h.imp fun _ _ h h₁ h₂ => h₁ h h₂

中文:
定理 mono_on
  条件: (hs : IsAntichain r₁ s) (h : s.两两 fun ⦃a b⦄ => r₂ a b -> r₁ a b)
  证明: hs.imp_on h.imp fun _ _ h h₁ h₂ => h₁ h h₂

Depends on / 依赖: h.imp, hs.imp_on, imp_on
-/
theorem mono_on (hs : IsAntichain r₁ s) (h : s.Pairwise fun ⦃a b⦄ => r₂ a b -> r₁ a b) :
    IsAntichain r₂ s :=
hs.imp_on h.imp fun _ _ h h₁ h₂ => h₁ h h₂

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (hs : IsAntichain r s) {a b : α} (ha : a in s) (hb : b in s) (h : r a b)
  proof: Set.Pairwise.eq hs ha hb not_not_intro h

中文:
定理 eq
  条件: (hs : IsAntichain r s) {a b : α} (ha : a in s) (hb : b in s) (h : r a b)
  证明: Set.Pairwise.eq hs ha hb not_not_intro h
-/
protected theorem eq (hs : IsAntichain r s) {a b : α} (ha : a in s) (hb : b in s) (h : r a b) :
    a = b :=
Set.Pairwise.eq hs ha hb not_not_intro h

/--
theorem `eq'` / 定理 `eq'`

English:
theorem eq'
  given: (hs : IsAntichain r s) {a b : α} (ha : a in s) (hb : b in s) (h : r b a)
  proof: (hs.eq hb ha h).symm

中文:
定理 eq'
  条件: (hs : IsAntichain r s) {a b : α} (ha : a in s) (hb : b in s) (h : r b a)
  证明: (hs.eq hb ha h).symm
-/
protected theorem eq' (hs : IsAntichain r s) {a b : α} (ha : a in s) (hb : b in s) (h : r b a) :
    a = b :=
  (hs.eq hb ha h).symm

/--
theorem `antisymm` / 定理 `antisymm`

English:
theorem antisymm
  given: (h : IsAntichain r univ)
  statement: Std.Antisymm r
  proof: ⟨fun _ _ ha _ => h.eq trivial trivial ha⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := antisymm

中文:
定理 antisymm
  条件: (h : IsAntichain r univ)
  结论: Std.反对称 r
  证明: ⟨fun _ _ ha _ => h.eq trivial trivial ha⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := antisymm
-/
protected theorem antisymm (h : IsAntichain r univ) : Std.Antisymm r :=
  ⟨fun _ _ ha _ => h.eq trivial trivial ha⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := antisymm

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: [Std.Trichotomous r] (h : IsAntichain r s)
  statement: s.Subsingleton
  proof: by
  rintro a ha b hb
  obtain hab | hab | hab := trichotomous_of r a b
  · exact h.eq ha hb hab
  · exact hab
  · exact h.eq' ha hb hab

中文:
定理 subsingleton
  条件: [Std.三歧 r] (h : IsAntichain r s)
  结论: s.子单例
  证明: by
  rintro a ha b hb
  obtain hab | hab | hab := trichotomous_of r a b
  · exact h.eq ha hb hab
  · exact hab
  · exact h.eq' ha hb hab
-/
protected theorem subsingleton [Std.Trichotomous r] (h : IsAntichain r s) : s.Subsingleton := by
  rintro a ha b hb
  obtain hab | hab | hab := trichotomous_of r a b
  · exact h.eq ha hb hab
  · exact hab
  · exact h.eq' ha hb hab

/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: (hs : IsAntichain r s)
  statement: IsAntichain (flip r) s
  proof: fun _ ha _ hb h =>
  hs hb ha h.symm

中文:
定理 flip
  条件: (hs : IsAntichain r s)
  结论: IsAntichain (flip r) s
  证明: fun _ ha _ hb h =>
  hs hb ha h.symm
-/
protected theorem flip (hs : IsAntichain r s) : IsAntichain (flip r) s := fun _ ha _ hb h =>
  hs hb ha h.symm

/--
theorem `swap` / 定理 `swap`

English:
theorem swap
  given: (hs : IsAntichain r s)
  statement: IsAntichain (swap r) s
  proof: hs.flip

中文:
定理 swap
  条件: (hs : IsAntichain r s)
  结论: IsAntichain (swap r) s
  证明: hs.flip

Depends on / 依赖: hs.flip
-/
theorem swap (hs : IsAntichain r s) : IsAntichain (swap r) s :=
  hs.flip

/--
theorem `image` / 定理 `image`

English:
theorem image
  given: (hs : IsAntichain r s) (f : α -> β) (h : forall ⦃a b⦄, r' (f a) (f b) -> r a b)
  proof: by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr)

中文:
定理 像
  条件: (hs : IsAntichain r s) (f : α -> β) (h : 对任意 ⦃a b⦄, r' (f a) (f b) -> r a b)
  证明: by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr)

Depends on / 依赖: ne_of_apply_ne
-/
theorem image (hs : IsAntichain r s) (f : α -> β) (h : forall ⦃a b⦄, r' (f a) (f b) -> r a b) :
    IsAntichain r' (f '' s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr)

/--
theorem `preimage` / 定理 `preimage`

English:
theorem preimage
  statement: (hs : IsAntichain r s) {f : β -> α} (hf : Injective f)
  proof: fun _ hb _ hc hbc hr =>
hs hb hc (hf.ne hbc) h hr

中文:
定理 原像
  结论: (hs : IsAntichain r s) {f : β -> α} (hf : 单射 f)
  证明: fun _ hb _ hc hbc hr =>
hs hb hc (hf.ne hbc) h hr
-/
theorem preimage (hs : IsAntichain r s) {f : β -> α} (hf : Injective f)
    (h : forall ⦃a b⦄, r' a b -> r (f a) (f b)) : IsAntichain r' (f ⁻¹' s) := fun _ hb _ hc hbc hr =>
hs hb hc (hf.ne hbc) h hr

/--
theorem `_root_.isAntichain_insert` / 定理 `_root_.isAntichain_insert`

English:
theorem _root_.isAntichain_insert
  proof: Set.pairwise_insert

中文:
定理 _root_.isAntichain_insert
  证明: Set.pairwise_insert

Depends on / 依赖: Set.pairwise_insert, pairwise_insert
-/
theorem _root_.isAntichain_insert :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ forall ⦃b⦄, b in s -> a != b -> ¬r a b ∧ ¬r b a :=
  Set.pairwise_insert

/--
theorem `insert` / 定理 `insert`

English:
theorem insert
  statement: (hs : IsAntichain r s) (hl : forall ⦃b⦄, b in s -> a != b -> ¬r b a)
  proof: isAntichain_insert.2 ⟨hs, fun _ hb hab => ⟨hr hb hab, hl hb hab⟩⟩

中文:
定理 insert
  结论: (hs : IsAntichain r s) (hl : 对任意 ⦃b⦄, b in s -> a != b -> ¬r b a)
  证明: isAntichain_insert.2 ⟨hs, fun _ hb hab => ⟨hr hb hab, hl hb hab⟩⟩
-/
protected theorem insert (hs : IsAntichain r s) (hl : forall ⦃b⦄, b in s -> a != b -> ¬r b a)
    (hr : forall ⦃b⦄, b in s -> a != b -> ¬r a b) : IsAntichain r (insert a s) :=
  isAntichain_insert.2 ⟨hs, fun _ hb hab => ⟨hr hb hab, hl hb hab⟩⟩

/--
theorem `_root_.isAntichain_insert_of_symm` / 定理 `_root_.isAntichain_insert_of_symm`

English:
theorem _root_.isAntichain_insert_of_symm
  given: [Std.Symm r]
  proof: pairwise_insert_of_symm

@[deprecated (since := "2026-06-10")]
alias _root_.isAntichain_insert_of_symmetric := _root_.isAntichain_insert_of_symm

中文:
定理 _root_.isAntichain_insert_of_symm
  条件: [Std.Symm r]
  证明: pairwise_insert_of_symm

@[deprecated (since := "2026-06-10")]
alias _root_.isAntichain_insert_of_symmetric := _root_.isAntichain_insert_of_symm

Depends on / 依赖: pairwise_insert_of_symm
-/
theorem _root_.isAntichain_insert_of_symm [Std.Symm r] :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ forall ⦃b⦄, b in s -> a != b -> ¬r a b :=
  pairwise_insert_of_symm

@[deprecated (since := "2026-06-10")]
alias _root_.isAntichain_insert_of_symmetric := _root_.isAntichain_insert_of_symm

/--
theorem `insert_of_symm` / 定理 `insert_of_symm`

English:
theorem insert_of_symm
  given: (hs : IsAntichain r s) [Std.Symm r] (h : forall ⦃b⦄, b in s -> a != b -> ¬r a b)
  proof: isAntichain_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias insert_of_symmetric := insert_of_symm

中文:
定理 insert_of_symm
  条件: (hs : IsAntichain r s) [Std.Symm r] (h : 对任意 ⦃b⦄, b in s -> a != b -> ¬r a b)
  证明: isAntichain_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias insert_of_symmetric := insert_of_symm

Depends on / 依赖: isAntichain_insert_of_symm, isAntichain_insert_of_symm.mpr
-/
theorem insert_of_symm (hs : IsAntichain r s) [Std.Symm r] (h : forall ⦃b⦄, b in s -> a != b -> ¬r a b) :
    IsAntichain r (insert a s) :=
  isAntichain_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias insert_of_symmetric := insert_of_symm

/--
theorem `image_relEmbedding` / 定理 `image_relEmbedding`

English:
theorem image_relEmbedding
  given: (hs : IsAntichain r s) (φ : r ↪r r')
  statement: IsAntichain r' (φ '' s)
  proof: by
  intro b hb b' hb' h₁ h₂
  rw [Set.mem_image] at hb hb'
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  exact hs has has' (fun haa' => h₁ (by rw [haa'])) (φ.map_rel_iff.mp h₂)

中文:
定理 image_relEmbedding
  条件: (hs : IsAntichain r s) (φ : r ↪r r')
  结论: IsAntichain r' (φ '' s)
  证明: by
  intro b hb b' hb' h₁ h₂
  rw [Set.mem_image] at hb hb'
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  exact hs has has' (fun haa' => h₁ (by rw [haa'])) (φ.map_rel_iff.mp h₂)

Depends on / 依赖: Set.mem_image, map_rel_iff, map_rel_iff.mp, mem_image
-/
theorem image_relEmbedding (hs : IsAntichain r s) (φ : r ↪r r') : IsAntichain r' (φ '' s) := by
  intro b hb b' hb' h₁ h₂
  rw [Set.mem_image] at hb hb'
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  exact hs has has' (fun haa' => h₁ (by rw [haa'])) (φ.map_rel_iff.mp h₂)

/--
theorem `preimage_relEmbedding` / 定理 `preimage_relEmbedding`

English:
theorem preimage_relEmbedding
  given: {t : Set β} (ht : IsAntichain r' t) (φ : r ↪r r')
  proof: fun _ ha _s ha' hne hle =>
  ht ha ha' (fun h => hne (φ.injective h)) (φ.map_rel_iff.mpr hle)

中文:
定理 preimage_relEmbedding
  条件: {t : 集合 β} (ht : IsAntichain r' t) (φ : r ↪r r')
  证明: fun _ ha _s ha' hne hle =>
  ht ha ha' (fun h => hne (φ.injective h)) (φ.map_rel_iff.mpr hle)
-/
theorem preimage_relEmbedding {t : Set β} (ht : IsAntichain r' t) (φ : r ↪r r') :
    IsAntichain r (φ ⁻¹' t) := fun _ ha _s ha' hne hle =>
  ht ha ha' (fun h => hne (φ.injective h)) (φ.map_rel_iff.mpr hle)

/--
theorem `image_relIso` / 定理 `image_relIso`

English:
theorem image_relIso
  given: (hs : IsAntichain r s) (φ : r ≃r r')
  statement: IsAntichain r' (φ '' s)
  proof: hs.image_relEmbedding φ.toRelEmbedding

中文:
定理 image_relIso
  条件: (hs : IsAntichain r s) (φ : r ≃r r')
  结论: IsAntichain r' (φ '' s)
  证明: hs.image_relEmbedding φ.toRelEmbedding

Depends on / 依赖: hs.image_relEmbedding, image_relEmbedding, toRelEmbedding
-/
theorem image_relIso (hs : IsAntichain r s) (φ : r ≃r r') : IsAntichain r' (φ '' s) :=
  hs.image_relEmbedding φ.toRelEmbedding

/--
theorem `preimage_relIso` / 定理 `preimage_relIso`

English:
theorem preimage_relIso
  given: {t : Set β} (hs : IsAntichain r' t) (φ : r ≃r r')
  proof: hs.preimage_relEmbedding φ.toRelEmbedding

中文:
定理 preimage_relIso
  条件: {t : 集合 β} (hs : IsAntichain r' t) (φ : r ≃r r')
  证明: hs.preimage_relEmbedding φ.toRelEmbedding

Depends on / 依赖: hs.preimage_relEmbedding, preimage_relEmbedding, toRelEmbedding
-/
theorem preimage_relIso {t : Set β} (hs : IsAntichain r' t) (φ : r ≃r r') :
    IsAntichain r (φ ⁻¹' t) :=
  hs.preimage_relEmbedding φ.toRelEmbedding

/--
theorem `image_relEmbedding_iff` / 定理 `image_relEmbedding_iff`

English:
theorem image_relEmbedding_iff
  given: {φ : r ↪r r'}
  statement: IsAntichain r' (φ '' s) ↔ IsAntichain r s
  proof: ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h =>
    h.image_relEmbedding φ⟩

中文:
定理 image_relEmbedding_iff
  条件: {φ : r ↪r r'}
  结论: IsAntichain r' (φ '' s) ↔ IsAntichain r s
  证明: ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h =>
    h.image_relEmbedding φ⟩

Depends on / 依赖: h.image_relEmbedding, h.preimage_relEmbedding, image_relEmbedding, injective, injective.preimage_image, preimage_image, preimage_relEmbedding
-/
theorem image_relEmbedding_iff {φ : r ↪r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h =>
    h.image_relEmbedding φ⟩

/--
theorem `image_relIso_iff` / 定理 `image_relIso_iff`

English:
theorem image_relIso_iff
  given: {φ : r ≃r r'}
  statement: IsAntichain r' (φ '' s) ↔ IsAntichain r s
  proof: @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

中文:
定理 image_relIso_iff
  条件: {φ : r ≃r r'}
  结论: IsAntichain r' (φ '' s) ↔ IsAntichain r s
  证明: @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

Depends on / 依赖: image_relEmbedding_iff
-/
theorem image_relIso_iff {φ : r ≃r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

/--
theorem `image_embedding` / 定理 `image_embedding`

English:
theorem image_embedding
  given: [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ↪o β)
  proof: image_relEmbedding hs _

中文:
定理 image_embedding
  条件: [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ↪o β)
  证明: image_relEmbedding hs _

Depends on / 依赖: image_relEmbedding
-/
theorem image_embedding [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ↪o β) :
    IsAntichain (· <= ·) (φ '' s) :=
  image_relEmbedding hs _

/--
theorem `preimage_embedding` / 定理 `preimage_embedding`

English:
theorem preimage_embedding
  given: [LE α] [LE β] {t : Set β} (ht : IsAntichain (· <= ·) t) (φ : α ↪o β)
  proof: preimage_relEmbedding ht _

中文:
定理 preimage_embedding
  条件: [LE α] [LE β] {t : 集合 β} (ht : IsAntichain (· <= ·) t) (φ : α ↪o β)
  证明: preimage_relEmbedding ht _

Depends on / 依赖: preimage_relEmbedding
-/
theorem preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsAntichain (· <= ·) t) (φ : α ↪o β) :
    IsAntichain (· <= ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _

/--
theorem `image_embedding_iff` / 定理 `image_embedding_iff`

English:
theorem image_embedding_iff
  given: [LE α] [LE β] {φ : α ↪o β}
  proof: image_relEmbedding_iff

中文:
定理 image_embedding_iff
  条件: [LE α] [LE β] {φ : α ↪o β}
  证明: image_relEmbedding_iff

Depends on / 依赖: image_relEmbedding_iff
-/
theorem image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsAntichain (· <= ·) (φ '' s) ↔ IsAntichain (· <= ·) s :=
  image_relEmbedding_iff

/--
theorem `image_iso` / 定理 `image_iso`

English:
theorem image_iso
  given: [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ≃o β)
  proof: image_relEmbedding hs _

中文:
定理 image_iso
  条件: [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ≃o β)
  证明: image_relEmbedding hs _

Depends on / 依赖: image_relEmbedding
-/
theorem image_iso [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ≃o β) :
    IsAntichain (· <= ·) (φ '' s) :=
  image_relEmbedding hs _

/--
theorem `image_iso_iff` / 定理 `image_iso_iff`

English:
theorem image_iso_iff
  given: [LE α] [LE β] {φ : α ≃o β}
  proof: image_relEmbedding_iff

中文:
定理 image_iso_iff
  条件: [LE α] [LE β] {φ : α ≃o β}
  证明: image_relEmbedding_iff

Depends on / 依赖: image_relEmbedding_iff
-/
theorem image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsAntichain (· <= ·) (φ '' s) ↔ IsAntichain (· <= ·) s :=
  image_relEmbedding_iff

/--
theorem `preimage_iso` / 定理 `preimage_iso`

English:
theorem preimage_iso
  given: [LE α] [LE β] {t : Set β} (ht : IsAntichain (· <= ·) t) (φ : α ≃o β)
  proof: preimage_relEmbedding ht _

中文:
定理 preimage_iso
  条件: [LE α] [LE β] {t : 集合 β} (ht : IsAntichain (· <= ·) t) (φ : α ≃o β)
  证明: preimage_relEmbedding ht _

Depends on / 依赖: preimage_relEmbedding
-/
theorem preimage_iso [LE α] [LE β] {t : Set β} (ht : IsAntichain (· <= ·) t) (φ : α ≃o β) :
    IsAntichain (· <= ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _

/--
theorem `preimage_iso_iff` / 定理 `preimage_iso_iff`

English:
theorem preimage_iso_iff
  given: [LE α] [LE β] {t : Set β} {φ : α ≃o β}
  proof: ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩

中文:
定理 preimage_iso_iff
  条件: [LE α] [LE β] {t : 集合 β} {φ : α ≃o β}
  证明: ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩

Depends on / 依赖: h.image_iso, h.preimage_iso, image_iso, image_preimage, preimage_iso
-/
theorem preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsAntichain (· <= ·) (φ ⁻¹' t) ↔ IsAntichain (· <= ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩

/--
theorem `to_dual` / 定理 `to_dual`

English:
theorem to_dual
  given: [LE α] (hs : IsAntichain (· <= ·) s)
  statement: @IsAntichain αᵒᵈ (· <= ·) s
  proof: fun _ ha _ hb hab => hs hb ha hab.symm

中文:
定理 to_dual
  条件: [LE α] (hs : IsAntichain (· <= ·) s)
  结论: @IsAntichain αᵒᵈ (· <= ·) s
  证明: fun _ ha _ hb hab => hs hb ha hab.symm

Depends on / 依赖: hab.symm
-/
theorem to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsAntichain αᵒᵈ (· <= ·) s :=
  fun _ ha _ hb hab => hs hb ha hab.symm

/--
theorem `to_dual_iff` / 定理 `to_dual_iff`

English:
theorem to_dual_iff
  given: [LE α]
  statement: IsAntichain (· <= ·) s ↔ @IsAntichain αᵒᵈ (· <= ·) s
  proof: ⟨to_dual, to_dual⟩

中文:
定理 to_dual_iff
  条件: [LE α]
  结论: IsAntichain (· <= ·) s ↔ @IsAntichain αᵒᵈ (· <= ·) s
  证明: ⟨to_dual, to_dual⟩

Depends on / 依赖: to_dual
-/
theorem to_dual_iff [LE α] : IsAntichain (· <= ·) s ↔ @IsAntichain αᵒᵈ (· <= ·) s :=
  ⟨to_dual, to_dual⟩

/--
theorem `image_compl` / 定理 `image_compl`

English:
theorem image_compl
  given: [BooleanAlgebra α] (hs : IsAntichain (· <= ·) s)
  proof: (hs.image_embedding (OrderIso.compl α).toOrderEmbedding).flip

中文:
定理 image_compl
  条件: [布尔代数 α] (hs : IsAntichain (· <= ·) s)
  证明: (hs.image_embedding (OrderIso.compl α).toOrderEmbedding).flip

Depends on / 依赖: OrderIso, OrderIso.compl, hs.image_embedding, image_embedding, toOrderEmbedding
-/
theorem image_compl [BooleanAlgebra α] (hs : IsAntichain (· <= ·) s) :
    IsAntichain (· <= ·) (compl '' s) :=
  (hs.image_embedding (OrderIso.compl α).toOrderEmbedding).flip

/--
theorem `preimage_compl` / 定理 `preimage_compl`

English:
theorem preimage_compl
  given: [BooleanAlgebra α] (hs : IsAntichain (· <= ·) s)
  proof: fun _ ha _ ha' hne hle =>
  hs ha' ha (fun h => hne (compl_inj_iff.mp h.symm)) (compl_le_compl hle)

中文:
定理 preimage_compl
  条件: [布尔代数 α] (hs : IsAntichain (· <= ·) s)
  证明: fun _ ha _ ha' hne hle =>
  hs ha' ha (fun h => hne (compl_inj_iff.mp h.symm)) (compl_le_compl hle)
-/
theorem preimage_compl [BooleanAlgebra α] (hs : IsAntichain (· <= ·) s) :
    IsAntichain (· <= ·) (compl ⁻¹' s) := fun _ ha _ ha' hne hle =>
  hs ha' ha (fun h => hne (compl_inj_iff.mp h.symm)) (compl_le_compl hle)

/--
theorem `diff` / 定理 `diff`

English:
theorem diff
  given: {s t : Set α} (h : IsAntichain r s)
  statement: IsAntichain r (s \ t)
  proof: h.subset Set.sdiff_subset

中文:
定理 diff
  条件: {s t : 集合 α} (h : IsAntichain r s)
  结论: IsAntichain r (s \ t)
  证明: h.subset Set.sdiff_subset
-/
@[simp] protected theorem diff {s t : Set α} (h : IsAntichain r s) : IsAntichain r (s \ t) :=
  h.subset Set.sdiff_subset

end IsAntichain

/--
theorem `isAntichain_preimage_subtypeVal` / 定理 `isAntichain_preimage_subtypeVal`

English:
theorem isAntichain_preimage_subtypeVal
  given: (s t : Set α)
  proof: by
  simp [IsAntichain, Set.Pairwise]

中文:
定理 isAntichain_preimage_subtypeVal
  条件: (s t : 集合 α)
  证明: by
  simp [IsAntichain, Set.Pairwise]

Depends on / 依赖: IsAntichain, Pairwise, Set.Pairwise
-/
theorem isAntichain_preimage_subtypeVal (s t : Set α) :
    @IsAntichain ↑s (r · ·) (s ↓inter t) ↔ IsAntichain r (s inter t) := by
  simp [IsAntichain, Set.Pairwise]

/--
theorem `isAntichain_coe_univ_iff` / 定理 `isAntichain_coe_univ_iff`

English:
theorem isAntichain_coe_univ_iff
  given: {s : Set α}
  statement: @IsAntichain ↑s (r · ·) univ ↔ IsAntichain r s
  proof: by
  simpa using isAntichain_preimage_subtypeVal s univ

中文:
定理 isAntichain_coe_univ_iff
  条件: {s : 集合 α}
  结论: @IsAntichain ↑s (r · ·) univ ↔ IsAntichain r s
  证明: by
  simpa using isAntichain_preimage_subtypeVal s univ

Depends on / 依赖: isAntichain_preimage_subtypeVal
-/
theorem isAntichain_coe_univ_iff {s : Set α} : @IsAntichain ↑s (r · ·) univ ↔ IsAntichain r s := by
  simpa using isAntichain_preimage_subtypeVal s univ

/--
theorem `isAntichain_union` / 定理 `isAntichain_union`

English:
theorem isAntichain_union
  proof: by
  rw [IsAntichain]; rw [IsAntichain]; rw [IsAntichain]; rw [pairwise_union]

中文:
定理 isAntichain_union
  证明: by
  rw [IsAntichain]; rw [IsAntichain]; rw [IsAntichain]; rw [pairwise_union]

Depends on / 依赖: IsAntichain, pairwise_union
-/
theorem isAntichain_union :
    IsAntichain r (s union t) ↔
      IsAntichain r s ∧ IsAntichain r t ∧ forall a in s, forall b in t, a != b -> rᶜ a b ∧ rᶜ b a := by
  rw [IsAntichain]; rw [IsAntichain]; rw [IsAntichain]; rw [pairwise_union]

/--
theorem `Set.Subsingleton.isAntichain` / 定理 `Set.Subsingleton.isAntichain`

English:
theorem Set.Subsingleton.isAntichain
  given: (hs : s.Subsingleton) (r : α -> α -> Prop)
  statement: IsAntichain r s
  proof: hs.pairwise _

中文:
定理 集合.子单例.isAntichain
  条件: (hs : s.子单例) (r : α -> α -> 命题)
  结论: IsAntichain r s
  证明: hs.pairwise _

Depends on / 依赖: hs.pairwise, pairwise
-/
theorem Set.Subsingleton.isAntichain (hs : s.Subsingleton) (r : α -> α -> Prop) : IsAntichain r s :=
  hs.pairwise _

/--
lemma `subsingleton_of_isChain_of_isAntichain` / 引理 `subsingleton_of_isChain_of_isAntichain`

English:
lemma subsingleton_of_isChain_of_isAntichain
  given: (hs : IsChain r s) (ht : IsAntichain r s)
  proof: by
  intro x hx y hy
  by_contra! hne
  cases hs hx hy hne with
  | inl h => exact ht hx hy hne h
  | inr h => exact ht hy hx hne.symm h

中文:
引理 subsingleton_of_isChain_of_isAntichain
  条件: (hs : IsChain r s) (ht : IsAntichain r s)
  证明: by
  intro x hx y hy
  by_contra! hne
  cases hs hx hy hne with
  | inl h => exact ht hx hy hne h
  | inr h => exact ht hy hx hne.symm h

Depends on / 依赖: hne.symm
-/
lemma subsingleton_of_isChain_of_isAntichain (hs : IsChain r s) (ht : IsAntichain r s) :
    s.Subsingleton := by
  intro x hx y hy
  by_contra! hne
  cases hs hx hy hne with
  | inl h => exact ht hx hy hne h
  | inr h => exact ht hy hx hne.symm h

/--
lemma `isChain_and_isAntichain_iff_subsingleton` / 引理 `isChain_and_isAntichain_iff_subsingleton`

English:
lemma isChain_and_isAntichain_iff_subsingleton
  statement: IsChain r s ∧ IsAntichain r s ↔ s.Subsingleton
  proof: ⟨fun h => subsingleton_of_isChain_of_isAntichain h.1 h.2, fun h => ⟨h.isChain, h.isAntichain _⟩⟩

中文:
引理 isChain_and_isAntichain_iff_subsingleton
  结论: IsChain r s ∧ IsAntichain r s ↔ s.子单例
  证明: ⟨fun h => subsingleton_of_isChain_of_isAntichain h.1 h.2, fun h => ⟨h.isChain, h.isAntichain _⟩⟩

Depends on / 依赖: h.isAntichain, h.isChain, isAntichain, isChain, subsingleton_of_isChain_of_isAntichain
-/
lemma isChain_and_isAntichain_iff_subsingleton : IsChain r s ∧ IsAntichain r s ↔ s.Subsingleton :=
  ⟨fun h => subsingleton_of_isChain_of_isAntichain h.1 h.2, fun h => ⟨h.isChain, h.isAntichain _⟩⟩

/--
lemma `inter_subsingleton_of_isChain_of_isAntichain` / 引理 `inter_subsingleton_of_isChain_of_isAntichain`

English:
lemma inter_subsingleton_of_isChain_of_isAntichain
  given: (hs : IsChain r s) (ht : IsAntichain r t)
  proof: subsingleton_of_isChain_of_isAntichain (hs.mono (by simp)) (ht.subset (by simp))

中文:
引理 inter_subsingleton_of_isChain_of_isAntichain
  条件: (hs : IsChain r s) (ht : IsAntichain r t)
  证明: subsingleton_of_isChain_of_isAntichain (hs.mono (by simp)) (ht.subset (by simp))

Depends on / 依赖: hs.mono, ht.subset, subset, subsingleton_of_isChain_of_isAntichain
-/
lemma inter_subsingleton_of_isChain_of_isAntichain (hs : IsChain r s) (ht : IsAntichain r t) :
    (s inter t).Subsingleton :=
  subsingleton_of_isChain_of_isAntichain (hs.mono (by simp)) (ht.subset (by simp))

/--
lemma `inter_subsingleton_of_isAntichain_of_isChain` / 引理 `inter_subsingleton_of_isAntichain_of_isChain`

English:
lemma inter_subsingleton_of_isAntichain_of_isChain
  given: (hs : IsAntichain r s) (ht : IsChain r t)
  proof: inter_comm _ _ ▸ inter_subsingleton_of_isChain_of_isAntichain ht hs

中文:
引理 inter_subsingleton_of_isAntichain_of_isChain
  条件: (hs : IsAntichain r s) (ht : IsChain r t)
  证明: inter_comm _ _ ▸ inter_subsingleton_of_isChain_of_isAntichain ht hs

Depends on / 依赖: inter_comm, inter_subsingleton_of_isChain_of_isAntichain
-/
lemma inter_subsingleton_of_isAntichain_of_isChain (hs : IsAntichain r s) (ht : IsChain r t) :
    (s inter t).Subsingleton :=
  inter_comm _ _ ▸ inter_subsingleton_of_isChain_of_isAntichain ht hs

section Preorder

variable [Preorder α]

/--
theorem `IsAntichain.not_lt` / 定理 `IsAntichain.not_lt`

English:
theorem IsAntichain.not_lt
  given: (hs : IsAntichain (· <= ·) s) (ha : a in s) (hb : b in s)
  statement: ¬a < b
  proof: fun h => hs ha hb h.ne h.le

中文:
定理 IsAntichain.not_lt
  条件: (hs : IsAntichain (· <= ·) s) (ha : a in s) (hb : b in s)
  结论: ¬a < b
  证明: fun h => hs ha hb h.ne h.le

Depends on / 依赖: h.le, h.ne
-/
theorem IsAntichain.not_lt (hs : IsAntichain (· <= ·) s) (ha : a in s) (hb : b in s) : ¬a < b :=
  fun h => hs ha hb h.ne h.le

/--
theorem `isAntichain_and_least_iff` / 定理 `isAntichain_and_least_iff`

English:
theorem isAntichain_and_least_iff
  statement: IsAntichain (· <= ·) s ∧ IsLeast s a ↔ s = {a}
  proof: ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq' hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isLeast_singleton⟩⟩

中文:
定理 isAntichain_and_least_iff
  结论: IsAntichain (· <= ·) s ∧ IsLeast s a ↔ s = {a}
  证明: ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq' hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isLeast_singleton⟩⟩

Depends on / 依赖: IsAntichain, IsAntichain.singleton, eq_singleton_iff_unique_mem, isLeast_singleton, singleton
-/
theorem isAntichain_and_least_iff : IsAntichain (· <= ·) s ∧ IsLeast s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq' hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isLeast_singleton⟩⟩

/--
theorem `isAntichain_and_greatest_iff` / 定理 `isAntichain_and_greatest_iff`

English:
theorem isAntichain_and_greatest_iff
  statement: IsAntichain (· <= ·) s ∧ IsGreatest s a ↔ s = {a}
  proof: ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isGreatest_singleton⟩⟩

中文:
定理 isAntichain_and_greatest_iff
  结论: IsAntichain (· <= ·) s ∧ IsGreatest s a ↔ s = {a}
  证明: ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isGreatest_singleton⟩⟩

Depends on / 依赖: IsAntichain, IsAntichain.singleton, eq_singleton_iff_unique_mem, isGreatest_singleton, singleton
-/
theorem isAntichain_and_greatest_iff : IsAntichain (· <= ·) s ∧ IsGreatest s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isGreatest_singleton⟩⟩

/--
theorem `IsAntichain.least_iff` / 定理 `IsAntichain.least_iff`

English:
theorem IsAntichain.least_iff
  given: (hs : IsAntichain (· <= ·) s)
  statement: IsLeast s a ↔ s = {a}
  proof: (and_iff_right hs).symm.trans isAntichain_and_least_iff

中文:
定理 IsAntichain.least_iff
  条件: (hs : IsAntichain (· <= ·) s)
  结论: IsLeast s a ↔ s = {a}
  证明: (and_iff_right hs).symm.trans isAntichain_and_least_iff

Depends on / 依赖: and_iff_right, isAntichain_and_least_iff, symm.trans
-/
theorem IsAntichain.least_iff (hs : IsAntichain (· <= ·) s) : IsLeast s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_least_iff

/--
theorem `IsAntichain.greatest_iff` / 定理 `IsAntichain.greatest_iff`

English:
theorem IsAntichain.greatest_iff
  given: (hs : IsAntichain (· <= ·) s)
  statement: IsGreatest s a ↔ s = {a}
  proof: (and_iff_right hs).symm.trans isAntichain_and_greatest_iff

中文:
定理 IsAntichain.greatest_iff
  条件: (hs : IsAntichain (· <= ·) s)
  结论: IsGreatest s a ↔ s = {a}
  证明: (and_iff_right hs).symm.trans isAntichain_and_greatest_iff

Depends on / 依赖: and_iff_right, isAntichain_and_greatest_iff, symm.trans
-/
theorem IsAntichain.greatest_iff (hs : IsAntichain (· <= ·) s) : IsGreatest s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_greatest_iff

/--
theorem `IsLeast.antichain_iff` / 定理 `IsLeast.antichain_iff`

English:
theorem IsLeast.antichain_iff
  given: (hs : IsLeast s a)
  statement: IsAntichain (· <= ·) s ↔ s = {a}
  proof: (and_iff_left hs).symm.trans isAntichain_and_least_iff

中文:
定理 IsLeast.antichain_iff
  条件: (hs : IsLeast s a)
  结论: IsAntichain (· <= ·) s ↔ s = {a}
  证明: (and_iff_left hs).symm.trans isAntichain_and_least_iff

Depends on / 依赖: and_iff_left, isAntichain_and_least_iff, symm.trans
-/
theorem IsLeast.antichain_iff (hs : IsLeast s a) : IsAntichain (· <= ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_least_iff

/--
theorem `IsGreatest.antichain_iff` / 定理 `IsGreatest.antichain_iff`

English:
theorem IsGreatest.antichain_iff
  given: (hs : IsGreatest s a)
  statement: IsAntichain (· <= ·) s ↔ s = {a}
  proof: (and_iff_left hs).symm.trans isAntichain_and_greatest_iff

中文:
定理 IsGreatest.antichain_iff
  条件: (hs : IsGreatest s a)
  结论: IsAntichain (· <= ·) s ↔ s = {a}
  证明: (and_iff_left hs).symm.trans isAntichain_and_greatest_iff

Depends on / 依赖: and_iff_left, isAntichain_and_greatest_iff, symm.trans
-/
theorem IsGreatest.antichain_iff (hs : IsGreatest s a) : IsAntichain (· <= ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_greatest_iff

/--
theorem `IsAntichain.bot_mem_iff` / 定理 `IsAntichain.bot_mem_iff`

English:
theorem IsAntichain.bot_mem_iff
  given: [OrderBot α] (hs : IsAntichain (· <= ·) s)
  statement: ⊥ in s ↔ s = {⊥}
  proof: isLeast_bot_iff.symm.trans hs.least_iff

中文:
定理 IsAntichain.bot_mem_iff
  条件: [有底序 α] (hs : IsAntichain (· <= ·) s)
  结论: ⊥ in s ↔ s = {⊥}
  证明: isLeast_bot_iff.symm.trans hs.least_iff

Depends on / 依赖: hs.least_iff, isLeast_bot_iff, isLeast_bot_iff.symm.trans, least_iff
-/
theorem IsAntichain.bot_mem_iff [OrderBot α] (hs : IsAntichain (· <= ·) s) : ⊥ in s ↔ s = {⊥} :=
  isLeast_bot_iff.symm.trans hs.least_iff

/--
theorem `IsAntichain.top_mem_iff` / 定理 `IsAntichain.top_mem_iff`

English:
theorem IsAntichain.top_mem_iff
  given: [OrderTop α] (hs : IsAntichain (· <= ·) s)
  statement: ⊤ in s ↔ s = {⊤}
  proof: isGreatest_top_iff.symm.trans hs.greatest_iff

中文:
定理 IsAntichain.top_mem_iff
  条件: [有顶序 α] (hs : IsAntichain (· <= ·) s)
  结论: ⊤ in s ↔ s = {⊤}
  证明: isGreatest_top_iff.symm.trans hs.greatest_iff

Depends on / 依赖: greatest_iff, hs.greatest_iff, isGreatest_top_iff, isGreatest_top_iff.symm.trans
-/
theorem IsAntichain.top_mem_iff [OrderTop α] (hs : IsAntichain (· <= ·) s) : ⊤ in s ↔ s = {⊤} :=
  isGreatest_top_iff.symm.trans hs.greatest_iff

/--
theorem `IsAntichain.minimal_mem_iff` / 定理 `IsAntichain.minimal_mem_iff`

English:
theorem IsAntichain.minimal_mem_iff
  given: (hs : IsAntichain (· <= ·) s)
  statement: Minimal (· in s) a ↔ a in s
  proof: ⟨fun h => h.prop, fun h => ⟨h, fun _ hys hyx => (hs.eq hys h hyx).symm.le⟩⟩

中文:
定理 IsAntichain.minimal_mem_iff
  条件: (hs : IsAntichain (· <= ·) s)
  结论: 极小 (· in s) a ↔ a in s
  证明: ⟨fun h => h.prop, fun h => ⟨h, fun _ hys hyx => (hs.eq hys h hyx).symm.le⟩⟩

Depends on / 依赖: h.prop, hs.eq, symm.le
-/
theorem IsAntichain.minimal_mem_iff (hs : IsAntichain (· <= ·) s) : Minimal (· in s) a ↔ a in s :=
  ⟨fun h => h.prop, fun h => ⟨h, fun _ hys hyx => (hs.eq hys h hyx).symm.le⟩⟩

/--
theorem `IsAntichain.maximal_mem_iff` / 定理 `IsAntichain.maximal_mem_iff`

English:
theorem IsAntichain.maximal_mem_iff
  given: (hs : IsAntichain (· <= ·) s)
  statement: Maximal (· in s) a ↔ a in s
  proof: hs.to_dual.minimal_mem_iff

中文:
定理 IsAntichain.maximal_mem_iff
  条件: (hs : IsAntichain (· <= ·) s)
  结论: 极大 (· in s) a ↔ a in s
  证明: hs.to_dual.minimal_mem_iff

Depends on / 依赖: hs.to_dual.minimal_mem_iff, minimal_mem_iff, to_dual
-/
theorem IsAntichain.maximal_mem_iff (hs : IsAntichain (· <= ·) s) : Maximal (· in s) a ↔ a in s :=
  hs.to_dual.minimal_mem_iff

/--
theorem `IsAntichain.eq_setOfPred_maximal` / 定理 `IsAntichain.eq_setOfPred_maximal`

English:
theorem IsAntichain.eq_setOfPred_maximal
  statement: (ht : IsAntichain (· <= ·) t)
  proof: by
  refine Set.ext fun x => ⟨h _, fun hx => ?_⟩
  obtain ⟨y, hyx, hy⟩ := hs x hx
  rwa [← ht.eq (h y hy) hx hyx]

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_maximal := IsAntichain.eq_setOfPred_maximal

中文:
定理 IsAntichain.eq_setOfPred_maximal
  结论: (ht : IsAntichain (· <= ·) t)
  证明: by
  refine Set.ext fun x => ⟨h _, fun hx => ?_⟩
  obtain ⟨y, hyx, hy⟩ := hs x hx
  rwa [← ht.eq (h y hy) hx hyx]

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_maximal := IsAntichain.eq_setOfPred_maximal

Depends on / 依赖: Set.ext, ht.eq
-/
theorem IsAntichain.eq_setOfPred_maximal (ht : IsAntichain (· <= ·) t)
    (h : forall x, Maximal (· in s) x -> x in t) (hs : forall a in t, exists b, b <= a ∧ Maximal (· in s) b) :
    {x | Maximal (· in s) x} = t := by
  refine Set.ext fun x => ⟨h _, fun hx => ?_⟩
  obtain ⟨y, hyx, hy⟩ := hs x hx
  rwa [← ht.eq (h y hy) hx hyx]

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_maximal := IsAntichain.eq_setOfPred_maximal

/--
theorem `IsAntichain.eq_setOfPred_minimal` / 定理 `IsAntichain.eq_setOfPred_minimal`

English:
theorem IsAntichain.eq_setOfPred_minimal
  statement: (ht : IsAntichain (· <= ·) t)
  proof: ht.to_dual.eq_setOfPred_maximal h hs

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_minimal := IsAntichain.eq_setOfPred_minimal

中文:
定理 IsAntichain.eq_setOfPred_minimal
  结论: (ht : IsAntichain (· <= ·) t)
  证明: ht.to_dual.eq_setOfPred_maximal h hs

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_minimal := IsAntichain.eq_setOfPred_minimal

Depends on / 依赖: eq_setOfPred_maximal, ht.to_dual.eq_setOfPred_maximal, to_dual
-/
theorem IsAntichain.eq_setOfPred_minimal (ht : IsAntichain (· <= ·) t)
    (h : forall x, Minimal (· in s) x -> x in t) (hs : forall a in t, exists b, a <= b ∧ Minimal (· in s) b) :
    {x | Minimal (· in s) x} = t :=
  ht.to_dual.eq_setOfPred_maximal h hs

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_minimal := IsAntichain.eq_setOfPred_minimal

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {f : α -> β} {s : Set α}

/--
lemma `IsAntichain.of_strictMonoOn_antitoneOn` / 引理 `IsAntichain.of_strictMonoOn_antitoneOn`

English:
lemma IsAntichain.of_strictMonoOn_antitoneOn
  given: (hf : StrictMonoOn f s) (hf' : AntitoneOn f s)
  proof: fun _a ha _b hb hab' hab => (hf ha hb <| hab.lt_of_ne hab').not_ge (hf' ha hb hab)

中文:
引理 IsAntichain.of_strictMonoOn_antitoneOn
  条件: (hf : StrictMonoOn f s) (hf' : AntitoneOn f s)
  证明: fun _a ha _b hb hab' hab => (hf ha hb <| hab.lt_of_ne hab').not_ge (hf' ha hb hab)

Depends on / 依赖: hab.lt_of_ne, lt_of_ne, not_ge
-/
lemma IsAntichain.of_strictMonoOn_antitoneOn (hf : StrictMonoOn f s) (hf' : AntitoneOn f s) :
    IsAntichain (· <= ·) s :=
  fun _a ha _b hb hab' hab => (hf ha hb <| hab.lt_of_ne hab').not_ge (hf' ha hb hab)

/--
lemma `IsAntichain.of_monotoneOn_strictAntiOn` / 引理 `IsAntichain.of_monotoneOn_strictAntiOn`

English:
lemma IsAntichain.of_monotoneOn_strictAntiOn
  given: (hf : MonotoneOn f s) (hf' : StrictAntiOn f s)
  proof: fun _a ha _b hb hab' hab => (hf ha hb hab).not_gt (hf' ha hb <| hab.lt_of_ne hab')

中文:
引理 IsAntichain.of_monotoneOn_strictAntiOn
  条件: (hf : MonotoneOn f s) (hf' : StrictAntiOn f s)
  证明: fun _a ha _b hb hab' hab => (hf ha hb hab).not_gt (hf' ha hb <| hab.lt_of_ne hab')

Depends on / 依赖: hab.lt_of_ne, lt_of_ne, not_gt
-/
lemma IsAntichain.of_monotoneOn_strictAntiOn (hf : MonotoneOn f s) (hf' : StrictAntiOn f s) :
    IsAntichain (· <= ·) s :=
  fun _a ha _b hb hab' hab => (hf ha hb hab).not_gt (hf' ha hb <| hab.lt_of_ne hab')

/--
theorem `isAntichain_iff_forall_not_lt` / 定理 `isAntichain_iff_forall_not_lt`

English:
theorem isAntichain_iff_forall_not_lt
  proof: ⟨fun hs _ ha _ => hs.not_lt ha, fun hs _ ha _ hb h h' => hs ha hb h'.lt_of_ne h⟩

中文:
定理 isAntichain_iff_对任意_not_lt
  证明: ⟨fun hs _ ha _ => hs.not_lt ha, fun hs _ ha _ hb h h' => hs ha hb h'.lt_of_ne h⟩

Depends on / 依赖: hs.not_lt, lt_of_ne, not_lt
-/
theorem isAntichain_iff_forall_not_lt :
    IsAntichain (· <= ·) s ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> ¬a < b :=
⟨fun hs _ ha _ => hs.not_lt ha, fun hs _ ha _ hb h h' => hs ha hb h'.lt_of_ne h⟩

/--
theorem `setOfPred_maximal_antichain` / 定理 `setOfPred_maximal_antichain`

English:
theorem setOfPred_maximal_antichain
  given: (P : α -> Prop)
  statement: IsAntichain (· <= ·) {x | Maximal P x}
  proof: fun _ hx _ ⟨hy, _⟩ hne hle => hne (hle.antisymm <| hx.2 hy hle)

@[deprecated (since := "2026-07-09")]
alias setOf_maximal_antichain := setOfPred_maximal_antichain

中文:
定理 setOfPred_maximal_antichain
  条件: (P : α -> 命题)
  结论: IsAntichain (· <= ·) {x | 极大 P x}
  证明: fun _ hx _ ⟨hy, _⟩ hne hle => hne (hle.antisymm <| hx.2 hy hle)

@[deprecated (since := "2026-07-09")]
alias setOf_maximal_antichain := setOfPred_maximal_antichain

Depends on / 依赖: antisymm, hle.antisymm
-/
theorem setOfPred_maximal_antichain (P : α -> Prop) : IsAntichain (· <= ·) {x | Maximal P x} :=
  fun _ hx _ ⟨hy, _⟩ hne hle => hne (hle.antisymm <| hx.2 hy hle)

@[deprecated (since := "2026-07-09")]
alias setOf_maximal_antichain := setOfPred_maximal_antichain

/--
theorem `setOfPred_minimal_antichain` / 定理 `setOfPred_minimal_antichain`

English:
theorem setOfPred_minimal_antichain
  given: (P : α -> Prop)
  statement: IsAntichain (· <= ·) {x | Minimal P x}
  proof: (setOfPred_maximal_antichain (α := αᵒᵈ) P).swap

@[deprecated (since := "2026-07-09")] alias setOf_minimal_antichain := setOfPred_minimal_antichain

中文:
定理 setOfPred_minimal_antichain
  条件: (P : α -> 命题)
  结论: IsAntichain (· <= ·) {x | 极小 P x}
  证明: (setOfPred_maximal_antichain (α := αᵒᵈ) P).swap

@[deprecated (since := "2026-07-09")] alias setOf_minimal_antichain := setOfPred_minimal_antichain

Depends on / 依赖: setOfPred_maximal_antichain
-/
theorem setOfPred_minimal_antichain (P : α -> Prop) : IsAntichain (· <= ·) {x | Minimal P x} :=
  (setOfPred_maximal_antichain (α := αᵒᵈ) P).swap

@[deprecated (since := "2026-07-09")] alias setOf_minimal_antichain := setOfPred_minimal_antichain

end PartialOrder

/-! ### Strong antichains -/


/--
Definition of `IsStrongAntichain` / `IsStrongAntichain` 的定义

English:
definition IsStrongAntichain
  signature: (r : α -> α -> Prop) (s : Set α)
  body: s.Pairwise fun a b => forall c, ¬r a c ∨ ¬r b c

中文:
定义 IsStrongAntichain
  签名: (r : α -> α -> 命题) (s : 集合 α)
  定义体: s.Pairwise fun a b => forall c, ¬r a c ∨ ¬r b c

Depends on / 依赖: Pairwise, s.Pairwise
-/
def IsStrongAntichain (r : α -> α -> Prop) (s : Set α) : Prop :=
  s.Pairwise fun a b => forall c, ¬r a c ∨ ¬r b c

namespace IsStrongAntichain

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (hs : IsStrongAntichain r s) (h : t subseteq s)
  statement: IsStrongAntichain r t
  proof: hs.mono h

中文:
定理 subset
  条件: (hs : IsStrongAntichain r s) (h : t subseteq s)
  结论: IsStrongAntichain r t
  证明: hs.mono h
-/
protected theorem subset (hs : IsStrongAntichain r s) (h : t subseteq s) : IsStrongAntichain r t :=
  hs.mono h

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hs : IsStrongAntichain r₁ s) (h : r₂ <= r₁)
  statement: IsStrongAntichain r₂ s
  proof: hs.mono' fun _ _ hab c => (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)

中文:
定理 mono
  条件: (hs : IsStrongAntichain r₁ s) (h : r₂ <= r₁)
  结论: IsStrongAntichain r₂ s
  证明: hs.mono' fun _ _ hab c => (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)

Depends on / 依赖: compl_le_compl, hs.mono
-/
theorem mono (hs : IsStrongAntichain r₁ s) (h : r₂ <= r₁) : IsStrongAntichain r₂ s :=
  hs.mono' fun _ _ hab c => (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  statement: (hs : IsStrongAntichain r s) {a b c : α} (ha : a in s) (hb : b in s) (hac : r a c)
  proof: (Set.Pairwise.eq hs ha hb) fun h =>
False.elim (h c).elim (not_not_intro hac) (not_not_intro hbc)

中文:
定理 eq
  结论: (hs : IsStrongAntichain r s) {a b c : α} (ha : a in s) (hb : b in s) (hac : r a c)
  证明: (Set.Pairwise.eq hs ha hb) fun h =>
False.elim (h c).elim (not_not_intro hac) (not_not_intro hbc)

Depends on / 依赖: False.elim, Pairwise, Set.Pairwise.eq, not_not_intro
-/
theorem eq (hs : IsStrongAntichain r s) {a b c : α} (ha : a in s) (hb : b in s) (hac : r a c)
    (hbc : r b c) : a = b :=
  (Set.Pairwise.eq hs ha hb) fun h =>
False.elim (h c).elim (not_not_intro hac) (not_not_intro hbc)

/--
theorem `isAntichain` / 定理 `isAntichain`

English:
theorem isAntichain
  given: [Std.Refl r] (h : IsStrongAntichain r s)
  statement: IsAntichain r s
  proof: h.imp fun _ b hab => (hab b).resolve_right (not_not_intro <| refl _)

中文:
定理 isAntichain
  条件: [Std.Refl r] (h : IsStrongAntichain r s)
  结论: IsAntichain r s
  证明: h.imp fun _ b hab => (hab b).resolve_right (not_not_intro <| refl _)
-/
protected theorem isAntichain [Std.Refl r] (h : IsStrongAntichain r s) : IsAntichain r s :=
  h.imp fun _ b hab => (hab b).resolve_right (not_not_intro <| refl _)

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: [IsDirected α r] (h : IsStrongAntichain r s)
  statement: s.Subsingleton
  proof: fun a ha b hb =>
  let ⟨_, hac, hbc⟩ := directed_of r a b
  h.eq ha hb hac hbc

中文:
定理 subsingleton
  条件: [是Directed α r] (h : IsStrongAntichain r s)
  结论: s.子单例
  证明: fun a ha b hb =>
  let ⟨_, hac, hbc⟩ := directed_of r a b
  h.eq ha hb hac hbc
-/
protected theorem subsingleton [IsDirected α r] (h : IsStrongAntichain r s) : s.Subsingleton :=
  fun a ha b hb =>
  let ⟨_, hac, hbc⟩ := directed_of r a b
  h.eq ha hb hac hbc

/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: [Std.Symm r] (hs : IsStrongAntichain r s)
  statement: IsStrongAntichain (flip r) s
  proof: fun _ ha _ hb h c => (hs ha hb h c).imp (mt <| symm_of r) (mt <| symm_of r)

中文:
定理 flip
  条件: [Std.Symm r] (hs : IsStrongAntichain r s)
  结论: IsStrongAntichain (flip r) s
  证明: fun _ ha _ hb h c => (hs ha hb h c).imp (mt <| symm_of r) (mt <| symm_of r)
-/
protected theorem flip [Std.Symm r] (hs : IsStrongAntichain r s) : IsStrongAntichain (flip r) s :=
  fun _ ha _ hb h c => (hs ha hb h c).imp (mt <| symm_of r) (mt <| symm_of r)

/--
theorem `swap` / 定理 `swap`

English:
theorem swap
  given: [Std.Symm r] (hs : IsStrongAntichain r s)
  statement: IsStrongAntichain (swap r) s
  proof: hs.flip

中文:
定理 swap
  条件: [Std.Symm r] (hs : IsStrongAntichain r s)
  结论: IsStrongAntichain (swap r) s
  证明: hs.flip

Depends on / 依赖: hs.flip
-/
theorem swap [Std.Symm r] (hs : IsStrongAntichain r s) : IsStrongAntichain (swap r) s :=
  hs.flip

/--
theorem `image` / 定理 `image`

English:
theorem image
  statement: (hs : IsStrongAntichain r s) {f : α -> β} (hf : Surjective f)
  proof: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c
  obtain ⟨c, rfl⟩ := hf c
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt <| h _ _) (mt <| h _ _)

中文:
定理 像
  结论: (hs : IsStrongAntichain r s) {f : α -> β} (hf : 满射 f)
  证明: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c
  obtain ⟨c, rfl⟩ := hf c
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt <| h _ _) (mt <| h _ _)

Depends on / 依赖: ne_of_apply_ne
-/
theorem image (hs : IsStrongAntichain r s) {f : α -> β} (hf : Surjective f)
    (h : forall a b, r' (f a) (f b) -> r a b) : IsStrongAntichain r' (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c
  obtain ⟨c, rfl⟩ := hf c
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt <| h _ _) (mt <| h _ _)

/--
theorem `preimage` / 定理 `preimage`

English:
theorem preimage
  statement: (hs : IsStrongAntichain r s) {f : β -> α} (hf : Injective f)
  proof: fun _ ha _ hb hab _ =>
  (hs ha hb (hf.ne hab) _).imp (mt <| h _ _) (mt <| h _ _)

中文:
定理 原像
  结论: (hs : IsStrongAntichain r s) {f : β -> α} (hf : 单射 f)
  证明: fun _ ha _ hb hab _ =>
  (hs ha hb (hf.ne hab) _).imp (mt <| h _ _) (mt <| h _ _)
-/
theorem preimage (hs : IsStrongAntichain r s) {f : β -> α} (hf : Injective f)
    (h : forall a b, r' a b -> r (f a) (f b)) : IsStrongAntichain r' (f ⁻¹' s) := fun _ ha _ hb hab _ =>
  (hs ha hb (hf.ne hab) _).imp (mt <| h _ _) (mt <| h _ _)

/--
theorem `_root_.isStrongAntichain_insert` / 定理 `_root_.isStrongAntichain_insert`

English:
theorem _root_.isStrongAntichain_insert
  proof: have : Std.Symm fun a b => forall c, ¬r a c ∨ ¬r b c := { symm _ _ h c := h c |>.symm }
  Set.pairwise_insert_of_symm

中文:
定理 _root_.isStrongAntichain_insert
  证明: have : Std.Symm fun a b => forall c, ¬r a c ∨ ¬r b c := { symm _ _ h c := h c |>.symm }
  Set.pairwise_insert_of_symm

Depends on / 依赖: Set.pairwise_insert_of_symm, Std.Symm, pairwise_insert_of_symm
-/
theorem _root_.isStrongAntichain_insert :
    IsStrongAntichain r (insert a s) ↔
      IsStrongAntichain r s ∧ forall ⦃b⦄, b in s -> a != b -> forall c, ¬r a c ∨ ¬r b c :=
  have : Std.Symm fun a b => forall c, ¬r a c ∨ ¬r b c := { symm _ _ h c := h c |>.symm }
  Set.pairwise_insert_of_symm

/--
theorem `insert` / 定理 `insert`

English:
theorem insert
  statement: (hs : IsStrongAntichain r s)
  proof: isStrongAntichain_insert.2 ⟨hs, h⟩

中文:
定理 insert
  结论: (hs : IsStrongAntichain r s)
  证明: isStrongAntichain_insert.2 ⟨hs, h⟩
-/
protected theorem insert (hs : IsStrongAntichain r s)
    (h : forall ⦃b⦄, b in s -> a != b -> forall c, ¬r a c ∨ ¬r b c) : IsStrongAntichain r (insert a s) :=
  isStrongAntichain_insert.2 ⟨hs, h⟩

end IsStrongAntichain

/--
theorem `Set.Subsingleton.isStrongAntichain` / 定理 `Set.Subsingleton.isStrongAntichain`

English:
theorem Set.Subsingleton.isStrongAntichain
  given: (hs : s.Subsingleton) (r : α -> α -> Prop)
  proof: hs.pairwise _

中文:
定理 集合.子单例.isStrongAntichain
  条件: (hs : s.子单例) (r : α -> α -> 命题)
  证明: hs.pairwise _

Depends on / 依赖: hs.pairwise, pairwise
-/
theorem Set.Subsingleton.isStrongAntichain (hs : s.Subsingleton) (r : α -> α -> Prop) :
    IsStrongAntichain r s :=
  hs.pairwise _

/-! ### Maximal antichains -/

/--
Definition of `IsMaxAntichain` / `IsMaxAntichain` 的定义

English:
definition IsMaxAntichain
  signature: (r : α -> α -> Prop) (s : Set α)
  body: IsAntichain r s ∧ forall ⦃t⦄, IsAntichain r t -> s subseteq t -> s = t

中文:
定义 IsMaxAntichain
  签名: (r : α -> α -> 命题) (s : 集合 α)
  定义体: IsAntichain r s ∧ forall ⦃t⦄, IsAntichain r t -> s subseteq t -> s = t

Depends on / 依赖: IsAntichain, subseteq
-/
def IsMaxAntichain (r : α -> α -> Prop) (s : Set α) : Prop :=
  IsAntichain r s ∧ forall ⦃t⦄, IsAntichain r t -> s subseteq t -> s = t

namespace IsMaxAntichain

/--
theorem `isAntichain` / 定理 `isAntichain`

English:
theorem isAntichain
  given: (h : IsMaxAntichain r s)
  statement: IsAntichain r s
  proof: h.1

中文:
定理 isAntichain
  条件: (h : IsMaxAntichain r s)
  结论: IsAntichain r s
  证明: h.1
-/
theorem isAntichain (h : IsMaxAntichain r s) : IsAntichain r s :=
  h.1

/--
theorem `image` / 定理 `image`

English:
theorem image
  given: {s : β -> β -> Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxAntichain r c)
  proof: hc.isAntichain.image _ fun _ _ => e.map_rel_iff'.mp
  right t ht hf := by
    rw [← e.coe_fn_toEquiv]; rw [← e.toEquiv.eq_preimage_iff_image_eq]; rw [← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image _ fun _ _ => e.symm.map_rel_iff.mp)
      ((e.toEquiv.subset_symm_image _ _).2 hf)

中文:
定理 像
  条件: {s : β -> β -> 命题} (e : r ≃r s) {c : 集合 α} (hc : IsMaxAntichain r c)
  证明: hc.isAntichain.image _ fun _ _ => e.map_rel_iff'.mp
  right t ht hf := by
    rw [← e.coe_fn_toEquiv]; rw [← e.toEquiv.eq_preimage_iff_image_eq]; rw [← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image _ fun _ _ => e.symm.map_rel_iff.mp)
      ((e.toEquiv.subset_symm_image _ _).2 hf)
-/
protected theorem image {s : β -> β -> Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxAntichain r c) :
    IsMaxAntichain s (e '' c) where
  left := hc.isAntichain.image _ fun _ _ => e.map_rel_iff'.mp
  right t ht hf := by
    rw [← e.coe_fn_toEquiv]; rw [← e.toEquiv.eq_preimage_iff_image_eq]; rw [← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image _ fun _ _ => e.symm.map_rel_iff.mp)
      ((e.toEquiv.subset_symm_image _ _).2 hf)

/--
theorem `isEmpty_iff` / 定理 `isEmpty_iff`

English:
theorem isEmpty_iff
  given: (h : IsMaxAntichain r s)
  statement: IsEmpty α ↔ s = ∅
  proof: by
  refine ⟨fun _ => s.eq_empty_of_isEmpty, fun h' => ?_⟩
  constructor
  intro x
  simp only [IsMaxAntichain, h', IsAntichain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsAntichain.singleton).symm

中文:
定理 isEmpty_iff
  条件: (h : IsMaxAntichain r s)
  结论: 是空 α ↔ s = ∅
  证明: by
  refine ⟨fun _ => s.eq_empty_of_isEmpty, fun h' => ?_⟩
  constructor
  intro x
  simp only [IsMaxAntichain, h', IsAntichain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsAntichain.singleton).symm
-/
protected theorem isEmpty_iff (h : IsMaxAntichain r s) : IsEmpty α ↔ s = ∅ := by
  refine ⟨fun _ => s.eq_empty_of_isEmpty, fun h' => ?_⟩
  constructor
  intro x
  simp only [IsMaxAntichain, h', IsAntichain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsAntichain.singleton).symm

/--
theorem `nonempty_iff` / 定理 `nonempty_iff`

English:
theorem nonempty_iff
  given: (h : IsMaxAntichain r s)
  statement: Nonempty α ↔ s.Nonempty
  proof: not_iff_not.mp by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff

中文:
定理 nonempty_iff
  条件: (h : IsMaxAntichain r s)
  结论: 非空 α ↔ s.非空
  证明: not_iff_not.mp by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff
-/
protected theorem nonempty_iff (h : IsMaxAntichain r s) : Nonempty α ↔ s.Nonempty :=
not_iff_not.mp by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : IsMaxAntichain r s)
  statement: IsMaxAntichain (flip r) s
  proof: ⟨h.isAntichain.flip, fun _ ht₁ ht₂ => h.2 ht₁.flip ht₂⟩

中文:
定理 symm
  条件: (h : IsMaxAntichain r s)
  结论: IsMaxAntichain (flip r) s
  证明: ⟨h.isAntichain.flip, fun _ ht₁ ht₂ => h.2 ht₁.flip ht₂⟩
-/
protected theorem symm (h : IsMaxAntichain r s) : IsMaxAntichain (flip r) s :=
  ⟨h.isAntichain.flip, fun _ ht₁ ht₂ => h.2 ht₁.flip ht₂⟩

end IsMaxAntichain

end General

/-! ### Weak antichains -/


section Pi

variable {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {s t : Set (forall i, α i)}
  {a b : forall i, α i}


@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

/--
Definition of `IsWeakAntichain` / `IsWeakAntichain` 的定义

English:
definition IsWeakAntichain
  signature: (s : Set (forall i, α i))
  body: IsAntichain (· ≺ ·) s

中文:
定义 IsWeakAntichain
  签名: (s : 集合 (对任意 i, α i))
  定义体: IsAntichain (· ≺ ·) s

Depends on / 依赖: IsAntichain
-/
def IsWeakAntichain (s : Set (forall i, α i)) : Prop :=
  IsAntichain (· ≺ ·) s

namespace IsWeakAntichain

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (hs : IsWeakAntichain s)
  statement: t subseteq s -> IsWeakAntichain t
  proof: IsAntichain.subset hs

中文:
定理 subset
  条件: (hs : IsWeakAntichain s)
  结论: t subseteq s -> IsWeakAntichain t
  证明: IsAntichain.subset hs
-/
protected theorem subset (hs : IsWeakAntichain s) : t subseteq s -> IsWeakAntichain t :=
  IsAntichain.subset hs

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (hs : IsWeakAntichain s)
  statement: a in s -> b in s -> a ≺ b -> a = b
  proof: IsAntichain.eq hs

中文:
定理 eq
  条件: (hs : IsWeakAntichain s)
  结论: a in s -> b in s -> a ≺ b -> a = b
  证明: IsAntichain.eq hs
-/
protected theorem eq (hs : IsWeakAntichain s) : a in s -> b in s -> a ≺ b -> a = b :=
  IsAntichain.eq hs

/--
theorem `insert` / 定理 `insert`

English:
theorem insert
  given: (hs : IsWeakAntichain s)
  proof: IsAntichain.insert hs

中文:
定理 insert
  条件: (hs : IsWeakAntichain s)
  证明: IsAntichain.insert hs
-/
protected theorem insert (hs : IsWeakAntichain s) :
    (forall ⦃b⦄, b in s -> a != b -> ¬b ≺ a) ->
      (forall ⦃b⦄, b in s -> a != b -> ¬a ≺ b) -> IsWeakAntichain (insert a s) :=
  IsAntichain.insert hs

end IsWeakAntichain

/--
theorem `_root_.isWeakAntichain_insert` / 定理 `_root_.isWeakAntichain_insert`

English:
theorem _root_.isWeakAntichain_insert
  proof: isAntichain_insert

中文:
定理 _root_.isWeakAntichain_insert
  证明: isAntichain_insert

Depends on / 依赖: isAntichain_insert
-/
theorem _root_.isWeakAntichain_insert :
    IsWeakAntichain (insert a s) ↔ IsWeakAntichain s ∧ forall ⦃b⦄, b in s -> a != b -> ¬a ≺ b ∧ ¬b ≺ a :=
  isAntichain_insert

/--
theorem `IsAntichain.isWeakAntichain` / 定理 `IsAntichain.isWeakAntichain`

English:
theorem IsAntichain.isWeakAntichain
  given: (hs : IsAntichain (· <= ·) s)
  statement: IsWeakAntichain s
  proof: hs.mono fun _ _ => le_of_strongLT

中文:
定理 IsAntichain.isWeakAntichain
  条件: (hs : IsAntichain (· <= ·) s)
  结论: IsWeakAntichain s
  证明: hs.mono fun _ _ => le_of_strongLT
-/
protected theorem IsAntichain.isWeakAntichain (hs : IsAntichain (· <= ·) s) : IsWeakAntichain s :=
  hs.mono fun _ _ => le_of_strongLT

/--
theorem `Set.Subsingleton.isWeakAntichain` / 定理 `Set.Subsingleton.isWeakAntichain`

English:
theorem Set.Subsingleton.isWeakAntichain
  given: (hs : s.Subsingleton)
  statement: IsWeakAntichain s
  proof: hs.isAntichain _

中文:
定理 集合.子单例.isWeakAntichain
  条件: (hs : s.子单例)
  结论: IsWeakAntichain s
  证明: hs.isAntichain _

Depends on / 依赖: hs.isAntichain, isAntichain
-/
theorem Set.Subsingleton.isWeakAntichain (hs : s.Subsingleton) : IsWeakAntichain s :=
  hs.isAntichain _

end Pi
