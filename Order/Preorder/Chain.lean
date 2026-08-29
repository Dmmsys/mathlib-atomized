/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Notation
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Directed
public import Mathlib.Order.Hom.Set

/-!
# Chains and flags

This file defines chains for an arbitrary relation and flags for an order.

## Main declarations

* `IsChain s`: A chain `s` is a set of comparable elements.
* `Flag`: The type of flags, aka maximal chains, of an order.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

@[expose] public section

assert_not_exists CompleteLattice

open Set Set.Notation

variable {α β F : Type*}

/-! ### Chains -/


section Chain

variable (r : α -> α -> Prop)

/-- In this file, we use `≺` as a local notation for any relation `r`. -/
local infixl:50 " ≺ " => r

/--
Definition of `IsChain` / `IsChain` 的定义

English:
definition IsChain
  signature: (s : Set α)
  body: s.Pairwise fun x y => x ≺ y ∨ y ≺ x

中文:
定义 IsChain
  签名: (s : Set α)
  定义体: s.Pairwise fun x y => x ≺ y ∨ y ≺ x

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_isUnit_le_isUnit, IsLocalization, IsLocalization.of_le_isUnit, Pairwise, algebraMapSubmonoid_isUnit_le_isUnit, of_le_isUnit, s.Pairwise
-/
def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x

/--
Definition of `SuperChain` / `SuperChain` 的定义

English:
definition SuperChain
  signature: (s t : Set α)
  body: IsChain r t ∧ s ⊂ t

中文:
定义 SuperChain
  签名: (s t : Set α)
  定义体: IsChain r t ∧ s ⊂ t

Depends on / 依赖: IsChain
-/
def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t

/--
Definition of `IsMaxChain` / `IsMaxChain` 的定义

English:
definition IsMaxChain
  signature: (s : Set α)
  body: IsChain r s ∧ forall ⦃t⦄, IsChain r t -> s subseteq t -> s = t

中文:
定义 IsMaxChain
  签名: (s : Set α)
  定义体: IsChain r s ∧ forall ⦃t⦄, IsChain r t -> s subseteq t -> s = t

Depends on / 依赖: IsChain, subseteq
-/
def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ forall ⦃t⦄, IsChain r t -> s subseteq t -> s = t

variable {r} {c c₁ c₂ s t : Set α} {a b x y : α}

/--
lemma `IsChain.empty` / 引理 `IsChain.empty`

English:
lemma IsChain.empty
  statement: IsChain r ∅
  proof: pairwise_empty _

中文:
引理 IsChain.empty
  结论: IsChain r ∅
  证明: pairwise_empty _

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearEquiv, Finsupp.mapRange.linearMap, IsLocalizedModule, IsLocalizedModule.iso, Localization, LocalizedModule, LocalizedModule.equivTensorProduct, classical, convert, equivTensorProduct, finsuppRight, isLocalizedModule_iff_isBaseChange, linearEquiv, linearMap, mapRange, of_linearEquiv, otimes, restrictScalars, symm.restrictScalars
-/
@[simp] lemma IsChain.empty : IsChain r ∅ := pairwise_empty _
/--
lemma `IsChain.singleton` / 引理 `IsChain.singleton`

English:
lemma IsChain.singleton
  statement: IsChain r {a}
  proof: pairwise_singleton ..

中文:
引理 IsChain.singleton
  结论: IsChain r {a}
  证明: pairwise_singleton ..
-/
@[simp] lemma IsChain.singleton : IsChain r {a} := pairwise_singleton ..

/--
theorem `Set.Subsingleton.isChain` / 定理 `Set.Subsingleton.isChain`

English:
theorem Set.Subsingleton.isChain
  given: (hs : s.Subsingleton)
  statement: IsChain r s
  proof: hs.pairwise _

中文:
定理 Set.Subsingleton.isChain
  条件: (hs : s.Subsingleton)
  结论: IsChain r s
  证明: hs.pairwise _

Depends on / 依赖: hs.pairwise, pairwise
-/
theorem Set.Subsingleton.isChain (hs : s.Subsingleton) : IsChain r s :=
  hs.pairwise _

/--
theorem `IsChain.mono` / 定理 `IsChain.mono`

English:
theorem IsChain.mono
  statement: s subseteq t -> IsChain r t -> IsChain r s
  proof: Set.Pairwise.mono

中文:
定理 IsChain.mono
  结论: s subseteq t -> IsChain r t -> IsChain r s
  证明: Set.Pairwise.mono

Depends on / 依赖: Pairwise, Set.Pairwise.mono
-/
theorem IsChain.mono : s subseteq t -> IsChain r t -> IsChain r s :=
  Set.Pairwise.mono

/--
theorem `IsChain.mono_rel` / 定理 `IsChain.mono_rel`

English:
theorem IsChain.mono_rel
  given: {r' : α -> α -> Prop} (h : IsChain r s) (h_imp : forall x y, r x y -> r' x y)
  proof: h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)

中文:
定理 IsChain.mono_rel
  条件: {r' : α -> α -> 命题} (h : IsChain r s) (h_imp : 对任意 x y, r x y -> r' x y)
  证明: h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)

Depends on / 依赖: Or.imp, h.mono, h_imp
-/
theorem IsChain.mono_rel {r' : α -> α -> Prop} (h : IsChain r s) (h_imp : forall x y, r x y -> r' x y) :
    IsChain r' s :=
  h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)

/--
theorem `IsChain.symm` / 定理 `IsChain.symm`

English:
theorem IsChain.symm
  given: (h : IsChain r s)
  statement: IsChain (flip r) s
  proof: h.mono' fun _ _ => Or.symm

中文:
定理 IsChain.symm
  条件: (h : IsChain r s)
  结论: IsChain (flip r) s
  证明: h.mono' fun _ _ => Or.symm

Depends on / 依赖: Or.symm, h.mono
-/
theorem IsChain.symm (h : IsChain r s) : IsChain (flip r) s :=
  h.mono' fun _ _ => Or.symm

/--
theorem `isChain_of_trichotomous` / 定理 `isChain_of_trichotomous`

English:
theorem isChain_of_trichotomous
  given: [Std.Trichotomous r] (s : Set α)
  statement: IsChain r s
  proof: fun a _ b _ hab => (trichotomous_of r a b).imp_right fun h => h.resolve_left hab

中文:
定理 isChain_of_trichotomous
  条件: [Std.Trichotomous r] (s : Set α)
  结论: IsChain r s
  证明: fun a _ b _ hab => (trichotomous_of r a b).imp_right fun h => h.resolve_left hab

Depends on / 依赖: h.resolve_left, imp_right, resolve_left, trichotomous_of
-/
theorem isChain_of_trichotomous [Std.Trichotomous r] (s : Set α) : IsChain r s :=
  fun a _ b _ hab => (trichotomous_of r a b).imp_right fun h => h.resolve_left hab

/--
theorem `IsChain.insert` / 定理 `IsChain.insert`

English:
theorem IsChain.insert
  given: (hs : IsChain r s) (ha : forall b in s, a != b -> a ≺ b ∨ b ≺ a)
  proof: have : Std.Symm fun a b => a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  hs.insert_of_symm ha

中文:
定理 IsChain.insert
  条件: (hs : IsChain r s) (ha : 对任意 b in s, a != b -> a ≺ b ∨ b ≺ a)
  证明: have : Std.Symm fun a b => a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  hs.insert_of_symm ha

Depends on / 依赖: IsLocalization, IsLocalization.eq_mk, RingHom, RingHom.algebraMap_toAlgebra, _iff_mul_eq, algebraMap_toAlgebra, eq_mk, map_mul
-/
protected theorem IsChain.insert (hs : IsChain r s) (ha : forall b in s, a != b -> a ≺ b ∨ b ≺ a) :
    IsChain r (insert a s) :=
  have : Std.Symm fun a b => a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  hs.insert_of_symm ha

/--
lemma `IsChain.pair` / 引理 `IsChain.pair`

English:
lemma IsChain.pair
  given: (h : r a b)
  statement: IsChain r {a, b}
  proof: IsChain.singleton.insert fun _ hb _ => .inl (eq_of_mem_singleton hb).symm.recOn ‹_›

中文:
引理 IsChain.pair
  条件: (h : r a b)
  结论: IsChain r {a, b}
  证明: IsChain.singleton.insert fun _ hb _ => .inl (eq_of_mem_singleton hb).symm.recOn ‹_›

Depends on / 依赖: IsChain, IsChain.singleton.insert, eq_of_mem_singleton, insert, singleton, symm.recOn
-/
lemma IsChain.pair (h : r a b) : IsChain r {a, b} :=
IsChain.singleton.insert fun _ hb _ => .inl (eq_of_mem_singleton hb).symm.recOn ‹_›

/--
theorem `isChain_univ_iff` / 定理 `isChain_univ_iff`

English:
theorem isChain_univ_iff
  statement: IsChain r (univ : Set α) ↔ Std.Trichotomous r
  proof: by
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h => @isChain_of_trichotomous _ _ h univ⟩
  have : a != b -> (r a b ∨ r b a) := h trivial trivial
  grind

中文:
定理 isChain_univ_iff
  结论: IsChain r (univ : Set α) ↔ Std.Trichotomous r
  证明: by
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h => @isChain_of_trichotomous _ _ h univ⟩
  have : a != b -> (r a b ∨ r b a) := h trivial trivial
  grind

Depends on / 依赖: isChain_of_trichotomous
-/
theorem isChain_univ_iff : IsChain r (univ : Set α) ↔ Std.Trichotomous r := by
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h => @isChain_of_trichotomous _ _ h univ⟩
  have : a != b -> (r a b ∨ r b a) := h trivial trivial
  grind

/--
theorem `IsChain.image_of_map_rel` / 定理 `IsChain.image_of_map_rel`

English:
theorem IsChain.image_of_map_rel
  statement: (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β)
  proof: fun _ ⟨_, ha₁, ha₂⟩ _ ⟨_, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)

中文:
定理 IsChain.image_of_map_rel
  结论: (r : α -> α -> 命题) (s : β -> β -> 命题) (f : α -> β)
  证明: fun _ ⟨_, ha₁, ha₂⟩ _ ⟨_, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)

Depends on / 依赖: ne_of_apply_ne
-/
theorem IsChain.image_of_map_rel (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β)
    (h : forall x y, r x y -> s (f x) (f y)) {c : Set α} (hrc : IsChain r c) : IsChain s (f '' c) :=
  fun _ ⟨_, ha₁, ha₂⟩ _ ⟨_, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)

/--
theorem `IsChain.preimage` / 定理 `IsChain.preimage`

English:
theorem IsChain.preimage
  statement: (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β)
  proof: by
  intro _ ha _ hb hne
  have := hrc ha hb (fun h => hne (hf h))
  grind

中文:
定理 IsChain.preimage
  结论: (r : α -> α -> 命题) (s : β -> β -> 命题) (f : α -> β)
  证明: by
  intro _ ha _ hb hne
  have := hrc ha hb (fun h => hne (hf h))
  grind
-/
theorem IsChain.preimage (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β)
    (hf : Function.Injective f) (h : forall x y, s (f x) (f y) -> r x y) {c : Set β} (hrc : IsChain s c) :
    IsChain r (f ⁻¹' c) := by
  intro _ ha _ hb hne
  have := hrc ha hb (fun h => hne (hf h))
  grind

/--
lemma `isChain_union` / 引理 `isChain_union`

English:
lemma isChain_union
  given: {s t : Set α}
  proof: by
  have : Std.Symm fun a b => a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  rw [IsChain]; rw [IsChain]; rw [IsChain]; rw [pairwise_union_of_symm]

中文:
引理 isChain_union
  条件: {s t : Set α}
  证明: by
  have : Std.Symm fun a b => a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  rw [IsChain]; rw [IsChain]; rw [IsChain]; rw [pairwise_union_of_symm]

Depends on / 依赖: IsChain, Or.symm, Std.Symm, pairwise_union_of_symm
-/
lemma isChain_union {s t : Set α} :
    IsChain r (s union t) ↔ IsChain r s ∧ IsChain r t ∧ forall a in s, forall b in t, a != b -> r a b ∨ r b a := by
  have : Std.Symm fun a b => a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  rw [IsChain]; rw [IsChain]; rw [IsChain]; rw [pairwise_union_of_symm]

/--
lemma `Monotone.isChain_image` / 引理 `Monotone.isChain_image`

English:
lemma Monotone.isChain_image
  statement: [Preorder α] [Preorder β] {s : Set α} {f : α -> β}
  proof: hs.image_of_map_rel _ _ _ (fun _ _ a => hf a)

中文:
引理 Monotone.isChain_image
  结论: [Preorder α] [Preorder β] {s : Set α} {f : α -> β}
  证明: hs.image_of_map_rel _ _ _ (fun _ _ a => hf a)

Depends on / 依赖: hs.image_of_map_rel, image_of_map_rel
-/
lemma Monotone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α -> β}
    (hf : Monotone f) (hs : IsChain (· <= ·) s) : IsChain (· <= ·) (f '' s) :=
  hs.image_of_map_rel _ _ _ (fun _ _ a => hf a)

/--
theorem `Monotone.isChain_range` / 定理 `Monotone.isChain_range`

English:
theorem Monotone.isChain_range
  given: [LinearOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: by
  rw [← image_univ]
  exact hf.isChain_image (isChain_of_trichotomous _)

中文:
定理 Monotone.isChain_range
  条件: [LinearOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: by
  rw [← image_univ]
  exact hf.isChain_image (isChain_of_trichotomous _)

Depends on / 依赖: hf.isChain_image, image_univ, isChain_image, isChain_of_trichotomous
-/
theorem Monotone.isChain_range [LinearOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    IsChain (· <= ·) (range f) := by
  rw [← image_univ]
  exact hf.isChain_image (isChain_of_trichotomous _)

/--
lemma `Antitone.isChain_image` / 引理 `Antitone.isChain_image`

English:
lemma Antitone.isChain_image
  statement: [Preorder α] [Preorder β] {s : Set α} {f : α -> β}
  proof: hf.dual_left.isChain_image hs.symm

中文:
引理 Antitone.isChain_image
  结论: [Preorder α] [Preorder β] {s : Set α} {f : α -> β}
  证明: hf.dual_left.isChain_image hs.symm

Depends on / 依赖: dual_left, hf.dual_left.isChain_image, hs.symm, isChain_image
-/
lemma Antitone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α -> β}
    (hf : Antitone f) (hs : IsChain (· <= ·) s) : IsChain (· <= ·) (f '' s) :=
  hf.dual_left.isChain_image hs.symm

/--
theorem `Antitone.isChain_range` / 定理 `Antitone.isChain_range`

English:
theorem Antitone.isChain_range
  given: [LinearOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.isChain_range

中文:
定理 Antitone.isChain_range
  条件: [LinearOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.isChain_range

Depends on / 依赖: dual_left, hf.dual_left.isChain_range, isChain_range
-/
theorem Antitone.isChain_range [LinearOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    IsChain (· <= ·) (range f) :=
  hf.dual_left.isChain_range

/--
theorem `IsChain.lt_of_le` / 定理 `IsChain.lt_of_le`

English:
theorem IsChain.lt_of_le
  given: [PartialOrder α] {s : Set α} (h : IsChain (· <= ·) s)
  proof: fun _a ha _b hb hne =>
  (h ha hb hne).imp hne.lt_of_le hne.lt_of_le'

中文:
定理 IsChain.lt_of_le
  条件: [PartialOrder α] {s : Set α} (h : IsChain (· <= ·) s)
  证明: fun _a ha _b hb hne =>
  (h ha hb hne).imp hne.lt_of_le hne.lt_of_le'
-/
theorem IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsChain (· <= ·) s) :
    IsChain (· < ·) s := fun _a ha _b hb hne =>
  (h ha hb hne).imp hne.lt_of_le hne.lt_of_le'

/--
theorem `IsChain.diff` / 定理 `IsChain.diff`

English:
theorem IsChain.diff
  given: {s t : Set α} (h : IsChain r s)
  statement: IsChain r (s \ t)
  proof: h.mono Set.sdiff_subset

中文:
定理 IsChain.diff
  条件: {s t : Set α} (h : IsChain r s)
  结论: IsChain r (s \ t)
  证明: h.mono Set.sdiff_subset
-/
@[simp] protected theorem IsChain.diff {s t : Set α} (h : IsChain r s) : IsChain r (s \ t) :=
  h.mono Set.sdiff_subset

/--
theorem `isChain_preimage_subtypeVal` / 定理 `isChain_preimage_subtypeVal`

English:
theorem isChain_preimage_subtypeVal
  given: (s t : Set α)
  proof: by
  simp [IsChain, Set.Pairwise]

中文:
定理 isChain_preimage_subtypeVal
  条件: (s t : Set α)
  证明: by
  simp [IsChain, Set.Pairwise]

Depends on / 依赖: IsChain, Pairwise, Set.Pairwise
-/
theorem isChain_preimage_subtypeVal (s t : Set α) :
    @IsChain ↑s (r · ·) (s ↓inter t) ↔ IsChain r (s inter t) := by
  simp [IsChain, Set.Pairwise]

/--
theorem `isChain_coe_univ_iff` / 定理 `isChain_coe_univ_iff`

English:
theorem isChain_coe_univ_iff
  given: {s : Set α}
  statement: @IsChain ↑s (r · ·) univ ↔ IsChain r s
  proof: by
  simpa using isChain_preimage_subtypeVal s univ

中文:
定理 isChain_coe_univ_iff
  条件: {s : Set α}
  结论: @IsChain ↑s (r · ·) univ ↔ IsChain r s
  证明: by
  simpa using isChain_preimage_subtypeVal s univ

Depends on / 依赖: isChain_preimage_subtypeVal
-/
theorem isChain_coe_univ_iff {s : Set α} : @IsChain ↑s (r · ·) univ ↔ IsChain r s := by
  simpa using isChain_preimage_subtypeVal s univ

section Rel

variable {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set α}

/--
theorem `IsChain.image` / 定理 `IsChain.image`

English:
theorem IsChain.image
  given: [FunLike F α β] [RelHomClass F r r'] (hs : IsChain r s) (φ : F)
  proof: hs.image_of_map_rel _ _ _ (fun _ _ h => map_rel φ h)

@[deprecated IsChain.image (since := "2026-02-26")]

中文:
定理 IsChain.image
  条件: [FunLike F α β] [RelHomClass F r r'] (hs : IsChain r s) (φ : F)
  证明: hs.image_of_map_rel _ _ _ (fun _ _ h => map_rel φ h)

@[deprecated IsChain.image (since := "2026-02-26")]

Depends on / 依赖: hs.image_of_map_rel, image_of_map_rel, map_rel
-/
theorem IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : IsChain r s) (φ : F) :
    IsChain r' (φ '' s) :=
  hs.image_of_map_rel _ _ _ (fun _ _ h => map_rel φ h)

@[deprecated IsChain.image (since := "2026-02-26")]
/--
theorem `IsChain.image_relEmbedding` / 定理 `IsChain.image_relEmbedding`

English:
theorem IsChain.image_relEmbedding
  given: (hs : IsChain r s) (φ : r ↪r r')
  statement: IsChain r' (φ '' s)
  proof: hs.image _

中文:
定理 IsChain.image_relEmbedding
  条件: (hs : IsChain r s) (φ : r ↪r r')
  结论: IsChain r' (φ '' s)
  证明: hs.image _

Depends on / 依赖: hs.image
-/
theorem IsChain.image_relEmbedding (hs : IsChain r s) (φ : r ↪r r') : IsChain r' (φ '' s) :=
  hs.image _

/--
theorem `IsChain.preimage_relEmbedding` / 定理 `IsChain.preimage_relEmbedding`

English:
theorem IsChain.preimage_relEmbedding
  given: {t : Set β} (ht : IsChain r' t) (φ : r ↪r r')
  proof: ht.preimage _ _ _ φ.injective (fun _ _ h => φ.map_rel_iff.mp h)

@[deprecated IsChain.image (since := "2026-02-26")]

中文:
定理 IsChain.preimage_relEmbedding
  条件: {t : Set β} (ht : IsChain r' t) (φ : r ↪r r')
  证明: ht.preimage _ _ _ φ.injective (fun _ _ h => φ.map_rel_iff.mp h)

@[deprecated IsChain.image (since := "2026-02-26")]

Depends on / 依赖: ht.preimage, injective, map_rel_iff, map_rel_iff.mp, preimage
-/
theorem IsChain.preimage_relEmbedding {t : Set β} (ht : IsChain r' t) (φ : r ↪r r') :
    IsChain r (φ ⁻¹' t) :=
  ht.preimage _ _ _ φ.injective (fun _ _ h => φ.map_rel_iff.mp h)

@[deprecated IsChain.image (since := "2026-02-26")]
/--
theorem `IsChain.image_relIso` / 定理 `IsChain.image_relIso`

English:
theorem IsChain.image_relIso
  given: (hs : IsChain r s) (φ : r ≃r r')
  statement: IsChain r' (φ '' s)
  proof: hs.image φ.toRelEmbedding

中文:
定理 IsChain.image_relIso
  条件: (hs : IsChain r s) (φ : r ≃r r')
  结论: IsChain r' (φ '' s)
  证明: hs.image φ.toRelEmbedding

Depends on / 依赖: hs.image, toRelEmbedding
-/
theorem IsChain.image_relIso (hs : IsChain r s) (φ : r ≃r r') : IsChain r' (φ '' s) :=
  hs.image φ.toRelEmbedding

/--
theorem `IsChain.preimage_relIso` / 定理 `IsChain.preimage_relIso`

English:
theorem IsChain.preimage_relIso
  given: {t : Set β} (hs : IsChain r' t) (φ : r ≃r r')
  proof: hs.preimage_relEmbedding φ.toRelEmbedding

中文:
定理 IsChain.preimage_relIso
  条件: {t : Set β} (hs : IsChain r' t) (φ : r ≃r r')
  证明: hs.preimage_relEmbedding φ.toRelEmbedding

Depends on / 依赖: hs.preimage_relEmbedding, preimage_relEmbedding, toRelEmbedding
-/
theorem IsChain.preimage_relIso {t : Set β} (hs : IsChain r' t) (φ : r ≃r r') :
    IsChain r (φ ⁻¹' t) :=
  hs.preimage_relEmbedding φ.toRelEmbedding

/--
theorem `IsChain.image_relEmbedding_iff` / 定理 `IsChain.image_relEmbedding_iff`

English:
theorem IsChain.image_relEmbedding_iff
  given: {φ : r ↪r r'}
  statement: IsChain r' (φ '' s) ↔ IsChain r s
  proof: ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h => h.image φ⟩

中文:
定理 IsChain.image_relEmbedding_iff
  条件: {φ : r ↪r r'}
  结论: IsChain r' (φ '' s) ↔ IsChain r s
  证明: ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h => h.image φ⟩

Depends on / 依赖: h.image, h.preimage_relEmbedding, injective, injective.preimage_image, preimage_image, preimage_relEmbedding
-/
theorem IsChain.image_relEmbedding_iff {φ : r ↪r r'} : IsChain r' (φ '' s) ↔ IsChain r s :=
  ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h => h.image φ⟩

/--
theorem `IsChain.image_relIso_iff` / 定理 `IsChain.image_relIso_iff`

English:
theorem IsChain.image_relIso_iff
  given: {φ : r ≃r r'}
  statement: IsChain r' (φ '' s) ↔ IsChain r s
  proof: @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

@[deprecated IsChain.image (since := "2026-02-26")]

中文:
定理 IsChain.image_relIso_iff
  条件: {φ : r ≃r r'}
  结论: IsChain r' (φ '' s) ↔ IsChain r s
  证明: @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

@[deprecated IsChain.image (since := "2026-02-26")]

Depends on / 依赖: image_relEmbedding_iff
-/
theorem IsChain.image_relIso_iff {φ : r ≃r r'} : IsChain r' (φ '' s) ↔ IsChain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

@[deprecated IsChain.image (since := "2026-02-26")]
/--
theorem `IsChain.image_embedding` / 定理 `IsChain.image_embedding`

English:
theorem IsChain.image_embedding
  given: [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ↪o β)
  proof: image hs _

中文:
定理 IsChain.image_embedding
  条件: [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ↪o β)
  证明: image hs _
-/
theorem IsChain.image_embedding [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ↪o β) :
    IsChain (· <= ·) (φ '' s) :=
  image hs _

/--
theorem `IsChain.preimage_embedding` / 定理 `IsChain.preimage_embedding`

English:
theorem IsChain.preimage_embedding
  given: [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (φ : α ↪o β)
  proof: preimage_relEmbedding ht _

中文:
定理 IsChain.preimage_embedding
  条件: [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (φ : α ↪o β)
  证明: preimage_relEmbedding ht _

Depends on / 依赖: preimage_relEmbedding
-/
theorem IsChain.preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (φ : α ↪o β) :
    IsChain (· <= ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _

/--
theorem `IsChain.image_embedding_iff` / 定理 `IsChain.image_embedding_iff`

English:
theorem IsChain.image_embedding_iff
  given: [LE α] [LE β] {φ : α ↪o β}
  proof: image_relEmbedding_iff

@[deprecated IsChain.image (since := "2026-02-26")]

中文:
定理 IsChain.image_embedding_iff
  条件: [LE α] [LE β] {φ : α ↪o β}
  证明: image_relEmbedding_iff

@[deprecated IsChain.image (since := "2026-02-26")]

Depends on / 依赖: image_relEmbedding_iff
-/
theorem IsChain.image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsChain (· <= ·) (φ '' s) ↔ IsChain (· <= ·) s :=
  image_relEmbedding_iff

@[deprecated IsChain.image (since := "2026-02-26")]
/--
theorem `IsChain.image_iso` / 定理 `IsChain.image_iso`

English:
theorem IsChain.image_iso
  given: [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ≃o β)
  proof: image hs _

中文:
定理 IsChain.image_iso
  条件: [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ≃o β)
  证明: image hs _
-/
theorem IsChain.image_iso [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ≃o β) :
    IsChain (· <= ·) (φ '' s) :=
  image hs _

/--
theorem `IsChain.image_iso_iff` / 定理 `IsChain.image_iso_iff`

English:
theorem IsChain.image_iso_iff
  given: [LE α] [LE β] {φ : α ≃o β}
  proof: image_relEmbedding_iff

中文:
定理 IsChain.image_iso_iff
  条件: [LE α] [LE β] {φ : α ≃o β}
  证明: image_relEmbedding_iff

Depends on / 依赖: image_relEmbedding_iff
-/
theorem IsChain.image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsChain (· <= ·) (φ '' s) ↔ IsChain (· <= ·) s :=
  image_relEmbedding_iff

/--
theorem `IsChain.preimage_iso` / 定理 `IsChain.preimage_iso`

English:
theorem IsChain.preimage_iso
  given: [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (φ : α ≃o β)
  proof: preimage_relEmbedding ht _

中文:
定理 IsChain.preimage_iso
  条件: [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (φ : α ≃o β)
  证明: preimage_relEmbedding ht _

Depends on / 依赖: preimage_relEmbedding
-/
theorem IsChain.preimage_iso [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (φ : α ≃o β) :
    IsChain (· <= ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _

/--
theorem `IsChain.preimage_iso_iff` / 定理 `IsChain.preimage_iso_iff`

English:
theorem IsChain.preimage_iso_iff
  given: [LE α] [LE β] {t : Set β} {φ : α ≃o β}
  proof: ⟨fun h => (φ.image_preimage t).subst (h.image φ), fun h => h.preimage_iso _⟩

中文:
定理 IsChain.preimage_iso_iff
  条件: [LE α] [LE β] {t : Set β} {φ : α ≃o β}
  证明: ⟨fun h => (φ.image_preimage t).subst (h.image φ), fun h => h.preimage_iso _⟩

Depends on / 依赖: h.image, h.preimage_iso, image_preimage, preimage_iso
-/
theorem IsChain.preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsChain (· <= ·) (φ ⁻¹' t) ↔ IsChain (· <= ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image φ), fun h => h.preimage_iso _⟩

end Rel

section Total

variable [Std.Refl r]

/--
theorem `IsChain.total` / 定理 `IsChain.total`

English:
theorem IsChain.total
  given: (h : IsChain r s) (hx : x in s) (hy : y in s)
  statement: x ≺ y ∨ y ≺ x
  proof: (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)

中文:
定理 IsChain.total
  条件: (h : IsChain r s) (hx : x in s) (hy : y in s)
  结论: x ≺ y ∨ y ≺ x
  证明: (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)

Depends on / 依赖: Or.inl, eq_or_ne
-/
theorem IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in s) : x ≺ y ∨ y ≺ x :=
  (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)

/--
theorem `IsChain.directedOn` / 定理 `IsChain.directedOn`

English:
theorem IsChain.directedOn
  given: (H : IsChain r s)
  statement: DirectedOn r s
  proof: fun x hx y hy =>
  ((H.total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩

中文:
定理 IsChain.directedOn
  条件: (H : IsChain r s)
  结论: DirectedOn r s
  证明: fun x hx y hy =>
  ((H.total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩
-/
theorem IsChain.directedOn (H : IsChain r s) : DirectedOn r s := fun x hx y hy =>
  ((H.total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩

/--
theorem `IsChain.directed` / 定理 `IsChain.directed`

English:
theorem IsChain.directed
  given: {f : β -> α} {c : Set β} (h : IsChain (f ⁻¹'o r) c)
  proof: fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    (by_cases fun hab : a = b => by
      simp only [hab, exists_prop, and_self_iff, Subtype.exists]
      exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩

中文:
定理 IsChain.directed
  条件: {f : β -> α} {c : Set β} (h : IsChain (f ⁻¹'o r) c)
  证明: fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    (by_cases fun hab : a = b => by
      simp only [hab, exists_prop, and_self_iff, Subtype.exists]
      exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩
-/
protected theorem IsChain.directed {f : β -> α} {c : Set β} (h : IsChain (f ⁻¹'o r) c) :
    Directed r fun x : { a : β // a in c } => f x :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    (by_cases fun hab : a = b => by
      simp only [hab, exists_prop, and_self_iff, Subtype.exists]
      exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩

/--
theorem `IsChain.exists3` / 定理 `IsChain.exists3`

English:
theorem IsChain.exists3
  statement: (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a in s) (mem2 : b in s)
  proof: by
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) a mem1 b mem2 with ⟨z, mem4, H1, H2⟩
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩
  exact ⟨z', mem5, _root_.trans H1 H3, _root_.trans H2 H3, H4⟩

中文:
定理 IsChain.exists3
  结论: (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a in s) (mem2 : b in s)
  证明: by
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) a mem1 b mem2 with ⟨z, mem4, H1, H2⟩
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩
  exact ⟨z', mem5, _root_.trans H1 H3, _root_.trans H2 H3, H4⟩

Depends on / 依赖: IsChain, IsChain.directed, _root_, _root_.trans, directed, directedOn_iff_directed, directedOn_iff_directed.mpr, hchain
-/
theorem IsChain.exists3 (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a in s) (mem2 : b in s)
    (mem3 : c in s) : exists (z : _) (_ : z in s), r a z ∧ r b z ∧ r c z := by
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) a mem1 b mem2 with ⟨z, mem4, H1, H2⟩
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩
  exact ⟨z', mem5, _root_.trans H1 H3, _root_.trans H2 H3, H4⟩

end Total

/-- A chain in a partial order is a linear order. -/
@[implicit_reducible]
/--
Definition of `IsChain.linearOrder` / `IsChain.linearOrder` 的定义

English:
definition IsChain.linearOrder
  signature: [PartialOrder α] [DecidableLE α] {s : Set α} (hs : IsChain (· <= ·) s)
  body: by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact hs.total ha hb
  toDecidableLE x y := inferInstanceAs (Decidable (x.1 <= y.1))

中文:
定义 IsChain.linearOrder
  签名: [PartialOrder α] [DecidableLE α] {s : Set α} (hs : IsChain (· <= ·) s)
  定义体: by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact hs.total ha hb
  toDecidableLE x y := inferInstanceAs (Decidable (x.1 <= y.1))

Depends on / 依赖: Decidable, hs.total, toDecidableLE
-/
def IsChain.linearOrder [PartialOrder α] [DecidableLE α] {s : Set α} (hs : IsChain (· <= ·) s) :
    LinearOrder s where
  le_total := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact hs.total ha hb
  toDecidableLE x y := inferInstanceAs (Decidable (x.1 <= y.1))

/--
lemma `IsChain.le_of_not_gt` / 引理 `IsChain.le_of_not_gt`

English:
lemma IsChain.le_of_not_gt
  statement: [Preorder α] (hs : IsChain (· <= ·) s)
  proof: by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_ge, h'] using h

中文:
引理 IsChain.le_of_not_gt
  结论: [Preorder α] (hs : IsChain (· <= ·) s)
  证明: by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_ge, h'] using h

Depends on / 依赖: hs.total, lt_iff_le_not_ge
-/
lemma IsChain.le_of_not_gt [Preorder α] (hs : IsChain (· <= ·) s)
    {x y : α} (hx : x in s) (hy : y in s) (h : ¬ x < y) : y <= x := by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_ge, h'] using h

/--
lemma `IsChain.not_lt` / 引理 `IsChain.not_lt`

English:
lemma IsChain.not_lt
  statement: [Preorder α] (hs : IsChain (· <= ·) s)
  proof: ⟨(hs.le_of_not_gt hx hy ·), fun h h' => h'.not_ge h⟩

中文:
引理 IsChain.not_lt
  结论: [Preorder α] (hs : IsChain (· <= ·) s)
  证明: ⟨(hs.le_of_not_gt hx hy ·), fun h h' => h'.not_ge h⟩

Depends on / 依赖: hs.le_of_not_gt, le_of_not_gt, not_ge
-/
lemma IsChain.not_lt [Preorder α] (hs : IsChain (· <= ·) s)
    {x y : α} (hx : x in s) (hy : y in s) : ¬ x < y ↔ y <= x :=
  ⟨(hs.le_of_not_gt hx hy ·), fun h h' => h'.not_ge h⟩

/--
lemma `IsChain.lt_of_not_ge` / 引理 `IsChain.lt_of_not_ge`

English:
lemma IsChain.lt_of_not_ge
  statement: [Preorder α] (hs : IsChain (· <= ·) s)
  proof: (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_ge · h)

中文:
引理 IsChain.lt_of_not_ge
  结论: [Preorder α] (hs : IsChain (· <= ·) s)
  证明: (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_ge · h)

Depends on / 依赖: hs.total, lt_of_le_not_ge
-/
lemma IsChain.lt_of_not_ge [Preorder α] (hs : IsChain (· <= ·) s)
    {x y : α} (hx : x in s) (hy : y in s) (h : ¬ x <= y) : y < x :=
  (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_ge · h)

/--
lemma `IsChain.not_le` / 引理 `IsChain.not_le`

English:
lemma IsChain.not_le
  statement: [Preorder α] (hs : IsChain (· <= ·) s)
  proof: ⟨(hs.lt_of_not_ge hx hy ·), fun h h' => h'.not_gt h⟩

中文:
引理 IsChain.not_le
  结论: [Preorder α] (hs : IsChain (· <= ·) s)
  证明: ⟨(hs.lt_of_not_ge hx hy ·), fun h h' => h'.not_gt h⟩

Depends on / 依赖: hs.lt_of_not_ge, lt_of_not_ge, not_gt
-/
lemma IsChain.not_le [Preorder α] (hs : IsChain (· <= ·) s)
    {x y : α} (hx : x in s) (hy : y in s) : ¬ x <= y ↔ y < x :=
  ⟨(hs.lt_of_not_ge hx hy ·), fun h h' => h'.not_gt h⟩

/--
theorem `IsMaxChain.isChain` / 定理 `IsMaxChain.isChain`

English:
theorem IsMaxChain.isChain
  given: (h : IsMaxChain r s)
  statement: IsChain r s
  proof: h.1

中文:
定理 IsMaxChain.isChain
  条件: (h : IsMaxChain r s)
  结论: IsChain r s
  证明: h.1
-/
theorem IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r s :=
  h.1

/--
theorem `IsMaxChain.not_superChain` / 定理 `IsMaxChain.not_superChain`

English:
theorem IsMaxChain.not_superChain
  given: (h : IsMaxChain r s)
  statement: ¬SuperChain r s t
  proof: fun ht =>
ht.2.ne h.2 ht.1 ht.2.1

中文:
定理 IsMaxChain.not_superChain
  条件: (h : IsMaxChain r s)
  结论: ¬SuperChain r s t
  证明: fun ht =>
ht.2.ne h.2 ht.1 ht.2.1
-/
theorem IsMaxChain.not_superChain (h : IsMaxChain r s) : ¬SuperChain r s t := fun ht =>
ht.2.ne h.2 ht.1 ht.2.1

/--
theorem `IsMaxChain.bot_mem` / 定理 `IsMaxChain.bot_mem`

English:
theorem IsMaxChain.bot_mem
  given: [LE α] [OrderBot α] (h : IsMaxChain (· <= ·) s)
  statement: ⊥ in s
  proof: (h.2 (h.1.insert fun _ _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _

中文:
定理 IsMaxChain.bot_mem
  条件: [LE α] [OrderBot α] (h : IsMaxChain (· <= ·) s)
  结论: ⊥ in s
  证明: (h.2 (h.1.insert fun _ _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _

Depends on / 依赖: Or.inl, bot_le, insert, mem_insert, subset_insert
-/
theorem IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxChain (· <= ·) s) : ⊥ in s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _

/--
theorem `IsMaxChain.top_mem` / 定理 `IsMaxChain.top_mem`

English:
theorem IsMaxChain.top_mem
  given: [LE α] [OrderTop α] (h : IsMaxChain (· <= ·) s)
  statement: ⊤ in s
  proof: (h.2 (h.1.insert fun _ _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _

中文:
定理 IsMaxChain.top_mem
  条件: [LE α] [OrderTop α] (h : IsMaxChain (· <= ·) s)
  结论: ⊤ in s
  证明: (h.2 (h.1.insert fun _ _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _

Depends on / 依赖: Or.inr, insert, le_top, mem_insert, subset_insert
-/
theorem IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxChain (· <= ·) s) : ⊤ in s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _

/--
lemma `IsMaxChain.image` / 引理 `IsMaxChain.image`

English:
lemma IsMaxChain.image
  given: {s : β -> β -> Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxChain r c)
  proof: hc.isChain.image e
  right t ht hf := by
    rw [← e.coe_fn_toEquiv]; rw [← e.toEquiv.eq_preimage_iff_image_eq]; rw [← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image e.symm) ((e.toEquiv.subset_symm_image _ _).2 hf)

中文:
引理 IsMaxChain.image
  条件: {s : β -> β -> 命题} (e : r ≃r s) {c : Set α} (hc : IsMaxChain r c)
  证明: hc.isChain.image e
  right t ht hf := by
    rw [← e.coe_fn_toEquiv]; rw [← e.toEquiv.eq_preimage_iff_image_eq]; rw [← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image e.symm) ((e.toEquiv.subset_symm_image _ _).2 hf)

Depends on / 依赖: hc.isChain.image, isChain
-/
lemma IsMaxChain.image {s : β -> β -> Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxChain r c) :
    IsMaxChain s (e '' c) where
  left := hc.isChain.image e
  right t ht hf := by
    rw [← e.coe_fn_toEquiv]; rw [← e.toEquiv.eq_preimage_iff_image_eq]; rw [← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image e.symm) ((e.toEquiv.subset_symm_image _ _).2 hf)

/--
theorem `IsMaxChain.isEmpty_iff` / 定理 `IsMaxChain.isEmpty_iff`

English:
theorem IsMaxChain.isEmpty_iff
  given: (h : IsMaxChain r s)
  statement: IsEmpty α ↔ s = ∅
  proof: by
  refine ⟨fun _ => s.eq_empty_of_isEmpty, fun h' => ?_⟩
  constructor
  intro x
  simp only [IsMaxChain, h', IsChain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsChain.singleton).symm

中文:
定理 IsMaxChain.isEmpty_iff
  条件: (h : IsMaxChain r s)
  结论: IsEmpty α ↔ s = ∅
  证明: by
  refine ⟨fun _ => s.eq_empty_of_isEmpty, fun h' => ?_⟩
  constructor
  intro x
  simp only [IsMaxChain, h', IsChain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsChain.singleton).symm
-/
protected theorem IsMaxChain.isEmpty_iff (h : IsMaxChain r s) : IsEmpty α ↔ s = ∅ := by
  refine ⟨fun _ => s.eq_empty_of_isEmpty, fun h' => ?_⟩
  constructor
  intro x
  simp only [IsMaxChain, h', IsChain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsChain.singleton).symm

/--
theorem `IsMaxChain.nonempty_iff` / 定理 `IsMaxChain.nonempty_iff`

English:
theorem IsMaxChain.nonempty_iff
  given: (h : IsMaxChain r s)
  statement: Nonempty α ↔ s.Nonempty
  proof: not_iff_not.mp by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff

中文:
定理 IsMaxChain.nonempty_iff
  条件: (h : IsMaxChain r s)
  结论: Nonempty α ↔ s.Nonempty
  证明: not_iff_not.mp by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff
-/
protected theorem IsMaxChain.nonempty_iff (h : IsMaxChain r s) : Nonempty α ↔ s.Nonempty :=
not_iff_not.mp by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff

/--
theorem `IsMaxChain.symm` / 定理 `IsMaxChain.symm`

English:
theorem IsMaxChain.symm
  given: (h : IsMaxChain r s)
  statement: IsMaxChain (flip r) s
  proof: ⟨h.isChain.symm, fun _ ht₁ ht₂ => h.2 ht₁.symm ht₂⟩

中文:
定理 IsMaxChain.symm
  条件: (h : IsMaxChain r s)
  结论: IsMaxChain (flip r) s
  证明: ⟨h.isChain.symm, fun _ ht₁ ht₂ => h.2 ht₁.symm ht₂⟩

Depends on / 依赖: h.isChain.symm, isChain
-/
theorem IsMaxChain.symm (h : IsMaxChain r s) : IsMaxChain (flip r) s :=
  ⟨h.isChain.symm, fun _ ht₁ ht₂ => h.2 ht₁.symm ht₂⟩

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `SuccChain` / `SuccChain` 的定义

English:
definition SuccChain
  signature: (r : α -> α -> Prop) (s : Set α)
  body: if h : exists t, IsChain r s ∧ SuperChain r s t then h.choose else s

中文:
定义 SuccChain
  签名: (r : α -> α -> 命题) (s : Set α)
  定义体: if h : exists t, IsChain r s ∧ SuperChain r s t then h.choose else s

Depends on / 依赖: IsChain, SuperChain, h.choose
-/
noncomputable def SuccChain (r : α -> α -> Prop) (s : Set α) : Set α :=
  if h : exists t, IsChain r s ∧ SuperChain r s t then h.choose else s

/--
theorem `succChain_spec` / 定理 `succChain_spec`

English:
theorem succChain_spec
  given: (h : exists t, IsChain r s ∧ SuperChain r s t)
  proof: by
  have : IsChain r s ∧ SuperChain r s h.choose := h.choose_spec
  simpa [SuccChain, dif_pos, exists_and_left.mp h] using this.2

中文:
定理 succChain_spec
  条件: (h : 存在 t, IsChain r s ∧ SuperChain r s t)
  证明: by
  have : IsChain r s ∧ SuperChain r s h.choose := h.choose_spec
  simpa [SuccChain, dif_pos, exists_and_left.mp h] using this.2

Depends on / 依赖: IsChain, SuccChain, SuperChain, choose_spec, dif_pos, exists_and_left, exists_and_left.mp, h.choose, h.choose_spec
-/
theorem succChain_spec (h : exists t, IsChain r s ∧ SuperChain r s t) :
    SuperChain r s (SuccChain r s) := by
  have : IsChain r s ∧ SuperChain r s h.choose := h.choose_spec
  simpa [SuccChain, dif_pos, exists_and_left.mp h] using this.2

/--
theorem `IsChain.succ` / 定理 `IsChain.succ`

English:
theorem IsChain.succ
  given: (hs : IsChain r s)
  statement: IsChain r (SuccChain r s)
  proof: by
  if h : exists t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).1
  else
    rw [exists_and_left] at h
    simpa [SuccChain, dif_neg, h] using hs

中文:
定理 IsChain.succ
  条件: (hs : IsChain r s)
  结论: IsChain r (SuccChain r s)
  证明: by
  if h : exists t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).1
  else
    rw [exists_and_left] at h
    simpa [SuccChain, dif_neg, h] using hs

Depends on / 依赖: IsChain, SuccChain, SuperChain, dif_neg, exists_and_left, succChain_spec
-/
theorem IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s) := by
  if h : exists t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).1
  else
    rw [exists_and_left] at h
    simpa [SuccChain, dif_neg, h] using hs

/--
theorem `IsChain.superChain_succChain` / 定理 `IsChain.superChain_succChain`

English:
theorem IsChain.superChain_succChain
  given: (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s)
  proof: by
  simp only [IsMaxChain, _root_.not_and, not_forall, exists_prop] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂ hs₁
  exact succChain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩

中文:
定理 IsChain.superChain_succChain
  条件: (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s)
  证明: by
  simp only [IsMaxChain, _root_.not_and, not_forall, exists_prop] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂ hs₁
  exact succChain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩

Depends on / 依赖: IsMaxChain, _root_, _root_.not_and, exists_prop, not_and, not_forall, ssubset_iff_subset_ne, succChain_spec
-/
theorem IsChain.superChain_succChain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) :
    SuperChain r s (SuccChain r s) := by
  simp only [IsMaxChain, _root_.not_and, not_forall, exists_prop] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂ hs₁
  exact succChain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩

/--
theorem `subset_succChain` / 定理 `subset_succChain`

English:
theorem subset_succChain
  statement: s subseteq SuccChain r s
  proof: by
  if h : exists t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).2.1
  else
    simp [SuccChain, h]

中文:
定理 subset_succChain
  结论: s subseteq SuccChain r s
  证明: by
  if h : exists t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).2.1
  else
    simp [SuccChain, h]

Depends on / 依赖: IsChain, SuccChain, SuperChain, succChain_spec
-/
theorem subset_succChain : s subseteq SuccChain r s := by
  if h : exists t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).2.1
  else
    simp [SuccChain, h]

end Chain

/-! ### Flags -/


/--
Definition of `Flag` / `Flag` 的定义

English:
structure Flag
  parameters: (α : Type*) [LE α]
  axioms and operations (3):
    - carrier : Set α
    - Chain' : IsChain (· <= ·) carrier
    - max_chain' : forall ⦃s⦄, IsChain (· <= ·) s -> carrier subseteq s -> carrier = s

中文:
结构 Flag
  参数: (α : 类型) [LE α]
  公理与运算 (3 个):
    - carrier : Set α
    - Chain' : IsChain (· <= ·) carrier
    - max_chain' : 对任意 ⦃s⦄, IsChain (· <= ·) s -> carrier subseteq s -> carrier = s
-/
structure Flag (α : Type*) [LE α] where
  /-- The `carrier` of a flag is the underlying set. -/
  carrier : Set α
  /-- By definition, a flag is a chain -/
  Chain' : IsChain (· <= ·) carrier
  /-- By definition, a flag is a maximal chain -/
  max_chain' : forall ⦃s⦄, IsChain (· <= ·) s -> carrier subseteq s -> carrier = s

namespace Flag

section LE

variable [LE α] {s t : Flag α} {a : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Flag α) α
  body: carrier
  coe_injective s t h := by
    cases s
    cases t
    congr

中文:
实例 :
  签名: SetLike (Flag α) α
  定义体: carrier
  coe_injective s t h := by
    cases s
    cases t
    congr

Depends on / 依赖: carrier
-/
instance : SetLike (Flag α) α where
  coe := carrier
  coe_injective s t h := by
    cases s
    cases t
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Flag α)
  body: .ofSetLike (Flag α) α

@[ext]

中文:
实例 :
  签名: PartialOrder (Flag α)
  定义体: .ofSetLike (Flag α) α

@[ext]

Depends on / 依赖: ofSetLike
-/
instance : PartialOrder (Flag α) := .ofSetLike (Flag α) α

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (s : Set α) = t -> s = t
  proof: SetLike.ext'

中文:
定理 ext
  结论: (s : Set α) = t -> s = t
  证明: SetLike.ext'

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext : (s : Set α) = t -> s = t :=
  SetLike.ext'

/--
theorem `mem_coe_iff` / 定理 `mem_coe_iff`

English:
theorem mem_coe_iff
  statement: a in (s : Set α) ↔ a in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_coe_iff
  结论: a in (s : Set α) ↔ a in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe_iff : a in (s : Set α) ↔ a in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Set α) (h₁ h₂)
  statement: (mk s h₁ h₂ : Set α) = s
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (s : Set α) (h₁ h₂)
  结论: (mk s h₁ h₂ : Set α) = s
  证明: rfl

@[simp]
-/
theorem coe_mk (s : Set α) (h₁ h₂) : (mk s h₁ h₂ : Set α) = s :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (s : Flag α)
  statement: mk (s : Set α) s.Chain' s.max_chain' = s
  proof: ext rfl

中文:
定理 mk_coe
  条件: (s : Flag α)
  结论: mk (s : Set α) s.Chain' s.max_chain' = s
  证明: ext rfl
-/
theorem mk_coe (s : Flag α) : mk (s : Set α) s.Chain' s.max_chain' = s :=
  ext rfl

/--
theorem `chain_le` / 定理 `chain_le`

English:
theorem chain_le
  given: (s : Flag α)
  statement: IsChain (· <= ·) (s : Set α)
  proof: s.Chain'

中文:
定理 chain_le
  条件: (s : Flag α)
  结论: IsChain (· <= ·) (s : Set α)
  证明: s.Chain'

Depends on / 依赖: s.Chain
-/
theorem chain_le (s : Flag α) : IsChain (· <= ·) (s : Set α) :=
  s.Chain'

/--
theorem `maxChain` / 定理 `maxChain`

English:
theorem maxChain
  given: (s : Flag α)
  statement: IsMaxChain (· <= ·) (s : Set α)
  proof: ⟨s.chain_le, s.max_chain'⟩

中文:
定理 maxChain
  条件: (s : Flag α)
  结论: IsMaxChain (· <= ·) (s : Set α)
  证明: ⟨s.chain_le, s.max_chain'⟩
-/
protected theorem maxChain (s : Flag α) : IsMaxChain (· <= ·) (s : Set α) :=
  ⟨s.chain_le, s.max_chain'⟩

/--
theorem `top_mem` / 定理 `top_mem`

English:
theorem top_mem
  given: [OrderTop α] (s : Flag α)
  statement: (⊤ : α) in s
  proof: s.maxChain.top_mem

中文:
定理 top_mem
  条件: [OrderTop α] (s : Flag α)
  结论: (⊤ : α) in s
  证明: s.maxChain.top_mem

Depends on / 依赖: maxChain, s.maxChain.top_mem, top_mem
-/
theorem top_mem [OrderTop α] (s : Flag α) : (⊤ : α) in s :=
  s.maxChain.top_mem

/--
theorem `bot_mem` / 定理 `bot_mem`

English:
theorem bot_mem
  given: [OrderBot α] (s : Flag α)
  statement: (⊥ : α) in s
  proof: s.maxChain.bot_mem

中文:
定理 bot_mem
  条件: [OrderBot α] (s : Flag α)
  结论: (⊥ : α) in s
  证明: s.maxChain.bot_mem

Depends on / 依赖: bot_mem, isScalarTower_localizationAlgebra, maxChain, s.maxChain.bot_mem
-/
theorem bot_mem [OrderBot α] (s : Flag α) : (⊥ : α) in s :=
  s.maxChain.bot_mem

/--
Definition of `ofIsMaxChain` / `ofIsMaxChain` 的定义

English:
definition ofIsMaxChain
  signature: (c : Set α) (hc : IsMaxChain (· <= ·) c)
  body: ⟨c, hc.isChain, hc.2⟩

@[simp, norm_cast]

中文:
定义 ofIsMaxChain
  签名: (c : Set α) (hc : IsMaxChain (· <= ·) c)
  定义体: ⟨c, hc.isChain, hc.2⟩

@[simp, norm_cast]

Depends on / 依赖: hc.isChain, isChain
-/
def ofIsMaxChain (c : Set α) (hc : IsMaxChain (· <= ·) c) : Flag α := ⟨c, hc.isChain, hc.2⟩

@[simp, norm_cast]
/--
lemma `coe_ofIsMaxChain` / 引理 `coe_ofIsMaxChain`

English:
lemma coe_ofIsMaxChain
  given: (c : Set α) (hc)
  statement: ofIsMaxChain c hc = c
  proof: rfl

中文:
引理 coe_ofIsMaxChain
  条件: (c : Set α) (hc)
  结论: ofIsMaxChain c hc = c
  证明: rfl
-/
lemma coe_ofIsMaxChain (c : Set α) (hc) : ofIsMaxChain c hc = c := rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] {a b : α} {s : Flag α}

/--
theorem `le_or_le` / 定理 `le_or_le`

English:
theorem le_or_le
  given: (s : Flag α) (ha : a in s) (hb : b in s)
  statement: a <= b ∨ b <= a
  proof: s.chain_le.total ha hb

中文:
定理 le_or_le
  条件: (s : Flag α) (ha : a in s) (hb : b in s)
  结论: a <= b ∨ b <= a
  证明: s.chain_le.total ha hb
-/
protected theorem le_or_le (s : Flag α) (ha : a in s) (hb : b in s) : a <= b ∨ b <= a :=
  s.chain_le.total ha hb

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderTop
  signature: α] (s
  body: Subtype.orderTop s.top_mem

中文:
实例 [OrderTop
  签名: α] (s
  定义体: Subtype.orderTop s.top_mem

Depends on / 依赖: Subtype, Subtype.orderTop, orderTop, s.top_mem, top_mem
-/
instance [OrderTop α] (s : Flag α) : OrderTop s :=
  Subtype.orderTop s.top_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderBot
  signature: α] (s
  body: Subtype.orderBot s.bot_mem

中文:
实例 [OrderBot
  签名: α] (s
  定义体: Subtype.orderBot s.bot_mem

Depends on / 依赖: Subtype, Subtype.orderBot, bot_mem, orderBot, s.bot_mem
-/
instance [OrderBot α] (s : Flag α) : OrderBot s :=
  Subtype.orderBot s.bot_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedOrder
  signature: α] (s
  body: Subtype.boundedOrder s.bot_mem s.top_mem

中文:
实例 [BoundedOrder
  签名: α] (s
  定义体: Subtype.boundedOrder s.bot_mem s.top_mem

Depends on / 依赖: Subtype, Subtype.boundedOrder, bot_mem, boundedOrder, s.bot_mem, s.top_mem, top_mem
-/
instance [BoundedOrder α] (s : Flag α) : BoundedOrder s :=
  Subtype.boundedOrder s.bot_mem s.top_mem

/--
lemma `mem_iff_forall_le_or_ge` / 引理 `mem_iff_forall_le_or_ge`

English:
lemma mem_iff_forall_le_or_ge
  statement: a in s ↔ forall ⦃b⦄, b in s -> a <= b ∨ b <= a
  proof: ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
Set.ne_insert_of_notMem _ ‹_›
s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) Set.subset_insert _ _⟩

中文:
引理 mem_iff_forall_le_or_ge
  结论: a in s ↔ 对任意 ⦃b⦄, b in s -> a <= b ∨ b <= a
  证明: ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
Set.ne_insert_of_notMem _ ‹_›
s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) Set.subset_insert _ _⟩

Depends on / 依赖: Set.ne_insert_of_notMem, Set.subset_insert, chain_le, insert, le_or_le, maxChain, ne_insert_of_notMem, of_not_not, s.chain_le.insert, s.le_or_le, s.maxChain, subset_insert
-/
lemma mem_iff_forall_le_or_ge : a in s ↔ forall ⦃b⦄, b in s -> a <= b ∨ b <= a :=
  ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
Set.ne_insert_of_notMem _ ‹_›
s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) Set.subset_insert _ _⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (e : α ≃o β)
  body: ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
left_inv s := ext e.symm_image_image s
right_inv s := ext e.image_symm_image s

中文:
定义 map
  签名: (e : α ≃o β)
  定义体: ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
left_inv s := ext e.symm_image_image s
right_inv s := ext e.image_symm_image s

Depends on / 依赖: maxChain, ofIsMaxChain, s.maxChain.image
-/
def map (e : α ≃o β) : Flag α ≃ Flag β where
  toFun s := ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
left_inv s := ext e.symm_image_image s
right_inv s := ext e.image_symm_image s

/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (e : α ≃o β) (s : Flag α)
  statement: ↑(map e s) = e '' s
  proof: rfl

中文:
引理 coe_map
  条件: (e : α ≃o β) (s : Flag α)
  结论: ↑(map e s) = e '' s
  证明: rfl
-/
@[simp, norm_cast] lemma coe_map (e : α ≃o β) (s : Flag α) : ↑(map e s) = e '' s := rfl

/--
lemma `symm_map` / 引理 `symm_map`

English:
lemma symm_map
  given: (e : α ≃o β)
  statement: (map e).symm = map e.symm
  proof: rfl

中文:
引理 symm_map
  条件: (e : α ≃o β)
  结论: (map e).symm = map e.symm
  证明: rfl
-/
@[simp] lemma symm_map (e : α ≃o β) : (map e).symm = map e.symm := rfl

end Preorder

section PartialOrder

variable [PartialOrder α]

/--
theorem `chain_lt` / 定理 `chain_lt`

English:
theorem chain_lt
  given: (s : Flag α)
  statement: IsChain (· < ·) (s : Set α)
  proof: s.chain_le.lt_of_le

中文:
定理 chain_lt
  条件: (s : Flag α)
  结论: IsChain (· < ·) (s : Set α)
  证明: s.chain_le.lt_of_le

Depends on / 依赖: chain_le, lt_of_le, s.chain_le.lt_of_le
-/
theorem chain_lt (s : Flag α) : IsChain (· < ·) (s : Set α) := s.chain_le.lt_of_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableLE
  signature: α] [DecidableLT α] [DecidableEq α] (s
  body: { Subtype.partialOrder _ with
    le_total := fun a b => s.le_or_le a.2 b.2
    toDecidableLE := Subtype.decidableLE
    toDecidableLT := Subtype.decidableLT
    toDecidableEq := Subtype.instDecidableEq }

中文:
实例 [DecidableLE
  签名: α] [DecidableLT α] [DecidableEq α] (s
  定义体: { Subtype.partialOrder _ with
    le_total := fun a b => s.le_or_le a.2 b.2
    toDecidableLE := Subtype.decidableLE
    toDecidableLT := Subtype.decidableLT
    toDecidableEq := Subtype.instDecidableEq }

Depends on / 依赖: Subtype, Subtype.decidableLE, Subtype.decidableLT, Subtype.instDecidableEq, Subtype.partialOrder, decidableLE, decidableLT, instDecidableEq, le_or_le, le_total, partialOrder, s.le_or_le, toDecidableEq, toDecidableLE, toDecidableLT
-/
instance [DecidableLE α] [DecidableLT α] [DecidableEq α] (s : Flag α) : LinearOrder s :=
  { Subtype.partialOrder _ with
    le_total := fun a b => s.le_or_le a.2 b.2
    toDecidableLE := Subtype.decidableLE
    toDecidableLT := Subtype.decidableLT
    toDecidableEq := Subtype.instDecidableEq }

end PartialOrder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : Unique (Flag α) where
  body: ⟨univ, isChain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
uniq s := SetLike.coe_injective s.3 (isChain_of_trichotomous _) subset_univ _

中文:
实例 [LinearOrder
  签名: α] : Unique (Flag α) where
  定义体: ⟨univ, isChain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
uniq s := SetLike.coe_injective s.3 (isChain_of_trichotomous _) subset_univ _

Depends on / 依赖: antisymm, isChain_of_trichotomous, s.subset_univ.antisymm, subset_univ
-/
instance [LinearOrder α] : Unique (Flag α) where
  default := ⟨univ, isChain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
uniq s := SetLike.coe_injective s.3 (isChain_of_trichotomous _) subset_univ _

end Flag
