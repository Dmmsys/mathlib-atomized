/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Set.Restrict

/-!
# Functions over sets

This file contains basic results on the following predicates of functions and sets:

* `Set.EqOn f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `Set.MapsTo f s t` : `f` sends every point of `s` to a point of `t`;
* `Set.InjOn f s` : restriction of `f` to `s` is injective;
* `Set.SurjOn f s t` : every point in `s` has a preimage in `s`;
* `Set.BijOn f s t` : `f` is a bijection between `s` and `t`;
* `Set.LeftInvOn f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `Set.RightInvOn f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `Set.InvOn f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `Set.LeftInvOn f' f s` and `Set.RightInvOn f' f t`.
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α -> Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Equality on a set -/
section equality

variable {s s₁ s₂ : Set α} {f₁ f₂ f₃ : α -> β} {g : β -> γ} {a : α}

/-- This lemma exists for use by `grind`/`aesop` as a forward rule. -/
@[aesop safe forward, grind ->]
/--
lemma `EqOn.eq_of_mem` / 引理 `EqOn.eq_of_mem`

English:
lemma EqOn.eq_of_mem
  given: (h : s.EqOn f₁ f₂) (ha : a in s)
  statement: f₁ a = f₂ a
  proof: h ha

@[simp]

中文:
引理 EqOn.eq_of_mem
  条件: (h : s.EqOn f₁ f₂) (ha : a in s)
  结论: f₁ a = f₂ a
  证明: h ha

@[simp]
-/
lemma EqOn.eq_of_mem (h : s.EqOn f₁ f₂) (ha : a in s) : f₁ a = f₂ a :=
  h ha

@[simp]
/--
theorem `eqOn_empty` / 定理 `eqOn_empty`

English:
theorem eqOn_empty
  given: (f₁ f₂ : α -> β)
  statement: EqOn f₁ f₂ ∅
  proof: fun _ => False.elim

@[simp]

中文:
定理 eqOn_empty
  条件: (f₁ f₂ : α -> β)
  结论: EqOn f₁ f₂ ∅
  证明: fun _ => False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem eqOn_empty (f₁ f₂ : α -> β) : EqOn f₁ f₂ ∅ := fun _ => False.elim

@[simp]
/--
theorem `eqOn_singleton` / 定理 `eqOn_singleton`

English:
theorem eqOn_singleton
  statement: Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a
  proof: by
  simp [Set.EqOn]

@[simp]

中文:
定理 eqOn_singleton
  结论: Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a
  证明: by
  simp [Set.EqOn]

@[simp]

Depends on / 依赖: Set.EqOn
-/
theorem eqOn_singleton : Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a := by
  simp [Set.EqOn]

@[simp]
/--
theorem `eqOn_univ` / 定理 `eqOn_univ`

English:
theorem eqOn_univ
  given: (f₁ f₂ : α -> β)
  statement: EqOn f₁ f₂ univ ↔ f₁ = f₂
  proof: by
  simp [EqOn, funext_iff]

@[symm]

中文:
定理 eqOn_univ
  条件: (f₁ f₂ : α -> β)
  结论: EqOn f₁ f₂ univ ↔ f₁ = f₂
  证明: by
  simp [EqOn, funext_iff]

@[symm]

Depends on / 依赖: funext_iff
-/
theorem eqOn_univ (f₁ f₂ : α -> β) : EqOn f₁ f₂ univ ↔ f₁ = f₂ := by
  simp [EqOn, funext_iff]

@[symm]
/--
theorem `EqOn.symm` / 定理 `EqOn.symm`

English:
theorem EqOn.symm
  given: (h : EqOn f₁ f₂ s)
  statement: EqOn f₂ f₁ s
  proof: fun _ hx => (h hx).symm

中文:
定理 EqOn.symm
  条件: (h : EqOn f₁ f₂ s)
  结论: EqOn f₂ f₁ s
  证明: fun _ hx => (h hx).symm
-/
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun _ hx => (h hx).symm

/--
theorem `eqOn_comm` / 定理 `eqOn_comm`

English:
theorem eqOn_comm
  statement: EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s
  proof: ⟨EqOn.symm, EqOn.symm⟩

中文:
定理 eqOn_comm
  结论: EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s
  证明: ⟨EqOn.symm, EqOn.symm⟩

Depends on / 依赖: EqOn.symm
-/
theorem eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩

-- This cannot be tagged as `@[refl]` with the current argument order.
-- See note below at `EqOn.trans`.
/--
theorem `eqOn_refl` / 定理 `eqOn_refl`

English:
theorem eqOn_refl
  given: (f : α -> β) (s : Set α)
  statement: EqOn f f s
  proof: fun _ _ => rfl

中文:
定理 eqOn_refl
  条件: (f : α -> β) (s : Set α)
  结论: EqOn f f s
  证明: fun _ _ => rfl
-/
theorem eqOn_refl (f : α -> β) (s : Set α) : EqOn f f s := fun _ _ => rfl

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in https://github.com/leanprover-community/mathlib4/pull/7014 will reject this attribute.
-- It can be restored by changing the argument order from `EqOn f₁ f₂ s` to `EqOn s f₁ f₂`.
-- This change will be made separately: [zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Reordering.20arguments.20of.20.60Set.2EEqOn.60/near/390467581).
/--
theorem `EqOn.trans` / 定理 `EqOn.trans`

English:
theorem EqOn.trans
  given: (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s)
  statement: EqOn f₁ f₃ s
  proof: fun _ hx =>
  (h₁ hx).trans (h₂ hx)

中文:
定理 EqOn.trans
  条件: (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s)
  结论: EqOn f₁ f₃ s
  证明: fun _ hx =>
  (h₁ hx).trans (h₂ hx)
-/
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun _ hx =>
  (h₁ hx).trans (h₂ hx)

/--
theorem `EqOn.image_eq` / 定理 `EqOn.image_eq`

English:
theorem EqOn.image_eq
  given: (heq : EqOn f₁ f₂ s)
  statement: f₁ '' s = f₂ '' s
  proof: by grind

中文:
定理 EqOn.image_eq
  条件: (heq : EqOn f₁ f₂ s)
  结论: f₁ '' s = f₂ '' s
  证明: by grind
-/
theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s := by grind

/--
theorem `EqOn.image_eq_self` / 定理 `EqOn.image_eq_self`

English:
theorem EqOn.image_eq_self
  given: {f : α -> α} (h : Set.EqOn f id s)
  statement: f '' s = s
  proof: by grind

中文:
定理 EqOn.image_eq_self
  条件: {f : α -> α} (h : Set.EqOn f id s)
  结论: f '' s = s
  证明: by grind
-/
theorem EqOn.image_eq_self {f : α -> α} (h : Set.EqOn f id s) : f '' s = s := by grind

/--
theorem `EqOn.inter_preimage_eq` / 定理 `EqOn.inter_preimage_eq`

English:
theorem EqOn.inter_preimage_eq
  given: (heq : EqOn f₁ f₂ s) (t : Set β)
  statement: s inter f₁ ⁻¹' t = s inter f₂ ⁻¹' t
  proof: by
  grind

中文:
定理 EqOn.inter_preimage_eq
  条件: (heq : EqOn f₁ f₂ s) (t : Set β)
  结论: s inter f₁ ⁻¹' t = s inter f₂ ⁻¹' t
  证明: by
  grind
-/
theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s inter f₁ ⁻¹' t = s inter f₂ ⁻¹' t := by
  grind

/--
theorem `EqOn.mono` / 定理 `EqOn.mono`

English:
theorem EqOn.mono
  given: (hs : s₁ subseteq s₂) (hf : EqOn f₁ f₂ s₂)
  statement: EqOn f₁ f₂ s₁
  proof: fun _ hx => hf (hs hx)

@[simp]

中文:
定理 EqOn.mono
  条件: (hs : s₁ subseteq s₂) (hf : EqOn f₁ f₂ s₂)
  结论: EqOn f₁ f₂ s₁
  证明: fun _ hx => hf (hs hx)

@[simp]
-/
theorem EqOn.mono (hs : s₁ subseteq s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun _ hx => hf (hs hx)

@[simp]
/--
theorem `eqOn_union` / 定理 `eqOn_union`

English:
theorem eqOn_union
  statement: EqOn f₁ f₂ (s₁ union s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂
  proof: forall₂_or_left

中文:
定理 eqOn_union
  结论: EqOn f₁ f₂ (s₁ union s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂
  证明: forall₂_or_left
-/
theorem eqOn_union : EqOn f₁ f₂ (s₁ union s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  forall₂_or_left

/--
theorem `EqOn.union` / 定理 `EqOn.union`

English:
theorem EqOn.union
  given: (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂)
  statement: EqOn f₁ f₂ (s₁ union s₂)
  proof: eqOn_union.2 ⟨h₁, h₂⟩

中文:
定理 EqOn.union
  条件: (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂)
  结论: EqOn f₁ f₂ (s₁ union s₂)
  证明: eqOn_union.2 ⟨h₁, h₂⟩

Depends on / 依赖: eqOn_union
-/
theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ union s₂) :=
  eqOn_union.2 ⟨h₁, h₂⟩

/--
theorem `EqOn.comp_left` / 定理 `EqOn.comp_left`

English:
theorem EqOn.comp_left
  given: (h : s.EqOn f₁ f₂)
  statement: s.EqOn (g ∘ f₁) (g ∘ f₂)
  proof: fun _ ha =>
congr_arg _ h ha

中文:
定理 EqOn.comp_left
  条件: (h : s.EqOn f₁ f₂)
  结论: s.EqOn (g ∘ f₁) (g ∘ f₂)
  证明: fun _ ha =>
congr_arg _ h ha
-/
theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun _ ha =>
congr_arg _ h ha

/--
theorem `EqOn.comp_left₂` / 定理 `EqOn.comp_left₂`

English:
theorem EqOn.comp_left₂
  statement: {α β δ γ} {op : α -> β -> δ} {a₁ a₂ : γ -> α}
  proof: fun _ hx => congr_arg₂ _ (ha hx) (hb hx)

@[simp]

中文:
定理 EqOn.comp_left₂
  结论: {α β δ γ} {op : α -> β -> δ} {a₁ a₂ : γ -> α}
  证明: fun _ hx => congr_arg₂ _ (ha hx) (hb hx)

@[simp]
-/
theorem EqOn.comp_left₂ {α β δ γ} {op : α -> β -> δ} {a₁ a₂ : γ -> α}
    {b₁ b₂ : γ -> β} {s : Set γ} (ha : s.EqOn a₁ a₂) (hb : s.EqOn b₁ b₂) :
    s.EqOn (fun x => op (a₁ x) (b₁ x)) (fun x => op (a₂ x) (b₂ x)) :=
  fun _ hx => congr_arg₂ _ (ha hx) (hb hx)

@[simp]
/--
theorem `eqOn_range` / 定理 `eqOn_range`

English:
theorem eqOn_range
  given: {ι : Sort*} {f : ι -> α} {g₁ g₂ : α -> β}
  proof: forall_mem_range.trans funext_iff.symm

alias ⟨EqOn.comp_eq, _⟩ := eqOn_range

中文:
定理 eqOn_range
  条件: {ι : Sort*} {f : ι -> α} {g₁ g₂ : α -> β}
  证明: forall_mem_range.trans funext_iff.symm

alias ⟨EqOn.comp_eq, _⟩ := eqOn_range

Depends on / 依赖: forall_mem_range, forall_mem_range.trans, funext_iff, funext_iff.symm
-/
theorem eqOn_range {ι : Sort*} {f : ι -> α} {g₁ g₂ : α -> β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
forall_mem_range.trans funext_iff.symm

alias ⟨EqOn.comp_eq, _⟩ := eqOn_range

end equality

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α -> β} {g g₁ g₂ : β -> γ}
  {f' f₁' f₂' : β -> α} {g' : γ -> β} {a : α} {b : β}

section MapsTo

/--
theorem `mapsTo_iff_image_subset` / 定理 `mapsTo_iff_image_subset`

English:
theorem mapsTo_iff_image_subset
  statement: MapsTo f s t ↔ f '' s subseteq t
  proof: image_subset_iff.symm

中文:
定理 mapsTo_iff_image_subset
  结论: MapsTo f s t ↔ f '' s subseteq t
  证明: image_subset_iff.symm

Depends on / 依赖: image_subset_iff, image_subset_iff.symm
-/
theorem mapsTo_iff_image_subset : MapsTo f s t ↔ f '' s subseteq t :=
  image_subset_iff.symm

/--
theorem `MapsTo.subset_preimage` / 定理 `MapsTo.subset_preimage`

English:
theorem MapsTo.subset_preimage
  given: (hf : MapsTo f s t)
  statement: s subseteq f ⁻¹' t
  proof: hf

中文:
定理 MapsTo.subset_preimage
  条件: (hf : MapsTo f s t)
  结论: s subseteq f ⁻¹' t
  证明: hf
-/
theorem MapsTo.subset_preimage (hf : MapsTo f s t) : s subseteq f ⁻¹' t := hf

/--
theorem `mapsTo_iff_subset_preimage` / 定理 `mapsTo_iff_subset_preimage`

English:
theorem mapsTo_iff_subset_preimage
  statement: MapsTo f s t ↔ s subseteq f ⁻¹' t
  proof: Iff.rfl

中文:
定理 mapsTo_iff_subset_preimage
  结论: MapsTo f s t ↔ s subseteq f ⁻¹' t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mapsTo_iff_subset_preimage : MapsTo f s t ↔ s subseteq f ⁻¹' t := Iff.rfl

/--
theorem `mapsTo_prodMap_diagonal` / 定理 `mapsTo_prodMap_diagonal`

English:
theorem mapsTo_prodMap_diagonal
  statement: MapsTo (Prod.map f f) (diagonal α) (diagonal β)
  proof: mapsTo_iff_subset_preimage.mpr diagonal_subset_iff.2 fun _ => rfl

@[simp]

中文:
定理 mapsTo_prodMap_diagonal
  结论: MapsTo (Prod.map f f) (diagonal α) (diagonal β)
  证明: mapsTo_iff_subset_preimage.mpr diagonal_subset_iff.2 fun _ => rfl

@[simp]

Depends on / 依赖: diagonal_subset_iff, mapsTo_iff_subset_preimage, mapsTo_iff_subset_preimage.mpr
-/
theorem mapsTo_prodMap_diagonal : MapsTo (Prod.map f f) (diagonal α) (diagonal β) :=
mapsTo_iff_subset_preimage.mpr diagonal_subset_iff.2 fun _ => rfl

@[simp]
/--
theorem `mapsTo_singleton` / 定理 `mapsTo_singleton`

English:
theorem mapsTo_singleton
  given: {x : α}
  statement: MapsTo f {x} t ↔ f x in t
  proof: mapsTo_iff_subset_preimage.trans singleton_subset_iff

中文:
定理 mapsTo_singleton
  条件: {x : α}
  结论: MapsTo f {x} t ↔ f x in t
  证明: mapsTo_iff_subset_preimage.trans singleton_subset_iff

Depends on / 依赖: mapsTo_iff_subset_preimage, mapsTo_iff_subset_preimage.trans, singleton_subset_iff
-/
theorem mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x in t :=
  mapsTo_iff_subset_preimage.trans singleton_subset_iff

/--
theorem `mapsTo_empty` / 定理 `mapsTo_empty`

English:
theorem mapsTo_empty
  given: (f : α -> β) (t : Set β)
  statement: MapsTo f ∅ t
  proof: fun _ => False.elim

中文:
定理 mapsTo_empty
  条件: (f : α -> β) (t : Set β)
  结论: MapsTo f ∅ t
  证明: fun _ => False.elim

Depends on / 依赖: False.elim
-/
theorem mapsTo_empty (f : α -> β) (t : Set β) : MapsTo f ∅ t :=
  fun _ => False.elim

/--
theorem `mapsTo_empty_iff` / 定理 `mapsTo_empty_iff`

English:
theorem mapsTo_empty_iff
  statement: MapsTo f s ∅ ↔ s = ∅
  proof: by
  simp [mapsTo_iff_image_subset, subset_empty_iff]

中文:
定理 mapsTo_empty_iff
  结论: MapsTo f s ∅ ↔ s = ∅
  证明: by
  simp [mapsTo_iff_image_subset, subset_empty_iff]
-/
@[simp] theorem mapsTo_empty_iff : MapsTo f s ∅ ↔ s = ∅ := by
  simp [mapsTo_iff_image_subset, subset_empty_iff]

/--
theorem `MapsTo.nonempty` / 定理 `MapsTo.nonempty`

English:
theorem MapsTo.nonempty
  given: (h : MapsTo f s t) (hs : s.Nonempty)
  statement: t.Nonempty
  proof: (hs.image f).mono (mapsTo_iff_image_subset.mp h)

中文:
定理 MapsTo.nonempty
  条件: (h : MapsTo f s t) (hs : s.Nonempty)
  结论: t.Nonempty
  证明: (hs.image f).mono (mapsTo_iff_image_subset.mp h)

Depends on / 依赖: hs.image, mapsTo_iff_image_subset, mapsTo_iff_image_subset.mp
-/
theorem MapsTo.nonempty (h : MapsTo f s t) (hs : s.Nonempty) : t.Nonempty :=
  (hs.image f).mono (mapsTo_iff_image_subset.mp h)

/--
theorem `MapsTo.image_subset` / 定理 `MapsTo.image_subset`

English:
theorem MapsTo.image_subset
  given: (h : MapsTo f s t)
  statement: f '' s subseteq t
  proof: mapsTo_iff_image_subset.1 h

中文:
定理 MapsTo.image_subset
  条件: (h : MapsTo f s t)
  结论: f '' s subseteq t
  证明: mapsTo_iff_image_subset.1 h

Depends on / 依赖: mapsTo_iff_image_subset
-/
theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s subseteq t :=
  mapsTo_iff_image_subset.1 h

/--
theorem `MapsTo.congr` / 定理 `MapsTo.congr`

English:
theorem MapsTo.congr
  given: (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s)
  statement: MapsTo f₂ s t
  proof: fun _ hx =>
  h hx ▸ h₁ hx

中文:
定理 MapsTo.congr
  条件: (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s)
  结论: MapsTo f₂ s t
  证明: fun _ hx =>
  h hx ▸ h₁ hx
-/
theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun _ hx =>
  h hx ▸ h₁ hx

/--
theorem `EqOn.comp_right` / 定理 `EqOn.comp_right`

English:
theorem EqOn.comp_right
  given: (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t)
  statement: s.EqOn (g₁ ∘ f) (g₂ ∘ f)
  proof: fun _ ha => hg hf ha

中文:
定理 EqOn.comp_right
  条件: (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t)
  结论: s.EqOn (g₁ ∘ f) (g₂ ∘ f)
  证明: fun _ ha => hg hf ha
-/
theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
fun _ ha => hg hf ha

/--
theorem `EqOn.mapsTo_iff` / 定理 `EqOn.mapsTo_iff`

English:
theorem EqOn.mapsTo_iff
  given: (H : EqOn f₁ f₂ s)
  statement: MapsTo f₁ s t ↔ MapsTo f₂ s t
  proof: ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

中文:
定理 EqOn.mapsTo_iff
  条件: (H : EqOn f₁ f₂ s)
  结论: MapsTo f₁ s t ↔ MapsTo f₂ s t
  证明: ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

Depends on / 依赖: H.symm, h.congr
-/
theorem EqOn.mapsTo_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

/--
theorem `MapsTo.comp` / 定理 `MapsTo.comp`

English:
theorem MapsTo.comp
  given: (h₁ : MapsTo g t p) (h₂ : MapsTo f s t)
  statement: MapsTo (g ∘ f) s p
  proof: fun _ h =>
  h₁ (h₂ h)

中文:
定理 MapsTo.comp
  条件: (h₁ : MapsTo g t p) (h₂ : MapsTo f s t)
  结论: MapsTo (g ∘ f) s p
  证明: fun _ h =>
  h₁ (h₂ h)
-/
theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun _ h =>
  h₁ (h₂ h)

/--
theorem `mapsTo_id` / 定理 `mapsTo_id`

English:
theorem mapsTo_id
  given: (s : Set α)
  statement: MapsTo id s s
  proof: fun _ => id

中文:
定理 mapsTo_id
  条件: (s : Set α)
  结论: MapsTo id s s
  证明: fun _ => id
-/
theorem mapsTo_id (s : Set α) : MapsTo id s s := fun _ => id

/--
theorem `MapsTo.iterate` / 定理 `MapsTo.iterate`

English:
theorem MapsTo.iterate
  given: {f : α -> α} {s : Set α} (h : MapsTo f s s)
  statement: forall n, MapsTo f^[n] s s

中文:
定理 MapsTo.iterate
  条件: {f : α -> α} {s : Set α} (h : MapsTo f s s)
  结论: 对任意 n, MapsTo f^[n] s s
-/
theorem MapsTo.iterate {f : α -> α} {s : Set α} (h : MapsTo f s s) : forall n, MapsTo f^[n] s s
  | 0 => fun _ => id
  | n + 1 => (MapsTo.iterate h n).comp h

/--
theorem `MapsTo.iterate_restrict` / 定理 `MapsTo.iterate_restrict`

English:
theorem MapsTo.iterate_restrict
  given: {f : α -> α} {s : Set α} (h : MapsTo f s s) (n : Nat)
  proof: by
  ext
  simpa using coe_iterate_restrict _ _ _

中文:
定理 MapsTo.iterate_restrict
  条件: {f : α -> α} {s : Set α} (h : MapsTo f s s) (n : 自然数)
  证明: by
  ext
  simpa using coe_iterate_restrict _ _ _

Depends on / 依赖: coe_iterate_restrict
-/
theorem MapsTo.iterate_restrict {f : α -> α} {s : Set α} (h : MapsTo f s s) (n : Nat) :
    (h.restrict f s s)^[n] = (h.iterate n).restrict _ _ _ := by
  ext
  simpa using coe_iterate_restrict _ _ _

/--
lemma `mapsTo_of_subsingleton'` / 引理 `mapsTo_of_subsingleton'`

English:
lemma mapsTo_of_subsingleton'
  given: [Subsingleton β] (f : α -> β) (h : s.Nonempty -> t.Nonempty)
  proof: fun a ha => Subsingleton.mem_iff_nonempty.2 h ⟨a, ha⟩

中文:
引理 mapsTo_of_subsingleton'
  条件: [Subsingleton β] (f : α -> β) (h : s.Nonempty -> t.Nonempty)
  证明: fun a ha => Subsingleton.mem_iff_nonempty.2 h ⟨a, ha⟩

Depends on / 依赖: Subsingleton, Subsingleton.mem_iff_nonempty, mem_iff_nonempty
-/
lemma mapsTo_of_subsingleton' [Subsingleton β] (f : α -> β) (h : s.Nonempty -> t.Nonempty) :
    MapsTo f s t :=
fun a ha => Subsingleton.mem_iff_nonempty.2 h ⟨a, ha⟩

/--
lemma `mapsTo_of_subsingleton` / 引理 `mapsTo_of_subsingleton`

English:
lemma mapsTo_of_subsingleton
  given: [Subsingleton α] (f : α -> α) (s : Set α)
  statement: MapsTo f s s
  proof: mapsTo_of_subsingleton' _ id

@[gcongr]

中文:
引理 mapsTo_of_subsingleton
  条件: [Subsingleton α] (f : α -> α) (s : Set α)
  结论: MapsTo f s s
  证明: mapsTo_of_subsingleton' _ id

@[gcongr]

Depends on / 依赖: mapsTo_of_subsingleton
-/
lemma mapsTo_of_subsingleton [Subsingleton α] (f : α -> α) (s : Set α) : MapsTo f s s :=
  mapsTo_of_subsingleton' _ id

@[gcongr]
/--
theorem `MapsTo.mono` / 定理 `MapsTo.mono`

English:
theorem MapsTo.mono
  given: (hf : MapsTo f s₁ t₁) (hs : s₂ subseteq s₁) (ht : t₁ subseteq t₂)
  statement: MapsTo f s₂ t₂
  proof: fun _ hx => ht (hf <| hs hx)

中文:
定理 MapsTo.mono
  条件: (hf : MapsTo f s₁ t₁) (hs : s₂ subseteq s₁) (ht : t₁ subseteq t₂)
  结论: MapsTo f s₂ t₂
  证明: fun _ hx => ht (hf <| hs hx)
-/
theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ subseteq s₁) (ht : t₁ subseteq t₂) : MapsTo f s₂ t₂ :=
  fun _ hx => ht (hf <| hs hx)

/--
theorem `MapsTo.mono_left` / 定理 `MapsTo.mono_left`

English:
theorem MapsTo.mono_left
  given: (hf : MapsTo f s₁ t) (hs : s₂ subseteq s₁)
  statement: MapsTo f s₂ t
  proof: fun _ hx =>
  hf (hs hx)

中文:
定理 MapsTo.mono_left
  条件: (hf : MapsTo f s₁ t) (hs : s₂ subseteq s₁)
  结论: MapsTo f s₂ t
  证明: fun _ hx =>
  hf (hs hx)
-/
theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ subseteq s₁) : MapsTo f s₂ t := fun _ hx =>
  hf (hs hx)

/--
theorem `MapsTo.mono_right` / 定理 `MapsTo.mono_right`

English:
theorem MapsTo.mono_right
  given: (hf : MapsTo f s t₁) (ht : t₁ subseteq t₂)
  statement: MapsTo f s t₂
  proof: fun _ hx =>
  ht (hf hx)

中文:
定理 MapsTo.mono_right
  条件: (hf : MapsTo f s t₁) (ht : t₁ subseteq t₂)
  结论: MapsTo f s t₂
  证明: fun _ hx =>
  ht (hf hx)
-/
theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ subseteq t₂) : MapsTo f s t₂ := fun _ hx =>
  ht (hf hx)

/--
theorem `MapsTo.union_union` / 定理 `MapsTo.union_union`

English:
theorem MapsTo.union_union
  given: (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂)
  proof: fun _ hx =>
hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr h₂ hx

中文:
定理 MapsTo.union_union
  条件: (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂)
  证明: fun _ hx =>
hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr h₂ hx
-/
theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ union s₂) (t₁ union t₂) := fun _ hx =>
hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr h₂ hx

/--
theorem `MapsTo.union` / 定理 `MapsTo.union`

English:
theorem MapsTo.union
  given: (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t)
  statement: MapsTo f (s₁ union s₂) t
  proof: union_self t ▸ h₁.union_union h₂

@[simp]

中文:
定理 MapsTo.union
  条件: (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t)
  结论: MapsTo f (s₁ union s₂) t
  证明: union_self t ▸ h₁.union_union h₂

@[simp]

Depends on / 依赖: union_self, union_union
-/
theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ union s₂) t :=
  union_self t ▸ h₁.union_union h₂

@[simp]
/--
theorem `mapsTo_union` / 定理 `mapsTo_union`

English:
theorem mapsTo_union
  statement: MapsTo f (s₁ union s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t
  proof: ⟨fun h =>
    ⟨h.mono subset_union_left (Subset.refl t),
      h.mono subset_union_right (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩

中文:
定理 mapsTo_union
  结论: MapsTo f (s₁ union s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t
  证明: ⟨fun h =>
    ⟨h.mono subset_union_left (Subset.refl t),
      h.mono subset_union_right (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩

Depends on / 依赖: Subset, Subset.refl, h.mono, subset_union_left, subset_union_right
-/
theorem mapsTo_union : MapsTo f (s₁ union s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono subset_union_left (Subset.refl t),
      h.mono subset_union_right (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩

/--
theorem `MapsTo.inter` / 定理 `MapsTo.inter`

English:
theorem MapsTo.inter
  given: (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂)
  statement: MapsTo f s (t₁ inter t₂)
  proof: fun _ hx =>
  ⟨h₁ hx, h₂ hx⟩

中文:
定理 MapsTo.inter
  条件: (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂)
  结论: MapsTo f s (t₁ inter t₂)
  证明: fun _ hx =>
  ⟨h₁ hx, h₂ hx⟩
-/
theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ inter t₂) := fun _ hx =>
  ⟨h₁ hx, h₂ hx⟩

/--
lemma `MapsTo.insert` / 引理 `MapsTo.insert`

English:
lemma MapsTo.insert
  given: (h : MapsTo f s t) (x : α)
  statement: MapsTo f (insert x s) (insert (f x) t)
  proof: by
  simpa [← singleton_union] using h.mono_right subset_union_right

中文:
引理 MapsTo.insert
  条件: (h : MapsTo f s t) (x : α)
  结论: MapsTo f (insert x s) (insert (f x) t)
  证明: by
  simpa [← singleton_union] using h.mono_right subset_union_right

Depends on / 依赖: h.mono_right, mono_right, singleton_union, subset_union_right
-/
lemma MapsTo.insert (h : MapsTo f s t) (x : α) : MapsTo f (insert x s) (insert (f x) t) := by
  simpa [← singleton_union] using h.mono_right subset_union_right

/--
theorem `MapsTo.inter_inter` / 定理 `MapsTo.inter_inter`

English:
theorem MapsTo.inter_inter
  given: (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂)
  proof: fun _ hx => ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]

中文:
定理 MapsTo.inter_inter
  条件: (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂)
  证明: fun _ hx => ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]
-/
theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ inter s₂) (t₁ inter t₂) := fun _ hx => ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]
/--
theorem `mapsTo_inter` / 定理 `mapsTo_inter`

English:
theorem mapsTo_inter
  statement: MapsTo f s (t₁ inter t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂
  proof: ⟨fun h =>
    ⟨h.mono (Subset.refl s) inter_subset_left,
      h.mono (Subset.refl s) inter_subset_right⟩,
    fun h => h.1.inter h.2⟩

中文:
定理 mapsTo_inter
  结论: MapsTo f s (t₁ inter t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂
  证明: ⟨fun h =>
    ⟨h.mono (Subset.refl s) inter_subset_left,
      h.mono (Subset.refl s) inter_subset_right⟩,
    fun h => h.1.inter h.2⟩

Depends on / 依赖: Subset, Subset.refl, h.mono, inter_subset_left, inter_subset_right
-/
theorem mapsTo_inter : MapsTo f s (t₁ inter t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) inter_subset_left,
      h.mono (Subset.refl s) inter_subset_right⟩,
    fun h => h.1.inter h.2⟩

/--
theorem `mapsTo_univ` / 定理 `mapsTo_univ`

English:
theorem mapsTo_univ
  given: (f : α -> β) (s : Set α)
  statement: MapsTo f s univ
  proof: fun _ _ => trivial

中文:
定理 mapsTo_univ
  条件: (f : α -> β) (s : Set α)
  结论: MapsTo f s univ
  证明: fun _ _ => trivial
-/
@[simp] theorem mapsTo_univ (f : α -> β) (s : Set α) : MapsTo f s univ := fun _ _ => trivial

/--
theorem `mapsTo_range` / 定理 `mapsTo_range`

English:
theorem mapsTo_range
  given: (f : α -> β) (s : Set α)
  statement: MapsTo f s (range f)
  proof: (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)

@[simp]

中文:
定理 mapsTo_range
  条件: (f : α -> β) (s : Set α)
  结论: MapsTo f s (range f)
  证明: (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)

@[simp]

Depends on / 依赖: Subset, Subset.refl, image_subset_range, mapsTo_image
-/
theorem mapsTo_range (f : α -> β) (s : Set α) : MapsTo f s (range f) :=
  (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)

@[simp]
/--
theorem `mapsTo_image_iff` / 定理 `mapsTo_image_iff`

English:
theorem mapsTo_image_iff
  given: {f : α -> β} {g : γ -> α} {s : Set γ} {t : Set β}
  proof: ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h _ ⟨_, hc⟩ => hc.2 ▸ h hc.1⟩

中文:
定理 mapsTo_image_iff
  条件: {f : α -> β} {g : γ -> α} {s : Set γ} {t : Set β}
  证明: ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h _ ⟨_, hc⟩ => hc.2 ▸ h hc.1⟩
-/
theorem mapsTo_image_iff {f : α -> β} {g : γ -> α} {s : Set γ} {t : Set β} :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h _ ⟨_, hc⟩ => hc.2 ▸ h hc.1⟩

/--
lemma `MapsTo.comp_left` / 引理 `MapsTo.comp_left`

English:
lemma MapsTo.comp_left
  given: (g : β -> γ) (hf : MapsTo f s t)
  statement: MapsTo (g ∘ f) s (g '' t)
  proof: fun x hx => ⟨f x, hf hx, rfl⟩

中文:
引理 MapsTo.comp_left
  条件: (g : β -> γ) (hf : MapsTo f s t)
  结论: MapsTo (g ∘ f) s (g '' t)
  证明: fun x hx => ⟨f x, hf hx, rfl⟩
-/
lemma MapsTo.comp_left (g : β -> γ) (hf : MapsTo f s t) : MapsTo (g ∘ f) s (g '' t) :=
  fun x hx => ⟨f x, hf hx, rfl⟩

/--
lemma `MapsTo.comp_right` / 引理 `MapsTo.comp_right`

English:
lemma MapsTo.comp_right
  given: {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α -> β)
  proof: fun _ hx => hg hx

@[simp]

中文:
引理 MapsTo.comp_right
  条件: {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α -> β)
  证明: fun _ hx => hg hx

@[simp]
-/
lemma MapsTo.comp_right {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α -> β) :
    MapsTo (g ∘ f) (f ⁻¹' s) t := fun _ hx => hg hx

@[simp]
/--
lemma `mapsTo_univ_iff` / 引理 `mapsTo_univ_iff`

English:
lemma mapsTo_univ_iff
  statement: MapsTo f univ t ↔ forall x, f x in t
  proof: ⟨fun h _ => h (mem_univ _), fun h x _ => h x⟩

中文:
引理 mapsTo_univ_iff
  结论: MapsTo f univ t ↔ 对任意 x, f x in t
  证明: ⟨fun h _ => h (mem_univ _), fun h x _ => h x⟩

Depends on / 依赖: mem_univ
-/
lemma mapsTo_univ_iff : MapsTo f univ t ↔ forall x, f x in t :=
  ⟨fun h _ => h (mem_univ _), fun h x _ => h x⟩

/--
lemma `mapsTo_univ_iff_range_subset` / 引理 `mapsTo_univ_iff_range_subset`

English:
lemma mapsTo_univ_iff_range_subset
  statement: MapsTo f univ t ↔ range f subseteq t
  proof: mapsTo_univ_iff.trans range_subset_iff.symm

@[simp]

中文:
引理 mapsTo_univ_iff_range_subset
  结论: MapsTo f univ t ↔ range f subseteq t
  证明: mapsTo_univ_iff.trans range_subset_iff.symm

@[simp]

Depends on / 依赖: mapsTo_univ_iff, mapsTo_univ_iff.trans, range_subset_iff, range_subset_iff.symm
-/
lemma mapsTo_univ_iff_range_subset : MapsTo f univ t ↔ range f subseteq t :=
  mapsTo_univ_iff.trans range_subset_iff.symm

@[simp]
/--
lemma `mapsTo_range_iff` / 引理 `mapsTo_range_iff`

English:
lemma mapsTo_range_iff
  given: {g : ι -> α}
  statement: MapsTo f (range g) t ↔ forall i, f (g i) in t
  proof: forall_mem_range

中文:
引理 mapsTo_range_iff
  条件: {g : ι -> α}
  结论: MapsTo f (range g) t ↔ 对任意 i, f (g i) in t
  证明: forall_mem_range

Depends on / 依赖: forall_mem_range
-/
lemma mapsTo_range_iff {g : ι -> α} : MapsTo f (range g) t ↔ forall i, f (g i) in t :=
  forall_mem_range

/--
theorem `MapsTo.mem_iff` / 定理 `MapsTo.mem_iff`

English:
theorem MapsTo.mem_iff
  given: (h : MapsTo f s t) (hc : MapsTo f sᶜ tᶜ) {x}
  statement: f x in t ↔ x in s
  proof: ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩

中文:
定理 MapsTo.mem_iff
  条件: (h : MapsTo f s t) (hc : MapsTo f sᶜ tᶜ) {x}
  结论: f x in t ↔ x in s
  证明: ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩
-/
theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f sᶜ tᶜ) {x} : f x in t ↔ x in s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩

end MapsTo

/-! ### Injectivity on a set -/
section injOn

/--
theorem `Subsingleton.injOn` / 定理 `Subsingleton.injOn`

English:
theorem Subsingleton.injOn
  given: (hs : s.Subsingleton) (f : α -> β)
  statement: InjOn f s
  proof: fun _ hx _ hy _ =>
  hs hx hy

@[simp]

中文:
定理 Subsingleton.injOn
  条件: (hs : s.Subsingleton) (f : α -> β)
  结论: InjOn f s
  证明: fun _ hx _ hy _ =>
  hs hx hy

@[simp]
-/
theorem Subsingleton.injOn (hs : s.Subsingleton) (f : α -> β) : InjOn f s := fun _ hx _ hy _ =>
  hs hx hy

@[simp]
/--
theorem `injOn_empty` / 定理 `injOn_empty`

English:
theorem injOn_empty
  given: (f : α -> β)
  statement: InjOn f ∅
  proof: subsingleton_empty.injOn f
@[simp]

中文:
定理 injOn_empty
  条件: (f : α -> β)
  结论: InjOn f ∅
  证明: subsingleton_empty.injOn f
@[simp]

Depends on / 依赖: subsingleton_empty, subsingleton_empty.injOn
-/
theorem injOn_empty (f : α -> β) : InjOn f ∅ :=
  subsingleton_empty.injOn f
@[simp]
/--
theorem `injOn_singleton` / 定理 `injOn_singleton`

English:
theorem injOn_singleton
  given: (f : α -> β) (a : α)
  statement: InjOn f {a}
  proof: subsingleton_singleton.injOn f

中文:
定理 injOn_singleton
  条件: (f : α -> β) (a : α)
  结论: InjOn f {a}
  证明: subsingleton_singleton.injOn f

Depends on / 依赖: subsingleton_singleton, subsingleton_singleton.injOn
-/
theorem injOn_singleton (f : α -> β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.injOn f

/--
lemma `injOn_pair` / 引理 `injOn_pair`

English:
lemma injOn_pair
  given: {b : α}
  statement: InjOn f {a, b} ↔ f a = f b -> a = b
  proof: by unfold InjOn; aesop

中文:
引理 injOn_pair
  条件: {b : α}
  结论: InjOn f {a, b} ↔ f a = f b -> a = b
  证明: by unfold InjOn; aesop
-/
@[simp] lemma injOn_pair {b : α} : InjOn f {a, b} ↔ f a = f b -> a = b := by unfold InjOn; aesop

/--
lemma `injOn_of_eq_iff_eq` / 引理 `injOn_of_eq_iff_eq`

English:
lemma injOn_of_eq_iff_eq
  given: (s : Set α) (h : forall x y, f x = f y ↔ x = y)
  statement: Set.InjOn f s
  proof: fun x _ y _ => (h x y).mp

中文:
引理 injOn_of_eq_iff_eq
  条件: (s : Set α) (h : 对任意 x y, f x = f y ↔ x = y)
  结论: Set.InjOn f s
  证明: fun x _ y _ => (h x y).mp
-/
@[simp low] lemma injOn_of_eq_iff_eq (s : Set α) (h : forall x y, f x = f y ↔ x = y) : Set.InjOn f s :=
  fun x _ y _ => (h x y).mp

/--
theorem `InjOn.eq_iff` / 定理 `InjOn.eq_iff`

English:
theorem InjOn.eq_iff
  given: {x y} (h : InjOn f s) (hx : x in s) (hy : y in s)
  statement: f x = f y ↔ x = y
  proof: ⟨h hx hy, fun h => h ▸ rfl⟩

中文:
定理 InjOn.eq_iff
  条件: {x y} (h : InjOn f s) (hx : x in s) (hy : y in s)
  结论: f x = f y ↔ x = y
  证明: ⟨h hx hy, fun h => h ▸ rfl⟩
-/
theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x in s) (hy : y in s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩

/--
theorem `InjOn.ne_iff` / 定理 `InjOn.ne_iff`

English:
theorem InjOn.ne_iff
  given: {x y} (h : InjOn f s) (hx : x in s) (hy : y in s)
  statement: f x != f y ↔ x != y
  proof: (h.eq_iff hx hy).not

alias ⟨_, InjOn.ne⟩ := InjOn.ne_iff

中文:
定理 InjOn.ne_iff
  条件: {x y} (h : InjOn f s) (hx : x in s) (hy : y in s)
  结论: f x != f y ↔ x != y
  证明: (h.eq_iff hx hy).not

alias ⟨_, InjOn.ne⟩ := InjOn.ne_iff

Depends on / 依赖: eq_iff, h.eq_iff
-/
theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x in s) (hy : y in s) : f x != f y ↔ x != y :=
  (h.eq_iff hx hy).not

alias ⟨_, InjOn.ne⟩ := InjOn.ne_iff

/--
theorem `InjOn.congr` / 定理 `InjOn.congr`

English:
theorem InjOn.congr
  given: (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s)
  statement: InjOn f₂ s
  proof: fun _ hx _ hy =>
  h hx ▸ h hy ▸ h₁ hx hy

中文:
定理 InjOn.congr
  条件: (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s)
  结论: InjOn f₂ s
  证明: fun _ hx _ hy =>
  h hx ▸ h hy ▸ h₁ hx hy
-/
theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun _ hx _ hy =>
  h hx ▸ h hy ▸ h₁ hx hy

/--
theorem `EqOn.injOn_iff` / 定理 `EqOn.injOn_iff`

English:
theorem EqOn.injOn_iff
  given: (H : EqOn f₁ f₂ s)
  statement: InjOn f₁ s ↔ InjOn f₂ s
  proof: ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

@[gcongr]

中文:
定理 EqOn.injOn_iff
  条件: (H : EqOn f₁ f₂ s)
  结论: InjOn f₁ s ↔ InjOn f₂ s
  证明: ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

@[gcongr]

Depends on / 依赖: H.symm, h.congr
-/
theorem EqOn.injOn_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

@[gcongr]
/--
theorem `InjOn.mono` / 定理 `InjOn.mono`

English:
theorem InjOn.mono
  given: (h : s₁ subseteq s₂) (ht : InjOn f s₂)
  statement: InjOn f s₁
  proof: fun _ hx _ hy H =>
  ht (h hx) (h hy) H

中文:
定理 InjOn.mono
  条件: (h : s₁ subseteq s₂) (ht : InjOn f s₂)
  结论: InjOn f s₁
  证明: fun _ hx _ hy H =>
  ht (h hx) (h hy) H
-/
theorem InjOn.mono (h : s₁ subseteq s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun _ hx _ hy H =>
  ht (h hx) (h hy) H

/--
theorem `injOn_union` / 定理 `injOn_union`

English:
theorem injOn_union
  given: (h : Disjoint s₁ s₂)
  proof: by
  refine ⟨fun H => ⟨H.mono subset_union_left, H.mono subset_union_right, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain rfl : x = y := H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hx

中文:
定理 injOn_union
  条件: (h : Disjoint s₁ s₂)
  证明: by
  refine ⟨fun H => ⟨H.mono subset_union_left, H.mono subset_union_right, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain rfl : x = y := H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hx

Depends on / 依赖: H.mono, Or.inl, Or.inr, exacts, h.le_bot, hxy.symm, le_bot, subset_union_left, subset_union_right
-/
theorem injOn_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ union s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ forall x in s₁, forall y in s₂, f x != f y := by
  refine ⟨fun H => ⟨H.mono subset_union_left, H.mono subset_union_right, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain rfl : x = y := H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]

/--
theorem `injOn_insert` / 定理 `injOn_insert`

English:
theorem injOn_insert
  given: {f : α -> β} {s : Set α} {a : α} (has : a ∉ s)
  proof: by
  rw [← union_singleton]; rw [injOn_union (disjoint_singleton_right.2 has)]
  simp

中文:
定理 injOn_insert
  条件: {f : α -> β} {s : Set α} {a : α} (has : a ∉ s)
  证明: by
  rw [← union_singleton]; rw [injOn_union (disjoint_singleton_right.2 has)]
  simp

Depends on / 依赖: disjoint_singleton_right, injOn_union, union_singleton
-/
theorem injOn_insert {f : α -> β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  rw [← union_singleton]; rw [injOn_union (disjoint_singleton_right.2 has)]
  simp

/--
lemma `injOn_univ` / 引理 `injOn_univ`

English:
lemma injOn_univ
  statement: InjOn f univ ↔ Injective f
  proof: by simp [InjOn, Injective]

中文:
引理 injOn_univ
  结论: InjOn f univ ↔ Injective f
  证明: by simp [InjOn, Injective]
-/
@[simp] lemma injOn_univ : InjOn f univ ↔ Injective f := by simp [InjOn, Injective]

/--
theorem `injOn_of_injective` / 定理 `injOn_of_injective`

English:
theorem injOn_of_injective
  given: (h : Injective f) {s : Set α}
  statement: InjOn f s
  proof: fun _ _ _ _ hxy => h hxy

alias _root_.Function.Injective.injOn := injOn_of_injective

中文:
定理 injOn_of_injective
  条件: (h : Injective f) {s : Set α}
  结论: InjOn f s
  证明: fun _ _ _ _ hxy => h hxy

alias _root_.Function.Injective.injOn := injOn_of_injective
-/
theorem injOn_of_injective (h : Injective f) {s : Set α} : InjOn f s := fun _ _ _ _ hxy => h hxy

alias _root_.Function.Injective.injOn := injOn_of_injective

-- A specialization of `injOn_of_injective` for `Subtype.val`.
/--
theorem `injOn_subtype_val` / 定理 `injOn_subtype_val`

English:
theorem injOn_subtype_val
  given: {p : α -> Prop} {s : Set {x // p x}}
  statement: Set.InjOn Subtype.val s
  proof: Subtype.coe_injective.injOn

中文:
定理 injOn_subtype_val
  条件: {p : α -> 命题} {s : Set {x // p x}}
  结论: Set.InjOn Subtype.val s
  证明: Subtype.coe_injective.injOn

Depends on / 依赖: Subtype, Subtype.coe_injective.injOn, coe_injective
-/
theorem injOn_subtype_val {p : α -> Prop} {s : Set {x // p x}} : Set.InjOn Subtype.val s :=
  Subtype.coe_injective.injOn

/--
lemma `injOn_id` / 引理 `injOn_id`

English:
lemma injOn_id
  given: (s : Set α)
  statement: InjOn id s
  proof: injective_id.injOn

中文:
引理 injOn_id
  条件: (s : Set α)
  结论: InjOn id s
  证明: injective_id.injOn

Depends on / 依赖: injective_id, injective_id.injOn
-/
lemma injOn_id (s : Set α) : InjOn id s := injective_id.injOn

/--
theorem `InjOn.comp` / 定理 `InjOn.comp`

English:
theorem InjOn.comp
  given: (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t)
  statement: InjOn (g ∘ f) s
  proof: fun _ hx _ hy heq => hf hx hy hg (h hx) (h hy) heq

中文:
定理 InjOn.comp
  条件: (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t)
  结论: InjOn (g ∘ f) s
  证明: fun _ hx _ hy heq => hf hx hy hg (h hx) (h hy) heq
-/
theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
fun _ hx _ hy heq => hf hx hy hg (h hx) (h hy) heq

/--
lemma `InjOn.of_comp` / 引理 `InjOn.of_comp`

English:
lemma InjOn.of_comp
  given: (h : InjOn (g ∘ f) s)
  statement: InjOn f s
  proof: fun _ hx _ hy heq => h hx hy (by simp [heq])

中文:
引理 InjOn.of_comp
  条件: (h : InjOn (g ∘ f) s)
  结论: InjOn f s
  证明: fun _ hx _ hy heq => h hx hy (by simp [heq])
-/
lemma InjOn.of_comp (h : InjOn (g ∘ f) s) : InjOn f s :=
  fun _ hx _ hy heq => h hx hy (by simp [heq])

/--
lemma `InjOn.image_of_comp` / 引理 `InjOn.image_of_comp`

English:
lemma InjOn.image_of_comp
  given: (h : InjOn (g ∘ f) s)
  statement: InjOn g (f '' s)
  proof: forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy heq => congr_arg f h hx hy heq

中文:
引理 InjOn.image_of_comp
  条件: (h : InjOn (g ∘ f) s)
  结论: InjOn g (f '' s)
  证明: forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy heq => congr_arg f h hx hy heq

Depends on / 依赖: congr_arg, forall_mem_image
-/
lemma InjOn.image_of_comp (h : InjOn (g ∘ f) s) : InjOn g (f '' s) :=
forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy heq => congr_arg f h hx hy heq

/--
lemma `InjOn.comp_iff` / 引理 `InjOn.comp_iff`

English:
lemma InjOn.comp_iff
  given: (hf : InjOn f s)
  statement: InjOn (g ∘ f) s ↔ InjOn g (f '' s)
  proof: ⟨image_of_comp, fun h => InjOn.comp h hf mapsTo_image f s⟩

中文:
引理 InjOn.comp_iff
  条件: (hf : InjOn f s)
  结论: InjOn (g ∘ f) s ↔ InjOn g (f '' s)
  证明: ⟨image_of_comp, fun h => InjOn.comp h hf mapsTo_image f s⟩

Depends on / 依赖: InjOn.comp, image_of_comp, mapsTo_image
-/
lemma InjOn.comp_iff (hf : InjOn f s) : InjOn (g ∘ f) s ↔ InjOn g (f '' s) :=
⟨image_of_comp, fun h => InjOn.comp h hf mapsTo_image f s⟩

/--
lemma `InjOn.iterate` / 引理 `InjOn.iterate`

English:
lemma InjOn.iterate
  given: {f : α -> α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s)

中文:
引理 InjOn.iterate
  条件: {f : α -> α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s)
-/
lemma InjOn.iterate {f : α -> α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s) :
    forall n, InjOn f^[n] s
  | 0 => injOn_id _
  | (n + 1) => (h.iterate hf n).comp h hf

/--
lemma `injOn_of_subsingleton` / 引理 `injOn_of_subsingleton`

English:
lemma injOn_of_subsingleton
  given: [Subsingleton α] (f : α -> β) (s : Set α)
  statement: InjOn f s
  proof: (injective_of_subsingleton _).injOn

中文:
引理 injOn_of_subsingleton
  条件: [Subsingleton α] (f : α -> β) (s : Set α)
  结论: InjOn f s
  证明: (injective_of_subsingleton _).injOn

Depends on / 依赖: injective_of_subsingleton
-/
lemma injOn_of_subsingleton [Subsingleton α] (f : α -> β) (s : Set α) : InjOn f s :=
  (injective_of_subsingleton _).injOn

/--
theorem `_root_.Function.Injective.injOn_range` / 定理 `_root_.Function.Injective.injOn_range`

English:
theorem _root_.Function.Injective.injOn_range
  given: (h : Injective (g ∘ f))
  statement: InjOn g (range f)
  proof: by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)

中文:
定理 _root_.Function.Injective.injOn_range
  条件: (h : Injective (g ∘ f))
  结论: InjOn g (range f)
  证明: by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)

Depends on / 依赖: congr_arg
-/
theorem _root_.Function.Injective.injOn_range (h : Injective (g ∘ f)) : InjOn g (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)

/--
theorem `_root_.Set.InjOn.injective_iff` / 定理 `_root_.Set.InjOn.injective_iff`

English:
theorem _root_.Set.InjOn.injective_iff
  given: (s : Set β) (h : InjOn g s) (hs : range f subseteq s)
  proof: ⟨(·.of_comp), fun h _ => by aesop⟩

中文:
定理 _root_.Set.InjOn.injective_iff
  条件: (s : Set β) (h : InjOn g s) (hs : range f subseteq s)
  证明: ⟨(·.of_comp), fun h _ => by aesop⟩

Depends on / 依赖: of_comp
-/
theorem _root_.Set.InjOn.injective_iff (s : Set β) (h : InjOn g s) (hs : range f subseteq s) :
    Injective (g ∘ f) ↔ Injective f :=
  ⟨(·.of_comp), fun h _ => by aesop⟩

/--
theorem `exists_injOn_iff_injective` / 定理 `exists_injOn_iff_injective`

English:
theorem exists_injOn_iff_injective
  given: [Nonempty β]
  proof: ⟨fun ⟨_, hf⟩ => ⟨_, hf.injective⟩,
   fun ⟨f, hf⟩ => by
    lift f to α -> β using trivial
    exact ⟨f, injOn_iff_injective.2 hf⟩⟩

中文:
定理 exists_injOn_iff_injective
  条件: [Nonempty β]
  证明: ⟨fun ⟨_, hf⟩ => ⟨_, hf.injective⟩,
   fun ⟨f, hf⟩ => by
    lift f to α -> β using trivial
    exact ⟨f, injOn_iff_injective.2 hf⟩⟩

Depends on / 依赖: hf.injective, injOn_iff_injective, injective
-/
theorem exists_injOn_iff_injective [Nonempty β] :
    (exists f : α -> β, InjOn f s) ↔ exists f : s -> β, Injective f :=
  ⟨fun ⟨_, hf⟩ => ⟨_, hf.injective⟩,
   fun ⟨f, hf⟩ => by
    lift f to α -> β using trivial
    exact ⟨f, injOn_iff_injective.2 hf⟩⟩

/--
theorem `injOn_preimage` / 定理 `injOn_preimage`

English:
theorem injOn_preimage
  given: {B : Set (Set β)} (hB : B subseteq 𝒫 range f)
  statement: InjOn (preimage f) B
  proof: fun _ hs _ ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

中文:
定理 injOn_preimage
  条件: {B : Set (Set β)} (hB : B subseteq 𝒫 range f)
  结论: InjOn (preimage f) B
  证明: fun _ hs _ ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

Depends on / 依赖: preimage_eq_preimage
-/
theorem injOn_preimage {B : Set (Set β)} (hB : B subseteq 𝒫 range f) : InjOn (preimage f) B :=
  fun _ hs _ ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

/--
theorem `InjOn.mem_of_mem_image` / 定理 `InjOn.mem_of_mem_image`

English:
theorem InjOn.mem_of_mem_image
  given: {x} (hf : InjOn f s) (hs : s₁ subseteq s) (h : x in s) (h₁ : f x in f '' s₁)
  proof: let ⟨_, h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'

中文:
定理 InjOn.mem_of_mem_image
  条件: {x} (hf : InjOn f s) (hs : s₁ subseteq s) (h : x in s) (h₁ : f x in f '' s₁)
  证明: let ⟨_, h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'
-/
theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ subseteq s) (h : x in s) (h₁ : f x in f '' s₁) :
    x in s₁ :=
  let ⟨_, h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'

/--
theorem `InjOn.mem_image_iff` / 定理 `InjOn.mem_image_iff`

English:
theorem InjOn.mem_image_iff
  given: {x} (hf : InjOn f s) (hs : s₁ subseteq s) (hx : x in s)
  proof: ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

中文:
定理 InjOn.mem_image_iff
  条件: {x} (hf : InjOn f s) (hs : s₁ subseteq s) (hx : x in s)
  证明: ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

Depends on / 依赖: hf.mem_of_mem_image, mem_image_of_mem, mem_of_mem_image
-/
theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ subseteq s) (hx : x in s) :
    f x in f '' s₁ ↔ x in s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

/--
theorem `InjOn.preimage_image_inter` / 定理 `InjOn.preimage_image_inter`

English:
theorem InjOn.preimage_image_inter
  given: (hf : InjOn f s) (hs : s₁ subseteq s)
  statement: f ⁻¹' f '' s₁ inter s = s₁
  proof: ext fun _ => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩

中文:
定理 InjOn.preimage_image_inter
  条件: (hf : InjOn f s) (hs : s₁ subseteq s)
  结论: f ⁻¹' f '' s₁ inter s = s₁
  证明: ext fun _ => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩

Depends on / 依赖: hf.mem_of_mem_image, mem_image_of_mem, mem_of_mem_image
-/
theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ subseteq s) : f ⁻¹' f '' s₁ inter s = s₁ :=
  ext fun _ => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩

/--
theorem `EqOn.cancel_left` / 定理 `EqOn.cancel_left`

English:
theorem EqOn.cancel_left
  statement: (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
  proof: fun _ ha => hg (hf₁ ha) (hf₂ ha) (h ha)

中文:
定理 EqOn.cancel_left
  结论: (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
  证明: fun _ ha => hg (hf₁ ha) (hf₂ ha) (h ha)
-/
theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun _ ha => hg (hf₁ ha) (hf₂ ha) (h ha)

/--
theorem `InjOn.cancel_left` / 定理 `InjOn.cancel_left`

English:
theorem InjOn.cancel_left
  given: (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t)
  proof: ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩

中文:
定理 InjOn.cancel_left
  条件: (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t)
  证明: ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩

Depends on / 依赖: EqOn.comp_left, cancel_left, comp_left, h.cancel_left
-/
theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩

/--
lemma `InjOn.image_inter` / 引理 `InjOn.image_inter`

English:
lemma InjOn.image_inter
  given: {s t u : Set α} (hf : u.InjOn f) (hs : s subseteq u) (ht : t subseteq u)
  proof: by
  apply Subset.antisymm (image_inter_subset _ _ _)
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩

中文:
引理 InjOn.image_inter
  条件: {s t u : Set α} (hf : u.InjOn f) (hs : s subseteq u) (ht : t subseteq u)
  证明: by
  apply Subset.antisymm (image_inter_subset _ _ _)
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm, image_inter_subset
-/
lemma InjOn.image_inter {s t u : Set α} (hf : u.InjOn f) (hs : s subseteq u) (ht : t subseteq u) :
    f '' (s inter t) = f '' s inter f '' t := by
  apply Subset.antisymm (image_inter_subset _ _ _)
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩

/--
lemma `InjOn.image` / 引理 `InjOn.image`

English:
lemma InjOn.image
  given: (h : s.InjOn f)
  statement: s.powerset.InjOn (image f)
  proof: fun s₁ hs₁ s₂ hs₂ h' => by rw [← h.preimage_image_inter hs₁, h', h.preimage_image_inter hs₂]

中文:
引理 InjOn.image
  条件: (h : s.InjOn f)
  结论: s.powerset.InjOn (image f)
  证明: fun s₁ hs₁ s₂ hs₂ h' => by rw [← h.preimage_image_inter hs₁, h', h.preimage_image_inter hs₂]

Depends on / 依赖: h.preimage_image_inter, preimage_image_inter
-/
lemma InjOn.image (h : s.InjOn f) : s.powerset.InjOn (image f) :=
  fun s₁ hs₁ s₂ hs₂ h' => by rw [← h.preimage_image_inter hs₁, h', h.preimage_image_inter hs₂]

/--
theorem `InjOn.image_eq_image_iff` / 定理 `InjOn.image_eq_image_iff`

English:
theorem InjOn.image_eq_image_iff
  given: (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s)
  proof: h.image.eq_iff h₁ h₂

中文:
定理 InjOn.image_eq_image_iff
  条件: (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s)
  证明: h.image.eq_iff h₁ h₂

Depends on / 依赖: eq_iff, h.image.eq_iff
-/
theorem InjOn.image_eq_image_iff (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) :
    f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
  h.image.eq_iff h₁ h₂

/--
lemma `InjOn.image_subset_image_iff` / 引理 `InjOn.image_subset_image_iff`

English:
lemma InjOn.image_subset_image_iff
  given: (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s)
  proof: by
  refine ⟨fun h' => ?_, image_mono⟩
  rw [← h.preimage_image_inter h₁]; rw [← h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

中文:
引理 InjOn.image_subset_image_iff
  条件: (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s)
  证明: by
  refine ⟨fun h' => ?_, image_mono⟩
  rw [← h.preimage_image_inter h₁]; rw [← h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

Depends on / 依赖: h.preimage_image_inter, image_mono, inter_subset_inter_left, preimage_image_inter, preimage_mono
-/
lemma InjOn.image_subset_image_iff (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) :
    f '' s₁ subseteq f '' s₂ ↔ s₁ subseteq s₂ := by
  refine ⟨fun h' => ?_, image_mono⟩
  rw [← h.preimage_image_inter h₁]; rw [← h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

/--
lemma `InjOn.image_ssubset_image_iff` / 引理 `InjOn.image_ssubset_image_iff`

English:
lemma InjOn.image_ssubset_image_iff
  given: (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s)
  proof: by
  simp_rw [ssubset_def, h.image_subset_image_iff h₁ h₂, h.image_subset_image_iff h₂ h₁]

中文:
引理 InjOn.image_ssubset_image_iff
  条件: (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s)
  证明: by
  simp_rw [ssubset_def, h.image_subset_image_iff h₁ h₂, h.image_subset_image_iff h₂ h₁]

Depends on / 依赖: h.image_subset_image_iff, image_subset_image_iff, simp_rw, ssubset_def
-/
lemma InjOn.image_ssubset_image_iff (h : s.InjOn f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) :
    f '' s₁ ⊂ f '' s₂ ↔ s₁ ⊂ s₂ := by
  simp_rw [ssubset_def, h.image_subset_image_iff h₁ h₂, h.image_subset_image_iff h₂ h₁]

-- TODO: can this move to a better place?
/--
theorem `_root_.Disjoint.image` / 定理 `_root_.Disjoint.image`

English:
theorem _root_.Disjoint.image
  statement: {s t u : Set α} {f : α -> β} (h : Disjoint s t) (hf : u.InjOn f)
  proof: by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht]; rw [h]; rw [image_empty]

中文:
定理 _root_.Disjoint.image
  结论: {s t u : Set α} {f : α -> β} (h : Disjoint s t) (hf : u.InjOn f)
  证明: by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht]; rw [h]; rw [image_empty]

Depends on / 依赖: disjoint_iff_inter_eq_empty, hf.image_inter, image_empty, image_inter
-/
theorem _root_.Disjoint.image {s t u : Set α} {f : α -> β} (h : Disjoint s t) (hf : u.InjOn f)
    (hs : s subseteq u) (ht : t subseteq u) : Disjoint (f '' s) (f '' t) := by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht]; rw [h]; rw [image_empty]

/--
lemma `InjOn.image_sdiff` / 引理 `InjOn.image_sdiff`

English:
lemma InjOn.image_sdiff
  given: {t : Set α} (h : s.InjOn f)
  statement: f '' (s \ t) = f '' s \ f '' (s inter t)
  proof: by
  refine subset_antisymm (subset_sdiff.2 ⟨image_mono sdiff_subset, ?_⟩)
    (sdiff_subset_iff.2 (by rw [← image_union, inter_union_sdiff]))
  exact Disjoint.image disjoint_sdiff_inter h sdiff_subset inter_subset_left

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff := InjOn.image_sdi

中文:
引理 InjOn.image_sdiff
  条件: {t : Set α} (h : s.InjOn f)
  结论: f '' (s \ t) = f '' s \ f '' (s inter t)
  证明: by
  refine subset_antisymm (subset_sdiff.2 ⟨image_mono sdiff_subset, ?_⟩)
    (sdiff_subset_iff.2 (by rw [← image_union, inter_union_sdiff]))
  exact Disjoint.image disjoint_sdiff_inter h sdiff_subset inter_subset_left

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff := InjOn.image_sdi

Depends on / 依赖: Disjoint, Disjoint.image, disjoint_sdiff_inter, image_mono, image_union, inter_subset_left, inter_union_sdiff, sdiff_subset, sdiff_subset_iff, subset_antisymm, subset_sdiff
-/
lemma InjOn.image_sdiff {t : Set α} (h : s.InjOn f) : f '' (s \ t) = f '' s \ f '' (s inter t) := by
  refine subset_antisymm (subset_sdiff.2 ⟨image_mono sdiff_subset, ?_⟩)
    (sdiff_subset_iff.2 (by rw [← image_union, inter_union_sdiff]))
  exact Disjoint.image disjoint_sdiff_inter h sdiff_subset inter_subset_left

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff := InjOn.image_sdiff

/--
lemma `InjOn.image_sdiff_subset` / 引理 `InjOn.image_sdiff_subset`

English:
lemma InjOn.image_sdiff_subset
  given: {f : α -> β} {t : Set α} (h : InjOn f s) (hst : t subseteq s)
  proof: by
  rw [h.image_sdiff]; rw [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff_subset := InjOn.image_sdiff_subset

alias image_sdiff_of_injOn := InjOn.image_sdiff_subset

@[deprecated (since := "2026-06-03")] alias image_diff_of_injOn := image_sdiff_of_

中文:
引理 InjOn.image_sdiff_subset
  条件: {f : α -> β} {t : Set α} (h : InjOn f s) (hst : t subseteq s)
  证明: by
  rw [h.image_sdiff]; rw [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff_subset := InjOn.image_sdiff_subset

alias image_sdiff_of_injOn := InjOn.image_sdiff_subset

@[deprecated (since := "2026-06-03")] alias image_diff_of_injOn := image_sdiff_of_

Depends on / 依赖: h.image_sdiff, image_sdiff, inter_eq_self_of_subset_right
-/
lemma InjOn.image_sdiff_subset {f : α -> β} {t : Set α} (h : InjOn f s) (hst : t subseteq s) :
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_sdiff]; rw [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff_subset := InjOn.image_sdiff_subset

alias image_sdiff_of_injOn := InjOn.image_sdiff_subset

@[deprecated (since := "2026-06-03")] alias image_diff_of_injOn := image_sdiff_of_injOn

/--
theorem `InjOn.imageFactorization_injective` / 定理 `InjOn.imageFactorization_injective`

English:
theorem InjOn.imageFactorization_injective
  given: (h : InjOn f s)
  proof: fun ⟨x, hx⟩ ⟨y, hy⟩ h' => by simpa [imageFactorization, h.eq_iff hx hy] using h'

中文:
定理 InjOn.imageFactorization_injective
  条件: (h : InjOn f s)
  证明: fun ⟨x, hx⟩ ⟨y, hy⟩ h' => by simpa [imageFactorization, h.eq_iff hx hy] using h'

Depends on / 依赖: eq_iff, h.eq_iff, imageFactorization
-/
theorem InjOn.imageFactorization_injective (h : InjOn f s) :
    Injective (s.imageFactorization f) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ h' => by simpa [imageFactorization, h.eq_iff hx hy] using h'

/--
theorem `imageFactorization_injective_iff` / 定理 `imageFactorization_injective_iff`

English:
theorem imageFactorization_injective_iff
  statement: Injective (s.imageFactorization f) ↔ InjOn f s
  proof: ⟨fun h x hx y hy _ => by simpa using @h ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [imageFactorization]),
    InjOn.imageFactorization_injective⟩

中文:
定理 imageFactorization_injective_iff
  结论: Injective (s.imageFactorization f) ↔ InjOn f s
  证明: ⟨fun h x hx y hy _ => by simpa using @h ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [imageFactorization]),
    InjOn.imageFactorization_injective⟩
-/
@[simp] theorem imageFactorization_injective_iff : Injective (s.imageFactorization f) ↔ InjOn f s :=
  ⟨fun h x hx y hy _ => by simpa using @h ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [imageFactorization]),
    InjOn.imageFactorization_injective⟩

end injOn

section graphOn
variable {x : α × β}

/--
lemma `graphOn_univ_inj` / 引理 `graphOn_univ_inj`

English:
lemma graphOn_univ_inj
  given: {g : α -> β}
  statement: univ.graphOn f = univ.graphOn g ↔ f = g
  proof: by simp

中文:
引理 graphOn_univ_inj
  条件: {g : α -> β}
  结论: univ.graphOn f = univ.graphOn g ↔ f = g
  证明: by simp
-/
lemma graphOn_univ_inj {g : α -> β} : univ.graphOn f = univ.graphOn g ↔ f = g := by simp

/--
lemma `graphOn_univ_injective` / 引理 `graphOn_univ_injective`

English:
lemma graphOn_univ_injective
  statement: Injective (univ.graphOn : (α -> β) -> Set (α × β))
  proof: fun _f _g => graphOn_univ_inj.1

中文:
引理 graphOn_univ_injective
  结论: Injective (univ.graphOn : (α -> β) -> Set (α × β))
  证明: fun _f _g => graphOn_univ_inj.1

Depends on / 依赖: graphOn_univ_inj
-/
lemma graphOn_univ_injective : Injective (univ.graphOn : (α -> β) -> Set (α × β)) :=
  fun _f _g => graphOn_univ_inj.1

/--
lemma `exists_eq_graphOn_image_fst` / 引理 `exists_eq_graphOn_image_fst`

English:
lemma exists_eq_graphOn_image_fst
  given: [Nonempty β] {s : Set (α × β)}
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf⟩
    rw [hf]
exact InjOn.image_of_comp injOn_id _
  · have : forall x in Prod.fst '' s, exists y, (x, y) in s := forall_mem_image.2 fun (x, y) h => ⟨y, h⟩
    choose! f hf using this
    rw [forall_mem_image] at hf
    use f
    rw [graphOn]; rw [image

中文:
引理 exists_eq_graphOn_image_fst
  条件: [Nonempty β] {s : Set (α × β)}
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf⟩
    rw [hf]
exact InjOn.image_of_comp injOn_id _
  · have : forall x in Prod.fst '' s, exists y, (x, y) in s := forall_mem_image.2 fun (x, y) h => ⟨y, h⟩
    choose! f hf using this
    rw [forall_mem_image] at hf
    use f
    rw [graphOn]; rw [image

Depends on / 依赖: EqOn.image_eq_self, InjOn.image_of_comp, Prod.fst, forall_mem_image, graphOn, image_eq_self, image_image, image_of_comp, injOn_id
-/
lemma exists_eq_graphOn_image_fst [Nonempty β] {s : Set (α × β)} :
    (exists f : α -> β, s = graphOn f (Prod.fst '' s)) ↔ InjOn Prod.fst s := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf⟩
    rw [hf]
exact InjOn.image_of_comp injOn_id _
  · have : forall x in Prod.fst '' s, exists y, (x, y) in s := forall_mem_image.2 fun (x, y) h => ⟨y, h⟩
    choose! f hf using this
    rw [forall_mem_image] at hf
    use f
    rw [graphOn]; rw [image_image]; rw [EqOn.image_eq_self]
    exact fun x hx => h (hf hx) hx rfl

/--
lemma `exists_eq_graphOn` / 引理 `exists_eq_graphOn`

English:
lemma exists_eq_graphOn
  given: [Nonempty β] {s : Set (α × β)}
  proof: .trans ⟨fun ⟨f, t, hs⟩ => ⟨f, by rw [hs, image_fst_graphOn]⟩, fun ⟨f, hf⟩ => ⟨f, _, hf⟩⟩
    exists_eq_graphOn_image_fst

中文:
引理 exists_eq_graphOn
  条件: [Nonempty β] {s : Set (α × β)}
  证明: .trans ⟨fun ⟨f, t, hs⟩ => ⟨f, by rw [hs, image_fst_graphOn]⟩, fun ⟨f, hf⟩ => ⟨f, _, hf⟩⟩
    exists_eq_graphOn_image_fst

Depends on / 依赖: exists_eq_graphOn_image_fst, image_fst_graphOn
-/
lemma exists_eq_graphOn [Nonempty β] {s : Set (α × β)} :
    (exists f t, s = graphOn f t) ↔ InjOn Prod.fst s :=
  .trans ⟨fun ⟨f, t, hs⟩ => ⟨f, by rw [hs, image_fst_graphOn]⟩, fun ⟨f, hf⟩ => ⟨f, _, hf⟩⟩
    exists_eq_graphOn_image_fst

end graphOn

/-! ### Surjectivity on a set -/
section surjOn

/--
theorem `SurjOn.subset_range` / 定理 `SurjOn.subset_range`

English:
theorem SurjOn.subset_range
  given: (h : SurjOn f s t)
  statement: t subseteq range f
  proof: Subset.trans h image_subset_range f s

中文:
定理 SurjOn.subset_range
  条件: (h : SurjOn f s t)
  结论: t subseteq range f
  证明: Subset.trans h image_subset_range f s

Depends on / 依赖: Subset, Subset.trans, image_subset_range
-/
theorem SurjOn.subset_range (h : SurjOn f s t) : t subseteq range f :=
Subset.trans h image_subset_range f s

/--
theorem `surjOn_iff_exists_map_subtype` / 定理 `surjOn_iff_exists_map_subtype`

English:
theorem surjOn_iff_exists_map_subtype
  proof: ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩

中文:
定理 surjOn_iff_exists_map_subtype
  证明: ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩

Depends on / 依赖: Subtype, Subtype.coe_mk, coe_mk, mapsTo_image, restrict, surjective_mapsTo_image_restrict
-/
theorem surjOn_iff_exists_map_subtype :
    SurjOn f s t ↔ exists (t' : Set β) (g : s -> t'), t subseteq t' ∧ Surjective g ∧ forall x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩

/--
theorem `surjOn_empty` / 定理 `surjOn_empty`

English:
theorem surjOn_empty
  given: (f : α -> β) (s : Set α)
  statement: SurjOn f s ∅
  proof: empty_subset _

中文:
定理 surjOn_empty
  条件: (f : α -> β) (s : Set α)
  结论: SurjOn f s ∅
  证明: empty_subset _

Depends on / 依赖: empty_subset
-/
theorem surjOn_empty (f : α -> β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _

/--
theorem `surjOn_empty_iff` / 定理 `surjOn_empty_iff`

English:
theorem surjOn_empty_iff
  statement: SurjOn f ∅ t ↔ t = ∅
  proof: by
  simp [SurjOn, subset_empty_iff]

中文:
定理 surjOn_empty_iff
  结论: SurjOn f ∅ t ↔ t = ∅
  证明: by
  simp [SurjOn, subset_empty_iff]
-/
@[simp] theorem surjOn_empty_iff : SurjOn f ∅ t ↔ t = ∅ := by
  simp [SurjOn, subset_empty_iff]

/--
lemma `surjOn_singleton` / 引理 `surjOn_singleton`

English:
lemma surjOn_singleton
  statement: SurjOn f s {b} ↔ b in f '' s
  proof: singleton_subset_iff

中文:
引理 surjOn_singleton
  结论: SurjOn f s {b} ↔ b in f '' s
  证明: singleton_subset_iff
-/
@[simp] lemma surjOn_singleton : SurjOn f s {b} ↔ b in f '' s := singleton_subset_iff

/--
lemma `surjOn_univ_of_subsingleton_nonempty` / 引理 `surjOn_univ_of_subsingleton_nonempty`

English:
lemma surjOn_univ_of_subsingleton_nonempty
  given: [Subsingleton β] [Nonempty β]
  proof: by
  cases nonempty_unique β; simp [univ_unique, Subsingleton.elim (f _) default, Set.Nonempty]

中文:
引理 surjOn_univ_of_subsingleton_nonempty
  条件: [Subsingleton β] [Nonempty β]
  证明: by
  cases nonempty_unique β; simp [univ_unique, Subsingleton.elim (f _) default, Set.Nonempty]
-/
@[simp] lemma surjOn_univ_of_subsingleton_nonempty [Subsingleton β] [Nonempty β] :
    SurjOn f s univ ↔ s.Nonempty := by
  cases nonempty_unique β; simp [univ_unique, Subsingleton.elim (f _) default, Set.Nonempty]

/--
theorem `surjOn_image` / 定理 `surjOn_image`

English:
theorem surjOn_image
  given: (f : α -> β) (s : Set α)
  statement: SurjOn f s (f '' s)
  proof: Subset.rfl

中文:
定理 surjOn_image
  条件: (f : α -> β) (s : Set α)
  结论: SurjOn f s (f '' s)
  证明: Subset.rfl

Depends on / 依赖: Subset, Subset.rfl
-/
theorem surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f '' s) :=
  Subset.rfl

/--
theorem `SurjOn.comap_nonempty` / 定理 `SurjOn.comap_nonempty`

English:
theorem SurjOn.comap_nonempty
  given: (h : SurjOn f s t) (ht : t.Nonempty)
  statement: s.Nonempty
  proof: (ht.mono h).of_image

中文:
定理 SurjOn.comap_nonempty
  条件: (h : SurjOn f s t) (ht : t.Nonempty)
  结论: s.Nonempty
  证明: (ht.mono h).of_image

Depends on / 依赖: ht.mono, of_image
-/
theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image

/--
lemma `SurjOn.nonempty_or_eq_empty` / 引理 `SurjOn.nonempty_or_eq_empty`

English:
lemma SurjOn.nonempty_or_eq_empty
  given: (h : SurjOn f s t)
  proof: by
  by_contra!
  exact (h.comap_nonempty this.2).ne_empty this.1

中文:
引理 SurjOn.nonempty_or_eq_empty
  条件: (h : SurjOn f s t)
  证明: by
  by_contra!
  exact (h.comap_nonempty this.2).ne_empty this.1

Depends on / 依赖: comap_nonempty, h.comap_nonempty, ne_empty
-/
lemma SurjOn.nonempty_or_eq_empty (h : SurjOn f s t) :
    s.Nonempty ∨ t = ∅ := by
  by_contra!
  exact (h.comap_nonempty this.2).ne_empty this.1

/--
theorem `SurjOn.congr` / 定理 `SurjOn.congr`

English:
theorem SurjOn.congr
  given: (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s)
  statement: SurjOn f₂ s t
  proof: by
  rwa [SurjOn, ← H.image_eq]

中文:
定理 SurjOn.congr
  条件: (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s)
  结论: SurjOn f₂ s t
  证明: by
  rwa [SurjOn, ← H.image_eq]

Depends on / 依赖: H.image_eq, SurjOn, image_eq
-/
theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [SurjOn, ← H.image_eq]

/--
theorem `EqOn.surjOn_iff` / 定理 `EqOn.surjOn_iff`

English:
theorem EqOn.surjOn_iff
  given: (h : EqOn f₁ f₂ s)
  statement: SurjOn f₁ s t ↔ SurjOn f₂ s t
  proof: ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

@[gcongr]

中文:
定理 EqOn.surjOn_iff
  条件: (h : EqOn f₁ f₂ s)
  结论: SurjOn f₁ s t ↔ SurjOn f₂ s t
  证明: ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

@[gcongr]

Depends on / 依赖: H.congr, h.symm
-/
theorem EqOn.surjOn_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

@[gcongr]
/--
theorem `SurjOn.mono` / 定理 `SurjOn.mono`

English:
theorem SurjOn.mono
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (hf : SurjOn f s₁ t₂)
  statement: SurjOn f s₂ t₁
  proof: Subset.trans ht Subset.trans hf image_mono hs

中文:
定理 SurjOn.mono
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (hf : SurjOn f s₁ t₂)
  结论: SurjOn f s₂ t₁
  证明: Subset.trans ht Subset.trans hf image_mono hs

Depends on / 依赖: Subset, Subset.trans, image_mono
-/
theorem SurjOn.mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
Subset.trans ht Subset.trans hf image_mono hs

/--
theorem `SurjOn.union` / 定理 `SurjOn.union`

English:
theorem SurjOn.union
  given: (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂)
  statement: SurjOn f s (t₁ union t₂)
  proof: fun _ hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx

中文:
定理 SurjOn.union
  条件: (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂)
  结论: SurjOn f s (t₁ union t₂)
  证明: fun _ hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx
-/
theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ union t₂) := fun _ hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx

/--
theorem `SurjOn.union_union` / 定理 `SurjOn.union_union`

English:
theorem SurjOn.union_union
  given: (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂)
  proof: (h₁.mono subset_union_left (Subset.refl _)).union
    (h₂.mono subset_union_right (Subset.refl _))

中文:
定理 SurjOn.union_union
  条件: (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂)
  证明: (h₁.mono subset_union_left (Subset.refl _)).union
    (h₂.mono subset_union_right (Subset.refl _))

Depends on / 依赖: Subset, Subset.refl, subset_union_left, subset_union_right
-/
theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ union s₂) (t₁ union t₂) :=
  (h₁.mono subset_union_left (Subset.refl _)).union
    (h₂.mono subset_union_right (Subset.refl _))

/--
theorem `SurjOn.inter_inter` / 定理 `SurjOn.inter_inter`

English:
theorem SurjOn.inter_inter
  given: (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ union s₂))
  proof: by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) heq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩

中文:
定理 SurjOn.inter_inter
  条件: (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ union s₂))
  证明: by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) heq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩

Depends on / 依赖: Or.inl, Or.inr, heq.symm, mem_image_of_mem
-/
theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ union s₂)) :
    SurjOn f (s₁ inter s₂) (t₁ inter t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) heq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩

/--
theorem `SurjOn.inter` / 定理 `SurjOn.inter`

English:
theorem SurjOn.inter
  given: (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ union s₂))
  proof: inter_self t ▸ h₁.inter_inter h₂ h

中文:
定理 SurjOn.inter
  条件: (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ union s₂))
  证明: inter_self t ▸ h₁.inter_inter h₂ h

Depends on / 依赖: inter_inter, inter_self
-/
theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ union s₂)) :
    SurjOn f (s₁ inter s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h

/--
lemma `surjOn_id` / 引理 `surjOn_id`

English:
lemma surjOn_id
  given: (s : Set α)
  statement: SurjOn id s s
  proof: by simp [SurjOn]

中文:
引理 surjOn_id
  条件: (s : Set α)
  结论: SurjOn id s s
  证明: by simp [SurjOn]

Depends on / 依赖: SurjOn
-/
lemma surjOn_id (s : Set α) : SurjOn id s s := by simp [SurjOn]

/--
theorem `SurjOn.comp` / 定理 `SurjOn.comp`

English:
theorem SurjOn.comp
  given: (hg : SurjOn g t p) (hf : SurjOn f s t)
  statement: SurjOn (g ∘ f) s p
  proof: Subset.trans hg Subset.trans (image_mono hf) image_comp g f s ▸ Subset.refl _

中文:
定理 SurjOn.comp
  条件: (hg : SurjOn g t p) (hf : SurjOn f s t)
  结论: SurjOn (g ∘ f) s p
  证明: Subset.trans hg Subset.trans (image_mono hf) image_comp g f s ▸ Subset.refl _

Depends on / 依赖: Subset, Subset.refl, Subset.trans, image_comp, image_mono
-/
theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
Subset.trans hg Subset.trans (image_mono hf) image_comp g f s ▸ Subset.refl _

/--
lemma `SurjOn.of_comp` / 引理 `SurjOn.of_comp`

English:
lemma SurjOn.of_comp
  given: (h : SurjOn (g ∘ f) s p) (hr : MapsTo f s t)
  statement: SurjOn g t p
  proof: by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩

中文:
引理 SurjOn.of_comp
  条件: (h : SurjOn (g ∘ f) s p) (hr : MapsTo f s t)
  结论: SurjOn g t p
  证明: by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩
-/
lemma SurjOn.of_comp (h : SurjOn (g ∘ f) s p) (hr : MapsTo f s t) : SurjOn g t p := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩

/--
lemma `surjOn_comp_iff` / 引理 `surjOn_comp_iff`

English:
lemma surjOn_comp_iff
  statement: SurjOn (g ∘ f) s p ↔ SurjOn g (f '' s) p
  proof: ⟨fun h => h.of_comp mapsTo_image f s, fun h => h.comp surjOn_image _ _⟩

中文:
引理 surjOn_comp_iff
  结论: SurjOn (g ∘ f) s p ↔ SurjOn g (f '' s) p
  证明: ⟨fun h => h.of_comp mapsTo_image f s, fun h => h.comp surjOn_image _ _⟩

Depends on / 依赖: h.comp, h.of_comp, mapsTo_image, of_comp, surjOn_image
-/
lemma surjOn_comp_iff : SurjOn (g ∘ f) s p ↔ SurjOn g (f '' s) p :=
⟨fun h => h.of_comp mapsTo_image f s, fun h => h.comp surjOn_image _ _⟩

/--
lemma `SurjOn.iterate` / 引理 `SurjOn.iterate`

English:
lemma SurjOn.iterate
  given: {f : α -> α} {s : Set α} (h : SurjOn f s s)
  statement: forall n, SurjOn f^[n] s s

中文:
引理 SurjOn.iterate
  条件: {f : α -> α} {s : Set α} (h : SurjOn f s s)
  结论: 对任意 n, SurjOn f^[n] s s
-/
lemma SurjOn.iterate {f : α -> α} {s : Set α} (h : SurjOn f s s) : forall n, SurjOn f^[n] s s
  | 0 => surjOn_id _
  | (n + 1) => (h.iterate n).comp h

/--
lemma `SurjOn.comp_left` / 引理 `SurjOn.comp_left`

English:
lemma SurjOn.comp_left
  given: (hf : SurjOn f s t) (g : β -> γ)
  statement: SurjOn (g ∘ f) s (g '' t)
  proof: by
  rw [SurjOn]; rw [image_comp g f]; exact image_mono hf

中文:
引理 SurjOn.comp_left
  条件: (hf : SurjOn f s t) (g : β -> γ)
  结论: SurjOn (g ∘ f) s (g '' t)
  证明: by
  rw [SurjOn]; rw [image_comp g f]; exact image_mono hf

Depends on / 依赖: SurjOn, image_comp, image_mono
-/
lemma SurjOn.comp_left (hf : SurjOn f s t) (g : β -> γ) : SurjOn (g ∘ f) s (g '' t) := by
  rw [SurjOn]; rw [image_comp g f]; exact image_mono hf

/--
lemma `SurjOn.comp_right` / 引理 `SurjOn.comp_right`

English:
lemma SurjOn.comp_right
  given: {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t)
  proof: by
  rwa [SurjOn, image_comp g f, image_preimage_eq _ hf]

中文:
引理 SurjOn.comp_right
  条件: {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t)
  证明: by
  rwa [SurjOn, image_comp g f, image_preimage_eq _ hf]

Depends on / 依赖: SurjOn, image_comp, image_preimage_eq
-/
lemma SurjOn.comp_right {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t) :
    SurjOn (g ∘ f) (f ⁻¹' s) t := by
  rwa [SurjOn, image_comp g f, image_preimage_eq _ hf]

/--
lemma `surjOn_of_subsingleton'` / 引理 `surjOn_of_subsingleton'`

English:
lemma surjOn_of_subsingleton'
  given: [Subsingleton β] (f : α -> β) (h : t.Nonempty -> s.Nonempty)
  proof: fun _ ha => Subsingleton.mem_iff_nonempty.2 (h ⟨_, ha⟩).image _

中文:
引理 surjOn_of_subsingleton'
  条件: [Subsingleton β] (f : α -> β) (h : t.Nonempty -> s.Nonempty)
  证明: fun _ ha => Subsingleton.mem_iff_nonempty.2 (h ⟨_, ha⟩).image _

Depends on / 依赖: Subsingleton, Subsingleton.mem_iff_nonempty, mem_iff_nonempty
-/
lemma surjOn_of_subsingleton' [Subsingleton β] (f : α -> β) (h : t.Nonempty -> s.Nonempty) :
    SurjOn f s t :=
fun _ ha => Subsingleton.mem_iff_nonempty.2 (h ⟨_, ha⟩).image _

/--
lemma `surjOn_of_subsingleton` / 引理 `surjOn_of_subsingleton`

English:
lemma surjOn_of_subsingleton
  given: [Subsingleton α] (f : α -> α) (s : Set α)
  statement: SurjOn f s s
  proof: surjOn_of_subsingleton' _ id

中文:
引理 surjOn_of_subsingleton
  条件: [Subsingleton α] (f : α -> α) (s : Set α)
  结论: SurjOn f s s
  证明: surjOn_of_subsingleton' _ id

Depends on / 依赖: surjOn_of_subsingleton
-/
lemma surjOn_of_subsingleton [Subsingleton α] (f : α -> α) (s : Set α) : SurjOn f s s :=
  surjOn_of_subsingleton' _ id

/--
lemma `surjOn_univ` / 引理 `surjOn_univ`

English:
lemma surjOn_univ
  statement: SurjOn f univ univ ↔ Surjective f
  proof: by
  simp [Surjective, SurjOn, subset_def]

中文:
引理 surjOn_univ
  结论: SurjOn f univ univ ↔ Surjective f
  证明: by
  simp [Surjective, SurjOn, subset_def]
-/
@[simp] lemma surjOn_univ : SurjOn f univ univ ↔ Surjective f := by
  simp [Surjective, SurjOn, subset_def]

/--
lemma `_root_.Function.Surjective.surjOn` / 引理 `_root_.Function.Surjective.surjOn`

English:
lemma _root_.Function.Surjective.surjOn
  given: (hf : Surjective f)
  statement: SurjOn f univ t
  proof: (surjOn_univ.2 hf).mono .rfl (subset_univ _)

中文:
引理 _root_.Function.Surjective.surjOn
  条件: (hf : Surjective f)
  结论: SurjOn f univ t
  证明: (surjOn_univ.2 hf).mono .rfl (subset_univ _)
-/
protected lemma _root_.Function.Surjective.surjOn (hf : Surjective f) : SurjOn f univ t :=
  (surjOn_univ.2 hf).mono .rfl (subset_univ _)

/--
lemma `SurjOn.surjective` / 引理 `SurjOn.surjective`

English:
lemma SurjOn.surjective
  given: (hf : SurjOn f s .univ)
  statement: f.Surjective
  proof: surjOn_univ.1 hf.mono s.subset_univ .rfl

中文:
引理 SurjOn.surjective
  条件: (hf : SurjOn f s .univ)
  结论: f.Surjective
  证明: surjOn_univ.1 hf.mono s.subset_univ .rfl

Depends on / 依赖: hf.mono, s.subset_univ, subset_univ, surjOn_univ
-/
lemma SurjOn.surjective (hf : SurjOn f s .univ) : f.Surjective :=
surjOn_univ.1 hf.mono s.subset_univ .rfl

/--
theorem `SurjOn.image_eq_of_mapsTo` / 定理 `SurjOn.image_eq_of_mapsTo`

English:
theorem SurjOn.image_eq_of_mapsTo
  given: (h₁ : SurjOn f s t) (h₂ : MapsTo f s t)
  statement: f '' s = t
  proof: eq_of_subset_of_subset h₂.image_subset h₁

中文:
定理 SurjOn.image_eq_of_mapsTo
  条件: (h₁ : SurjOn f s t) (h₂ : MapsTo f s t)
  结论: f '' s = t
  证明: eq_of_subset_of_subset h₂.image_subset h₁

Depends on / 依赖: eq_of_subset_of_subset, image_subset
-/
theorem SurjOn.image_eq_of_mapsTo (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁

/--
theorem `image_eq_iff_surjOn_mapsTo` / 定理 `image_eq_iff_surjOn_mapsTo`

English:
theorem image_eq_iff_surjOn_mapsTo
  statement: f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t
  proof: by
  refine ⟨?_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surjOn_image f, s.mapsTo_image f⟩

中文:
定理 image_eq_iff_surjOn_mapsTo
  结论: f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t
  证明: by
  refine ⟨?_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surjOn_image f, s.mapsTo_image f⟩

Depends on / 依赖: image_eq_of_mapsTo, mapsTo_image, s.mapsTo_image, s.surjOn_image, surjOn_image
-/
theorem image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t := by
  refine ⟨?_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surjOn_image f, s.mapsTo_image f⟩

/--
lemma `SurjOn.image_preimage` / 引理 `SurjOn.image_preimage`

English:
lemma SurjOn.image_preimage
  given: (h : Set.SurjOn f s t) (ht : t₁ subseteq t)
  statement: f '' f ⁻¹' t₁ = t₁
  proof: image_preimage_eq_iff.2 fun _ hx => mem_range_of_mem_image f s h ht hx

中文:
引理 SurjOn.image_preimage
  条件: (h : Set.SurjOn f s t) (ht : t₁ subseteq t)
  结论: f '' f ⁻¹' t₁ = t₁
  证明: image_preimage_eq_iff.2 fun _ hx => mem_range_of_mem_image f s h ht hx

Depends on / 依赖: image_preimage_eq_iff, mem_range_of_mem_image
-/
lemma SurjOn.image_preimage (h : Set.SurjOn f s t) (ht : t₁ subseteq t) : f '' f ⁻¹' t₁ = t₁ :=
image_preimage_eq_iff.2 fun _ hx => mem_range_of_mem_image f s h ht hx

/--
theorem `SurjOn.mapsTo_compl` / 定理 `SurjOn.mapsTo_compl`

English:
theorem SurjOn.mapsTo_compl
  given: (h : SurjOn f s t) (h' : Injective f)
  statement: MapsTo f sᶜ tᶜ
  proof: fun _ hs ht =>
  let ⟨_, hx', HEq⟩ := h ht
hs h' HEq ▸ hx'

中文:
定理 SurjOn.mapsTo_compl
  条件: (h : SurjOn f s t) (h' : Injective f)
  结论: MapsTo f sᶜ tᶜ
  证明: fun _ hs ht =>
  let ⟨_, hx', HEq⟩ := h ht
hs h' HEq ▸ hx'
-/
theorem SurjOn.mapsTo_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f sᶜ tᶜ :=
  fun _ hs ht =>
  let ⟨_, hx', HEq⟩ := h ht
hs h' HEq ▸ hx'

/--
theorem `MapsTo.surjOn_compl` / 定理 `MapsTo.surjOn_compl`

English:
theorem MapsTo.surjOn_compl
  given: (h : MapsTo f s t) (h' : Surjective f)
  statement: SurjOn f sᶜ tᶜ
  proof: h'.forall.2 fun _ ht => (mem_image_of_mem _) fun hs => ht (h hs)

中文:
定理 MapsTo.surjOn_compl
  条件: (h : MapsTo f s t) (h' : Surjective f)
  结论: SurjOn f sᶜ tᶜ
  证明: h'.forall.2 fun _ ht => (mem_image_of_mem _) fun hs => ht (h hs)

Depends on / 依赖: mem_image_of_mem
-/
theorem MapsTo.surjOn_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f sᶜ tᶜ :=
  h'.forall.2 fun _ ht => (mem_image_of_mem _) fun hs => ht (h hs)

/--
theorem `EqOn.cancel_right` / 定理 `EqOn.cancel_right`

English:
theorem EqOn.cancel_right
  given: (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t)
  statement: t.EqOn g₁ g₂
  proof: by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha

中文:
定理 EqOn.cancel_right
  条件: (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t)
  结论: t.EqOn g₁ g₂
  证明: by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha
-/
theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha

/--
theorem `SurjOn.cancel_right` / 定理 `SurjOn.cancel_right`

English:
theorem SurjOn.cancel_right
  given: (hf : s.SurjOn f t) (hf' : s.MapsTo f t)
  proof: ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩

中文:
定理 SurjOn.cancel_right
  条件: (hf : s.SurjOn f t) (hf' : s.MapsTo f t)
  证明: ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩

Depends on / 依赖: cancel_right, comp_right, h.cancel_right, h.comp_right
-/
theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩

/--
theorem `eqOn_comp_right_iff` / 定理 `eqOn_comp_right_iff`

English:
theorem eqOn_comp_right_iff
  statement: s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂
  proof: (s.surjOn_image f).cancel_right s.mapsTo_image f

中文:
定理 eqOn_comp_right_iff
  结论: s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂
  证明: (s.surjOn_image f).cancel_right s.mapsTo_image f

Depends on / 依赖: cancel_right, mapsTo_image, s.mapsTo_image, s.surjOn_image, surjOn_image
-/
theorem eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
(s.surjOn_image f).cancel_right s.mapsTo_image f

/--
theorem `SurjOn.forall` / 定理 `SurjOn.forall`

English:
theorem SurjOn.forall
  given: {p : β -> Prop} (hf : s.SurjOn f t) (hf' : s.MapsTo f t)
  proof: ⟨fun H x hx => H (f x) (hf' hx), fun H _y hy => let ⟨x, hx, hxy⟩ := hf hy; hxy ▸ H x hx⟩

中文:
定理 SurjOn.forall
  条件: {p : β -> 命题} (hf : s.SurjOn f t) (hf' : s.MapsTo f t)
  证明: ⟨fun H x hx => H (f x) (hf' hx), fun H _y hy => let ⟨x, hx, hxy⟩ := hf hy; hxy ▸ H x hx⟩
-/
theorem SurjOn.forall {p : β -> Prop} (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    (forall y in t, p y) ↔ (forall x in s, p (f x)) :=
  ⟨fun H x hx => H (f x) (hf' hx), fun H _y hy => let ⟨x, hx, hxy⟩ := hf hy; hxy ▸ H x hx⟩

/--
theorem `_root_.Subtype.coind_surjective` / 定理 `_root_.Subtype.coind_surjective`

English:
theorem _root_.Subtype.coind_surjective
  statement: {α β} {f : α -> β} {p : Set β} (h : forall a, f a in p)
  proof: fun ⟨_, hb⟩ =>
  let ⟨a, _, ha⟩ := hf hb
  ⟨a, Subtype.coe_injective ha⟩

中文:
定理 _root_.Subtype.coind_surjective
  结论: {α β} {f : α -> β} {p : Set β} (h : 对任意 a, f a in p)
  证明: fun ⟨_, hb⟩ =>
  let ⟨a, _, ha⟩ := hf hb
  ⟨a, Subtype.coe_injective ha⟩
-/
theorem _root_.Subtype.coind_surjective {α β} {f : α -> β} {p : Set β} (h : forall a, f a in p)
    (hf : Set.SurjOn f Set.univ p) :
    (Subtype.coind f h).Surjective := fun ⟨_, hb⟩ =>
  let ⟨a, _, ha⟩ := hf hb
  ⟨a, Subtype.coe_injective ha⟩

/--
theorem `_root_.Subtype.coind_bijective` / 定理 `_root_.Subtype.coind_bijective`

English:
theorem _root_.Subtype.coind_bijective
  statement: {α β} {f : α -> β} {p : Set β} (h : forall a, f a in p)
  proof: ⟨Subtype.coind_injective h hf_inj, Subtype.coind_surjective h hf_surj⟩

中文:
定理 _root_.Subtype.coind_bijective
  结论: {α β} {f : α -> β} {p : Set β} (h : 对任意 a, f a in p)
  证明: ⟨Subtype.coind_injective h hf_inj, Subtype.coind_surjective h hf_surj⟩

Depends on / 依赖: Subtype, Subtype.coind_injective, Subtype.coind_surjective, coind_injective, coind_surjective, hf_inj, hf_surj
-/
theorem _root_.Subtype.coind_bijective {α β} {f : α -> β} {p : Set β} (h : forall a, f a in p)
    (hf_inj : f.Injective) (hf_surj : Set.SurjOn f Set.univ p) :
    (Subtype.coind f h).Bijective :=
  ⟨Subtype.coind_injective h hf_inj, Subtype.coind_surjective h hf_surj⟩

end surjOn

/-! ### Bijectivity -/
section bijOn

/--
theorem `BijOn.mapsTo` / 定理 `BijOn.mapsTo`

English:
theorem BijOn.mapsTo
  given: (h : BijOn f s t)
  statement: MapsTo f s t
  proof: h.left

中文:
定理 BijOn.mapsTo
  条件: (h : BijOn f s t)
  结论: MapsTo f s t
  证明: h.left

Depends on / 依赖: h.left
-/
theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left

/--
theorem `BijOn.injOn` / 定理 `BijOn.injOn`

English:
theorem BijOn.injOn
  given: (h : BijOn f s t)
  statement: InjOn f s
  proof: h.right.left

中文:
定理 BijOn.injOn
  条件: (h : BijOn f s t)
  结论: InjOn f s
  证明: h.right.left

Depends on / 依赖: h.right.left
-/
theorem BijOn.injOn (h : BijOn f s t) : InjOn f s :=
  h.right.left

/--
theorem `BijOn.surjOn` / 定理 `BijOn.surjOn`

English:
theorem BijOn.surjOn
  given: (h : BijOn f s t)
  statement: SurjOn f s t
  proof: h.right.right

中文:
定理 BijOn.surjOn
  条件: (h : BijOn f s t)
  结论: SurjOn f s t
  证明: h.right.right

Depends on / 依赖: h.right.right
-/
theorem BijOn.surjOn (h : BijOn f s t) : SurjOn f s t :=
  h.right.right

/--
theorem `BijOn.mk` / 定理 `BijOn.mk`

English:
theorem BijOn.mk
  given: (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t)
  statement: BijOn f s t
  proof: ⟨h₁, h₂, h₃⟩

中文:
定理 BijOn.mk
  条件: (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t)
  结论: BijOn f s t
  证明: ⟨h₁, h₂, h₃⟩
-/
theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩

/--
theorem `bijOn_empty` / 定理 `bijOn_empty`

English:
theorem bijOn_empty
  given: (f : α -> β)
  statement: BijOn f ∅ ∅
  proof: ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩

中文:
定理 bijOn_empty
  条件: (f : α -> β)
  结论: BijOn f ∅ ∅
  证明: ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩

Depends on / 依赖: injOn_empty, mapsTo_empty, surjOn_empty
-/
theorem bijOn_empty (f : α -> β) : BijOn f ∅ ∅ :=
  ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩

/--
theorem `bijOn_empty_iff_left` / 定理 `bijOn_empty_iff_left`

English:
theorem bijOn_empty_iff_left
  statement: BijOn f s ∅ ↔ s = ∅
  proof: ⟨fun h => by simpa using h.mapsTo, by rintro rfl; exact bijOn_empty f⟩

中文:
定理 bijOn_empty_iff_left
  结论: BijOn f s ∅ ↔ s = ∅
  证明: ⟨fun h => by simpa using h.mapsTo, by rintro rfl; exact bijOn_empty f⟩
-/
@[simp] theorem bijOn_empty_iff_left : BijOn f s ∅ ↔ s = ∅ :=
  ⟨fun h => by simpa using h.mapsTo, by rintro rfl; exact bijOn_empty f⟩

/--
theorem `bijOn_empty_iff_right` / 定理 `bijOn_empty_iff_right`

English:
theorem bijOn_empty_iff_right
  statement: BijOn f ∅ t ↔ t = ∅
  proof: ⟨fun h => by simpa using h.surjOn, by rintro rfl; exact bijOn_empty f⟩

中文:
定理 bijOn_empty_iff_right
  结论: BijOn f ∅ t ↔ t = ∅
  证明: ⟨fun h => by simpa using h.surjOn, by rintro rfl; exact bijOn_empty f⟩
-/
@[simp] theorem bijOn_empty_iff_right : BijOn f ∅ t ↔ t = ∅ :=
  ⟨fun h => by simpa using h.surjOn, by rintro rfl; exact bijOn_empty f⟩

/--
lemma `bijOn_singleton` / 引理 `bijOn_singleton`

English:
lemma bijOn_singleton
  statement: BijOn f {a} {b} ↔ f a = b
  proof: by simp [BijOn, eq_comm]

中文:
引理 bijOn_singleton
  结论: BijOn f {a} {b} ↔ f a = b
  证明: by simp [BijOn, eq_comm]
-/
@[simp] lemma bijOn_singleton : BijOn f {a} {b} ↔ f a = b := by simp [BijOn, eq_comm]

/--
theorem `BijOn.inter_mapsTo` / 定理 `BijOn.inter_mapsTo`

English:
theorem BijOn.inter_mapsTo
  given: (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ inter f ⁻¹' t₂ subseteq s₂)
  proof: ⟨h₁.mapsTo.inter_inter h₂, h₁.injOn.mono inter_subset_left, fun _ hy =>
    let ⟨x, hx, hxy⟩ := h₁.surjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.subst hy.2⟩⟩, hxy⟩⟩

中文:
定理 BijOn.inter_mapsTo
  条件: (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ inter f ⁻¹' t₂ subseteq s₂)
  证明: ⟨h₁.mapsTo.inter_inter h₂, h₁.injOn.mono inter_subset_left, fun _ hy =>
    let ⟨x, hx, hxy⟩ := h₁.surjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.subst hy.2⟩⟩, hxy⟩⟩

Depends on / 依赖: hxy.symm.subst, injOn.mono, inter_inter, inter_subset_left, mapsTo, mapsTo.inter_inter, surjOn
-/
theorem BijOn.inter_mapsTo (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ inter f ⁻¹' t₂ subseteq s₂) :
    BijOn f (s₁ inter s₂) (t₁ inter t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂, h₁.injOn.mono inter_subset_left, fun _ hy =>
    let ⟨x, hx, hxy⟩ := h₁.surjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.subst hy.2⟩⟩, hxy⟩⟩

/--
theorem `MapsTo.inter_bijOn` / 定理 `MapsTo.inter_bijOn`

English:
theorem MapsTo.inter_bijOn
  given: (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ inter f ⁻¹' t₁ subseteq s₁)
  proof: inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃

中文:
定理 MapsTo.inter_bijOn
  条件: (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ inter f ⁻¹' t₁ subseteq s₁)
  证明: inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃

Depends on / 依赖: inter_comm, inter_mapsTo
-/
theorem MapsTo.inter_bijOn (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ inter f ⁻¹' t₁ subseteq s₁) :
    BijOn f (s₁ inter s₂) (t₁ inter t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃

/--
theorem `BijOn.inter` / 定理 `BijOn.inter`

English:
theorem BijOn.inter
  given: (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ union s₂))
  proof: ⟨h₁.mapsTo.inter_inter h₂.mapsTo, h₁.injOn.mono inter_subset_left,
    h₁.surjOn.inter_inter h₂.surjOn h⟩

中文:
定理 BijOn.inter
  条件: (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ union s₂))
  证明: ⟨h₁.mapsTo.inter_inter h₂.mapsTo, h₁.injOn.mono inter_subset_left,
    h₁.surjOn.inter_inter h₂.surjOn h⟩

Depends on / 依赖: injOn.mono, inter_inter, inter_subset_left, mapsTo, mapsTo.inter_inter, surjOn, surjOn.inter_inter
-/
theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ union s₂)) :
    BijOn f (s₁ inter s₂) (t₁ inter t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂.mapsTo, h₁.injOn.mono inter_subset_left,
    h₁.surjOn.inter_inter h₂.surjOn h⟩

/--
theorem `BijOn.union` / 定理 `BijOn.union`

English:
theorem BijOn.union
  given: (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ union s₂))
  proof: ⟨h₁.mapsTo.union_union h₂.mapsTo, h, h₁.surjOn.union_union h₂.surjOn⟩

中文:
定理 BijOn.union
  条件: (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ union s₂))
  证明: ⟨h₁.mapsTo.union_union h₂.mapsTo, h, h₁.surjOn.union_union h₂.surjOn⟩

Depends on / 依赖: mapsTo, mapsTo.union_union, surjOn, surjOn.union_union, union_union
-/
theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ union s₂)) :
    BijOn f (s₁ union s₂) (t₁ union t₂) :=
  ⟨h₁.mapsTo.union_union h₂.mapsTo, h, h₁.surjOn.union_union h₂.surjOn⟩

/--
theorem `BijOn.subset_range` / 定理 `BijOn.subset_range`

English:
theorem BijOn.subset_range
  given: (h : BijOn f s t)
  statement: t subseteq range f
  proof: h.surjOn.subset_range

中文:
定理 BijOn.subset_range
  条件: (h : BijOn f s t)
  结论: t subseteq range f
  证明: h.surjOn.subset_range

Depends on / 依赖: h.surjOn.subset_range, subset_range, surjOn
-/
theorem BijOn.subset_range (h : BijOn f s t) : t subseteq range f :=
  h.surjOn.subset_range

/--
theorem `InjOn.bijOn_image` / 定理 `InjOn.bijOn_image`

English:
theorem InjOn.bijOn_image
  given: (h : InjOn f s)
  statement: BijOn f s (f '' s)
  proof: BijOn.mk (mapsTo_image f s) h (Subset.refl _)

中文:
定理 InjOn.bijOn_image
  条件: (h : InjOn f s)
  结论: BijOn f s (f '' s)
  证明: BijOn.mk (mapsTo_image f s) h (Subset.refl _)

Depends on / 依赖: BijOn.mk, Subset, Subset.refl, mapsTo_image
-/
theorem InjOn.bijOn_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (mapsTo_image f s) h (Subset.refl _)

/--
theorem `SurjOn.preimage` / 定理 `SurjOn.preimage`

English:
theorem SurjOn.preimage
  given: (h : SurjOn f s t)
  statement: SurjOn f (f ⁻¹' t) t
  proof: by
  intro u hu
  rw [image_preimage_eq_inter_range]
  exact ⟨hu, mem_range.mpr (subset_range h hu)⟩

中文:
定理 SurjOn.preimage
  条件: (h : SurjOn f s t)
  结论: SurjOn f (f ⁻¹' t) t
  证明: by
  intro u hu
  rw [image_preimage_eq_inter_range]
  exact ⟨hu, mem_range.mpr (subset_range h hu)⟩

Depends on / 依赖: image_preimage_eq_inter_range, mem_range, mem_range.mpr, subset_range
-/
theorem SurjOn.preimage (h : SurjOn f s t) : SurjOn f (f ⁻¹' t) t := by
  intro u hu
  rw [image_preimage_eq_inter_range]
  exact ⟨hu, mem_range.mpr (subset_range h hu)⟩

/--
theorem `BijOn.congr` / 定理 `BijOn.congr`

English:
theorem BijOn.congr
  given: (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s)
  statement: BijOn f₂ s t
  proof: BijOn.mk (h₁.mapsTo.congr h) (h₁.injOn.congr h) (h₁.surjOn.congr h)

中文:
定理 BijOn.congr
  条件: (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s)
  结论: BijOn f₂ s t
  证明: BijOn.mk (h₁.mapsTo.congr h) (h₁.injOn.congr h) (h₁.surjOn.congr h)

Depends on / 依赖: BijOn.mk, injOn.congr, mapsTo, mapsTo.congr, surjOn, surjOn.congr
-/
theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.mapsTo.congr h) (h₁.injOn.congr h) (h₁.surjOn.congr h)

/--
theorem `EqOn.bijOn_iff` / 定理 `EqOn.bijOn_iff`

English:
theorem EqOn.bijOn_iff
  given: (H : EqOn f₁ f₂ s)
  statement: BijOn f₁ s t ↔ BijOn f₂ s t
  proof: ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

中文:
定理 EqOn.bijOn_iff
  条件: (H : EqOn f₁ f₂ s)
  结论: BijOn f₁ s t ↔ BijOn f₂ s t
  证明: ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

Depends on / 依赖: H.symm, h.congr
-/
theorem EqOn.bijOn_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

/--
theorem `BijOn.image_eq` / 定理 `BijOn.image_eq`

English:
theorem BijOn.image_eq
  given: (h : BijOn f s t)
  statement: f '' s = t
  proof: h.surjOn.image_eq_of_mapsTo h.mapsTo

中文:
定理 BijOn.image_eq
  条件: (h : BijOn f s t)
  结论: f '' s = t
  证明: h.surjOn.image_eq_of_mapsTo h.mapsTo

Depends on / 依赖: h.mapsTo, h.surjOn.image_eq_of_mapsTo, image_eq_of_mapsTo, mapsTo, surjOn
-/
theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.surjOn.image_eq_of_mapsTo h.mapsTo

/--
lemma `BijOn.forall` / 引理 `BijOn.forall`

English:
lemma BijOn.forall
  given: {p : β -> Prop} (hf : BijOn f s t)
  statement: (forall b in t, p b) ↔ forall a in s, p (f a) where
  proof: h _ hf.mapsTo ha
  mpr h b hb := by obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact h _ ha

中文:
引理 BijOn.forall
  条件: {p : β -> 命题} (hf : BijOn f s t)
  结论: (对任意 b in t, p b) ↔ 对任意 a in s, p (f a) where
  证明: h _ hf.mapsTo ha
  mpr h b hb := by obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact h _ ha

Depends on / 依赖: hf.mapsTo, mapsTo
-/
lemma BijOn.forall {p : β -> Prop} (hf : BijOn f s t) : (forall b in t, p b) ↔ forall a in s, p (f a) where
mp h _ ha := h _ hf.mapsTo ha
  mpr h b hb := by obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact h _ ha

/--
lemma `BijOn.exists` / 引理 `BijOn.exists`

English:
lemma BijOn.exists
  given: {p : β -> Prop} (hf : BijOn f s t)
  statement: (exists b in t, p b) ↔ exists a in s, p (f a) where
  proof: by rintro ⟨b, hb, h⟩; obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact ⟨a, ha, h⟩
  mpr := by rintro ⟨a, ha, h⟩; exact ⟨f a, hf.mapsTo ha, h⟩

中文:
引理 BijOn.exists
  条件: {p : β -> 命题} (hf : BijOn f s t)
  结论: (存在 b in t, p b) ↔ 存在 a in s, p (f a) where
  证明: by rintro ⟨b, hb, h⟩; obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact ⟨a, ha, h⟩
  mpr := by rintro ⟨a, ha, h⟩; exact ⟨f a, hf.mapsTo ha, h⟩

Depends on / 依赖: hf.mapsTo, hf.surjOn, mapsTo, surjOn
-/
lemma BijOn.exists {p : β -> Prop} (hf : BijOn f s t) : (exists b in t, p b) ↔ exists a in s, p (f a) where
  mp := by rintro ⟨b, hb, h⟩; obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact ⟨a, ha, h⟩
  mpr := by rintro ⟨a, ha, h⟩; exact ⟨f a, hf.mapsTo ha, h⟩

/--
lemma `_root_.Equiv.image_eq_iff_bijOn` / 引理 `_root_.Equiv.image_eq_iff_bijOn`

English:
lemma _root_.Equiv.image_eq_iff_bijOn
  given: (e : α ≃ β)
  statement: e '' s = t ↔ BijOn e s t
  proof: ⟨fun h => ⟨(mapsTo_image e s).mono_right h.subset, e.injective.injOn, h ▸ surjOn_image e s⟩,
  BijOn.image_eq⟩

中文:
引理 _root_.Equiv.image_eq_iff_bijOn
  条件: (e : α ≃ β)
  结论: e '' s = t ↔ BijOn e s t
  证明: ⟨fun h => ⟨(mapsTo_image e s).mono_right h.subset, e.injective.injOn, h ▸ surjOn_image e s⟩,
  BijOn.image_eq⟩

Depends on / 依赖: BijOn.image_eq, e.injective.injOn, h.subset, image_eq, injective, mapsTo_image, mono_right, subset, surjOn_image
-/
lemma _root_.Equiv.image_eq_iff_bijOn (e : α ≃ β) : e '' s = t ↔ BijOn e s t :=
  ⟨fun h => ⟨(mapsTo_image e s).mono_right h.subset, e.injective.injOn, h ▸ surjOn_image e s⟩,
  BijOn.image_eq⟩

/--
lemma `bijOn_id` / 引理 `bijOn_id`

English:
lemma bijOn_id
  given: (s : Set α)
  statement: BijOn id s s
  proof: ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩

中文:
引理 bijOn_id
  条件: (s : Set α)
  结论: BijOn id s s
  证明: ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩

Depends on / 依赖: injOn_id, mapsTo_id, s.injOn_id, s.mapsTo_id, s.surjOn_id, surjOn_id
-/
lemma bijOn_id (s : Set α) : BijOn id s s := ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩

/--
theorem `BijOn.comp` / 定理 `BijOn.comp`

English:
theorem BijOn.comp
  given: (hg : BijOn g t p) (hf : BijOn f s t)
  statement: BijOn (g ∘ f) s p
  proof: BijOn.mk (hg.mapsTo.comp hf.mapsTo) (hg.injOn.comp hf.injOn hf.mapsTo) (hg.surjOn.comp hf.surjOn)

中文:
定理 BijOn.comp
  条件: (hg : BijOn g t p) (hf : BijOn f s t)
  结论: BijOn (g ∘ f) s p
  证明: BijOn.mk (hg.mapsTo.comp hf.mapsTo) (hg.injOn.comp hf.injOn hf.mapsTo) (hg.surjOn.comp hf.surjOn)

Depends on / 依赖: BijOn.mk, hf.injOn, hf.mapsTo, hf.surjOn, hg.injOn.comp, hg.mapsTo.comp, hg.surjOn.comp, mapsTo, surjOn
-/
theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.mapsTo.comp hf.mapsTo) (hg.injOn.comp hf.injOn hf.mapsTo) (hg.surjOn.comp hf.surjOn)

/--
theorem `bijOn_comp_iff` / 定理 `bijOn_comp_iff`

English:
theorem bijOn_comp_iff
  given: (hf : InjOn f s)
  statement: BijOn (g ∘ f) s p ↔ BijOn g (f '' s) p
  proof: by
  simp only [BijOn, InjOn.comp_iff, surjOn_comp_iff, mapsTo_image_iff, hf]

中文:
定理 bijOn_comp_iff
  条件: (hf : InjOn f s)
  结论: BijOn (g ∘ f) s p ↔ BijOn g (f '' s) p
  证明: by
  simp only [BijOn, InjOn.comp_iff, surjOn_comp_iff, mapsTo_image_iff, hf]

Depends on / 依赖: InjOn.comp_iff, comp_iff, mapsTo_image_iff, surjOn_comp_iff
-/
theorem bijOn_comp_iff (hf : InjOn f s) : BijOn (g ∘ f) s p ↔ BijOn g (f '' s) p := by
  simp only [BijOn, InjOn.comp_iff, surjOn_comp_iff, mapsTo_image_iff, hf]

/--
theorem `bijOn_image_image` / 定理 `bijOn_image_image`

English:
theorem bijOn_image_image
  statement: {p₁ : α -> γ} {p₂ : β -> δ} {g : γ -> δ} (comm : forall a, p₂ (f a) = g (p₁ a))
  proof: by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    grind

中文:
定理 bijOn_image_image
  结论: {p₁ : α -> γ} {p₂ : β -> δ} {g : γ -> δ} (comm : 对任意 a, p₂ (f a) = g (p₁ a))
  证明: by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    grind
-/
theorem bijOn_image_image {p₁ : α -> γ} {p₂ : β -> δ} {g : γ -> δ} (comm : forall a, p₂ (f a) = g (p₁ a))
    (hbij : BijOn f s t) (hinj : InjOn g (p₁ '' s)) : BijOn g (p₁ '' s) (p₂ '' t) := by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    grind

/--
lemma `BijOn.iterate` / 引理 `BijOn.iterate`

English:
lemma BijOn.iterate
  given: {f : α -> α} {s : Set α} (h : BijOn f s s)
  statement: forall n, BijOn f^[n] s s

中文:
引理 BijOn.iterate
  条件: {f : α -> α} {s : Set α} (h : BijOn f s s)
  结论: 对任意 n, BijOn f^[n] s s
-/
lemma BijOn.iterate {f : α -> α} {s : Set α} (h : BijOn f s s) : forall n, BijOn f^[n] s s
  | 0 => s.bijOn_id
  | (n + 1) => (h.iterate n).comp h

/--
lemma `bijOn_of_subsingleton'` / 引理 `bijOn_of_subsingleton'`

English:
lemma bijOn_of_subsingleton'
  statement: [Subsingleton α] [Subsingleton β] (f : α -> β)
  proof: ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩

中文:
引理 bijOn_of_subsingleton'
  结论: [Subsingleton α] [Subsingleton β] (f : α -> β)
  证明: ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩

Depends on / 依赖: injOn_of_subsingleton, mapsTo_of_subsingleton, surjOn_of_subsingleton
-/
lemma bijOn_of_subsingleton' [Subsingleton α] [Subsingleton β] (f : α -> β)
    (h : s.Nonempty ↔ t.Nonempty) : BijOn f s t :=
  ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩

/--
lemma `bijOn_of_subsingleton` / 引理 `bijOn_of_subsingleton`

English:
lemma bijOn_of_subsingleton
  given: [Subsingleton α] (f : α -> α) (s : Set α)
  statement: BijOn f s s
  proof: bijOn_of_subsingleton' _ Iff.rfl

中文:
引理 bijOn_of_subsingleton
  条件: [Subsingleton α] (f : α -> α) (s : Set α)
  结论: BijOn f s s
  证明: bijOn_of_subsingleton' _ Iff.rfl

Depends on / 依赖: Iff.rfl, bijOn_of_subsingleton
-/
lemma bijOn_of_subsingleton [Subsingleton α] (f : α -> α) (s : Set α) : BijOn f s s :=
  bijOn_of_subsingleton' _ Iff.rfl

/--
theorem `BijOn.bijective` / 定理 `BijOn.bijective`

English:
theorem BijOn.bijective
  given: (h : BijOn f s t)
  statement: Bijective (h.mapsTo.restrict f s t)
  proof: ⟨fun x y h' => Subtype.ext h.injOn x.2 y.2 Subtype.ext_iff.1 h', fun ⟨_, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surjOn hy
    ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

中文:
定理 BijOn.bijective
  条件: (h : BijOn f s t)
  结论: Bijective (h.mapsTo.restrict f s t)
  证明: ⟨fun x y h' => Subtype.ext h.injOn x.2 y.2 Subtype.ext_iff.1 h', fun ⟨_, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surjOn hy
    ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.ext_iff, ext_iff, h.injOn, h.surjOn, surjOn
-/
theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.mapsTo.restrict f s t) :=
⟨fun x y h' => Subtype.ext h.injOn x.2 y.2 Subtype.ext_iff.1 h', fun ⟨_, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surjOn hy
    ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/--
lemma `bijOn_univ` / 引理 `bijOn_univ`

English:
lemma bijOn_univ
  statement: BijOn f univ univ ↔ Bijective f
  proof: by simp [Bijective, BijOn]

protected alias ⟨_, _root_.Function.Bijective.bijOn_univ⟩ := bijOn_univ

中文:
引理 bijOn_univ
  结论: BijOn f univ univ ↔ Bijective f
  证明: by simp [Bijective, BijOn]

protected alias ⟨_, _root_.Function.Bijective.bijOn_univ⟩ := bijOn_univ
-/
@[simp] lemma bijOn_univ : BijOn f univ univ ↔ Bijective f := by simp [Bijective, BijOn]

protected alias ⟨_, _root_.Function.Bijective.bijOn_univ⟩ := bijOn_univ

/--
lemma `_root_.Function.Injective.bijOn_image` / 引理 `_root_.Function.Injective.bijOn_image`

English:
lemma _root_.Function.Injective.bijOn_image
  given: (hf : f.Injective)
  statement: BijOn f s (f '' s)
  proof: hf.injOn.bijOn_image

中文:
引理 _root_.Function.Injective.bijOn_image
  条件: (hf : f.Injective)
  结论: BijOn f s (f '' s)
  证明: hf.injOn.bijOn_image

Depends on / 依赖: bijOn_image, hf.injOn.bijOn_image
-/
lemma _root_.Function.Injective.bijOn_image (hf : f.Injective) : BijOn f s (f '' s) :=
  hf.injOn.bijOn_image

/--
lemma `_root_.Function.Surjective.surjOn_preimage` / 引理 `_root_.Function.Surjective.surjOn_preimage`

English:
lemma _root_.Function.Surjective.surjOn_preimage
  given: (hf : f.Surjective)
  statement: SurjOn f (f ⁻¹' t) t
  proof: hf.surjOn.preimage

中文:
引理 _root_.Function.Surjective.surjOn_preimage
  条件: (hf : f.Surjective)
  结论: SurjOn f (f ⁻¹' t) t
  证明: hf.surjOn.preimage

Depends on / 依赖: hf.surjOn.preimage, preimage, surjOn
-/
lemma _root_.Function.Surjective.surjOn_preimage (hf : f.Surjective) : SurjOn f (f ⁻¹' t) t :=
  hf.surjOn.preimage

/--
lemma `_root_.Function.Bijective.bijOn_preimage` / 引理 `_root_.Function.Bijective.bijOn_preimage`

English:
lemma _root_.Function.Bijective.bijOn_preimage
  given: (hf : f.Bijective)
  statement: BijOn f (f ⁻¹' t) t
  proof: ⟨fun _ => id, hf.injective.injOn, hf.surjective.surjOn_preimage⟩

中文:
引理 _root_.Function.Bijective.bijOn_preimage
  条件: (hf : f.Bijective)
  结论: BijOn f (f ⁻¹' t) t
  证明: ⟨fun _ => id, hf.injective.injOn, hf.surjective.surjOn_preimage⟩

Depends on / 依赖: hf.injective.injOn, hf.surjective.surjOn_preimage, injective, surjOn_preimage, surjective
-/
lemma _root_.Function.Bijective.bijOn_preimage (hf : f.Bijective) : BijOn f (f ⁻¹' t) t :=
  ⟨fun _ => id, hf.injective.injOn, hf.surjective.surjOn_preimage⟩

/--
theorem `BijOn.compl` / 定理 `BijOn.compl`

English:
theorem BijOn.compl
  given: (hst : BijOn f s t) (hf : Bijective f)
  statement: BijOn f sᶜ tᶜ
  proof: ⟨hst.surjOn.mapsTo_compl hf.1, hf.1.injOn, hst.mapsTo.surjOn_compl hf.2⟩

中文:
定理 BijOn.compl
  条件: (hst : BijOn f s t) (hf : Bijective f)
  结论: BijOn f sᶜ tᶜ
  证明: ⟨hst.surjOn.mapsTo_compl hf.1, hf.1.injOn, hst.mapsTo.surjOn_compl hf.2⟩

Depends on / 依赖: hst.mapsTo.surjOn_compl, hst.surjOn.mapsTo_compl, mapsTo, mapsTo_compl, surjOn, surjOn_compl
-/
theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f sᶜ tᶜ :=
  ⟨hst.surjOn.mapsTo_compl hf.1, hf.1.injOn, hst.mapsTo.surjOn_compl hf.2⟩

/--
theorem `BijOn.subset_right` / 定理 `BijOn.subset_right`

English:
theorem BijOn.subset_right
  given: {r : Set β} (hf : BijOn f s t) (hrt : r subseteq t)
  proof: by
  refine ⟨inter_subset_right, hf.injOn.mono inter_subset_left, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hrt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩

中文:
定理 BijOn.subset_right
  条件: {r : Set β} (hf : BijOn f s t) (hrt : r subseteq t)
  证明: by
  refine ⟨inter_subset_right, hf.injOn.mono inter_subset_left, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hrt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩

Depends on / 依赖: hf.injOn.mono, hf.surjOn, inter_subset_left, inter_subset_right, surjOn
-/
theorem BijOn.subset_right {r : Set β} (hf : BijOn f s t) (hrt : r subseteq t) :
    BijOn f (s inter f ⁻¹' r) r := by
  refine ⟨inter_subset_right, hf.injOn.mono inter_subset_left, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hrt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩

/--
theorem `BijOn.subset_left` / 定理 `BijOn.subset_left`

English:
theorem BijOn.subset_left
  given: {r : Set α} (hf : BijOn f s t) (hrs : r subseteq s)
  proof: (hf.injOn.mono hrs).bijOn_image

中文:
定理 BijOn.subset_left
  条件: {r : Set α} (hf : BijOn f s t) (hrs : r subseteq s)
  证明: (hf.injOn.mono hrs).bijOn_image

Depends on / 依赖: bijOn_image, hf.injOn.mono
-/
theorem BijOn.subset_left {r : Set α} (hf : BijOn f s t) (hrs : r subseteq s) :
    BijOn f r (f '' r) :=
  (hf.injOn.mono hrs).bijOn_image

/--
theorem `BijOn.insert_iff` / 定理 `BijOn.insert_iff`

English:
theorem BijOn.insert_iff
  given: (ha : a ∉ s) (hfa : f a ∉ t)
  proof: by
    have := congrArg (· \ {f a}) (image_insert_eq ▸ h.image_eq)
    simp only [mem_singleton_iff, insert_sdiff_of_mem] at this
    rw [sdiff_singleton_eq_self hfa]; rw [sdiff_singleton_eq_self] at this
    · exact ⟨by simp [← this, mapsTo_iff_image_subset], h.injOn.mono (subset_insert ..),
      

中文:
定理 BijOn.insert_iff
  条件: (ha : a ∉ s) (hfa : f a ∉ t)
  证明: by
    have := congrArg (· \ {f a}) (image_insert_eq ▸ h.image_eq)
    simp only [mem_singleton_iff, insert_sdiff_of_mem] at this
    rw [sdiff_singleton_eq_self hfa]; rw [sdiff_singleton_eq_self] at this
    · exact ⟨by simp [← this, mapsTo_iff_image_subset], h.injOn.mono (subset_insert ..),
      

Depends on / 依赖: bijOn_singleton, bijOn_singleton.mpr, eq_iff, h.image_eq, h.injOn.eq_iff, h.injOn.mono, image_eq, image_insert_eq, insert_eq, insert_sdiff_of_mem, mapsTo_iff_image_subset, mem_image, mem_singleton_iff, not_and, not_exists, repeat, sdiff_singleton_eq_self, subset_insert, surjOn_image
-/
theorem BijOn.insert_iff (ha : a ∉ s) (hfa : f a ∉ t) :
    BijOn f (insert a s) (insert (f a) t) ↔ BijOn f s t where
  mp h := by
    have := congrArg (· \ {f a}) (image_insert_eq ▸ h.image_eq)
    simp only [mem_singleton_iff, insert_sdiff_of_mem] at this
    rw [sdiff_singleton_eq_self hfa]; rw [sdiff_singleton_eq_self] at this
    · exact ⟨by simp [← this, mapsTo_iff_image_subset], h.injOn.mono (subset_insert ..),
        by simp [← this, surjOn_image]⟩
    simp only [mem_image, not_exists, not_and]
    intro x hx
    rw [h.injOn.eq_iff (by simp [hx]) (by simp)]
    exact ha ∘ (· ▸ hx)
  mpr h := by
    repeat rw [insert_eq]
    refine (bijOn_singleton.mpr rfl).union h ?_
    simp only [singleton_union, injOn_insert fun x => (hfa (h.mapsTo x)), h.injOn, mem_image,
      not_exists, not_and, true_and]
    exact fun _ hx h₂ => hfa (h₂ ▸ h.mapsTo hx)

/--
theorem `BijOn.insert` / 定理 `BijOn.insert`

English:
theorem BijOn.insert
  given: (h₁ : BijOn f s t) (h₂ : f a ∉ t)
  proof: (insert_iff (h₂ <| h₁.mapsTo ·) h₂).mpr h₁

中文:
定理 BijOn.insert
  条件: (h₁ : BijOn f s t) (h₂ : f a ∉ t)
  证明: (insert_iff (h₂ <| h₁.mapsTo ·) h₂).mpr h₁

Depends on / 依赖: insert_iff, mapsTo
-/
theorem BijOn.insert (h₁ : BijOn f s t) (h₂ : f a ∉ t) :
    BijOn f (insert a s) (insert (f a) t) :=
  (insert_iff (h₂ <| h₁.mapsTo ·) h₂).mpr h₁

/--
theorem `BijOn.sdiff_singleton` / 定理 `BijOn.sdiff_singleton`

English:
theorem BijOn.sdiff_singleton
  given: (h₁ : BijOn f s t) (h₂ : a in s)
  proof: by
  convert! h₁.subset_left sdiff_subset
  simp [h₁.injOn.image_sdiff, h₁.image_eq, h₂, inter_eq_self_of_subset_right]

中文:
定理 BijOn.sdiff_singleton
  条件: (h₁ : BijOn f s t) (h₂ : a in s)
  证明: by
  convert! h₁.subset_left sdiff_subset
  simp [h₁.injOn.image_sdiff, h₁.image_eq, h₂, inter_eq_self_of_subset_right]

Depends on / 依赖: convert, image_eq, image_sdiff, injOn.image_sdiff, inter_eq_self_of_subset_right, sdiff_subset, subset_left
-/
theorem BijOn.sdiff_singleton (h₁ : BijOn f s t) (h₂ : a in s) :
    BijOn f (s \ {a}) (t \ {f a}) := by
  convert! h₁.subset_left sdiff_subset
  simp [h₁.injOn.image_sdiff, h₁.image_eq, h₂, inter_eq_self_of_subset_right]

end bijOn

/-! ### left inverse -/
namespace LeftInvOn

/--
theorem `eqOn` / 定理 `eqOn`

English:
theorem eqOn
  given: (h : LeftInvOn f' f s)
  statement: EqOn (f' ∘ f) id s
  proof: h

中文:
定理 eqOn
  条件: (h : LeftInvOn f' f s)
  结论: EqOn (f' ∘ f) id s
  证明: h
-/
theorem eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (h : LeftInvOn f' f s) {x} (hx : x in s)
  statement: f' (f x) = x
  proof: h hx

中文:
定理 eq
  条件: (h : LeftInvOn f' f s) {x} (hx : x in s)
  结论: f' (f x) = x
  证明: h hx
-/
theorem eq (h : LeftInvOn f' f s) {x} (hx : x in s) : f' (f x) = x :=
  h hx

/--
theorem `congr_left` / 定理 `congr_left`

English:
theorem congr_left
  statement: (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
  proof: fun _ hx => heq (h₁' hx) ▸ h₁ hx

中文:
定理 congr_left
  结论: (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
  证明: fun _ hx => heq (h₁' hx) ▸ h₁ hx
-/
theorem congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun _ hx => heq (h₁' hx) ▸ h₁ hx

/--
theorem `congr_right` / 定理 `congr_right`

English:
theorem congr_right
  given: (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s)
  statement: LeftInvOn f₁' f₂ s
  proof: fun _ hx => heq hx ▸ h₁ hx

中文:
定理 congr_right
  条件: (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s)
  结论: LeftInvOn f₁' f₂ s
  证明: fun _ hx => heq hx ▸ h₁ hx
-/
theorem congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun _ hx => heq hx ▸ h₁ hx

/--
theorem `injOn` / 定理 `injOn`

English:
theorem injOn
  given: (h : LeftInvOn f₁' f s)
  statement: InjOn f s
  proof: fun x₁ h₁ x₂ h₂ heq =>
  calc
x₁ = f₁' (f x₁) := Eq.symm h h₁
    _ = f₁' (f x₂) := congr_arg f₁' heq
    _ = x₂ := h h₂

中文:
定理 injOn
  条件: (h : LeftInvOn f₁' f s)
  结论: InjOn f s
  证明: fun x₁ h₁ x₂ h₂ heq =>
  calc
x₁ = f₁' (f x₁) := Eq.symm h h₁
    _ = f₁' (f x₂) := congr_arg f₁' heq
    _ = x₂ := h h₂
-/
theorem injOn (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
x₁ = f₁' (f x₁) := Eq.symm h h₁
    _ = f₁' (f x₂) := congr_arg f₁' heq
    _ = x₂ := h h₂

/--
theorem `surjOn` / 定理 `surjOn`

English:
theorem surjOn
  given: (h : LeftInvOn f' f s) (hf : MapsTo f s t)
  statement: SurjOn f' t s
  proof: fun x hx =>
  ⟨f x, hf hx, h hx⟩

中文:
定理 surjOn
  条件: (h : LeftInvOn f' f s) (hf : MapsTo f s t)
  结论: SurjOn f' t s
  证明: fun x hx =>
  ⟨f x, hf hx, h hx⟩
-/
theorem surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩

/--
theorem `mapsTo` / 定理 `mapsTo`

English:
theorem mapsTo
  given: (h : LeftInvOn f' f s) (hf : SurjOn f s t)
  proof: fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]

中文:
定理 mapsTo
  条件: (h : LeftInvOn f' f s) (hf : SurjOn f s t)
  证明: fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]
-/
theorem mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) :
    MapsTo f' t s := fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]

/--
lemma `_root_.Set.leftInvOn_id` / 引理 `_root_.Set.leftInvOn_id`

English:
lemma _root_.Set.leftInvOn_id
  given: (s : Set α)
  statement: LeftInvOn id id s
  proof: fun _ _ => rfl

中文:
引理 _root_.Set.leftInvOn_id
  条件: (s : Set α)
  结论: LeftInvOn id id s
  证明: fun _ _ => rfl
-/
lemma _root_.Set.leftInvOn_id (s : Set α) : LeftInvOn id id s := fun _ _ => rfl

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t)
  proof: fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h

中文:
定理 comp
  条件: (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t)
  证明: fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h
-/
theorem comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : LeftInvOn f' f s) (ht : s₁ subseteq s)
  statement: LeftInvOn f' f s₁
  proof: fun _ hx =>
  hf (ht hx)

中文:
定理 mono
  条件: (hf : LeftInvOn f' f s) (ht : s₁ subseteq s)
  结论: LeftInvOn f' f s₁
  证明: fun _ hx =>
  hf (ht hx)
-/
theorem mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : LeftInvOn f' f s₁ := fun _ hx =>
  hf (ht hx)

/--
theorem `image_inter'` / 定理 `image_inter'`

English:
theorem image_inter'
  given: (hf : LeftInvOn f' f s)
  statement: f '' (s₁ inter s) = f' ⁻¹' s₁ inter f '' s
  proof: by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩

中文:
定理 image_inter'
  条件: (hf : LeftInvOn f' f s)
  结论: f '' (s₁ inter s) = f' ⁻¹' s₁ inter f '' s
  证明: by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm, mem_image_of_mem, mem_preimage
-/
theorem image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ inter s) = f' ⁻¹' s₁ inter f '' s := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩

/--
theorem `image_inter` / 定理 `image_inter`

English:
theorem image_inter
  given: (hf : LeftInvOn f' f s)
  proof: by
  rw [hf.image_inter']
  refine Subset.antisymm ?_ (inter_subset_inter_left _ (preimage_mono inter_subset_left))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩

中文:
定理 image_inter
  条件: (hf : LeftInvOn f' f s)
  证明: by
  rw [hf.image_inter']
  refine Subset.antisymm ?_ (inter_subset_inter_left _ (preimage_mono inter_subset_left))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm, hf.image_inter, image_inter, inter_subset_inter_left, inter_subset_left, mem_image_of_mem, preimage_mono
-/
theorem image_inter (hf : LeftInvOn f' f s) :
    f '' (s₁ inter s) = f' ⁻¹' (s₁ inter s) inter f '' s := by
  rw [hf.image_inter']
  refine Subset.antisymm ?_ (inter_subset_inter_left _ (preimage_mono inter_subset_left))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩

/--
theorem `image_image` / 定理 `image_image`

English:
theorem image_image
  given: (hf : LeftInvOn f' f s)
  statement: f' '' f '' s = s
  proof: by
  rw [Set.image_image]; rw [image_congr hf]; rw [image_id']

中文:
定理 image_image
  条件: (hf : LeftInvOn f' f s)
  结论: f' '' f '' s = s
  证明: by
  rw [Set.image_image]; rw [image_congr hf]; rw [image_id']

Depends on / 依赖: Set.image_image, image_congr, image_id, image_image
-/
theorem image_image (hf : LeftInvOn f' f s) : f' '' f '' s = s := by
  rw [Set.image_image]; rw [image_congr hf]; rw [image_id']

/--
theorem `image_image'` / 定理 `image_image'`

English:
theorem image_image'
  given: (hf : LeftInvOn f' f s) (hs : s₁ subseteq s)
  statement: f' '' f '' s₁ = s₁
  proof: (hf.mono hs).image_image

中文:
定理 image_image'
  条件: (hf : LeftInvOn f' f s) (hs : s₁ subseteq s)
  结论: f' '' f '' s₁ = s₁
  证明: (hf.mono hs).image_image

Depends on / 依赖: hf.mono, image_image
-/
theorem image_image' (hf : LeftInvOn f' f s) (hs : s₁ subseteq s) : f' '' f '' s₁ = s₁ :=
  (hf.mono hs).image_image

end LeftInvOn

/-! ### Right inverse -/
section RightInvOn
namespace RightInvOn

/--
theorem `eqOn` / 定理 `eqOn`

English:
theorem eqOn
  given: (h : RightInvOn f' f t)
  statement: EqOn (f ∘ f') id t
  proof: h

中文:
定理 eqOn
  条件: (h : RightInvOn f' f t)
  结论: EqOn (f ∘ f') id t
  证明: h
-/
theorem eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (h : RightInvOn f' f t) {y} (hy : y in t)
  statement: f (f' y) = y
  proof: h hy

中文:
定理 eq
  条件: (h : RightInvOn f' f t) {y} (hy : y in t)
  结论: f (f' y) = y
  证明: h hy
-/
theorem eq (h : RightInvOn f' f t) {y} (hy : y in t) : f (f' y) = y :=
  h hy

/--
theorem `_root_.Set.LeftInvOn.rightInvOn_image` / 定理 `_root_.Set.LeftInvOn.rightInvOn_image`

English:
theorem _root_.Set.LeftInvOn.rightInvOn_image
  given: (h : LeftInvOn f' f s)
  statement: RightInvOn f' f (f '' s)
  proof: fun _y ⟨_x, hx, heq⟩ => heq ▸ (congr_arg f <| h.eq hx)

中文:
定理 _root_.Set.LeftInvOn.rightInvOn_image
  条件: (h : LeftInvOn f' f s)
  结论: RightInvOn f' f (f '' s)
  证明: fun _y ⟨_x, hx, heq⟩ => heq ▸ (congr_arg f <| h.eq hx)

Depends on / 依赖: congr_arg, h.eq
-/
theorem _root_.Set.LeftInvOn.rightInvOn_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun _y ⟨_x, hx, heq⟩ => heq ▸ (congr_arg f <| h.eq hx)

/--
theorem `congr_left` / 定理 `congr_left`

English:
theorem congr_left
  given: (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t)
  proof: h₁.congr_right heq

中文:
定理 congr_left
  条件: (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t)
  证明: h₁.congr_right heq

Depends on / 依赖: congr_right
-/
theorem congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right heq

/--
theorem `congr_right` / 定理 `congr_right`

English:
theorem congr_right
  given: (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s)
  proof: LeftInvOn.congr_left h₁ hg heq

中文:
定理 congr_right
  条件: (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s)
  证明: LeftInvOn.congr_left h₁ hg heq

Depends on / 依赖: LeftInvOn, LeftInvOn.congr_left, congr_left
-/
theorem congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg heq

/--
theorem `surjOn` / 定理 `surjOn`

English:
theorem surjOn
  given: (hf : RightInvOn f' f t) (hf' : MapsTo f' t s)
  statement: SurjOn f s t
  proof: LeftInvOn.surjOn hf hf'

中文:
定理 surjOn
  条件: (hf : RightInvOn f' f t) (hf' : MapsTo f' t s)
  结论: SurjOn f s t
  证明: LeftInvOn.surjOn hf hf'

Depends on / 依赖: LeftInvOn, LeftInvOn.surjOn, surjOn
-/
theorem surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  LeftInvOn.surjOn hf hf'

/--
theorem `mapsTo` / 定理 `mapsTo`

English:
theorem mapsTo
  given: (h : RightInvOn f' f t) (hf : SurjOn f' t s)
  statement: MapsTo f s t
  proof: LeftInvOn.mapsTo h hf

中文:
定理 mapsTo
  条件: (h : RightInvOn f' f t) (hf : SurjOn f' t s)
  结论: MapsTo f s t
  证明: LeftInvOn.mapsTo h hf

Depends on / 依赖: LeftInvOn, LeftInvOn.mapsTo, mapsTo
-/
theorem mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  LeftInvOn.mapsTo h hf

/--
lemma `_root_.Set.rightInvOn_id` / 引理 `_root_.Set.rightInvOn_id`

English:
lemma _root_.Set.rightInvOn_id
  given: (s : Set α)
  statement: RightInvOn id id s
  proof: fun _ _ => rfl

中文:
引理 _root_.Set.rightInvOn_id
  条件: (s : Set α)
  结论: RightInvOn id id s
  证明: fun _ _ => rfl
-/
lemma _root_.Set.rightInvOn_id (s : Set α) : RightInvOn id id s := fun _ _ => rfl

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t)
  proof: LeftInvOn.comp hg hf g'pt

中文:
定理 comp
  条件: (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t)
  证明: LeftInvOn.comp hg hf g'pt

Depends on / 依赖: LeftInvOn, LeftInvOn.comp
-/
theorem comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  LeftInvOn.comp hg hf g'pt

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : RightInvOn f' f t) (ht : t₁ subseteq t)
  statement: RightInvOn f' f t₁
  proof: LeftInvOn.mono hf ht

中文:
定理 mono
  条件: (hf : RightInvOn f' f t) (ht : t₁ subseteq t)
  结论: RightInvOn f' f t₁
  证明: LeftInvOn.mono hf ht

Depends on / 依赖: LeftInvOn, LeftInvOn.mono
-/
theorem mono (hf : RightInvOn f' f t) (ht : t₁ subseteq t) : RightInvOn f' f t₁ :=
  LeftInvOn.mono hf ht
end RightInvOn

/--
theorem `InjOn.rightInvOn_of_leftInvOn` / 定理 `InjOn.rightInvOn_of_leftInvOn`

English:
theorem InjOn.rightInvOn_of_leftInvOn
  statement: (hf : InjOn f s) (hf' : LeftInvOn f f' t)
  proof: fun _ h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))

中文:
定理 InjOn.rightInvOn_of_leftInvOn
  结论: (hf : InjOn f s) (hf' : LeftInvOn f f' t)
  证明: fun _ h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))
-/
theorem InjOn.rightInvOn_of_leftInvOn (hf : InjOn f s) (hf' : LeftInvOn f f' t)
    (h₁ : MapsTo f s t) (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun _ h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))

/--
theorem `eqOn_of_leftInvOn_of_rightInvOn` / 定理 `eqOn_of_leftInvOn_of_rightInvOn`

English:
theorem eqOn_of_leftInvOn_of_rightInvOn
  statement: (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
  proof: fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)

中文:
定理 eqOn_of_leftInvOn_of_rightInvOn
  结论: (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
  证明: fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
-/
theorem eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)

/--
theorem `SurjOn.leftInvOn_of_rightInvOn` / 定理 `SurjOn.leftInvOn_of_rightInvOn`

English:
theorem SurjOn.leftInvOn_of_rightInvOn
  given: (hf : SurjOn f s t) (hf' : RightInvOn f f' s)
  proof: fun y hy => by
  let ⟨x, hx, heq⟩ := hf hy
  rw [← heq]; rw [hf' hx]

中文:
定理 SurjOn.leftInvOn_of_rightInvOn
  条件: (hf : SurjOn f s t) (hf' : RightInvOn f f' s)
  证明: fun y hy => by
  let ⟨x, hx, heq⟩ := hf hy
  rw [← heq]; rw [hf' hx]
-/
theorem SurjOn.leftInvOn_of_rightInvOn (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by
  let ⟨x, hx, heq⟩ := hf hy
  rw [← heq]; rw [hf' hx]

/--
theorem `image_eq_preimage_of_leftInvOn_injOn` / 定理 `image_eq_preimage_of_leftInvOn_injOn`

English:
theorem image_eq_preimage_of_leftInvOn_injOn
  statement: {f : α -> β} {g : β -> α} {s : Set α}
  proof: by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_preimage]; rw [hgf hy]; exact hy
  · intro hx
    refine ⟨g x, hx, Set.InjOn.rightInvOn_of_leftInvOn ginj hgf (Set.mapsTo_preimage g s) ?_ hx⟩
    intro y hy
    simpa [hgf hy] using hy

@[deprecated (since := "2026-03-27")]
alias image_eq

中文:
定理 image_eq_preimage_of_leftInvOn_injOn
  结论: {f : α -> β} {g : β -> α} {s : Set α}
  证明: by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_preimage]; rw [hgf hy]; exact hy
  · intro hx
    refine ⟨g x, hx, Set.InjOn.rightInvOn_of_leftInvOn ginj hgf (Set.mapsTo_preimage g s) ?_ hx⟩
    intro y hy
    simpa [hgf hy] using hy

@[deprecated (since := "2026-03-27")]
alias image_eq

Depends on / 依赖: Set.InjOn.rightInvOn_of_leftInvOn, Set.mapsTo_preimage, mapsTo_preimage, mem_preimage, rightInvOn_of_leftInvOn
-/
theorem image_eq_preimage_of_leftInvOn_injOn {f : α -> β} {g : β -> α} {s : Set α}
    (hgf : LeftInvOn g f s) (ginj : Set.InjOn g (g ⁻¹' s)) : f '' s = g ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_preimage]; rw [hgf hy]; exact hy
  · intro hx
    refine ⟨g x, hx, Set.InjOn.rightInvOn_of_leftInvOn ginj hgf (Set.mapsTo_preimage g s) ?_ hx⟩
    intro y hy
    simpa [hgf hy] using hy

@[deprecated (since := "2026-03-27")]
alias image_eq_preimage_of_leftInvOn_injOn_mapsTo := image_eq_preimage_of_leftInvOn_injOn

end RightInvOn

/-! ### Two-side inverses -/
namespace InvOn

/--
lemma `_root_.Set.invOn_id` / 引理 `_root_.Set.invOn_id`

English:
lemma _root_.Set.invOn_id
  given: (s : Set α)
  statement: InvOn id id s s
  proof: ⟨s.leftInvOn_id, s.rightInvOn_id⟩

中文:
引理 _root_.Set.invOn_id
  条件: (s : Set α)
  结论: InvOn id id s s
  证明: ⟨s.leftInvOn_id, s.rightInvOn_id⟩

Depends on / 依赖: leftInvOn_id, rightInvOn_id, s.leftInvOn_id, s.rightInvOn_id
-/
lemma _root_.Set.invOn_id (s : Set α) : InvOn id id s s := ⟨s.leftInvOn_id, s.rightInvOn_id⟩

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
  proof: ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩

@[symm]

中文:
引理 comp
  结论: (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
  证明: ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩

@[symm]
-/
lemma comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
    (g'pt : MapsTo g' p t) :
    InvOn (f' ∘ g') (g ∘ f) s p :=
  ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : InvOn f' f s t)
  statement: InvOn f f' t s
  proof: ⟨h.right, h.left⟩

中文:
定理 symm
  条件: (h : InvOn f' f s t)
  结论: InvOn f f' t s
  证明: ⟨h.right, h.left⟩

Depends on / 依赖: h.left, h.right
-/
theorem symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : InvOn f' f s t) (hs : s₁ subseteq s) (ht : t₁ subseteq t)
  statement: InvOn f' f s₁ t₁
  proof: ⟨h.1.mono hs, h.2.mono ht⟩

中文:
定理 mono
  条件: (h : InvOn f' f s t) (hs : s₁ subseteq s) (ht : t₁ subseteq t)
  结论: InvOn f' f s₁ t₁
  证明: ⟨h.1.mono hs, h.2.mono ht⟩
-/
theorem mono (h : InvOn f' f s t) (hs : s₁ subseteq s) (ht : t₁ subseteq t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩

/--
theorem `bijOn` / 定理 `bijOn`

English:
theorem bijOn
  given: (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s)
  statement: BijOn f s t
  proof: ⟨hf, h.left.injOn, h.right.surjOn hf'⟩

中文:
定理 bijOn
  条件: (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s)
  结论: BijOn f s t
  证明: ⟨hf, h.left.injOn, h.right.surjOn hf'⟩

Depends on / 依赖: h.left.injOn, h.right.surjOn, surjOn
-/
theorem bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.injOn, h.right.surjOn hf'⟩

end InvOn

end Set

/-! ### `invFunOn` is a left/right inverse -/
namespace Function

variable {s : Set α} {f : α -> β} {a : α} {b : β}

/--
Definition of `invFunOn` / `invFunOn` 的定义

English:
definition invFunOn
  signature: [Nonempty α] (f : α -> β) (s : Set α) (b : β)
  body: open scoped Classical in
  if h : exists a, a in s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›

中文:
定义 invFunOn
  签名: [Nonempty α] (f : α -> β) (s : Set α) (b : β)
  定义体: open scoped Classical in
  if h : exists a, a in s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›

Depends on / 依赖: Classical, Classical.choice, Classical.choose, Nonempty, choice, scoped
-/
noncomputable def invFunOn [Nonempty α] (f : α -> β) (s : Set α) (b : β) : α :=
  open scoped Classical in
  if h : exists a, a in s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›

variable [Nonempty α]

/--
theorem `invFunOn_pos` / 定理 `invFunOn_pos`

English:
theorem invFunOn_pos
  given: (h : exists a in s, f a = b)
  statement: invFunOn f s b in s ∧ f (invFunOn f s b) = b
  proof: by
  rw [invFunOn]; rw [dif_pos h]
  exact Classical.choose_spec h

中文:
定理 invFunOn_pos
  条件: (h : 存在 a in s, f a = b)
  结论: invFunOn f s b in s ∧ f (invFunOn f s b) = b
  证明: by
  rw [invFunOn]; rw [dif_pos h]
  exact Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_pos, invFunOn
-/
theorem invFunOn_pos (h : exists a in s, f a = b) : invFunOn f s b in s ∧ f (invFunOn f s b) = b := by
  rw [invFunOn]; rw [dif_pos h]
  exact Classical.choose_spec h

/--
theorem `invFunOn_mem` / 定理 `invFunOn_mem`

English:
theorem invFunOn_mem
  given: (h : exists a in s, f a = b)
  statement: invFunOn f s b in s
  proof: (invFunOn_pos h).left

中文:
定理 invFunOn_mem
  条件: (h : 存在 a in s, f a = b)
  结论: invFunOn f s b in s
  证明: (invFunOn_pos h).left

Depends on / 依赖: invFunOn_pos
-/
theorem invFunOn_mem (h : exists a in s, f a = b) : invFunOn f s b in s :=
  (invFunOn_pos h).left

/--
theorem `invFunOn_eq` / 定理 `invFunOn_eq`

English:
theorem invFunOn_eq
  given: (h : exists a in s, f a = b)
  statement: f (invFunOn f s b) = b
  proof: (invFunOn_pos h).right

中文:
定理 invFunOn_eq
  条件: (h : 存在 a in s, f a = b)
  结论: f (invFunOn f s b) = b
  证明: (invFunOn_pos h).right

Depends on / 依赖: invFunOn_pos
-/
theorem invFunOn_eq (h : exists a in s, f a = b) : f (invFunOn f s b) = b :=
  (invFunOn_pos h).right

/--
theorem `invFunOn_neg` / 定理 `invFunOn_neg`

English:
theorem invFunOn_neg
  given: (h : ¬exists a in s, f a = b)
  statement: invFunOn f s b = Classical.choice ‹Nonempty α›
  proof: by
  rw [invFunOn]; rw [dif_neg h]

@[simp]

中文:
定理 invFunOn_neg
  条件: (h : ¬存在 a in s, f a = b)
  结论: invFunOn f s b = Classical.choice ‹Nonempty α›
  证明: by
  rw [invFunOn]; rw [dif_neg h]

@[simp]

Depends on / 依赖: dif_neg, invFunOn
-/
theorem invFunOn_neg (h : ¬exists a in s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [invFunOn]; rw [dif_neg h]

@[simp]
/--
theorem `invFunOn_apply_mem` / 定理 `invFunOn_apply_mem`

English:
theorem invFunOn_apply_mem
  given: (h : a in s)
  statement: invFunOn f s (f a) in s
  proof: invFunOn_mem ⟨a, h, rfl⟩

中文:
定理 invFunOn_apply_mem
  条件: (h : a in s)
  结论: invFunOn f s (f a) in s
  证明: invFunOn_mem ⟨a, h, rfl⟩

Depends on / 依赖: invFunOn_mem
-/
theorem invFunOn_apply_mem (h : a in s) : invFunOn f s (f a) in s :=
  invFunOn_mem ⟨a, h, rfl⟩

/--
theorem `invFunOn_apply_eq` / 定理 `invFunOn_apply_eq`

English:
theorem invFunOn_apply_eq
  given: (h : a in s)
  statement: f (invFunOn f s (f a)) = f a
  proof: invFunOn_eq ⟨a, h, rfl⟩

中文:
定理 invFunOn_apply_eq
  条件: (h : a in s)
  结论: f (invFunOn f s (f a)) = f a
  证明: invFunOn_eq ⟨a, h, rfl⟩

Depends on / 依赖: invFunOn_eq
-/
theorem invFunOn_apply_eq (h : a in s) : f (invFunOn f s (f a)) = f a :=
  invFunOn_eq ⟨a, h, rfl⟩

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α -> β}

/--
theorem `InjOn.leftInvOn_invFunOn` / 定理 `InjOn.leftInvOn_invFunOn`

English:
theorem InjOn.leftInvOn_invFunOn
  given: [Nonempty α] (h : InjOn f s)
  statement: LeftInvOn (invFunOn f s) f s
  proof: fun _a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)

中文:
定理 InjOn.leftInvOn_invFunOn
  条件: [Nonempty α] (h : InjOn f s)
  结论: LeftInvOn (invFunOn f s) f s
  证明: fun _a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)

Depends on / 依赖: invFunOn_apply_eq, invFunOn_apply_mem
-/
theorem InjOn.leftInvOn_invFunOn [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun _a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)

/--
theorem `InjOn.invFunOn_image` / 定理 `InjOn.invFunOn_image`

English:
theorem InjOn.invFunOn_image
  given: [Nonempty α] (h : InjOn f s₂) (ht : s₁ subseteq s₂)
  proof: h.leftInvOn_invFunOn.image_image' ht

中文:
定理 InjOn.invFunOn_image
  条件: [Nonempty α] (h : InjOn f s₂) (ht : s₁ subseteq s₂)
  证明: h.leftInvOn_invFunOn.image_image' ht

Depends on / 依赖: h.leftInvOn_invFunOn.image_image, image_image, leftInvOn_invFunOn
-/
theorem InjOn.invFunOn_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ subseteq s₂) :
    invFunOn f s₂ '' f '' s₁ = s₁ :=
  h.leftInvOn_invFunOn.image_image' ht

/--
theorem `_root_.Function.leftInvOn_invFunOn_of_subset_image_image` / 定理 `_root_.Function.leftInvOn_invFunOn_of_subset_image_image`

English:
theorem _root_.Function.leftInvOn_invFunOn_of_subset_image_image
  statement: [Nonempty α]
  proof: fun x hx => by
    obtain ⟨-, ⟨x, hx', rfl⟩, rfl⟩ := h hx
    rw [invFunOn_apply_eq (f := f) hx']

中文:
定理 _root_.Function.leftInvOn_invFunOn_of_subset_image_image
  结论: [Nonempty α]
  证明: fun x hx => by
    obtain ⟨-, ⟨x, hx', rfl⟩, rfl⟩ := h hx
    rw [invFunOn_apply_eq (f := f) hx']

Depends on / 依赖: invFunOn_apply_eq
-/
theorem _root_.Function.leftInvOn_invFunOn_of_subset_image_image [Nonempty α]
    (h : s subseteq (invFunOn f s) '' f '' s) : LeftInvOn (invFunOn f s) f s :=
  fun x hx => by
    obtain ⟨-, ⟨x, hx', rfl⟩, rfl⟩ := h hx
    rw [invFunOn_apply_eq (f := f) hx']

/--
theorem `injOn_iff_invFunOn_image_image_eq_self` / 定理 `injOn_iff_invFunOn_image_image_eq_self`

English:
theorem injOn_iff_invFunOn_image_image_eq_self
  given: [Nonempty α]
  proof: ⟨fun h => h.invFunOn_image Subset.rfl, fun h =>
    (Function.leftInvOn_invFunOn_of_subset_image_image h.symm.subset).injOn⟩

中文:
定理 injOn_iff_invFunOn_image_image_eq_self
  条件: [Nonempty α]
  证明: ⟨fun h => h.invFunOn_image Subset.rfl, fun h =>
    (Function.leftInvOn_invFunOn_of_subset_image_image h.symm.subset).injOn⟩

Depends on / 依赖: Function, Function.leftInvOn_invFunOn_of_subset_image_image, Subset, Subset.rfl, h.invFunOn_image, h.symm.subset, invFunOn_image, leftInvOn_invFunOn_of_subset_image_image, subset
-/
theorem injOn_iff_invFunOn_image_image_eq_self [Nonempty α] :
    InjOn f s ↔ (invFunOn f s) '' f '' s = s :=
  ⟨fun h => h.invFunOn_image Subset.rfl, fun h =>
    (Function.leftInvOn_invFunOn_of_subset_image_image h.symm.subset).injOn⟩

/--
theorem `_root_.Function.invFunOn_injOn_image` / 定理 `_root_.Function.invFunOn_injOn_image`

English:
theorem _root_.Function.invFunOn_injOn_image
  given: [Nonempty α] (f : α -> β) (s : Set α)
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [← invFunOn_apply_eq (f := f) hx]; rw [he]; rw [invFunOn_apply_eq (f := f) hx']

中文:
定理 _root_.Function.invFunOn_injOn_image
  条件: [Nonempty α] (f : α -> β) (s : Set α)
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [← invFunOn_apply_eq (f := f) hx]; rw [he]; rw [invFunOn_apply_eq (f := f) hx']

Depends on / 依赖: invFunOn_apply_eq
-/
theorem _root_.Function.invFunOn_injOn_image [Nonempty α] (f : α -> β) (s : Set α) :
    Set.InjOn (invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [← invFunOn_apply_eq (f := f) hx]; rw [he]; rw [invFunOn_apply_eq (f := f) hx']

/--
theorem `_root_.Function.invFunOn_image_image_subset` / 定理 `_root_.Function.invFunOn_image_image_subset`

English:
theorem _root_.Function.invFunOn_image_image_subset
  given: [Nonempty α] (f : α -> β) (s : Set α)
  proof: by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact invFunOn_apply_mem hx

中文:
定理 _root_.Function.invFunOn_image_image_subset
  条件: [Nonempty α] (f : α -> β) (s : Set α)
  证明: by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact invFunOn_apply_mem hx

Depends on / 依赖: invFunOn_apply_mem
-/
theorem _root_.Function.invFunOn_image_image_subset [Nonempty α] (f : α -> β) (s : Set α) :
    (invFunOn f s) '' f '' s subseteq s := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact invFunOn_apply_mem hx

/--
theorem `SurjOn.rightInvOn_invFunOn` / 定理 `SurjOn.rightInvOn_invFunOn`

English:
theorem SurjOn.rightInvOn_invFunOn
  given: [Nonempty α] (h : SurjOn f s t)
  proof: fun _y hy => invFunOn_eq h hy

中文:
定理 SurjOn.rightInvOn_invFunOn
  条件: [Nonempty α] (h : SurjOn f s t)
  证明: fun _y hy => invFunOn_eq h hy

Depends on / 依赖: invFunOn_eq
-/
theorem SurjOn.rightInvOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
RightInvOn (invFunOn f s) f t := fun _y hy => invFunOn_eq h hy

/--
theorem `BijOn.invOn_invFunOn` / 定理 `BijOn.invOn_invFunOn`

English:
theorem BijOn.invOn_invFunOn
  given: [Nonempty α] (h : BijOn f s t)
  statement: InvOn (invFunOn f s) f s t
  proof: ⟨h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn⟩

中文:
定理 BijOn.invOn_invFunOn
  条件: [Nonempty α] (h : BijOn f s t)
  结论: InvOn (invFunOn f s) f s t
  证明: ⟨h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn⟩

Depends on / 依赖: h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn, leftInvOn_invFunOn, rightInvOn_invFunOn, surjOn
-/
theorem BijOn.invOn_invFunOn [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn⟩

/--
theorem `SurjOn.invOn_invFunOn` / 定理 `SurjOn.invOn_invFunOn`

English:
theorem SurjOn.invOn_invFunOn
  given: [Nonempty α] (h : SurjOn f s t)
  proof: by
  refine ⟨?_, h.rightInvOn_invFunOn⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.rightInvOn_invFunOn hy]

中文:
定理 SurjOn.invOn_invFunOn
  条件: [Nonempty α] (h : SurjOn f s t)
  证明: by
  refine ⟨?_, h.rightInvOn_invFunOn⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.rightInvOn_invFunOn hy]

Depends on / 依赖: h.rightInvOn_invFunOn, rightInvOn_invFunOn
-/
theorem SurjOn.invOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t := by
  refine ⟨?_, h.rightInvOn_invFunOn⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.rightInvOn_invFunOn hy]

/--
theorem `SurjOn.mapsTo_invFunOn` / 定理 `SurjOn.mapsTo_invFunOn`

English:
theorem SurjOn.mapsTo_invFunOn
  given: [Nonempty α] (h : SurjOn f s t)
  statement: MapsTo (invFunOn f s) t s
  proof: fun _y hy => mem_preimage.2 invFunOn_mem h hy

中文:
定理 SurjOn.mapsTo_invFunOn
  条件: [Nonempty α] (h : SurjOn f s t)
  结论: MapsTo (invFunOn f s) t s
  证明: fun _y hy => mem_preimage.2 invFunOn_mem h hy

Depends on / 依赖: invFunOn_mem, mem_preimage
-/
theorem SurjOn.mapsTo_invFunOn [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
fun _y hy => mem_preimage.2 invFunOn_mem h hy

/--
theorem `SurjOn.image_invFunOn_image_of_subset` / 定理 `SurjOn.image_invFunOn_image_of_subset`

English:
theorem SurjOn.image_invFunOn_image_of_subset
  statement: [Nonempty α] {r : Set β} (hf : SurjOn f s t)
  proof: hf.rightInvOn_invFunOn.image_image' hrt

中文:
定理 SurjOn.image_invFunOn_image_of_subset
  结论: [Nonempty α] {r : Set β} (hf : SurjOn f s t)
  证明: hf.rightInvOn_invFunOn.image_image' hrt

Depends on / 依赖: hf.rightInvOn_invFunOn.image_image, image_image, rightInvOn_invFunOn
-/
theorem SurjOn.image_invFunOn_image_of_subset [Nonempty α] {r : Set β} (hf : SurjOn f s t)
    (hrt : r subseteq t) : f '' f.invFunOn s '' r = r :=
  hf.rightInvOn_invFunOn.image_image' hrt

/--
theorem `SurjOn.image_invFunOn_image` / 定理 `SurjOn.image_invFunOn_image`

English:
theorem SurjOn.image_invFunOn_image
  given: [Nonempty α] (hf : SurjOn f s t)
  proof: hf.rightInvOn_invFunOn.image_image

中文:
定理 SurjOn.image_invFunOn_image
  条件: [Nonempty α] (hf : SurjOn f s t)
  证明: hf.rightInvOn_invFunOn.image_image

Depends on / 依赖: hf.rightInvOn_invFunOn.image_image, image_image, rightInvOn_invFunOn
-/
theorem SurjOn.image_invFunOn_image [Nonempty α] (hf : SurjOn f s t) :
    f '' f.invFunOn s '' t = t :=
  hf.rightInvOn_invFunOn.image_image

/--
theorem `SurjOn.bijOn_subset` / 定理 `SurjOn.bijOn_subset`

English:
theorem SurjOn.bijOn_subset
  given: [Nonempty α] (h : SurjOn f s t)
  statement: BijOn f (invFunOn f s '' t) t
  proof: by
  refine h.invOn_invFunOn.bijOn ?_ (mapsTo_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.rightInvOn_invFunOn hy]

中文:
定理 SurjOn.bijOn_subset
  条件: [Nonempty α] (h : SurjOn f s t)
  结论: BijOn f (invFunOn f s '' t) t
  证明: by
  refine h.invOn_invFunOn.bijOn ?_ (mapsTo_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.rightInvOn_invFunOn hy]

Depends on / 依赖: h.invOn_invFunOn.bijOn, h.rightInvOn_invFunOn, invOn_invFunOn, mapsTo_image, rightInvOn_invFunOn
-/
theorem SurjOn.bijOn_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t := by
  refine h.invOn_invFunOn.bijOn ?_ (mapsTo_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.rightInvOn_invFunOn hy]

/--
theorem `surjOn_iff_exists_bijOn_subset` / 定理 `surjOn_iff_exists_bijOn_subset`

English:
theorem surjOn_iff_exists_bijOn_subset
  statement: SurjOn f s t ↔ exists s' subseteq s, BijOn f s' t
  proof: by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bijOn_empty f⟩
    · intro h
      have : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.mapsTo_invFunOn.image_subset, h.bijOn_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    

中文:
定理 surjOn_iff_exists_bijOn_subset
  结论: SurjOn f s t ↔ 存在 s' subseteq s, BijOn f s' t
  证明: by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bijOn_empty f⟩
    · intro h
      have : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.mapsTo_invFunOn.image_subset, h.bijOn_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    

Depends on / 依赖: Classical, Classical.choose, Nonempty, Subset, Subset.refl, bijOn_empty, bijOn_subset, comap_nonempty, empty_subset, eq_empty_or_nonempty, h.bijOn_subset, h.comap_nonempty, h.mapsTo_invFunOn.image_subset, image_subset, mapsTo_invFunOn, surjOn, surjOn.mono
-/
theorem surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ exists s' subseteq s, BijOn f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bijOn_empty f⟩
    · intro h
      have : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.mapsTo_invFunOn.image_subset, h.bijOn_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surjOn.mono hs' (Subset.refl _)

alias ⟨SurjOn.exists_bijOn_subset, _⟩ := Set.surjOn_iff_exists_bijOn_subset

variable (f s)

/--
lemma `exists_subset_bijOn` / 引理 `exists_subset_bijOn`

English:
lemma exists_subset_bijOn
  statement: exists s' subseteq s, BijOn f s' (f '' s)
  proof: surjOn_iff_exists_bijOn_subset.mp (surjOn_image f s)

中文:
引理 exists_subset_bijOn
  结论: 存在 s' subseteq s, BijOn f s' (f '' s)
  证明: surjOn_iff_exists_bijOn_subset.mp (surjOn_image f s)

Depends on / 依赖: surjOn_iff_exists_bijOn_subset, surjOn_iff_exists_bijOn_subset.mp, surjOn_image
-/
lemma exists_subset_bijOn : exists s' subseteq s, BijOn f s' (f '' s) :=
  surjOn_iff_exists_bijOn_subset.mp (surjOn_image f s)

/--
lemma `exists_image_eq_and_injOn` / 引理 `exists_image_eq_and_injOn`

English:
lemma exists_image_eq_and_injOn
  statement: exists u, f '' u = f '' s ∧ InjOn f u
  proof: let ⟨u, _, hfu⟩ := exists_subset_bijOn s f
  ⟨u, hfu.image_eq, hfu.injOn⟩

中文:
引理 exists_image_eq_and_injOn
  结论: 存在 u, f '' u = f '' s ∧ InjOn f u
  证明: let ⟨u, _, hfu⟩ := exists_subset_bijOn s f
  ⟨u, hfu.image_eq, hfu.injOn⟩

Depends on / 依赖: exists_subset_bijOn, hfu.image_eq, hfu.injOn, image_eq
-/
lemma exists_image_eq_and_injOn : exists u, f '' u = f '' s ∧ InjOn f u :=
  let ⟨u, _, hfu⟩ := exists_subset_bijOn s f
  ⟨u, hfu.image_eq, hfu.injOn⟩

variable {f s}

/--
lemma `exists_image_eq_injOn_of_subset_range` / 引理 `exists_image_eq_injOn_of_subset_range`

English:
lemma exists_image_eq_injOn_of_subset_range
  given: (ht : t subseteq range f)
  proof: image_preimage_eq_of_subset ht ▸ exists_image_eq_and_injOn _ _

中文:
引理 exists_image_eq_injOn_of_subset_range
  条件: (ht : t subseteq range f)
  证明: image_preimage_eq_of_subset ht ▸ exists_image_eq_and_injOn _ _

Depends on / 依赖: exists_image_eq_and_injOn, image_preimage_eq_of_subset
-/
lemma exists_image_eq_injOn_of_subset_range (ht : t subseteq range f) :
    exists s, f '' s = t ∧ InjOn f s :=
  image_preimage_eq_of_subset ht ▸ exists_image_eq_and_injOn _ _

/--
theorem `BijOn.exists_extend_of_subset` / 定理 `BijOn.exists_extend_of_subset`

English:
theorem BijOn.exists_extend_of_subset
  statement: {t' : Set β} (h : BijOn f s t) (hss₁ : s subseteq s₁) (htt' : t subseteq t')
  proof: by
  obtain ⟨r, hrss, hbij⟩ := exists_subset_bijOn ((s₁ inter f ⁻¹' t') \ f ⁻¹' t) f
  rw [image_sdiff_preimage]; rw [image_inter_preimage] at hbij
  refine ⟨s union r, subset_union_left, ?_, ?_, ?_, fun y hyt' => ?_⟩
· exact union_subset hss₁ hrss.trans sdiff_subset.trans inter_subset_left
  · rw [

中文:
定理 BijOn.exists_extend_of_subset
  结论: {t' : Set β} (h : BijOn f s t) (hss₁ : s subseteq s₁) (htt' : t subseteq t')
  证明: by
  obtain ⟨r, hrss, hbij⟩ := exists_subset_bijOn ((s₁ inter f ⁻¹' t') \ f ⁻¹' t) f
  rw [image_sdiff_preimage]; rw [image_inter_preimage] at hbij
  refine ⟨s union r, subset_union_left, ?_, ?_, ?_, fun y hyt' => ?_⟩
· exact union_subset hss₁ hrss.trans sdiff_subset.trans inter_subset_left
  · rw [

Depends on / 依赖: and_iff_right, exists_subset_bijOn, h.image_eq, h.injOn, hbij.image_eq, hbij.injOn, hrss.trans, image_eq, image_inter_preimage, image_sdiff_preimage, image_union, injOn_union, inter_subset_left, inter_subset_right, mapsTo_iff_image_subset, sdiff_subset, sdiff_subset.trans, subset_union_left, union_subset, union_subset_iff
-/
theorem BijOn.exists_extend_of_subset {t' : Set β} (h : BijOn f s t) (hss₁ : s subseteq s₁) (htt' : t subseteq t')
    (ht' : SurjOn f s₁ t') : exists s', s subseteq s' ∧ s' subseteq s₁ ∧ Set.BijOn f s' t' := by
  obtain ⟨r, hrss, hbij⟩ := exists_subset_bijOn ((s₁ inter f ⁻¹' t') \ f ⁻¹' t) f
  rw [image_sdiff_preimage]; rw [image_inter_preimage] at hbij
  refine ⟨s union r, subset_union_left, ?_, ?_, ?_, fun y hyt' => ?_⟩
· exact union_subset hss₁ hrss.trans sdiff_subset.trans inter_subset_left
  · rw [mapsTo_iff_image_subset, image_union, hbij.image_eq, h.image_eq, union_subset_iff]
    exact ⟨htt', sdiff_subset.trans inter_subset_right⟩
  · rw [injOn_union, and_iff_right h.injOn, and_iff_right hbij.injOn]
    · refine fun x hxs y hyr hxy => (hrss hyr).2 ?_
      rw [← h.image_eq]
      exact ⟨x, hxs, hxy⟩
    exact (subset_sdiff.1 hrss).2.symm.mono_left h.mapsTo
  rw [image_union]; rw [h.image_eq]; rw [hbij.image_eq]; rw [union_sdiff_self]
  exact .inr ⟨ht' hyt', hyt'⟩

/--
theorem `BijOn.exists_extend` / 定理 `BijOn.exists_extend`

English:
theorem BijOn.exists_extend
  given: {t' : Set β} (h : BijOn f s t) (htt' : t subseteq t') (ht' : t' subseteq range f)
  proof: by
  simpa using h.exists_extend_of_subset (subset_univ s) htt' (by simpa [SurjOn])

中文:
定理 BijOn.exists_extend
  条件: {t' : Set β} (h : BijOn f s t) (htt' : t subseteq t') (ht' : t' subseteq range f)
  证明: by
  simpa using h.exists_extend_of_subset (subset_univ s) htt' (by simpa [SurjOn])

Depends on / 依赖: SurjOn, exists_extend_of_subset, h.exists_extend_of_subset, subset_univ
-/
theorem BijOn.exists_extend {t' : Set β} (h : BijOn f s t) (htt' : t subseteq t') (ht' : t' subseteq range f) :
    exists s', s subseteq s' ∧ BijOn f s' t' := by
  simpa using h.exists_extend_of_subset (subset_univ s) htt' (by simpa [SurjOn])

/--
theorem `InjOn.exists_subset_injOn_subset_range_eq` / 定理 `InjOn.exists_subset_injOn_subset_range_eq`

English:
theorem InjOn.exists_subset_injOn_subset_range_eq
  given: {r : Set α} (hinj : InjOn f r) (hrs : r subseteq s)
  proof: by
  obtain ⟨u, hru, hus, h⟩ := hinj.bijOn_image.exists_extend_of_subset hrs
    (image_mono hrs) Subset.rfl
  exact ⟨u, hru, hus, h.image_eq, h.injOn⟩

中文:
定理 InjOn.exists_subset_injOn_subset_range_eq
  条件: {r : Set α} (hinj : InjOn f r) (hrs : r subseteq s)
  证明: by
  obtain ⟨u, hru, hus, h⟩ := hinj.bijOn_image.exists_extend_of_subset hrs
    (image_mono hrs) Subset.rfl
  exact ⟨u, hru, hus, h.image_eq, h.injOn⟩

Depends on / 依赖: Subset, Subset.rfl, bijOn_image, exists_extend_of_subset, h.image_eq, h.injOn, hinj.bijOn_image.exists_extend_of_subset, image_eq, image_mono
-/
theorem InjOn.exists_subset_injOn_subset_range_eq {r : Set α} (hinj : InjOn f r) (hrs : r subseteq s) :
    exists u : Set α, r subseteq u ∧ u subseteq s ∧ f '' u = f '' s ∧ InjOn f u := by
  obtain ⟨u, hru, hus, h⟩ := hinj.bijOn_image.exists_extend_of_subset hrs
    (image_mono hrs) Subset.rfl
  exact ⟨u, hru, hus, h.image_eq, h.injOn⟩

/--
theorem `preimage_invFun_of_mem` / 定理 `preimage_invFun_of_mem`

English:
theorem preimage_invFun_of_mem
  statement: [n : Nonempty α] {f : α -> β} (hf : Injective f) {s : Set α}
  proof: by
  ext x
  rcases em (x in range f) with (⟨a, rfl⟩ | hx)
  · simp only [mem_preimage, mem_union, mem_compl_iff, mem_range_self, not_true, or_false,
      leftInverse_invFun hf _, hf.mem_set_image]
  · simp only [mem_preimage, invFun_neg hx, h, hx, mem_union, mem_compl_iff, not_false_iff, or_true]

中文:
定理 preimage_invFun_of_mem
  结论: [n : Nonempty α] {f : α -> β} (hf : Injective f) {s : Set α}
  证明: by
  ext x
  rcases em (x in range f) with (⟨a, rfl⟩ | hx)
  · simp only [mem_preimage, mem_union, mem_compl_iff, mem_range_self, not_true, or_false,
      leftInverse_invFun hf _, hf.mem_set_image]
  · simp only [mem_preimage, invFun_neg hx, h, hx, mem_union, mem_compl_iff, not_false_iff, or_true]

Depends on / 依赖: hf.mem_set_image, invFun_neg, leftInverse_invFun, mem_compl_iff, mem_preimage, mem_range_self, mem_set_image, mem_union, not_false_iff, not_true, or_false, or_true
-/
theorem preimage_invFun_of_mem [n : Nonempty α] {f : α -> β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n in s) : invFun f ⁻¹' s = f '' s union (range f)ᶜ := by
  ext x
  rcases em (x in range f) with (⟨a, rfl⟩ | hx)
  · simp only [mem_preimage, mem_union, mem_compl_iff, mem_range_self, not_true, or_false,
      leftInverse_invFun hf _, hf.mem_set_image]
  · simp only [mem_preimage, invFun_neg hx, h, hx, mem_union, mem_compl_iff, not_false_iff, or_true]

/--
theorem `preimage_invFun_of_notMem` / 定理 `preimage_invFun_of_notMem`

English:
theorem preimage_invFun_of_notMem
  statement: [n : Nonempty α] {f : α -> β} (hf : Injective f) {s : Set α}
  proof: by
  ext x
  rcases em (x in range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, leftInverse_invFun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, invFun_neg hx, h, this]

中文:
定理 preimage_invFun_of_notMem
  结论: [n : Nonempty α] {f : α -> β} (hf : Injective f) {s : Set α}
  证明: by
  ext x
  rcases em (x in range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, leftInverse_invFun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, invFun_neg hx, h, this]

Depends on / 依赖: hf.mem_set_image, image_subset_range, invFun_neg, leftInverse_invFun, mem_preimage, mem_set_image
-/
theorem preimage_invFun_of_notMem [n : Nonempty α] {f : α -> β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x in range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, leftInverse_invFun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, invFun_neg hx, h, this]

/--
lemma `BijOn.symm` / 引理 `BijOn.symm`

English:
lemma BijOn.symm
  given: {g : β -> α} (h : InvOn f g t s) (hf : BijOn f s t)
  statement: BijOn g t s
  proof: ⟨h.2.mapsTo hf.surjOn, h.1.injOn, h.2.surjOn hf.mapsTo⟩

中文:
引理 BijOn.symm
  条件: {g : β -> α} (h : InvOn f g t s) (hf : BijOn f s t)
  结论: BijOn g t s
  证明: ⟨h.2.mapsTo hf.surjOn, h.1.injOn, h.2.surjOn hf.mapsTo⟩

Depends on / 依赖: hf.mapsTo, hf.surjOn, mapsTo, surjOn
-/
lemma BijOn.symm {g : β -> α} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s :=
  ⟨h.2.mapsTo hf.surjOn, h.1.injOn, h.2.surjOn hf.mapsTo⟩

/--
lemma `bijOn_comm` / 引理 `bijOn_comm`

English:
lemma bijOn_comm
  given: {g : β -> α} (h : InvOn f g t s)
  statement: BijOn f s t ↔ BijOn g t s
  proof: ⟨BijOn.symm h, BijOn.symm h.symm⟩

中文:
引理 bijOn_comm
  条件: {g : β -> α} (h : InvOn f g t s)
  结论: BijOn f s t ↔ BijOn g t s
  证明: ⟨BijOn.symm h, BijOn.symm h.symm⟩

Depends on / 依赖: BijOn.symm, h.symm
-/
lemma bijOn_comm {g : β -> α} (h : InvOn f g t s) : BijOn f s t ↔ BijOn g t s :=
  ⟨BijOn.symm h, BijOn.symm h.symm⟩

/--
lemma `SurjOn.exists_subset_injOn_image_eq` / 引理 `SurjOn.exists_subset_injOn_image_eq`

English:
lemma SurjOn.exists_subset_injOn_image_eq
  given: (hfs : s.SurjOn f t)
  proof: by
  choose x hmem heq using hfs
  exact ⟨range (fun a : t => x a.2), by grind, fun _ => by grind, by aesop⟩

中文:
引理 SurjOn.exists_subset_injOn_image_eq
  条件: (hfs : s.SurjOn f t)
  证明: by
  choose x hmem heq using hfs
  exact ⟨range (fun a : t => x a.2), by grind, fun _ => by grind, by aesop⟩
-/
lemma SurjOn.exists_subset_injOn_image_eq (hfs : s.SurjOn f t) :
    exists u subseteq s, u.InjOn f ∧ f '' u = t := by
  choose x hmem heq using hfs
  exact ⟨range (fun a : t => x a.2), by grind, fun _ => by grind, by aesop⟩

end Set

namespace Function

open Set

variable {fa : α -> α} {fb : β -> β} {f : α -> β} {g : β -> γ} {s t : Set α}

/--
theorem `Injective.comp_injOn` / 定理 `Injective.comp_injOn`

English:
theorem Injective.comp_injOn
  given: (hg : Injective g) (hf : s.InjOn f)
  statement: s.InjOn (g ∘ f)
  proof: hg.injOn.comp hf (mapsTo_univ _ _)

中文:
定理 Injective.comp_injOn
  条件: (hg : Injective g) (hf : s.InjOn f)
  结论: s.InjOn (g ∘ f)
  证明: hg.injOn.comp hf (mapsTo_univ _ _)

Depends on / 依赖: hg.injOn.comp, mapsTo_univ
-/
theorem Injective.comp_injOn (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  hg.injOn.comp hf (mapsTo_univ _ _)

/--
theorem `LeftInverse.leftInvOn` / 定理 `LeftInverse.leftInvOn`

English:
theorem LeftInverse.leftInvOn
  given: {g : β -> α} (h : LeftInverse f g) (s : Set β)
  statement: LeftInvOn f g s
  proof: fun x _ => h x

中文:
定理 LeftInverse.leftInvOn
  条件: {g : β -> α} (h : LeftInverse f g) (s : Set β)
  结论: LeftInvOn f g s
  证明: fun x _ => h x
-/
theorem LeftInverse.leftInvOn {g : β -> α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x _ => h x

/--
theorem `RightInverse.rightInvOn` / 定理 `RightInverse.rightInvOn`

English:
theorem RightInverse.rightInvOn
  given: {g : β -> α} (h : RightInverse f g) (s : Set α)
  proof: fun x _ => h x

中文:
定理 RightInverse.rightInvOn
  条件: {g : β -> α} (h : RightInverse f g) (s : Set α)
  证明: fun x _ => h x
-/
theorem RightInverse.rightInvOn {g : β -> α} (h : RightInverse f g) (s : Set α) :
    RightInvOn f g s := fun x _ => h x

/--
theorem `LeftInverse.rightInvOn_range` / 定理 `LeftInverse.rightInvOn_range`

English:
theorem LeftInverse.rightInvOn_range
  given: {g : β -> α} (h : LeftInverse f g)
  proof: forall_mem_range.2 fun i => congr_arg g (h i)

中文:
定理 LeftInverse.rightInvOn_range
  条件: {g : β -> α} (h : LeftInverse f g)
  证明: forall_mem_range.2 fun i => congr_arg g (h i)

Depends on / 依赖: congr_arg, forall_mem_range
-/
theorem LeftInverse.rightInvOn_range {g : β -> α} (h : LeftInverse f g) :
    RightInvOn f g (range g) :=
  forall_mem_range.2 fun i => congr_arg g (h i)

namespace Semiconj

/--
theorem `mapsTo_image` / 定理 `mapsTo_image`

English:
theorem mapsTo_image
  given: (h : Semiconj f fa fb) (ha : MapsTo fa s t)
  statement: MapsTo fb (f '' s) (f '' t)
  proof: fun _y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩

中文:
定理 mapsTo_image
  条件: (h : Semiconj f fa fb) (ha : MapsTo fa s t)
  结论: MapsTo fb (f '' s) (f '' t)
  证明: fun _y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩
-/
theorem mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun _y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩

/--
theorem `mapsTo_image_right` / 定理 `mapsTo_image_right`

English:
theorem mapsTo_image_right
  given: {t : Set β} (h : Semiconj f fa fb) (hst : MapsTo f s t)
  proof: mapsTo_image_iff.2 fun x hx => ⟨f x, hst hx, (h x).symm⟩

中文:
定理 mapsTo_image_right
  条件: {t : Set β} (h : Semiconj f fa fb) (hst : MapsTo f s t)
  证明: mapsTo_image_iff.2 fun x hx => ⟨f x, hst hx, (h x).symm⟩

Depends on / 依赖: mapsTo_image_iff
-/
theorem mapsTo_image_right {t : Set β} (h : Semiconj f fa fb) (hst : MapsTo f s t) :
    MapsTo f (fa '' s) (fb '' t) :=
  mapsTo_image_iff.2 fun x hx => ⟨f x, hst hx, (h x).symm⟩

/--
theorem `mapsTo_range` / 定理 `mapsTo_range`

English:
theorem mapsTo_range
  given: (h : Semiconj f fa fb)
  statement: MapsTo fb (range f) (range f)
  proof: fun _y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩

中文:
定理 mapsTo_range
  条件: (h : Semiconj f fa fb)
  结论: MapsTo fb (range f) (range f)
  证明: fun _y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩
-/
theorem mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun _y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩

/--
theorem `surjOn_image` / 定理 `surjOn_image`

English:
theorem surjOn_image
  given: (h : Semiconj f fa fb) (ha : SurjOn fa s t)
  statement: SurjOn fb (f '' s) (f '' t)
  proof: by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)

中文:
定理 surjOn_image
  条件: (h : Semiconj f fa fb) (ha : SurjOn fa s t)
  结论: SurjOn fb (f '' s) (f '' t)
  证明: by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)

Depends on / 依赖: mem_image_of_mem
-/
theorem surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) := by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)

/--
theorem `surjOn_range` / 定理 `surjOn_range`

English:
theorem surjOn_range
  given: (h : Semiconj f fa fb) (ha : Surjective fa)
  proof: by
  rw [← image_univ]
  exact h.surjOn_image ha.surjOn

中文:
定理 surjOn_range
  条件: (h : Semiconj f fa fb) (ha : Surjective fa)
  证明: by
  rw [← image_univ]
  exact h.surjOn_image ha.surjOn

Depends on / 依赖: h.surjOn_image, ha.surjOn, image_univ, surjOn, surjOn_image
-/
theorem surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) :
    SurjOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.surjOn_image ha.surjOn

/--
theorem `injOn_image` / 定理 `injOn_image`

English:
theorem injOn_image
  given: (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s))
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)

中文:
定理 injOn_image
  条件: (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s))
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)

Depends on / 依赖: congr_arg, h.eq, mem_image_of_mem
-/
theorem injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)

/--
theorem `injOn_range` / 定理 `injOn_range`

English:
theorem injOn_range
  given: (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa))
  proof: by
  rw [← image_univ] at *
  exact h.injOn_image ha.injOn hf

中文:
定理 injOn_range
  条件: (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa))
  证明: by
  rw [← image_univ] at *
  exact h.injOn_image ha.injOn hf

Depends on / 依赖: h.injOn_image, ha.injOn, image_univ, injOn_image
-/
theorem injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by
  rw [← image_univ] at *
  exact h.injOn_image ha.injOn hf

/--
theorem `bijOn_image` / 定理 `bijOn_image`

English:
theorem bijOn_image
  given: (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t)
  proof: ⟨h.mapsTo_image ha.mapsTo, h.injOn_image ha.injOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.surjOn⟩

中文:
定理 bijOn_image
  条件: (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t)
  证明: ⟨h.mapsTo_image ha.mapsTo, h.injOn_image ha.injOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.surjOn⟩

Depends on / 依赖: h.injOn_image, h.mapsTo_image, h.surjOn_image, ha.image_eq.symm, ha.injOn, ha.mapsTo, ha.surjOn, image_eq, injOn_image, mapsTo, mapsTo_image, surjOn, surjOn_image
-/
theorem bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.mapsTo_image ha.mapsTo, h.injOn_image ha.injOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.surjOn⟩

/--
theorem `bijOn_range` / 定理 `bijOn_range`

English:
theorem bijOn_range
  given: (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f)
  proof: by
  rw [← image_univ]
  exact h.bijOn_image ha.bijOn_univ hf.injOn

中文:
定理 bijOn_range
  条件: (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f)
  证明: by
  rw [← image_univ]
  exact h.bijOn_image ha.bijOn_univ hf.injOn

Depends on / 依赖: bijOn_image, bijOn_univ, h.bijOn_image, ha.bijOn_univ, hf.injOn, image_univ
-/
theorem bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bijOn_image ha.bijOn_univ hf.injOn

/--
theorem `mapsTo_preimage` / 定理 `mapsTo_preimage`

English:
theorem mapsTo_preimage
  given: (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t)
  proof: fun x hx => by simp only [mem_preimage, h x, hb hx]

中文:
定理 mapsTo_preimage
  条件: (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t)
  证明: fun x hx => by simp only [mem_preimage, h x, hb hx]

Depends on / 依赖: mem_preimage
-/
theorem mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]

/--
theorem `injOn_preimage` / 定理 `injOn_preimage`

English:
theorem injOn_preimage
  statement: (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
  proof: by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq]; rw [h.eq] at this
  exact hf hx hy (hb hx hy this)

中文:
定理 injOn_preimage
  结论: (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
  证明: by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq]; rw [h.eq] at this
  exact hf hx hy (hb hx hy this)

Depends on / 依赖: congr_arg, h.eq
-/
theorem injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq]; rw [h.eq] at this
  exact hf hx hy (hb hx hy this)

end Semiconj

/--
theorem `update_comp_eq_of_notMem_range'` / 定理 `update_comp_eq_of_notMem_range'`

English:
theorem update_comp_eq_of_notMem_range'
  statement: {α : Sort*} {β : Type*} {γ : β -> Sort*} [DecidableEq β]
  proof: (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

中文:
定理 update_comp_eq_of_notMem_range'
  结论: {α : Sort*} {β : 类型} {γ : β -> Sort*} [DecidableEq β]
  证明: (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

Depends on / 依赖: update_comp_eq_of_forall_ne
-/
theorem update_comp_eq_of_notMem_range' {α : Sort*} {β : Type*} {γ : β -> Sort*} [DecidableEq β]
    (g : forall b, γ b) {f : α -> β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => update g i a (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

/--
theorem `update_comp_eq_of_notMem_range` / 定理 `update_comp_eq_of_notMem_range`

English:
theorem update_comp_eq_of_notMem_range
  statement: {α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β]
  proof: update_comp_eq_of_notMem_range' g a h

中文:
定理 update_comp_eq_of_notMem_range
  结论: {α : Sort*} {β : 类型} {γ : Sort*} [DecidableEq β]
  证明: update_comp_eq_of_notMem_range' g a h

Depends on / 依赖: update_comp_eq_of_notMem_range
-/
theorem update_comp_eq_of_notMem_range {α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β]
    (g : β -> γ) {f : α -> β} {i : β} (a : γ) (h : i ∉ Set.range f) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_notMem_range' g a h

/--
theorem `insert_injOn` / 定理 `insert_injOn`

English:
theorem insert_injOn
  given: (s : Set α)
  statement: sᶜ.InjOn fun a => insert a s
  proof: fun _a ha _ _ =>
  (insert_inj ha).1

中文:
定理 insert_injOn
  条件: (s : Set α)
  结论: sᶜ.InjOn fun a => insert a s
  证明: fun _a ha _ _ =>
  (insert_inj ha).1
-/
theorem insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s := fun _a ha _ _ =>
  (insert_inj ha).1

/--
lemma `apply_eq_of_range_eq_singleton` / 引理 `apply_eq_of_range_eq_singleton`

English:
lemma apply_eq_of_range_eq_singleton
  given: {f : α -> β} {b : β} (h : range f = {b}) (a : α)
  proof: by
  simpa only [h, mem_singleton_iff] using mem_range_self (f := f) a

中文:
引理 apply_eq_of_range_eq_singleton
  条件: {f : α -> β} {b : β} (h : range f = {b}) (a : α)
  证明: by
  simpa only [h, mem_singleton_iff] using mem_range_self (f := f) a

Depends on / 依赖: mem_range_self, mem_singleton_iff
-/
lemma apply_eq_of_range_eq_singleton {f : α -> β} {b : β} (h : range f = {b}) (a : α) :
    f a = b := by
  simpa only [h, mem_singleton_iff] using mem_range_self (f := f) a

end Function

/-! ### Equivalences, permutations -/
namespace Set

variable {p : β -> Prop} [DecidablePred p] {f : α ≃ Subtype p} {g g₁ g₂ : Perm α} {s t : Set α}

/--
lemma `MapsTo.extendDomain` / 引理 `MapsTo.extendDomain`

English:
lemma MapsTo.extendDomain
  given: (h : MapsTo g s t)
  proof: by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨_, h ha, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩

中文:
引理 MapsTo.extendDomain
  条件: (h : MapsTo g s t)
  证明: by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨_, h ha, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩
-/
protected lemma MapsTo.extendDomain (h : MapsTo g s t) :
    MapsTo (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨_, h ha, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩

/--
lemma `SurjOn.extendDomain` / 引理 `SurjOn.extendDomain`

English:
lemma SurjOn.extendDomain
  given: (h : SurjOn g s t)
  proof: by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩

中文:
引理 SurjOn.extendDomain
  条件: (h : SurjOn g s t)
  证明: by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩
-/
protected lemma SurjOn.extendDomain (h : SurjOn g s t) :
    SurjOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩

/--
lemma `BijOn.extendDomain` / 引理 `BijOn.extendDomain`

English:
lemma BijOn.extendDomain
  given: (h : BijOn g s t)
  proof: ⟨h.mapsTo.extendDomain, (g.extendDomain f).injective.injOn, h.surjOn.extendDomain⟩

中文:
引理 BijOn.extendDomain
  条件: (h : BijOn g s t)
  证明: ⟨h.mapsTo.extendDomain, (g.extendDomain f).injective.injOn, h.surjOn.extendDomain⟩
-/
protected lemma BijOn.extendDomain (h : BijOn g s t) :
    BijOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.mapsTo.extendDomain, (g.extendDomain f).injective.injOn, h.surjOn.extendDomain⟩

/--
lemma `LeftInvOn.extendDomain` / 引理 `LeftInvOn.extendDomain`

English:
lemma LeftInvOn.extendDomain
  given: (h : LeftInvOn g₁ g₂ s)
  proof: by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]

中文:
引理 LeftInvOn.extendDomain
  条件: (h : LeftInvOn g₁ g₂ s)
  证明: by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]
-/
protected lemma LeftInvOn.extendDomain (h : LeftInvOn g₁ g₂ s) :
    LeftInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]

/--
lemma `RightInvOn.extendDomain` / 引理 `RightInvOn.extendDomain`

English:
lemma RightInvOn.extendDomain
  given: (h : RightInvOn g₁ g₂ t)
  proof: by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]

中文:
引理 RightInvOn.extendDomain
  条件: (h : RightInvOn g₁ g₂ t)
  证明: by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]
-/
protected lemma RightInvOn.extendDomain (h : RightInvOn g₁ g₂ t) :
    RightInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]

/--
lemma `InvOn.extendDomain` / 引理 `InvOn.extendDomain`

English:
lemma InvOn.extendDomain
  given: (h : InvOn g₁ g₂ s t)
  proof: ⟨h.1.extendDomain, h.2.extendDomain⟩

中文:
引理 InvOn.extendDomain
  条件: (h : InvOn g₁ g₂ s t)
  证明: ⟨h.1.extendDomain, h.2.extendDomain⟩
-/
protected lemma InvOn.extendDomain (h : InvOn g₁ g₂ s t) :
    InvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.1.extendDomain, h.2.extendDomain⟩

end Set

namespace Set

section Prod

variable {α β₁ β₂ : Type*} {s : Set α} {t₁ : Set β₁} {t₂ : Set β₂}
  {f₁ : α -> β₁} {f₂ : α -> β₂} {g₁ : β₁ -> α} {g₂ : β₂ -> α}

/--
lemma `InjOn.left_prodMk` / 引理 `InjOn.left_prodMk`

English:
lemma InjOn.left_prodMk
  given: (h₁ : s.InjOn f₁)
  statement: s.InjOn fun x => (f₁ x, f₂ x)
  proof: fun _ hx _ hy h => h₁ hx hy (Prod.ext_iff.1 h).1

中文:
引理 InjOn.left_prodMk
  条件: (h₁ : s.InjOn f₁)
  结论: s.InjOn fun x => (f₁ x, f₂ x)
  证明: fun _ hx _ hy h => h₁ hx hy (Prod.ext_iff.1 h).1

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
lemma InjOn.left_prodMk (h₁ : s.InjOn f₁) : s.InjOn fun x => (f₁ x, f₂ x) :=
  fun _ hx _ hy h => h₁ hx hy (Prod.ext_iff.1 h).1

/--
lemma `InjOn.right_prodMk` / 引理 `InjOn.right_prodMk`

English:
lemma InjOn.right_prodMk
  given: (h₂ : s.InjOn f₂)
  statement: s.InjOn fun x => (f₁ x, f₂ x)
  proof: fun _ hx _ hy h => h₂ hx hy (Prod.ext_iff.1 h).2

中文:
引理 InjOn.right_prodMk
  条件: (h₂ : s.InjOn f₂)
  结论: s.InjOn fun x => (f₁ x, f₂ x)
  证明: fun _ hx _ hy h => h₂ hx hy (Prod.ext_iff.1 h).2

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
lemma InjOn.right_prodMk (h₂ : s.InjOn f₂) : s.InjOn fun x => (f₁ x, f₂ x) :=
  fun _ hx _ hy h => h₂ hx hy (Prod.ext_iff.1 h).2

/--
lemma `prod_surjOn_fst` / 引理 `prod_surjOn_fst`

English:
lemma prod_surjOn_fst
  given: (h : t₂.Nonempty)
  statement: (t₁ ×ˢ t₂).SurjOn Prod.fst t₁
  proof: fun _ h => by simpa [h]

中文:
引理 prod_surjOn_fst
  条件: (h : t₂.Nonempty)
  结论: (t₁ ×ˢ t₂).SurjOn Prod.fst t₁
  证明: fun _ h => by simpa [h]
-/
lemma prod_surjOn_fst (h : t₂.Nonempty) : (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ :=
  fun _ h => by simpa [h]
/--
lemma `prod_surjOn_snd` / 引理 `prod_surjOn_snd`

English:
lemma prod_surjOn_snd
  given: (h : t₁.Nonempty)
  statement: (t₁ ×ˢ t₂).SurjOn Prod.snd t₂
  proof: fun _ h => by simpa [h]

中文:
引理 prod_surjOn_snd
  条件: (h : t₁.Nonempty)
  结论: (t₁ ×ˢ t₂).SurjOn Prod.snd t₂
  证明: fun _ h => by simpa [h]
-/
lemma prod_surjOn_snd (h : t₁.Nonempty) : (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ :=
  fun _ h => by simpa [h]

/--
lemma `prod_surjOn_fst_iff` / 引理 `prod_surjOn_fst_iff`

English:
lemma prod_surjOn_fst_iff
  statement: (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ ↔ t₁ = ∅ ∨ t₂.Nonempty
  proof: ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_fst]⟩

中文:
引理 prod_surjOn_fst_iff
  结论: (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ ↔ t₁ = ∅ ∨ t₂.Nonempty
  证明: ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_fst]⟩

Depends on / 依赖: contextual, or_imp, prod_surjOn_fst
-/
lemma prod_surjOn_fst_iff : (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ ↔ t₁ = ∅ ∨ t₂.Nonempty :=
  ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_fst]⟩

/--
lemma `prod_surjOn_snd_iff` / 引理 `prod_surjOn_snd_iff`

English:
lemma prod_surjOn_snd_iff
  statement: (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ ↔ t₁.Nonempty ∨ t₂ = ∅
  proof: ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_snd]⟩

中文:
引理 prod_surjOn_snd_iff
  结论: (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ ↔ t₁.Nonempty ∨ t₂ = ∅
  证明: ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_snd]⟩

Depends on / 依赖: contextual, or_imp, prod_surjOn_snd
-/
lemma prod_surjOn_snd_iff : (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ ↔ t₁.Nonempty ∨ t₂ = ∅ :=
  ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_snd]⟩

/--
lemma `MapsTo.prodMk` / 引理 `MapsTo.prodMk`

English:
lemma MapsTo.prodMk
  given: (h₁ : MapsTo f₁ s t₁) (h₂ : MapsTo f₂ s t₂)
  proof: fun _ hx => ⟨h₁ hx, h₂ hx⟩

中文:
引理 MapsTo.prodMk
  条件: (h₁ : MapsTo f₁ s t₁) (h₂ : MapsTo f₂ s t₂)
  证明: fun _ hx => ⟨h₁ hx, h₂ hx⟩
-/
lemma MapsTo.prodMk (h₁ : MapsTo f₁ s t₁) (h₂ : MapsTo f₂ s t₂) :
    MapsTo (fun x => (f₁ x, f₂ x)) s (t₁ ×ˢ t₂) :=
  fun _ hx => ⟨h₁ hx, h₂ hx⟩

/--
lemma `LeftInvOn.left_prodMk` / 引理 `LeftInvOn.left_prodMk`

English:
lemma LeftInvOn.left_prodMk
  given: (h₁ : LeftInvOn g₁ f₁ s)
  proof: h₁

中文:
引理 LeftInvOn.left_prodMk
  条件: (h₁ : LeftInvOn g₁ f₁ s)
  证明: h₁
-/
lemma LeftInvOn.left_prodMk (h₁ : LeftInvOn g₁ f₁ s) :
    LeftInvOn (fun x => g₁ x.1) (fun x => (f₁ x, f₂ x)) s := h₁

/--
lemma `LeftInvOn.right_prodMk` / 引理 `LeftInvOn.right_prodMk`

English:
lemma LeftInvOn.right_prodMk
  given: (h₂ : LeftInvOn g₂ f₂ s)
  proof: h₂

中文:
引理 LeftInvOn.right_prodMk
  条件: (h₂ : LeftInvOn g₂ f₂ s)
  证明: h₂
-/
lemma LeftInvOn.right_prodMk (h₂ : LeftInvOn g₂ f₂ s) :
    LeftInvOn (fun x => g₂ x.2) (fun x => (f₁ x, f₂ x)) s := h₂

end Prod

section ProdMap

variable {α₁ α₂ β₁ β₂ : Type*} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂}
  {f₁ : α₁ -> β₁} {f₂ : α₂ -> β₂} {g₁ : β₁ -> α₁} {g₂ : β₂ -> α₂}

/--
lemma `InjOn.prodMap` / 引理 `InjOn.prodMap`

English:
lemma InjOn.prodMap
  given: (h₁ : s₁.InjOn f₁) (h₂ : s₂.InjOn f₂)
  proof: fun x hx y hy => by simp_rw [Prod.ext_iff]; exact And.imp (h₁ hx.1 hy.1) (h₂ hx.2 hy.2)

中文:
引理 InjOn.prodMap
  条件: (h₁ : s₁.InjOn f₁) (h₂ : s₂.InjOn f₂)
  证明: fun x hx y hy => by simp_rw [Prod.ext_iff]; exact And.imp (h₁ hx.1 hy.1) (h₂ hx.2 hy.2)

Depends on / 依赖: And.imp, Prod.ext_iff, ext_iff, simp_rw
-/
lemma InjOn.prodMap (h₁ : s₁.InjOn f₁) (h₂ : s₂.InjOn f₂) :
    (s₁ ×ˢ s₂).InjOn fun x => (f₁ x.1, f₂ x.2) :=
  fun x hx y hy => by simp_rw [Prod.ext_iff]; exact And.imp (h₁ hx.1 hy.1) (h₂ hx.2 hy.2)

/--
lemma `SurjOn.prodMap` / 引理 `SurjOn.prodMap`

English:
lemma SurjOn.prodMap
  given: (h₁ : SurjOn f₁ s₁ t₁) (h₂ : SurjOn f₂ s₂ t₂)
  proof: by
  rintro x hx
  obtain ⟨a₁, ha₁, hx₁⟩ := h₁ hx.1
  obtain ⟨a₂, ha₂, hx₂⟩ := h₂ hx.2
  exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, Prod.ext hx₁ hx₂⟩

中文:
引理 SurjOn.prodMap
  条件: (h₁ : SurjOn f₁ s₁ t₁) (h₂ : SurjOn f₂ s₂ t₂)
  证明: by
  rintro x hx
  obtain ⟨a₁, ha₁, hx₁⟩ := h₁ hx.1
  obtain ⟨a₂, ha₂, hx₂⟩ := h₂ hx.2
  exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, Prod.ext hx₁ hx₂⟩

Depends on / 依赖: Prod.ext
-/
lemma SurjOn.prodMap (h₁ : SurjOn f₁ s₁ t₁) (h₂ : SurjOn f₂ s₂ t₂) :
    SurjOn (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := by
  rintro x hx
  obtain ⟨a₁, ha₁, hx₁⟩ := h₁ hx.1
  obtain ⟨a₂, ha₂, hx₂⟩ := h₂ hx.2
  exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, Prod.ext hx₁ hx₂⟩

/--
lemma `MapsTo.prodMap` / 引理 `MapsTo.prodMap`

English:
lemma MapsTo.prodMap
  given: (h₁ : MapsTo f₁ s₁ t₁) (h₂ : MapsTo f₂ s₂ t₂)
  proof: fun _x hx => ⟨h₁ hx.1, h₂ hx.2⟩

中文:
引理 MapsTo.prodMap
  条件: (h₁ : MapsTo f₁ s₁ t₁) (h₂ : MapsTo f₂ s₂ t₂)
  证明: fun _x hx => ⟨h₁ hx.1, h₂ hx.2⟩
-/
lemma MapsTo.prodMap (h₁ : MapsTo f₁ s₁ t₁) (h₂ : MapsTo f₂ s₂ t₂) :
    MapsTo (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  fun _x hx => ⟨h₁ hx.1, h₂ hx.2⟩

/--
lemma `BijOn.prodMap` / 引理 `BijOn.prodMap`

English:
lemma BijOn.prodMap
  given: (h₁ : BijOn f₁ s₁ t₁) (h₂ : BijOn f₂ s₂ t₂)
  proof: ⟨h₁.mapsTo.prodMap h₂.mapsTo, h₁.injOn.prodMap h₂.injOn, h₁.surjOn.prodMap h₂.surjOn⟩

中文:
引理 BijOn.prodMap
  条件: (h₁ : BijOn f₁ s₁ t₁) (h₂ : BijOn f₂ s₂ t₂)
  证明: ⟨h₁.mapsTo.prodMap h₂.mapsTo, h₁.injOn.prodMap h₂.injOn, h₁.surjOn.prodMap h₂.surjOn⟩

Depends on / 依赖: injOn.prodMap, mapsTo, mapsTo.prodMap, prodMap, surjOn, surjOn.prodMap
-/
lemma BijOn.prodMap (h₁ : BijOn f₁ s₁ t₁) (h₂ : BijOn f₂ s₂ t₂) :
    BijOn (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.mapsTo.prodMap h₂.mapsTo, h₁.injOn.prodMap h₂.injOn, h₁.surjOn.prodMap h₂.surjOn⟩

/--
lemma `LeftInvOn.prodMap` / 引理 `LeftInvOn.prodMap`

English:
lemma LeftInvOn.prodMap
  given: (h₁ : LeftInvOn g₁ f₁ s₁) (h₂ : LeftInvOn g₂ f₂ s₂)
  proof: fun _x hx => Prod.ext (h₁ hx.1) (h₂ hx.2)

中文:
引理 LeftInvOn.prodMap
  条件: (h₁ : LeftInvOn g₁ f₁ s₁) (h₂ : LeftInvOn g₂ f₂ s₂)
  证明: fun _x hx => Prod.ext (h₁ hx.1) (h₂ hx.2)

Depends on / 依赖: Prod.ext
-/
lemma LeftInvOn.prodMap (h₁ : LeftInvOn g₁ f₁ s₁) (h₂ : LeftInvOn g₂ f₂ s₂) :
    LeftInvOn (fun x => (g₁ x.1, g₂ x.2)) (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) :=
  fun _x hx => Prod.ext (h₁ hx.1) (h₂ hx.2)

/--
lemma `RightInvOn.prodMap` / 引理 `RightInvOn.prodMap`

English:
lemma RightInvOn.prodMap
  given: (h₁ : RightInvOn g₁ f₁ t₁) (h₂ : RightInvOn g₂ f₂ t₂)
  proof: fun _x hx => Prod.ext (h₁ hx.1) (h₂ hx.2)

中文:
引理 RightInvOn.prodMap
  条件: (h₁ : RightInvOn g₁ f₁ t₁) (h₂ : RightInvOn g₂ f₂ t₂)
  证明: fun _x hx => Prod.ext (h₁ hx.1) (h₂ hx.2)

Depends on / 依赖: Prod.ext
-/
lemma RightInvOn.prodMap (h₁ : RightInvOn g₁ f₁ t₁) (h₂ : RightInvOn g₂ f₂ t₂) :
    RightInvOn (fun x => (g₁ x.1, g₂ x.2)) (fun x => (f₁ x.1, f₂ x.2)) (t₁ ×ˢ t₂) :=
  fun _x hx => Prod.ext (h₁ hx.1) (h₂ hx.2)

/--
lemma `InvOn.prodMap` / 引理 `InvOn.prodMap`

English:
lemma InvOn.prodMap
  given: (h₁ : InvOn g₁ f₁ s₁ t₁) (h₂ : InvOn g₂ f₂ s₂ t₂)
  proof: ⟨h₁.1.prodMap h₂.1, h₁.2.prodMap h₂.2⟩

中文:
引理 InvOn.prodMap
  条件: (h₁ : InvOn g₁ f₁ s₁ t₁) (h₂ : InvOn g₂ f₂ s₂ t₂)
  证明: ⟨h₁.1.prodMap h₂.1, h₁.2.prodMap h₂.2⟩

Depends on / 依赖: prodMap
-/
lemma InvOn.prodMap (h₁ : InvOn g₁ f₁ s₁ t₁) (h₂ : InvOn g₂ f₂ s₂ t₂) :
    InvOn (fun x => (g₁ x.1, g₂ x.2)) (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.1.prodMap h₂.1, h₁.2.prodMap h₂.2⟩

end ProdMap

end Set

namespace Equiv
open Set

variable (e : α ≃ β) {s : Set α} {t : Set β}

/--
lemma `bijOn'` / 引理 `bijOn'`

English:
lemma bijOn'
  given: (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s)
  statement: BijOn e s t
  proof: ⟨h₁, e.injective.injOn, fun b hb => ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩

中文:
引理 bijOn'
  条件: (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s)
  结论: BijOn e s t
  证明: ⟨h₁, e.injective.injOn, fun b hb => ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩

Depends on / 依赖: apply_symm_apply, e.injective.injOn, e.symm, injective
-/
lemma bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijOn e s t :=
  ⟨h₁, e.injective.injOn, fun b hb => ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩

/--
lemma `bijOn` / 引理 `bijOn`

English:
lemma bijOn
  given: (h : forall a, e a in t ↔ a in s)
  statement: BijOn e s t
  proof: e.bijOn' (fun _ => (h _).2) fun b hb => (h _).1 by rwa [apply_symm_apply]

中文:
引理 bijOn
  条件: (h : 对任意 a, e a in t ↔ a in s)
  结论: BijOn e s t
  证明: e.bijOn' (fun _ => (h _).2) fun b hb => (h _).1 by rwa [apply_symm_apply]
-/
protected lemma bijOn (h : forall a, e a in t ↔ a in s) : BijOn e s t :=
e.bijOn' (fun _ => (h _).2) fun b hb => (h _).1 by rwa [apply_symm_apply]

/--
lemma `invOn` / 引理 `invOn`

English:
lemma invOn
  statement: InvOn e e.symm t s
  proof: ⟨e.rightInverse_symm.leftInvOn _, e.leftInverse_symm.leftInvOn _⟩

中文:
引理 invOn
  结论: InvOn e e.symm t s
  证明: ⟨e.rightInverse_symm.leftInvOn _, e.leftInverse_symm.leftInvOn _⟩

Depends on / 依赖: e.leftInverse_symm.leftInvOn, e.rightInverse_symm.leftInvOn, leftInvOn, leftInverse_symm, rightInverse_symm
-/
lemma invOn : InvOn e e.symm t s :=
  ⟨e.rightInverse_symm.leftInvOn _, e.leftInverse_symm.leftInvOn _⟩

/--
lemma `bijOn_image` / 引理 `bijOn_image`

English:
lemma bijOn_image
  statement: BijOn e s (e '' s)
  proof: e.injective.injOn.bijOn_image

中文:
引理 bijOn_image
  结论: BijOn e s (e '' s)
  证明: e.injective.injOn.bijOn_image

Depends on / 依赖: bijOn_image, e.injective.injOn.bijOn_image, injective
-/
lemma bijOn_image : BijOn e s (e '' s) := e.injective.injOn.bijOn_image
/--
lemma `bijOn_symm_image` / 引理 `bijOn_symm_image`

English:
lemma bijOn_symm_image
  statement: BijOn e.symm (e '' s) s
  proof: e.bijOn_image.symm e.invOn

中文:
引理 bijOn_symm_image
  结论: BijOn e.symm (e '' s) s
  证明: e.bijOn_image.symm e.invOn

Depends on / 依赖: bijOn_image, e.bijOn_image.symm, e.invOn
-/
lemma bijOn_symm_image : BijOn e.symm (e '' s) s := e.bijOn_image.symm e.invOn

variable {e}

/--
lemma `bijOn_symm` / 引理 `bijOn_symm`

English:
lemma bijOn_symm
  statement: BijOn e.symm t s ↔ BijOn e s t
  proof: bijOn_comm e.symm.invOn

alias ⟨_root_.Set.BijOn.of_equiv_symm, _root_.Set.BijOn.equiv_symm⟩ := bijOn_symm

中文:
引理 bijOn_symm
  结论: BijOn e.symm t s ↔ BijOn e s t
  证明: bijOn_comm e.symm.invOn

alias ⟨_root_.Set.BijOn.of_equiv_symm, _root_.Set.BijOn.equiv_symm⟩ := bijOn_symm
-/
@[simp] lemma bijOn_symm : BijOn e.symm t s ↔ BijOn e s t := bijOn_comm e.symm.invOn

alias ⟨_root_.Set.BijOn.of_equiv_symm, _root_.Set.BijOn.equiv_symm⟩ := bijOn_symm

variable [DecidableEq α] {a b : α}

/--
lemma `bijOn_swap` / 引理 `bijOn_swap`

English:
lemma bijOn_swap
  given: (ha : a in s) (hb : b in s)
  statement: BijOn (swap a b) s s
  proof: (swap a b).bijOn fun x => by
    obtain rfl | hxa := eq_or_ne x a <;>
    obtain rfl | hxb := eq_or_ne x b <;>
    simp [*, swap_apply_of_ne_of_ne]

中文:
引理 bijOn_swap
  条件: (ha : a in s) (hb : b in s)
  结论: BijOn (swap a b) s s
  证明: (swap a b).bijOn fun x => by
    obtain rfl | hxa := eq_or_ne x a <;>
    obtain rfl | hxb := eq_or_ne x b <;>
    simp [*, swap_apply_of_ne_of_ne]

Depends on / 依赖: eq_or_ne, swap_apply_of_ne_of_ne
-/
lemma bijOn_swap (ha : a in s) (hb : b in s) : BijOn (swap a b) s s :=
  (swap a b).bijOn fun x => by
    obtain rfl | hxa := eq_or_ne x a <;>
    obtain rfl | hxb := eq_or_ne x b <;>
    simp [*, swap_apply_of_ne_of_ne]

end Equiv
