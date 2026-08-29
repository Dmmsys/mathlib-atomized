/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Set.Lattice.Image

/-!
# Lattice operations on finsets

This file is concerned with how big lattice or set operations behave when indexed by a finset.

See also `Mathlib/Data/Finset/Lattice/Fold.lean`, which is concerned with folding binary lattice
operations over a finset.
-/

public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

section Lattice

variable {ι' : Sort*} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iSup_eq_iSup_finset'` for a version
that works for `ι : Sort*`. -/
@[to_dual
/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iInf_eq_iInf_finset'` for a version
that works for `ι : Sort*`. -/]
/--
theorem `iSup_eq_iSup_finset` / 定理 `iSup_eq_iSup_finset`

English:
theorem iSup_eq_iSup_finset
  given: (s : ι -> α)
  statement: ⨆ i, s i = ⨆ t : Finset ι, ⨆ i in t, s i
  proof: by
  refine le_antisymm ?_ ?_
· exact iSup_le fun b => le_iSup_of_le {b} le_iSup_of_le b le_iSup_of_le (by simp) le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _

中文:
定理 iSup_eq_iSup_finset
  条件: (s : ι -> α)
  结论: ⨆ i, s i = ⨆ t : Finset ι, ⨆ i in t, s i
  证明: by
  refine le_antisymm ?_ ?_
· exact iSup_le fun b => le_iSup_of_le {b} le_iSup_of_le b le_iSup_of_le (by simp) le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _

Depends on / 依赖: iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_rfl
-/
theorem iSup_eq_iSup_finset (s : ι -> α) : ⨆ i, s i = ⨆ t : Finset ι, ⨆ i in t, s i := by
  refine le_antisymm ?_ ?_
· exact iSup_le fun b => le_iSup_of_le {b} le_iSup_of_le b le_iSup_of_le (by simp) le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `iSup_eq_iSup_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/
@[to_dual
/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `iInf_eq_iInf_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/]
/--
theorem `iSup_eq_iSup_finset'` / 定理 `iSup_eq_iSup_finset'`

English:
theorem iSup_eq_iSup_finset'
  given: (s : ι' -> α)
  proof: by
  rw [← iSup_eq_iSup_finset]; rw [← Equiv.plift.surjective.iSup_comp]; rfl

中文:
定理 iSup_eq_iSup_finset'
  条件: (s : ι' -> α)
  证明: by
  rw [← iSup_eq_iSup_finset]; rw [← Equiv.plift.surjective.iSup_comp]; rfl

Depends on / 依赖: Equiv.plift.surjective.iSup_comp, iSup_comp, iSup_eq_iSup_finset, surjective
-/
theorem iSup_eq_iSup_finset' (s : ι' -> α) :
    ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆ i in t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset]; rw [← Equiv.plift.surjective.iSup_comp]; rfl

end Lattice

namespace Set

variable {ι' : Sort*}

/--
theorem `iUnion_eq_iUnion_finset` / 定理 `iUnion_eq_iUnion_finset`

English:
theorem iUnion_eq_iUnion_finset
  given: (s : ι -> Set α)
  statement: ⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
  proof: iSup_eq_iSup_finset s

中文:
定理 iUnion_eq_iUnion_finset
  条件: (s : ι -> Set α)
  结论: ⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
  证明: iSup_eq_iSup_finset s

Depends on / 依赖: iSup_eq_iSup_finset
-/
theorem iUnion_eq_iUnion_finset (s : ι -> Set α) : ⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i :=
  iSup_eq_iSup_finset s

/--
theorem `iUnion_eq_iUnion_finset'` / 定理 `iUnion_eq_iUnion_finset'`

English:
theorem iUnion_eq_iUnion_finset'
  given: (s : ι' -> Set α)
  proof: iSup_eq_iSup_finset' s

中文:
定理 iUnion_eq_iUnion_finset'
  条件: (s : ι' -> Set α)
  证明: iSup_eq_iSup_finset' s

Depends on / 依赖: iSup_eq_iSup_finset
-/
theorem iUnion_eq_iUnion_finset' (s : ι' -> Set α) :
    ⋃ i, s i = ⋃ t : Finset (PLift ι'), ⋃ i in t, s (PLift.down i) :=
  iSup_eq_iSup_finset' s

/--
theorem `iInter_eq_iInter_finset` / 定理 `iInter_eq_iInter_finset`

English:
theorem iInter_eq_iInter_finset
  given: (s : ι -> Set α)
  statement: ⋂ i, s i = ⋂ t : Finset ι, ⋂ i in t, s i
  proof: iInf_eq_iInf_finset s

中文:
定理 iInter_eq_iInter_finset
  条件: (s : ι -> Set α)
  结论: ⋂ i, s i = ⋂ t : Finset ι, ⋂ i in t, s i
  证明: iInf_eq_iInf_finset s

Depends on / 依赖: iInf_eq_iInf_finset
-/
theorem iInter_eq_iInter_finset (s : ι -> Set α) : ⋂ i, s i = ⋂ t : Finset ι, ⋂ i in t, s i :=
  iInf_eq_iInf_finset s

/--
theorem `iInter_eq_iInter_finset'` / 定理 `iInter_eq_iInter_finset'`

English:
theorem iInter_eq_iInter_finset'
  given: (s : ι' -> Set α)
  proof: iInf_eq_iInf_finset' s

中文:
定理 iInter_eq_iInter_finset'
  条件: (s : ι' -> Set α)
  证明: iInf_eq_iInf_finset' s

Depends on / 依赖: iInf_eq_iInf_finset
-/
theorem iInter_eq_iInter_finset' (s : ι' -> Set α) :
    ⋂ i, s i = ⋂ t : Finset (PLift ι'), ⋂ i in t, s (PLift.down i) :=
  iInf_eq_iInf_finset' s

/--
theorem `iUnion_finset_eq_set` / 定理 `iUnion_finset_eq_set`

English:
theorem iUnion_finset_eq_set
  given: (s : Set ι)
  proof: by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨{⟨x, hx⟩}, hx, by simp⟩⟩

中文:
定理 iUnion_finset_eq_set
  条件: (s : Set ι)
  证明: by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨{⟨x, hx⟩}, hx, by simp⟩⟩

Depends on / 依赖: Set.mem_iUnion, Set.mem_image, SetLike, SetLike.mem_coe, Subtype, Subtype.exists, exists_and_right, exists_eq_right, mem_coe, mem_iUnion, mem_image
-/
theorem iUnion_finset_eq_set (s : Set ι) :
    ⋃ s' : Finset s, Subtype.val '' (s' : Set s) = s := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨{⟨x, hx⟩}, hx, by simp⟩⟩

end Set

namespace Finset

section minimal

variable [DecidableEq α] {P : Finset α -> Prop} {s : Finset α}

/--
theorem `maximal_iff_forall_insert` / 定理 `maximal_iff_forall_insert`

English:
theorem maximal_iff_forall_insert
  given: (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s)
  proof: by
  simp only [Maximal, and_congr_right_iff]
exact fun _ => ⟨fun h x hxs hx => hxs h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt => by_contra fun hxs => h x hxs (hP ht (insert_subset hxt hst))⟩

中文:
定理 maximal_iff_forall_insert
  条件: (hP : 对任意 ⦃s t⦄, P t -> s subseteq t -> P s)
  证明: by
  simp only [Maximal, and_congr_right_iff]
exact fun _ => ⟨fun h x hxs hx => hxs h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt => by_contra fun hxs => h x hxs (hP ht (insert_subset hxt hst))⟩

Depends on / 依赖: Maximal, and_congr_right_iff, insert_subset, mem_insert_self, subset_insert
-/
theorem maximal_iff_forall_insert (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s) :
    Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (insert x s) := by
  simp only [Maximal, and_congr_right_iff]
exact fun _ => ⟨fun h x hxs hx => hxs h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt => by_contra fun hxs => h x hxs (hP ht (insert_subset hxt hst))⟩

/--
theorem `minimal_iff_forall_erase` / 定理 `minimal_iff_forall_erase`

English:
theorem minimal_iff_forall_erase
  given: (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s)
  proof: ⟨h.prop, fun x hxs hx => by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs => by_contra fun hxt =>
h.2 x hxs hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

@[deprecated (since := "2026-06-03")]
alias minimal_iff_forall_diff_singleton := minimal_iff_forall_erase

中文:
定理 minimal_iff_forall_erase
  条件: (hP : 对任意 ⦃s t⦄, P t -> t subseteq s -> P s)
  证明: ⟨h.prop, fun x hxs hx => by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs => by_contra fun hxt =>
h.2 x hxs hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

@[deprecated (since := "2026-06-03")]
alias minimal_iff_forall_diff_singleton := minimal_iff_forall_erase

Depends on / 依赖: erase_subset, h.le_of_le, h.prop, le_of_le
-/
theorem minimal_iff_forall_erase (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) :
    Minimal P s ↔ P s ∧ forall x in s, ¬ P (s.erase x) where
  mp h := ⟨h.prop, fun x hxs hx => by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs => by_contra fun hxt =>
h.2 x hxs hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

@[deprecated (since := "2026-06-03")]
alias minimal_iff_forall_diff_singleton := minimal_iff_forall_erase

end minimal

/-! ### Interaction with big lattice/set operations -/

section Lattice

@[to_dual]
/--
theorem `iSup_coe` / 定理 `iSup_coe`

English:
theorem iSup_coe
  given: [SupSet β] (f : α -> β) (s : Finset α)
  statement: ⨆ x in (↑s : Set α), f x = ⨆ x in s, f x
  proof: rfl

中文:
定理 iSup_coe
  条件: [SupSet β] (f : α -> β) (s : Finset α)
  结论: ⨆ x in (↑s : Set α), f x = ⨆ x in s, f x
  证明: rfl
-/
theorem iSup_coe [SupSet β] (f : α -> β) (s : Finset α) : ⨆ x in (↑s : Set α), f x = ⨆ x in s, f x :=
  rfl

variable [CompleteLattice β]

@[to_dual]
/--
theorem `iSup_singleton` / 定理 `iSup_singleton`

English:
theorem iSup_singleton
  given: (a : α) (s : α -> β)
  statement: ⨆ x in ({a} : Finset α), s x = s a
  proof: by simp

@[to_dual]

中文:
定理 iSup_singleton
  条件: (a : α) (s : α -> β)
  结论: ⨆ x in ({a} : Finset α), s x = s a
  证明: by simp

@[to_dual]
-/
theorem iSup_singleton (a : α) (s : α -> β) : ⨆ x in ({a} : Finset α), s x = s a := by simp

@[to_dual]
/--
theorem `iSup_option_toFinset` / 定理 `iSup_option_toFinset`

English:
theorem iSup_option_toFinset
  given: (o : Option α) (f : α -> β)
  statement: ⨆ x in o.toFinset, f x = ⨆ x in o, f x
  proof: by
  simp

中文:
定理 iSup_option_toFinset
  条件: (o : Option α) (f : α -> β)
  结论: ⨆ x in o.toFinset, f x = ⨆ x in o, f x
  证明: by
  simp
-/
theorem iSup_option_toFinset (o : Option α) (f : α -> β) : ⨆ x in o.toFinset, f x = ⨆ x in o, f x := by
  simp

variable [DecidableEq α]

@[to_dual]
/--
theorem `iSup_union` / 定理 `iSup_union`

English:
theorem iSup_union
  given: {f : α -> β} {s t : Finset α}
  proof: by
  simpa using! _root_.iSup_union

@[to_dual]

中文:
定理 iSup_union
  条件: {f : α -> β} {s t : Finset α}
  证明: by
  simpa using! _root_.iSup_union

@[to_dual]

Depends on / 依赖: _root_, _root_.iSup_union, iSup_union
-/
theorem iSup_union {f : α -> β} {s t : Finset α} :
    ⨆ x in s union t, f x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x := by
  simpa using! _root_.iSup_union

@[to_dual]
/--
theorem `iSup_insert` / 定理 `iSup_insert`

English:
theorem iSup_insert
  given: (a : α) (s : Finset α) (t : α -> β)
  proof: by
  simpa using! _root_.iSup_insert

@[to_dual]

中文:
定理 iSup_insert
  条件: (a : α) (s : Finset α) (t : α -> β)
  证明: by
  simpa using! _root_.iSup_insert

@[to_dual]

Depends on / 依赖: _root_, _root_.iSup_insert, iSup_insert
-/
theorem iSup_insert (a : α) (s : Finset α) (t : α -> β) :
    ⨆ x in insert a s, t x = t a ⊔ ⨆ x in s, t x := by
  simpa using! _root_.iSup_insert

@[to_dual]
/--
theorem `iSup_finset_image` / 定理 `iSup_finset_image`

English:
theorem iSup_finset_image
  given: {f : γ -> α} {g : α -> β} {s : Finset γ}
  proof: by
  simpa using! iSup_image

@[to_dual]

中文:
定理 iSup_finset_image
  条件: {f : γ -> α} {g : α -> β} {s : Finset γ}
  证明: by
  simpa using! iSup_image

@[to_dual]

Depends on / 依赖: iSup_image
-/
theorem iSup_finset_image {f : γ -> α} {g : α -> β} {s : Finset γ} :
    ⨆ x in s.image f, g x = ⨆ y in s, g (f y) := by
  simpa using! iSup_image

@[to_dual]
/--
theorem `iSup_insert_update` / 定理 `iSup_insert_update`

English:
theorem iSup_insert_update
  given: {x : α} {t : Finset α} (f : α -> β) {s : β} (hx : x ∉ t)
  proof: by
  rw [Finset.iSup_insert]
  grind

@[to_dual]

中文:
定理 iSup_insert_update
  条件: {x : α} {t : Finset α} (f : α -> β) {s : β} (hx : x ∉ t)
  证明: by
  rw [Finset.iSup_insert]
  grind

@[to_dual]

Depends on / 依赖: Finset, Finset.iSup_insert, iSup_insert
-/
theorem iSup_insert_update {x : α} {t : Finset α} (f : α -> β) {s : β} (hx : x ∉ t) :
    ⨆ i in insert x t, Function.update f x s i = s ⊔ ⨆ i in t, f i := by
  rw [Finset.iSup_insert]
  grind

@[to_dual]
/--
theorem `iSup_biUnion` / 定理 `iSup_biUnion`

English:
theorem iSup_biUnion
  given: (s : Finset γ) (t : γ -> Finset α) (f : α -> β)
  proof: by simp [@iSup_comm _ α, iSup_and]

中文:
定理 iSup_biUnion
  条件: (s : Finset γ) (t : γ -> Finset α) (f : α -> β)
  证明: by simp [@iSup_comm _ α, iSup_and]

Depends on / 依赖: iSup_and, iSup_comm
-/
theorem iSup_biUnion (s : Finset γ) (t : γ -> Finset α) (f : α -> β) :
    ⨆ y in s.biUnion t, f y = ⨆ (x in s) (y in t x), f y := by simp [@iSup_comm _ α, iSup_and]

end Lattice

/--
theorem `set_biUnion_coe` / 定理 `set_biUnion_coe`

English:
theorem set_biUnion_coe
  given: (s : Finset α) (t : α -> Set β)
  statement: ⋃ x in (↑s : Set α), t x = ⋃ x in s, t x
  proof: rfl

中文:
定理 set_biUnion_coe
  条件: (s : Finset α) (t : α -> Set β)
  结论: ⋃ x in (↑s : Set α), t x = ⋃ x in s, t x
  证明: rfl
-/
theorem set_biUnion_coe (s : Finset α) (t : α -> Set β) : ⋃ x in (↑s : Set α), t x = ⋃ x in s, t x :=
  rfl

/--
theorem `set_biInter_coe` / 定理 `set_biInter_coe`

English:
theorem set_biInter_coe
  given: (s : Finset α) (t : α -> Set β)
  statement: ⋂ x in (↑s : Set α), t x = ⋂ x in s, t x
  proof: rfl

中文:
定理 set_biInter_coe
  条件: (s : Finset α) (t : α -> Set β)
  结论: ⋂ x in (↑s : Set α), t x = ⋂ x in s, t x
  证明: rfl
-/
theorem set_biInter_coe (s : Finset α) (t : α -> Set β) : ⋂ x in (↑s : Set α), t x = ⋂ x in s, t x :=
  rfl

/--
theorem `set_biUnion_singleton` / 定理 `set_biUnion_singleton`

English:
theorem set_biUnion_singleton
  given: (a : α) (s : α -> Set β)
  statement: ⋃ x in ({a} : Finset α), s x = s a
  proof: iSup_singleton a s

中文:
定理 set_biUnion_singleton
  条件: (a : α) (s : α -> Set β)
  结论: ⋃ x in ({a} : Finset α), s x = s a
  证明: iSup_singleton a s

Depends on / 依赖: iSup_singleton
-/
theorem set_biUnion_singleton (a : α) (s : α -> Set β) : ⋃ x in ({a} : Finset α), s x = s a :=
  iSup_singleton a s

/--
theorem `set_biInter_singleton` / 定理 `set_biInter_singleton`

English:
theorem set_biInter_singleton
  given: (a : α) (s : α -> Set β)
  statement: ⋂ x in ({a} : Finset α), s x = s a
  proof: iInf_singleton a s

@[simp]

中文:
定理 set_biInter_singleton
  条件: (a : α) (s : α -> Set β)
  结论: ⋂ x in ({a} : Finset α), s x = s a
  证明: iInf_singleton a s

@[simp]

Depends on / 依赖: iInf_singleton
-/
theorem set_biInter_singleton (a : α) (s : α -> Set β) : ⋂ x in ({a} : Finset α), s x = s a :=
  iInf_singleton a s

@[simp]
/--
theorem `set_biUnion_preimage_singleton` / 定理 `set_biUnion_preimage_singleton`

English:
theorem set_biUnion_preimage_singleton
  given: (f : α -> β) (s : Finset β)
  proof: Set.biUnion_preimage_singleton f s

中文:
定理 set_biUnion_preimage_singleton
  条件: (f : α -> β) (s : Finset β)
  证明: Set.biUnion_preimage_singleton f s

Depends on / 依赖: Set.biUnion_preimage_singleton, biUnion_preimage_singleton
-/
theorem set_biUnion_preimage_singleton (f : α -> β) (s : Finset β) :
    ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s :=
  Set.biUnion_preimage_singleton f s

/--
theorem `set_biUnion_option_toFinset` / 定理 `set_biUnion_option_toFinset`

English:
theorem set_biUnion_option_toFinset
  given: (o : Option α) (f : α -> Set β)
  proof: iSup_option_toFinset o f

中文:
定理 set_biUnion_option_toFinset
  条件: (o : Option α) (f : α -> Set β)
  证明: iSup_option_toFinset o f

Depends on / 依赖: iSup_option_toFinset
-/
theorem set_biUnion_option_toFinset (o : Option α) (f : α -> Set β) :
    ⋃ x in o.toFinset, f x = ⋃ x in o, f x :=
  iSup_option_toFinset o f

/--
theorem `set_biInter_option_toFinset` / 定理 `set_biInter_option_toFinset`

English:
theorem set_biInter_option_toFinset
  given: (o : Option α) (f : α -> Set β)
  proof: iInf_option_toFinset o f

中文:
定理 set_biInter_option_toFinset
  条件: (o : Option α) (f : α -> Set β)
  证明: iInf_option_toFinset o f

Depends on / 依赖: iInf_option_toFinset
-/
theorem set_biInter_option_toFinset (o : Option α) (f : α -> Set β) :
    ⋂ x in o.toFinset, f x = ⋂ x in o, f x :=
  iInf_option_toFinset o f

/--
theorem `subset_set_biUnion_of_mem` / 定理 `subset_set_biUnion_of_mem`

English:
theorem subset_set_biUnion_of_mem
  given: {s : Finset α} {f : α -> Set β} {x : α} (h : x in s)
  proof: le_iSup_of_le x by simp [h]

中文:
定理 subset_set_biUnion_of_mem
  条件: {s : Finset α} {f : α -> Set β} {x : α} (h : x in s)
  证明: le_iSup_of_le x by simp [h]

Depends on / 依赖: le_iSup_of_le
-/
theorem subset_set_biUnion_of_mem {s : Finset α} {f : α -> Set β} {x : α} (h : x in s) :
    f x subseteq ⋃ y in s, f y :=
le_iSup_of_le x by simp [h]

variable [DecidableEq α]

/--
theorem `set_biUnion_union` / 定理 `set_biUnion_union`

English:
theorem set_biUnion_union
  given: (s t : Finset α) (u : α -> Set β)
  proof: iSup_union

中文:
定理 set_biUnion_union
  条件: (s t : Finset α) (u : α -> Set β)
  证明: iSup_union

Depends on / 依赖: iSup_union
-/
theorem set_biUnion_union (s t : Finset α) (u : α -> Set β) :
    ⋃ x in s union t, u x = (⋃ x in s, u x) union ⋃ x in t, u x :=
  iSup_union

/--
theorem `set_biInter_inter` / 定理 `set_biInter_inter`

English:
theorem set_biInter_inter
  given: (s t : Finset α) (u : α -> Set β)
  proof: iInf_union

中文:
定理 set_biInter_inter
  条件: (s t : Finset α) (u : α -> Set β)
  证明: iInf_union

Depends on / 依赖: iInf_union
-/
theorem set_biInter_inter (s t : Finset α) (u : α -> Set β) :
    ⋂ x in s union t, u x = (⋂ x in s, u x) inter ⋂ x in t, u x :=
  iInf_union

/--
theorem `set_biUnion_insert` / 定理 `set_biUnion_insert`

English:
theorem set_biUnion_insert
  given: (a : α) (s : Finset α) (t : α -> Set β)
  proof: iSup_insert a s t

中文:
定理 set_biUnion_insert
  条件: (a : α) (s : Finset α) (t : α -> Set β)
  证明: iSup_insert a s t

Depends on / 依赖: iSup_insert
-/
theorem set_biUnion_insert (a : α) (s : Finset α) (t : α -> Set β) :
    ⋃ x in insert a s, t x = t a union ⋃ x in s, t x :=
  iSup_insert a s t

/--
theorem `set_biInter_insert` / 定理 `set_biInter_insert`

English:
theorem set_biInter_insert
  given: (a : α) (s : Finset α) (t : α -> Set β)
  proof: iInf_insert a s t

中文:
定理 set_biInter_insert
  条件: (a : α) (s : Finset α) (t : α -> Set β)
  证明: iInf_insert a s t

Depends on / 依赖: iInf_insert
-/
theorem set_biInter_insert (a : α) (s : Finset α) (t : α -> Set β) :
    ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x :=
  iInf_insert a s t

/--
theorem `set_biUnion_finset_image` / 定理 `set_biUnion_finset_image`

English:
theorem set_biUnion_finset_image
  given: {f : γ -> α} {g : α -> Set β} {s : Finset γ}
  proof: iSup_finset_image

中文:
定理 set_biUnion_finset_image
  条件: {f : γ -> α} {g : α -> Set β} {s : Finset γ}
  证明: iSup_finset_image

Depends on / 依赖: iSup_finset_image
-/
theorem set_biUnion_finset_image {f : γ -> α} {g : α -> Set β} {s : Finset γ} :
    ⋃ x in s.image f, g x = ⋃ y in s, g (f y) :=
  iSup_finset_image

/--
theorem `set_biInter_finset_image` / 定理 `set_biInter_finset_image`

English:
theorem set_biInter_finset_image
  given: {f : γ -> α} {g : α -> Set β} {s : Finset γ}
  proof: iInf_finset_image

中文:
定理 set_biInter_finset_image
  条件: {f : γ -> α} {g : α -> Set β} {s : Finset γ}
  证明: iInf_finset_image

Depends on / 依赖: iInf_finset_image
-/
theorem set_biInter_finset_image {f : γ -> α} {g : α -> Set β} {s : Finset γ} :
    ⋂ x in s.image f, g x = ⋂ y in s, g (f y) :=
  iInf_finset_image

/--
theorem `set_biUnion_insert_update` / 定理 `set_biUnion_insert_update`

English:
theorem set_biUnion_insert_update
  given: {x : α} {t : Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t)
  proof: iSup_insert_update f hx

中文:
定理 set_biUnion_insert_update
  条件: {x : α} {t : Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t)
  证明: iSup_insert_update f hx

Depends on / 依赖: iSup_insert_update
-/
theorem set_biUnion_insert_update {x : α} {t : Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t) :
    ⋃ i in insert x t, @update _ _ _ f x s i = s union ⋃ i in t, f i :=
  iSup_insert_update f hx

/--
theorem `set_biInter_insert_update` / 定理 `set_biInter_insert_update`

English:
theorem set_biInter_insert_update
  given: {x : α} {t : Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t)
  proof: iInf_insert_update f hx

中文:
定理 set_biInter_insert_update
  条件: {x : α} {t : Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t)
  证明: iInf_insert_update f hx

Depends on / 依赖: iInf_insert_update
-/
theorem set_biInter_insert_update {x : α} {t : Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t) :
    ⋂ i in insert x t, @update _ _ _ f x s i = s inter ⋂ i in t, f i :=
  iInf_insert_update f hx

/--
theorem `set_biUnion_biUnion` / 定理 `set_biUnion_biUnion`

English:
theorem set_biUnion_biUnion
  given: (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β)
  proof: iSup_biUnion s t f

中文:
定理 set_biUnion_biUnion
  条件: (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β)
  证明: iSup_biUnion s t f

Depends on / 依赖: iSup_biUnion
-/
theorem set_biUnion_biUnion (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β) :
    ⋃ y in s.biUnion t, f y = ⋃ (x in s) (y in t x), f y :=
  iSup_biUnion s t f

/--
theorem `set_biInter_biUnion` / 定理 `set_biInter_biUnion`

English:
theorem set_biInter_biUnion
  given: (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β)
  proof: iInf_biUnion s t f

中文:
定理 set_biInter_biUnion
  条件: (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β)
  证明: iInf_biUnion s t f

Depends on / 依赖: iInf_biUnion
-/
theorem set_biInter_biUnion (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β) :
    ⋂ y in s.biUnion t, f y = ⋂ (x in s) (y in t x), f y :=
  iInf_biUnion s t f

end Finset
