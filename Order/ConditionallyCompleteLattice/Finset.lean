/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Conditionally complete lattices and finite sets.

-/

public section


open Set

variable {ι α β γ : Type*}

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/--
theorem `Finset.Nonempty.csSup_eq_max'` / 定理 `Finset.Nonempty.csSup_eq_max'`

English:
theorem Finset.Nonempty.csSup_eq_max'
  given: {s : Finset α} (h : s.Nonempty)
  statement: sSup ↑s = s.max' h
  proof: eq_of_forall_ge_iff fun _ => (csSup_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm

中文:
定理 Finset.Nonempty.csSup_eq_max'
  条件: {s : Finset α} (h : s.Nonempty)
  结论: sSup ↑s = s.max' h
  证明: eq_of_forall_ge_iff fun _ => (csSup_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm

Depends on / 依赖: _le_iff, bddAbove, csSup_le_iff, eq_of_forall_ge_iff, h.to_set, s.bddAbove, s.max, to_set
-/
theorem Finset.Nonempty.csSup_eq_max' {s : Finset α} (h : s.Nonempty) : sSup ↑s = s.max' h :=
  eq_of_forall_ge_iff fun _ => (csSup_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm

/--
theorem `Finset.Nonempty.csInf_eq_min'` / 定理 `Finset.Nonempty.csInf_eq_min'`

English:
theorem Finset.Nonempty.csInf_eq_min'
  given: {s : Finset α} (h : s.Nonempty)
  statement: sInf ↑s = s.min' h
  proof: @Finset.Nonempty.csSup_eq_max' αᵒᵈ _ s h

中文:
定理 Finset.Nonempty.csInf_eq_min'
  条件: {s : Finset α} (h : s.Nonempty)
  结论: sInf ↑s = s.min' h
  证明: @Finset.Nonempty.csSup_eq_max' αᵒᵈ _ s h

Depends on / 依赖: Finset, Finset.Nonempty.csSup_eq_max, Nonempty, csSup_eq_max
-/
theorem Finset.Nonempty.csInf_eq_min' {s : Finset α} (h : s.Nonempty) : sInf ↑s = s.min' h :=
  @Finset.Nonempty.csSup_eq_max' αᵒᵈ _ s h

/--
theorem `Finset.Nonempty.csSup_mem` / 定理 `Finset.Nonempty.csSup_mem`

English:
theorem Finset.Nonempty.csSup_mem
  given: {s : Finset α} (h : s.Nonempty)
  statement: sSup (s : Set α) in s
  proof: by
  rw [h.csSup_eq_max']
  exact s.max'_mem _

中文:
定理 Finset.Nonempty.csSup_mem
  条件: {s : Finset α} (h : s.Nonempty)
  结论: sSup (s : Set α) in s
  证明: by
  rw [h.csSup_eq_max']
  exact s.max'_mem _

Depends on / 依赖: _mem, csSup_eq_max, h.csSup_eq_max, s.max
-/
theorem Finset.Nonempty.csSup_mem {s : Finset α} (h : s.Nonempty) : sSup (s : Set α) in s := by
  rw [h.csSup_eq_max']
  exact s.max'_mem _

/--
theorem `Finset.Nonempty.csInf_mem` / 定理 `Finset.Nonempty.csInf_mem`

English:
theorem Finset.Nonempty.csInf_mem
  given: {s : Finset α} (h : s.Nonempty)
  statement: sInf (s : Set α) in s
  proof: @Finset.Nonempty.csSup_mem αᵒᵈ _ _ h

中文:
定理 Finset.Nonempty.csInf_mem
  条件: {s : Finset α} (h : s.Nonempty)
  结论: sInf (s : Set α) in s
  证明: @Finset.Nonempty.csSup_mem αᵒᵈ _ _ h

Depends on / 依赖: Finset, Finset.Nonempty.csSup_mem, Nonempty, csSup_mem
-/
theorem Finset.Nonempty.csInf_mem {s : Finset α} (h : s.Nonempty) : sInf (s : Set α) in s :=
  @Finset.Nonempty.csSup_mem αᵒᵈ _ _ h

/--
theorem `Set.Nonempty.csSup_mem` / 定理 `Set.Nonempty.csSup_mem`

English:
theorem Set.Nonempty.csSup_mem
  given: (h : s.Nonempty) (hs : s.Finite)
  statement: sSup s in s
  proof: by
  lift s to Finset α using hs
  exact Finset.Nonempty.csSup_mem h

中文:
定理 Set.Nonempty.csSup_mem
  条件: (h : s.Nonempty) (hs : s.Finite)
  结论: sSup s in s
  证明: by
  lift s to Finset α using hs
  exact Finset.Nonempty.csSup_mem h

Depends on / 依赖: Finset, Finset.Nonempty.csSup_mem, Nonempty, csSup_mem
-/
theorem Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.Finite) : sSup s in s := by
  lift s to Finset α using hs
  exact Finset.Nonempty.csSup_mem h

/--
theorem `Set.Nonempty.csInf_mem` / 定理 `Set.Nonempty.csInf_mem`

English:
theorem Set.Nonempty.csInf_mem
  given: (h : s.Nonempty) (hs : s.Finite)
  statement: sInf s in s
  proof: @Set.Nonempty.csSup_mem αᵒᵈ _ _ h hs

中文:
定理 Set.Nonempty.csInf_mem
  条件: (h : s.Nonempty) (hs : s.Finite)
  结论: sInf s in s
  证明: @Set.Nonempty.csSup_mem αᵒᵈ _ _ h hs

Depends on / 依赖: Nonempty, Set.Nonempty.csSup_mem, csSup_mem
-/
theorem Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.Finite) : sInf s in s :=
  @Set.Nonempty.csSup_mem αᵒᵈ _ _ h hs

/--
theorem `Set.Finite.csSup_lt_iff` / 定理 `Set.Finite.csSup_lt_iff`

English:
theorem Set.Finite.csSup_lt_iff
  given: (hs : s.Finite) (h : s.Nonempty)
  statement: sSup s < a ↔ forall x in s, x < a
  proof: ⟨fun h _ hx => (le_csSup hs.bddAbove hx).trans_lt h, fun H => H _ h.csSup_mem hs⟩

中文:
定理 Set.Finite.csSup_lt_iff
  条件: (hs : s.Finite) (h : s.Nonempty)
  结论: sSup s < a ↔ 对任意 x in s, x < a
  证明: ⟨fun h _ hx => (le_csSup hs.bddAbove hx).trans_lt h, fun H => H _ h.csSup_mem hs⟩

Depends on / 依赖: bddAbove, csSup_mem, h.csSup_mem, hs.bddAbove, le_csSup, trans_lt
-/
theorem Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sSup s < a ↔ forall x in s, x < a :=
⟨fun h _ hx => (le_csSup hs.bddAbove hx).trans_lt h, fun H => H _ h.csSup_mem hs⟩

/--
theorem `Set.Finite.lt_csInf_iff` / 定理 `Set.Finite.lt_csInf_iff`

English:
theorem Set.Finite.lt_csInf_iff
  given: (hs : s.Finite) (h : s.Nonempty)
  statement: a < sInf s ↔ forall x in s, a < x
  proof: @Set.Finite.csSup_lt_iff αᵒᵈ _ _ _ hs h

中文:
定理 Set.Finite.lt_csInf_iff
  条件: (hs : s.Finite) (h : s.Nonempty)
  结论: a < sInf s ↔ 对任意 x in s, a < x
  证明: @Set.Finite.csSup_lt_iff αᵒᵈ _ _ _ hs h

Depends on / 依赖: Finite, Set.Finite.csSup_lt_iff, csSup_lt_iff
-/
theorem Set.Finite.lt_csInf_iff (hs : s.Finite) (h : s.Nonempty) : a < sInf s ↔ forall x in s, a < x :=
  @Set.Finite.csSup_lt_iff αᵒᵈ _ _ _ hs h

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {f : α -> β} (hmono : Monotone f)
include hmono

/--
theorem `Set.Finite.map_sSup_of_monotone` / 定理 `Set.Finite.map_sSup_of_monotone`

English:
theorem Set.Finite.map_sSup_of_monotone
  given: {s : Set α} (hne : s.Nonempty) (hfin : s.Finite)
  proof: le_antisymm (hmono.le_csSup_image (hne.csSup_mem hfin) hfin.bddAbove)
    (hmono.csSup_image_le_map_csSup hne hfin.bddAbove)

中文:
定理 Set.Finite.map_sSup_of_monotone
  条件: {s : Set α} (hne : s.Nonempty) (hfin : s.Finite)
  证明: le_antisymm (hmono.le_csSup_image (hne.csSup_mem hfin) hfin.bddAbove)
    (hmono.csSup_image_le_map_csSup hne hfin.bddAbove)

Depends on / 依赖: bddAbove, csSup_image_le_map_csSup, csSup_mem, hfin.bddAbove, hmono.csSup_image_le_map_csSup, hmono.le_csSup_image, hne.csSup_mem, le_antisymm, le_csSup_image
-/
theorem Set.Finite.map_sSup_of_monotone {s : Set α} (hne : s.Nonempty) (hfin : s.Finite) :
    f (sSup s) = sSup (f '' s) :=
  le_antisymm (hmono.le_csSup_image (hne.csSup_mem hfin) hfin.bddAbove)
    (hmono.csSup_image_le_map_csSup hne hfin.bddAbove)

/--
theorem `Set.Finite.map_sInf_of_monotone` / 定理 `Set.Finite.map_sInf_of_monotone`

English:
theorem Set.Finite.map_sInf_of_monotone
  given: {s : Set α} (hne : s.Nonempty) (hfin : s.Finite)
  proof: le_antisymm (hmono.map_csInf_le_csInf_image hne hfin.bddBelow)
    (hmono.csInf_image_le (hne.csInf_mem hfin) hfin.bddBelow)

中文:
定理 Set.Finite.map_sInf_of_monotone
  条件: {s : Set α} (hne : s.Nonempty) (hfin : s.Finite)
  证明: le_antisymm (hmono.map_csInf_le_csInf_image hne hfin.bddBelow)
    (hmono.csInf_image_le (hne.csInf_mem hfin) hfin.bddBelow)

Depends on / 依赖: bddBelow, csInf_image_le, csInf_mem, hfin.bddBelow, hmono.csInf_image_le, hmono.map_csInf_le_csInf_image, hne.csInf_mem, le_antisymm, map_csInf_le_csInf_image
-/
theorem Set.Finite.map_sInf_of_monotone {s : Set α} (hne : s.Nonempty) (hfin : s.Finite) :
    f (sInf s) = sInf (f '' s) :=
  le_antisymm (hmono.map_csInf_le_csInf_image hne hfin.bddBelow)
    (hmono.csInf_image_le (hne.csInf_mem hfin) hfin.bddBelow)

end ConditionallyCompleteLattice

variable (f : ι -> α)

/--
theorem `Finset.ciSup_eq_max'_image` / 定理 `Finset.ciSup_eq_max'_image`

English:
theorem Finset.ciSup_eq_max'_image
  statement: {s : Finset ι} (h : exists x in s, sSup ∅ <= f x)
  proof: by
  classical
  rw [iSup]; rw [← h'.csSup_eq_max']; rw [coe_image]
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  · simp only [ciSup_eq_ite, dite_eq_ite, Set.mem_range, Set.mem_image, mem_coe,
      exists_exists_and_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    split_i

中文:
定理 Finset.ciSup_eq_max'_image
  结论: {s : Finset ι} (h : 存在 x in s, sSup ∅ <= f x)
  证明: by
  classical
  rw [iSup]; rw [← h'.csSup_eq_max']; rw [coe_image]
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  · simp only [ciSup_eq_ite, dite_eq_ite, Set.mem_range, Set.mem_image, mem_coe,
      exists_exists_and_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    split_i

Depends on / 依赖: And.left, Set.mem_image, Set.mem_ran, Set.mem_range, ciSup_eq_ite, classical, coe_image, csSup_eq_csSup_of_forall_exists_le, csSup_eq_max, dite_eq_ite, exists_exists_and_eq_and, forall_apply_eq_imp_iff, forall_exists_index, h.imp, image_nonempty, image_nonempty.mpr, le_rfl, mem_coe, mem_image, mem_ran
-/
theorem Finset.ciSup_eq_max'_image {s : Finset ι} (h : exists x in s, sSup ∅ <= f x)
    (h' : (s.image f).Nonempty := by exact image_nonempty.mpr (h.imp fun _ => And.left)) :
    ⨆ i in s, f i = (s.image f).max' h' := by
  classical
  rw [iSup]; rw [← h'.csSup_eq_max']; rw [coe_image]
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  · simp only [ciSup_eq_ite, dite_eq_ite, Set.mem_range, Set.mem_image, mem_coe,
      exists_exists_and_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    split_ifs
    · exact ⟨_, by assumption, le_rfl⟩
    · assumption
  · simp only [Set.mem_image, mem_coe, ciSup_eq_ite, dite_eq_ite, Set.mem_range,
      exists_exists_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro i hi
    refine ⟨i, ?_⟩
    simp [hi]

/--
theorem `Finset.ciInf_eq_min'_image` / 定理 `Finset.ciInf_eq_min'_image`

English:
theorem Finset.ciInf_eq_min'_image
  statement: {s : Finset ι} (h : exists x in s, f x <= sInf ∅)
  proof: by
  rw [← OrderDual.toDual_inj]; rw [toDual_min']; rw [toDual_iInf]
  simp only [toDual_iInf]
  rw [ciSup_eq_max'_image _ h]
  simp only [image_image]
  congr

中文:
定理 Finset.ciInf_eq_min'_image
  结论: {s : Finset ι} (h : 存在 x in s, f x <= sInf ∅)
  证明: by
  rw [← OrderDual.toDual_inj]; rw [toDual_min']; rw [toDual_iInf]
  simp only [toDual_iInf]
  rw [ciSup_eq_max'_image _ h]
  simp only [image_image]
  congr

Depends on / 依赖: And.left, OrderDual, OrderDual.toDual_inj, _image, ciSup_eq_max, h.imp, image_image, image_nonempty, image_nonempty.mpr, s.image, toDual_iInf, toDual_inj, toDual_min
-/
theorem Finset.ciInf_eq_min'_image {s : Finset ι} (h : exists x in s, f x <= sInf ∅)
    (h' : (s.image f).Nonempty := by exact image_nonempty.mpr (h.imp fun _ => And.left)) :
    ⨅ i in s, f i = (s.image f).min' h' := by
  rw [← OrderDual.toDual_inj]; rw [toDual_min']; rw [toDual_iInf]
  simp only [toDual_iInf]
  rw [ciSup_eq_max'_image _ h]
  simp only [image_image]
  congr

/--
theorem `Finset.ciSup_mem_image` / 定理 `Finset.ciSup_mem_image`

English:
theorem Finset.ciSup_mem_image
  given: {s : Finset ι} (h : exists x in s, sSup ∅ <= f x)
  proof: by
  rw [ciSup_eq_max'_image _ h]
  exact max'_mem (image f s) _

中文:
定理 Finset.ciSup_mem_image
  条件: {s : Finset ι} (h : 存在 x in s, sSup ∅ <= f x)
  证明: by
  rw [ciSup_eq_max'_image _ h]
  exact max'_mem (image f s) _

Depends on / 依赖: _image, _mem, ciSup_eq_max
-/
theorem Finset.ciSup_mem_image {s : Finset ι} (h : exists x in s, sSup ∅ <= f x) :
    ⨆ i in s, f i in s.image f := by
  rw [ciSup_eq_max'_image _ h]
  exact max'_mem (image f s) _

/--
theorem `Finset.ciInf_mem_image` / 定理 `Finset.ciInf_mem_image`

English:
theorem Finset.ciInf_mem_image
  given: {s : Finset ι} (h : exists x in s, f x <= sInf ∅)
  proof: by
  rw [ciInf_eq_min'_image _ h]
  exact min'_mem (image f s) _

中文:
定理 Finset.ciInf_mem_image
  条件: {s : Finset ι} (h : 存在 x in s, f x <= sInf ∅)
  证明: by
  rw [ciInf_eq_min'_image _ h]
  exact min'_mem (image f s) _

Depends on / 依赖: _image, _mem, ciInf_eq_min
-/
theorem Finset.ciInf_mem_image {s : Finset ι} (h : exists x in s, f x <= sInf ∅) :
    ⨅ i in s, f i in s.image f := by
  rw [ciInf_eq_min'_image _ h]
  exact min'_mem (image f s) _

/--
theorem `Set.Finite.ciSup_mem_image` / 定理 `Set.Finite.ciSup_mem_image`

English:
theorem Set.Finite.ciSup_mem_image
  given: {s : Set ι} (hs : s.Finite) (h : exists x in s, sSup ∅ <= f x)
  proof: by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciSup_mem_image f h

中文:
定理 Set.Finite.ciSup_mem_image
  条件: {s : Set ι} (hs : s.Finite) (h : 存在 x in s, sSup ∅ <= f x)
  证明: by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciSup_mem_image f h

Depends on / 依赖: Finset, Finset.ciSup_mem_image, Finset.mem_coe, ciSup_mem_image, mem_coe
-/
theorem Set.Finite.ciSup_mem_image {s : Set ι} (hs : s.Finite) (h : exists x in s, sSup ∅ <= f x) :
    ⨆ i in s, f i in f '' s := by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciSup_mem_image f h

/--
theorem `Set.Finite.ciInf_mem_image` / 定理 `Set.Finite.ciInf_mem_image`

English:
theorem Set.Finite.ciInf_mem_image
  given: {s : Set ι} (hs : s.Finite) (h : exists x in s, f x <= sInf ∅)
  proof: by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciInf_mem_image f h

中文:
定理 Set.Finite.ciInf_mem_image
  条件: {s : Set ι} (hs : s.Finite) (h : 存在 x in s, f x <= sInf ∅)
  证明: by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciInf_mem_image f h

Depends on / 依赖: Finset, Finset.ciInf_mem_image, Finset.mem_coe, ciInf_mem_image, mem_coe
-/
theorem Set.Finite.ciInf_mem_image {s : Set ι} (hs : s.Finite) (h : exists x in s, f x <= sInf ∅) :
    ⨅ i in s, f i in f '' s := by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciInf_mem_image f h

/--
theorem `Set.Finite.ciSup_lt_iff` / 定理 `Set.Finite.ciSup_lt_iff`

English:
theorem Set.Finite.ciSup_lt_iff
  statement: {s : Set ι} {f : ι -> α} (hs : s.Finite)
  proof: by
  constructor
  · intro h x hx
    refine h.trans_le' (le_csSup ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sSup ∅))).subset ?_).bddAbove
      intro
      simp only [ciSup_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_e

中文:
定理 Set.Finite.ciSup_lt_iff
  结论: {s : Set ι} {f : ι -> α} (hs : s.Finite)
  证明: by
  constructor
  · intro h x hx
    refine h.trans_le' (le_csSup ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sSup ∅))).subset ?_).bddAbove
      intro
      simp only [ciSup_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_e

Depends on / 依赖: bddAbove, ciSup_eq_ite, ciSup_mem_image, classical, dite_eq_ite, finite_singleton, forall_exists_index, h.trans_le, hs.ciSup_mem_image, hs.image, le_csSup, mem_image, mem_insert_iff, mem_range, subset, trans_le, union_singleton
-/
theorem Set.Finite.ciSup_lt_iff {s : Set ι} {f : ι -> α} (hs : s.Finite)
    (h : exists x in s, sSup ∅ <= f x) :
    ⨆ i in s, f i < a ↔ forall x in s, f x < a := by
  constructor
  · intro h x hx
    refine h.trans_le' (le_csSup ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sSup ∅))).subset ?_).bddAbove
      intro
      simp only [ciSup_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_exists_index]
      grind
    · simp only [mem_range]
      refine ⟨x, ?_⟩
      simp [hx]
  · have := hs.ciSup_mem_image _ h
    grind

/--
theorem `Set.Finite.lt_ciInf_iff` / 定理 `Set.Finite.lt_ciInf_iff`

English:
theorem Set.Finite.lt_ciInf_iff
  statement: {s : Set ι} {f : ι -> α} (hs : s.Finite)
  proof: by
  constructor
  · intro h x hx
    refine h.trans_le (csInf_le ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sInf ∅))).subset ?_).bddBelow
      intro
      simp only [ciInf_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_ex

中文:
定理 Set.Finite.lt_ciInf_iff
  结论: {s : Set ι} {f : ι -> α} (hs : s.Finite)
  证明: by
  constructor
  · intro h x hx
    refine h.trans_le (csInf_le ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sInf ∅))).subset ?_).bddBelow
      intro
      simp only [ciInf_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_ex

Depends on / 依赖: bddBelow, ciInf_eq_ite, ciInf_mem_image, classical, csInf_le, dite_eq_ite, finite_singleton, forall_exists_index, h.trans_le, hs.ciInf_mem_image, hs.image, mem_image, mem_insert_iff, mem_range, subset, trans_le, union_singleton
-/
theorem Set.Finite.lt_ciInf_iff {s : Set ι} {f : ι -> α} (hs : s.Finite)
    (h : exists x in s, f x <= sInf ∅) :
    a < ⨅ i in s, f i ↔ forall x in s, a < f x := by
  constructor
  · intro h x hx
    refine h.trans_le (csInf_le ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sInf ∅))).subset ?_).bddBelow
      intro
      simp only [ciInf_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_exists_index]
      grind
    · simp only [mem_range]
      refine ⟨x, ?_⟩
      simp [hx]
  · intro H
    have := hs.ciInf_mem_image _ h
    simp only [mem_image] at this
    obtain ⟨_, hmem, hx⟩ := this
    rw [← hx]
    exact H _ hmem

section ListMultiset

/--
lemma `List.iSup_mem_map_of_exists_sSup_empty_le` / 引理 `List.iSup_mem_map_of_exists_sSup_empty_le`

English:
lemma List.iSup_mem_map_of_exists_sSup_empty_le
  statement: {l : List ι} (f : ι -> α)
  proof: by
  classical
  simpa using l.toFinset.ciSup_mem_image f (by simpa using h)

中文:
引理 List.iSup_mem_map_of_exists_sSup_empty_le
  结论: {l : List ι} (f : ι -> α)
  证明: by
  classical
  simpa using l.toFinset.ciSup_mem_image f (by simpa using h)

Depends on / 依赖: ciSup_mem_image, classical, l.toFinset.ciSup_mem_image, toFinset
-/
lemma List.iSup_mem_map_of_exists_sSup_empty_le {l : List ι} (f : ι -> α)
    (h : exists x in l, sSup ∅ <= f x) :
    ⨆ x in l, f x in l.map f := by
  classical
  simpa using l.toFinset.ciSup_mem_image f (by simpa using h)

/--
lemma `List.iInf_mem_map_of_exists_le_sInf_empty` / 引理 `List.iInf_mem_map_of_exists_le_sInf_empty`

English:
lemma List.iInf_mem_map_of_exists_le_sInf_empty
  statement: {l : List ι} (f : ι -> α)
  proof: by
  classical
  simpa using l.toFinset.ciInf_mem_image f (by simpa using h)

中文:
引理 List.iInf_mem_map_of_exists_le_sInf_empty
  结论: {l : List ι} (f : ι -> α)
  证明: by
  classical
  simpa using l.toFinset.ciInf_mem_image f (by simpa using h)

Depends on / 依赖: ciInf_mem_image, classical, l.toFinset.ciInf_mem_image, toFinset
-/
lemma List.iInf_mem_map_of_exists_le_sInf_empty {l : List ι} (f : ι -> α)
    (h : exists x in l, f x <= sInf ∅) :
    ⨅ x in l, f x in l.map f := by
  classical
  simpa using l.toFinset.ciInf_mem_image f (by simpa using h)

/--
lemma `Multiset.iSup_mem_map_of_exists_sSup_empty_le` / 引理 `Multiset.iSup_mem_map_of_exists_sSup_empty_le`

English:
lemma Multiset.iSup_mem_map_of_exists_sSup_empty_le
  statement: {s : Multiset ι} (f : ι -> α)
  proof: by
  classical
  simpa using s.toFinset.ciSup_mem_image f (by simpa using h)

中文:
引理 Multiset.iSup_mem_map_of_exists_sSup_empty_le
  结论: {s : Multiset ι} (f : ι -> α)
  证明: by
  classical
  simpa using s.toFinset.ciSup_mem_image f (by simpa using h)

Depends on / 依赖: ciSup_mem_image, classical, s.toFinset.ciSup_mem_image, toFinset
-/
lemma Multiset.iSup_mem_map_of_exists_sSup_empty_le {s : Multiset ι} (f : ι -> α)
    (h : exists x in s, sSup ∅ <= f x) :
    ⨆ x in s, f x in s.map f := by
  classical
  simpa using s.toFinset.ciSup_mem_image f (by simpa using h)

/--
lemma `Multiset.iInf_mem_map_of_exists_le_sInf_empty` / 引理 `Multiset.iInf_mem_map_of_exists_le_sInf_empty`

English:
lemma Multiset.iInf_mem_map_of_exists_le_sInf_empty
  statement: {s : Multiset ι} (f : ι -> α)
  proof: by
  classical
  simpa using s.toFinset.ciInf_mem_image f (by simpa using h)

中文:
引理 Multiset.iInf_mem_map_of_exists_le_sInf_empty
  结论: {s : Multiset ι} (f : ι -> α)
  证明: by
  classical
  simpa using s.toFinset.ciInf_mem_image f (by simpa using h)

Depends on / 依赖: ciInf_mem_image, classical, s.toFinset.ciInf_mem_image, toFinset
-/
lemma Multiset.iInf_mem_map_of_exists_le_sInf_empty {s : Multiset ι} (f : ι -> α)
    (h : exists x in s, f x <= sInf ∅) :
    ⨅ x in s, f x in s.map f := by
  classical
  simpa using s.toFinset.ciInf_mem_image f (by simpa using h)

/--
theorem `exists_eq_ciSup_of_finite` / 定理 `exists_eq_ciSup_of_finite`

English:
theorem exists_eq_ciSup_of_finite
  given: [Nonempty ι] [Finite ι] {f : ι -> α}
  statement: exists i, f i = ⨆ i, f i
  proof: Nonempty.csSup_mem (range_nonempty f) (finite_range f)

中文:
定理 exists_eq_ciSup_of_finite
  条件: [Nonempty ι] [Finite ι] {f : ι -> α}
  结论: 存在 i, f i = ⨆ i, f i
  证明: Nonempty.csSup_mem (range_nonempty f) (finite_range f)

Depends on / 依赖: Nonempty, Nonempty.csSup_mem, csSup_mem, finite_range, range_nonempty
-/
theorem exists_eq_ciSup_of_finite [Nonempty ι] [Finite ι] {f : ι -> α} : exists i, f i = ⨆ i, f i :=
  Nonempty.csSup_mem (range_nonempty f) (finite_range f)

/--
theorem `exists_eq_ciInf_of_finite` / 定理 `exists_eq_ciInf_of_finite`

English:
theorem exists_eq_ciInf_of_finite
  given: [Nonempty ι] [Finite ι] {f : ι -> α}
  statement: exists i, f i = ⨅ i, f i
  proof: Nonempty.csInf_mem (range_nonempty f) (finite_range f)

中文:
定理 exists_eq_ciInf_of_finite
  条件: [Nonempty ι] [Finite ι] {f : ι -> α}
  结论: 存在 i, f i = ⨅ i, f i
  证明: Nonempty.csInf_mem (range_nonempty f) (finite_range f)

Depends on / 依赖: Nonempty, Nonempty.csInf_mem, csInf_mem, finite_range, range_nonempty
-/
theorem exists_eq_ciInf_of_finite [Nonempty ι] [Finite ι] {f : ι -> α} : exists i, f i = ⨅ i, f i :=
  Nonempty.csInf_mem (range_nonempty f) (finite_range f)

end ListMultiset

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable {α : Type*} [CompleteLinearOrder α] {ι : Sort*}

/--
theorem `sSup_ne_of_notMem` / 定理 `sSup_ne_of_notMem`

English:
theorem sSup_ne_of_notMem
  given: {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊥) (hmem : a ∉ s)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp [eq_comm, hne]
  exact (hmem <| · ▸ hnonempty.csSup_mem hfin)

中文:
定理 sSup_ne_of_notMem
  条件: {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊥) (hmem : a ∉ s)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp [eq_comm, hne]
  exact (hmem <| · ▸ hnonempty.csSup_mem hfin)

Depends on / 依赖: csSup_mem, eq_comm, eq_empty_or_nonempty, hnonempty, hnonempty.csSup_mem, s.eq_empty_or_nonempty
-/
theorem sSup_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊥) (hmem : a ∉ s) :
    sSup s != a := by
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp [eq_comm, hne]
  exact (hmem <| · ▸ hnonempty.csSup_mem hfin)

/--
theorem `sInf_ne_of_notMem` / 定理 `sInf_ne_of_notMem`

English:
theorem sInf_ne_of_notMem
  given: {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊤) (hmem : a ∉ s)
  proof: sSup_ne_of_notMem (α := αᵒᵈ) hfin hne hmem

中文:
定理 sInf_ne_of_notMem
  条件: {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊤) (hmem : a ∉ s)
  证明: sSup_ne_of_notMem (α := αᵒᵈ) hfin hne hmem

Depends on / 依赖: sSup_ne_of_notMem
-/
theorem sInf_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊤) (hmem : a ∉ s) :
    sInf s != a :=
  sSup_ne_of_notMem (α := αᵒᵈ) hfin hne hmem

/--
theorem `sSup_ne_top` / 定理 `sSup_ne_top`

English:
theorem sSup_ne_top
  given: [Nontrivial α] {s : Set α} (hfin : s.Finite) (htop : ⊤ ∉ s)
  statement: sSup s != ⊤
  proof: sSup_ne_of_notMem hfin top_ne_bot htop

中文:
定理 sSup_ne_top
  条件: [Nontrivial α] {s : Set α} (hfin : s.Finite) (htop : ⊤ ∉ s)
  结论: sSup s != ⊤
  证明: sSup_ne_of_notMem hfin top_ne_bot htop

Depends on / 依赖: sSup_ne_of_notMem, top_ne_bot
-/
theorem sSup_ne_top [Nontrivial α] {s : Set α} (hfin : s.Finite) (htop : ⊤ ∉ s) : sSup s != ⊤ :=
  sSup_ne_of_notMem hfin top_ne_bot htop

/--
theorem `sInf_ne_bot` / 定理 `sInf_ne_bot`

English:
theorem sInf_ne_bot
  given: [Nontrivial α] {s : Set α} (hfin : s.Finite) (hbot : ⊥ ∉ s)
  statement: sInf s != ⊥
  proof: sSup_ne_top (α := αᵒᵈ) hfin hbot

中文:
定理 sInf_ne_bot
  条件: [Nontrivial α] {s : Set α} (hfin : s.Finite) (hbot : ⊥ ∉ s)
  结论: sInf s != ⊥
  证明: sSup_ne_top (α := αᵒᵈ) hfin hbot

Depends on / 依赖: sSup_ne_top
-/
theorem sInf_ne_bot [Nontrivial α] {s : Set α} (hfin : s.Finite) (hbot : ⊥ ∉ s) : sInf s != ⊥ :=
  sSup_ne_top (α := αᵒᵈ) hfin hbot

/--
theorem `iSup_ne_of_notMem` / 定理 `iSup_ne_of_notMem`

English:
theorem iSup_ne_of_notMem
  given: [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊥) (h : forall x, f x != a)
  proof: sSup_ne_of_notMem (Set.finite_range f) hne by grind

中文:
定理 iSup_ne_of_notMem
  条件: [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊥) (h : 对任意 x, f x != a)
  证明: sSup_ne_of_notMem (Set.finite_range f) hne by grind

Depends on / 依赖: Set.finite_range, finite_range, sSup_ne_of_notMem
-/
theorem iSup_ne_of_notMem [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊥) (h : forall x, f x != a) :
    iSup f != a :=
sSup_ne_of_notMem (Set.finite_range f) hne by grind

/--
theorem `iInf_ne_of_notMem` / 定理 `iInf_ne_of_notMem`

English:
theorem iInf_ne_of_notMem
  given: [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊤) (h : forall x, f x != a)
  proof: iSup_ne_of_notMem (α := αᵒᵈ) hne h

中文:
定理 iInf_ne_of_notMem
  条件: [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊤) (h : 对任意 x, f x != a)
  证明: iSup_ne_of_notMem (α := αᵒᵈ) hne h

Depends on / 依赖: iSup_ne_of_notMem
-/
theorem iInf_ne_of_notMem [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊤) (h : forall x, f x != a) :
    iInf f != a :=
  iSup_ne_of_notMem (α := αᵒᵈ) hne h

/--
theorem `iSup_ne_top` / 定理 `iSup_ne_top`

English:
theorem iSup_ne_top
  given: [Finite ι] [Nontrivial α] {f : ι -> α} (h : forall x, f x != ⊤)
  statement: iSup f != ⊤
  proof: iSup_ne_of_notMem top_ne_bot h

中文:
定理 iSup_ne_top
  条件: [Finite ι] [Nontrivial α] {f : ι -> α} (h : 对任意 x, f x != ⊤)
  结论: iSup f != ⊤
  证明: iSup_ne_of_notMem top_ne_bot h

Depends on / 依赖: iSup_ne_of_notMem, top_ne_bot
-/
theorem iSup_ne_top [Finite ι] [Nontrivial α] {f : ι -> α} (h : forall x, f x != ⊤) : iSup f != ⊤ :=
  iSup_ne_of_notMem top_ne_bot h

/--
theorem `iInf_ne_bot` / 定理 `iInf_ne_bot`

English:
theorem iInf_ne_bot
  given: [Finite ι] [Nontrivial α] {f : ι -> α} (h : forall x, f x != ⊥)
  statement: iInf f != ⊥
  proof: iSup_ne_top (α := αᵒᵈ) h

中文:
定理 iInf_ne_bot
  条件: [Finite ι] [Nontrivial α] {f : ι -> α} (h : 对任意 x, f x != ⊥)
  结论: iInf f != ⊥
  证明: iSup_ne_top (α := αᵒᵈ) h

Depends on / 依赖: iSup_ne_top
-/
theorem iInf_ne_bot [Finite ι] [Nontrivial α] {f : ι -> α} (h : forall x, f x != ⊥) : iInf f != ⊥ :=
  iSup_ne_top (α := αᵒᵈ) h

end CompleteLinearOrder

/-!
### Relation between `sSup` / `sInf` and `Finset.sup'` / `Finset.inf'`

Like the `Sup` of a `ConditionallyCompleteLattice`, `Finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/

namespace Finset

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α]

/--
theorem `sup'_eq_csSup_image` / 定理 `sup'_eq_csSup_image`

English:
theorem sup'_eq_csSup_image
  given: (s : Finset ι) (H : s.Nonempty) (f : ι -> α)
  proof: eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (H.to_set.image f)]

中文:
定理 sup'_eq_csSup_image
  条件: (s : Finset ι) (H : s.Nonempty) (f : ι -> α)
  证明: eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (H.to_set.image f)]
-/
theorem sup'_eq_csSup_image (s : Finset ι) (H : s.Nonempty) (f : ι -> α) :
    s.sup' H f = sSup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (H.to_set.image f)]

/--
theorem `inf'_eq_csInf_image` / 定理 `inf'_eq_csInf_image`

English:
theorem inf'_eq_csInf_image
  given: (s : Finset ι) (H : s.Nonempty) (f : ι -> α)
  proof: sup'_eq_csSup_image (α := αᵒᵈ) _ H _

中文:
定理 inf'_eq_csInf_image
  条件: (s : Finset ι) (H : s.Nonempty) (f : ι -> α)
  证明: sup'_eq_csSup_image (α := αᵒᵈ) _ H _
-/
theorem inf'_eq_csInf_image (s : Finset ι) (H : s.Nonempty) (f : ι -> α) :
    s.inf' H f = sInf (f '' s) :=
  sup'_eq_csSup_image (α := αᵒᵈ) _ H _

/--
theorem `sup'_id_eq_csSup` / 定理 `sup'_id_eq_csSup`

English:
theorem sup'_id_eq_csSup
  given: (s : Finset α) (hs)
  statement: s.sup' hs id = sSup s
  proof: by
  rw [sup'_eq_csSup_image s hs]; rw [Set.image_id]

中文:
定理 sup'_id_eq_csSup
  条件: (s : Finset α) (hs)
  结论: s.sup' hs id = sSup s
  证明: by
  rw [sup'_eq_csSup_image s hs]; rw [Set.image_id]
-/
theorem sup'_id_eq_csSup (s : Finset α) (hs) : s.sup' hs id = sSup s := by
  rw [sup'_eq_csSup_image s hs]; rw [Set.image_id]

/--
theorem `inf'_id_eq_csInf` / 定理 `inf'_id_eq_csInf`

English:
theorem inf'_id_eq_csInf
  given: (s : Finset α) (hs)
  statement: s.inf' hs id = sInf s
  proof: sup'_id_eq_csSup (α := αᵒᵈ) _ hs

中文:
定理 inf'_id_eq_csInf
  条件: (s : Finset α) (hs)
  结论: s.inf' hs id = sInf s
  证明: sup'_id_eq_csSup (α := αᵒᵈ) _ hs
-/
theorem inf'_id_eq_csInf (s : Finset α) (hs) : s.inf' hs id = sInf s :=
  sup'_id_eq_csSup (α := αᵒᵈ) _ hs

variable [Fintype ι] [Nonempty ι]

/--
lemma `sup'_univ_eq_ciSup` / 引理 `sup'_univ_eq_ciSup`

English:
lemma sup'_univ_eq_ciSup
  given: (f : ι -> α)
  statement: univ.sup' univ_nonempty f = ⨆ i, f i
  proof: by
  simp [sup'_eq_csSup_image, iSup]

@[to_dual existing]

中文:
引理 sup'_univ_eq_ciSup
  条件: (f : ι -> α)
  结论: univ.sup' univ_nonempty f = ⨆ i, f i
  证明: by
  simp [sup'_eq_csSup_image, iSup]

@[to_dual existing]
-/
lemma sup'_univ_eq_ciSup (f : ι -> α) : univ.sup' univ_nonempty f = ⨆ i, f i := by
  simp [sup'_eq_csSup_image, iSup]

@[to_dual existing]
/--
lemma `inf'_univ_eq_ciInf` / 引理 `inf'_univ_eq_ciInf`

English:
lemma inf'_univ_eq_ciInf
  given: (f : ι -> α)
  statement: univ.inf' univ_nonempty f = ⨅ i, f i
  proof: by
  simp [inf'_eq_csInf_image, iInf]

中文:
引理 inf'_univ_eq_ciInf
  条件: (f : ι -> α)
  结论: univ.inf' univ_nonempty f = ⨅ i, f i
  证明: by
  simp [inf'_eq_csInf_image, iInf]
-/
lemma inf'_univ_eq_ciInf (f : ι -> α) : univ.inf' univ_nonempty f = ⨅ i, f i := by
  simp [inf'_eq_csInf_image, iInf]

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α]

/--
lemma `sup_univ_eq_ciSup` / 引理 `sup_univ_eq_ciSup`

English:
lemma sup_univ_eq_ciSup
  given: [Fintype ι] (f : ι -> α)
  statement: univ.sup f = ⨆ i, f i
  proof: le_antisymm
    (Finset.sup_le fun _ _ => le_ciSup (finite_range _).bddAbove _)
    (ciSup_le' fun _ => Finset.le_sup (mem_univ _))

中文:
引理 sup_univ_eq_ciSup
  条件: [Fintype ι] (f : ι -> α)
  结论: univ.sup f = ⨆ i, f i
  证明: le_antisymm
    (Finset.sup_le fun _ _ => le_ciSup (finite_range _).bddAbove _)
    (ciSup_le' fun _ => Finset.le_sup (mem_univ _))

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_le, bddAbove, ciSup_le, finite_range, le_antisymm, le_ciSup, le_sup, mem_univ, sup_le
-/
lemma sup_univ_eq_ciSup [Fintype ι] (f : ι -> α) : univ.sup f = ⨆ i, f i :=
  le_antisymm
    (Finset.sup_le fun _ _ => le_ciSup (finite_range _).bddAbove _)
    (ciSup_le' fun _ => Finset.le_sup (mem_univ _))

/--
theorem `ciSup_union` / 定理 `ciSup_union`

English:
theorem ciSup_union
  given: [DecidableEq ι] {f : ι -> α} {s t : Finset ι}
  proof: by
suffices forall st : Finset ι, BddAbove .range fun x => ⨆ (_ : x in st), f x by
    simp [ciSup_or', ciSup_sup_eq, this]
  refine fun st => ⟨st.sup f, fun a ⟨i, ha⟩ => ha ▸ ?_⟩
  by_cases h : i in st <;>
    simp [h, le_sup]

中文:
定理 ciSup_union
  条件: [DecidableEq ι] {f : ι -> α} {s t : Finset ι}
  证明: by
suffices forall st : Finset ι, BddAbove .range fun x => ⨆ (_ : x in st), f x by
    simp [ciSup_or', ciSup_sup_eq, this]
  refine fun st => ⟨st.sup f, fun a ⟨i, ha⟩ => ha ▸ ?_⟩
  by_cases h : i in st <;>
    simp [h, le_sup]

Depends on / 依赖: BddAbove, Finset, ciSup_or, ciSup_sup_eq, le_sup, st.sup
-/
theorem ciSup_union [DecidableEq ι] {f : ι -> α} {s t : Finset ι} :
    (⨆ x in s union t, f x) = (⨆ x in s, f x) ⊔ (⨆ x in t, f x) := by
suffices forall st : Finset ι, BddAbove .range fun x => ⨆ (_ : x in st), f x by
    simp [ciSup_or', ciSup_sup_eq, this]
  refine fun st => ⟨st.sup f, fun a ⟨i, ha⟩ => ha ▸ ?_⟩
  by_cases h : i in st <;>
    simp [h, le_sup]

end ConditionallyCompleteLinearOrderBot

end Finset

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] (f : ι -> α)

/--
theorem `Finset.Nonempty.ciSup_eq_max'_image` / 定理 `Finset.Nonempty.ciSup_eq_max'_image`

English:
theorem Finset.Nonempty.ciSup_eq_max'_image
  statement: {s : Finset ι} (h : s.Nonempty)
  proof: s.ciSup_eq_max'_image _ (h.imp (by simp)) _

中文:
定理 Finset.Nonempty.ciSup_eq_max'_image
  结论: {s : Finset ι} (h : s.Nonempty)
  证明: s.ciSup_eq_max'_image _ (h.imp (by simp)) _

Depends on / 依赖: h.image
-/
theorem Finset.Nonempty.ciSup_eq_max'_image {s : Finset ι} (h : s.Nonempty)
    (h' : (s.image f).Nonempty := h.image f) :
    ⨆ i in s, f i = (s.image f).max' h' :=
  s.ciSup_eq_max'_image _ (h.imp (by simp)) _

/--
theorem `Finset.Nonempty.ciSup_mem_image` / 定理 `Finset.Nonempty.ciSup_mem_image`

English:
theorem Finset.Nonempty.ciSup_mem_image
  given: {s : Finset ι} (h : s.Nonempty)
  proof: s.ciSup_mem_image _ (h.imp (by simp))

中文:
定理 Finset.Nonempty.ciSup_mem_image
  条件: {s : Finset ι} (h : s.Nonempty)
  证明: s.ciSup_mem_image _ (h.imp (by simp))

Depends on / 依赖: ciSup_mem_image, h.imp, s.ciSup_mem_image
-/
theorem Finset.Nonempty.ciSup_mem_image {s : Finset ι} (h : s.Nonempty) :
    ⨆ i in s, f i in s.image f :=
  s.ciSup_mem_image _ (h.imp (by simp))

/--
theorem `Set.Nonempty.ciSup_mem_image` / 定理 `Set.Nonempty.ciSup_mem_image`

English:
theorem Set.Nonempty.ciSup_mem_image
  given: {s : Set ι} (h : s.Nonempty) (hs : s.Finite)
  proof: hs.ciSup_mem_image _ (h.imp (by simp))

中文:
定理 Set.Nonempty.ciSup_mem_image
  条件: {s : Set ι} (h : s.Nonempty) (hs : s.Finite)
  证明: hs.ciSup_mem_image _ (h.imp (by simp))

Depends on / 依赖: ciSup_mem_image, h.imp, hs.ciSup_mem_image
-/
theorem Set.Nonempty.ciSup_mem_image {s : Set ι} (h : s.Nonempty) (hs : s.Finite) :
    ⨆ i in s, f i in f '' s :=
  hs.ciSup_mem_image _ (h.imp (by simp))

/--
theorem `Set.Nonempty.ciSup_lt_iff` / 定理 `Set.Nonempty.ciSup_lt_iff`

English:
theorem Set.Nonempty.ciSup_lt_iff
  given: {s : Set ι} {a : α} {f : ι -> α} (h : s.Nonempty) (hs : s.Finite)
  proof: hs.ciSup_lt_iff (h.imp (by simp))

中文:
定理 Set.Nonempty.ciSup_lt_iff
  条件: {s : Set ι} {a : α} {f : ι -> α} (h : s.Nonempty) (hs : s.Finite)
  证明: hs.ciSup_lt_iff (h.imp (by simp))

Depends on / 依赖: ciSup_lt_iff, h.imp, hs.ciSup_lt_iff
-/
theorem Set.Nonempty.ciSup_lt_iff {s : Set ι} {a : α} {f : ι -> α} (h : s.Nonempty) (hs : s.Finite) :
    ⨆ i in s, f i < a ↔ forall x in s, f x < a :=
  hs.ciSup_lt_iff (h.imp (by simp))

section ListMultiset

/--
lemma `List.iSup_mem_map_of_ne_nil` / 引理 `List.iSup_mem_map_of_ne_nil`

English:
lemma List.iSup_mem_map_of_ne_nil
  given: {l : List ι} (f : ι -> α) (h : l != [])
  proof: l.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_nil _ h)

中文:
引理 List.iSup_mem_map_of_ne_nil
  条件: {l : List ι} (f : ι -> α) (h : l != [])
  证明: l.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_nil _ h)

Depends on / 依赖: exists_mem_of_ne_nil, iSup_mem_map_of_exists_sSup_empty_le, l.iSup_mem_map_of_exists_sSup_empty_le
-/
lemma List.iSup_mem_map_of_ne_nil {l : List ι} (f : ι -> α) (h : l != []) :
    ⨆ x in l, f x in l.map f :=
  l.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_nil _ h)

/--
lemma `Multiset.iSup_mem_map_of_ne_zero` / 引理 `Multiset.iSup_mem_map_of_ne_zero`

English:
lemma Multiset.iSup_mem_map_of_ne_zero
  given: {s : Multiset ι} (f : ι -> α) (h : s != 0)
  proof: s.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_zero h)

中文:
引理 Multiset.iSup_mem_map_of_ne_zero
  条件: {s : Multiset ι} (f : ι -> α) (h : s != 0)
  证明: s.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_zero h)

Depends on / 依赖: exists_mem_of_ne_zero, iSup_mem_map_of_exists_sSup_empty_le, s.iSup_mem_map_of_exists_sSup_empty_le
-/
lemma Multiset.iSup_mem_map_of_ne_zero {s : Multiset ι} (f : ι -> α) (h : s != 0) :
    ⨆ x in s, f x in s.map f :=
  s.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_zero h)

end ListMultiset

end ConditionallyCompleteLinearOrderBot
