/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Results about compactness properties for intervals in complete lattices
-/

public section

variable {ι α : Type*} [CompleteLattice α]

namespace Set.Iic

/--
theorem `isCompactElement` / 定理 `isCompactElement`

English:
theorem isCompactElement
  given: {a : α} {b : Iic a} (h : IsCompactElement (b : α))
  proof: by
  simp only [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup,
    Finset.sup_eq_iSup] at h ⊢
  intro ι s hb
replace hb : (b : α) <= iSup ((↑) ∘ s) := le_trans hb (coe_iSup s) ▸ le_refl _
  obtain ⟨t, ht⟩ := h ι ((↑) ∘ s) hb
  exact ⟨t, (by simpa using ht : (b : α) <= _)⟩

中文:
定理 isCompactElement
  条件: {a : α} {b : Iic a} (h : IsCompactElement (b : α))
  证明: by
  simp only [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup,
    Finset.sup_eq_iSup] at h ⊢
  intro ι s hb
replace hb : (b : α) <= iSup ((↑) ∘ s) := le_trans hb (coe_iSup s) ▸ le_refl _
  obtain ⟨t, ht⟩ := h ι ((↑) ∘ s) hb
  exact ⟨t, (by simpa using ht : (b : α) <= _)⟩

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup, Finset, Finset.sup_eq_iSup, coe_iSup, isCompactElement_iff_exists_le_iSup_of_le_iSup, le_refl, le_trans, replace, sup_eq_iSup
-/
theorem isCompactElement {a : α} {b : Iic a} (h : IsCompactElement (b : α)) :
    IsCompactElement b := by
  simp only [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup,
    Finset.sup_eq_iSup] at h ⊢
  intro ι s hb
replace hb : (b : α) <= iSup ((↑) ∘ s) := le_trans hb (coe_iSup s) ▸ le_refl _
  obtain ⟨t, ht⟩ := h ι ((↑) ∘ s) hb
  exact ⟨t, (by simpa using ht : (b : α) <= _)⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instIsCompactlyGenerated` / 实例 `instIsCompactlyGenerated`

English:
instance instIsCompactlyGenerated
  signature: [IsCompactlyGenerated α] {a : α}
  body: by
  refine ⟨fun ⟨x, (hx : x <= a)⟩ => ?_⟩
  obtain ⟨s, hs, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq x
  rw [sSup_le_iff] at hx
  let f : s -> Iic a := fun y => ⟨y, hx _ y.property⟩
  refine ⟨range f, ?_, ?_⟩
  · rintro - ⟨⟨y, hy⟩, hy', rfl⟩
    exact isCompactElement (hs _ hy)
  · rw [Subtype.ex

中文:
实例 instIsCompactlyGenerated
  签名: [IsCompactlyGenerated α] {a : α}
  定义体: by
  refine ⟨fun ⟨x, (hx : x <= a)⟩ => ?_⟩
  obtain ⟨s, hs, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq x
  rw [sSup_le_iff] at hx
  let f : s -> Iic a := fun y => ⟨y, hx _ y.property⟩
  refine ⟨range f, ?_, ?_⟩
  · rintro - ⟨⟨y, hy⟩, hy', rfl⟩
    exact isCompactElement (hs _ hy)
  · rw [Subtype.ex

Depends on / 依赖: IsCompactlyGenerated, IsCompactlyGenerated.exists_sSup_eq, Subtype, Subtype.ext_iff, exists_sSup_eq, ext_iff, isCompactElement, property, sSup_le_iff, y.property
-/
instance instIsCompactlyGenerated [IsCompactlyGenerated α] {a : α} :
    IsCompactlyGenerated (Iic a) := by
  refine ⟨fun ⟨x, (hx : x <= a)⟩ => ?_⟩
  obtain ⟨s, hs, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq x
  rw [sSup_le_iff] at hx
  let f : s -> Iic a := fun y => ⟨y, hx _ y.property⟩
  refine ⟨range f, ?_, ?_⟩
  · rintro - ⟨⟨y, hy⟩, hy', rfl⟩
    exact isCompactElement (hs _ hy)
  · rw [Subtype.ext_iff]
    change sSup (((↑) : Iic a -> α) '' (range f)) = sSup s
    congr
    ext b
    simpa [f] using hx b

end Set.Iic

open Set (Iic)

/--
theorem `complementedLattice_of_complementedLattice_Iic` / 定理 `complementedLattice_of_complementedLattice_Iic`

English:
theorem complementedLattice_of_complementedLattice_Iic
  proof: by
  apply complementedLattice_of_sSup_atoms_eq_top
  have : forall i in s, exists t : Set α, f i = sSup t ∧ forall a in t, IsAtom a := fun i hi => by
    replace h := complementedLattice_iff_isAtomistic.mp (h i hi)
    obtain ⟨u, hu, hu'⟩ := eq_sSup_atoms (⊤ : Iic (f i))
    refine ⟨(↑) '' u, ?_, ?

中文:
定理 complementedLattice_of_complementedLattice_Iic
  证明: by
  apply complementedLattice_of_sSup_atoms_eq_top
  have : forall i in s, exists t : Set α, f i = sSup t ∧ forall a in t, IsAtom a := fun i hi => by
    replace h := complementedLattice_iff_isAtomistic.mp (h i hi)
    obtain ⟨u, hu, hu'⟩ := eq_sSup_atoms (⊤ : Iic (f i))
    refine ⟨(↑) '' u, ?_, ?

Depends on / 依赖: Iic.coe_sSup, IsAtom, IsAtom.of_isAtom_coe_Iic, Subtype, Subtype.ext_iff.mp, coe_sSup, complementedLattice_iff_isAtomistic, complementedLattice_iff_isAtomistic.mp, complementedLattice_of_sSup_atoms_eq_top, eq_sSup_atoms, ext_iff, of_isAtom_coe_Iic, replace, simp_rw
-/
theorem complementedLattice_of_complementedLattice_Iic
    [IsModularLattice α] [IsCompactlyGenerated α]
    {s : Set ι} {f : ι -> α}
    (h : forall i in s, ComplementedLattice <| Iic (f i))
    (h' : ⨆ i in s, f i = ⊤) :
    ComplementedLattice α := by
  apply complementedLattice_of_sSup_atoms_eq_top
  have : forall i in s, exists t : Set α, f i = sSup t ∧ forall a in t, IsAtom a := fun i hi => by
    replace h := complementedLattice_iff_isAtomistic.mp (h i hi)
    obtain ⟨u, hu, hu'⟩ := eq_sSup_atoms (⊤ : Iic (f i))
    refine ⟨(↑) '' u, ?_, ?_⟩
    · replace hu : f i = ↑(sSup u) := Subtype.ext_iff.mp hu
      simp_rw [hu, Iic.coe_sSup]
    · rintro b ⟨⟨a, ha'⟩, ha, rfl⟩
      exact IsAtom.of_isAtom_coe_Iic (hu' _ ha)
  choose t ht ht' using this
  let u : Set α := ⋃ i, ⋃ hi : i in s, t i hi
  have hu₁ : u subseteq {a | IsAtom a} := by
    rintro a ⟨-, ⟨i, rfl⟩, ⟨-, ⟨hi, rfl⟩, ha : a in t i hi⟩⟩
    exact ht' i hi a ha
  have hu₂ : sSup u = ⨆ i in s, f i := by simp_rw [u, sSup_iUnion, biSup_congr' ht]
  rw [eq_top_iff]; rw [← h']; rw [← hu₂]
  exact sSup_le_sSup hu₁
