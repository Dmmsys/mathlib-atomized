/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Pairwise.List

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about the interaction of `Set.PairwiseDisjoint` and `Finset`,
as well as the interaction of `List.Pairwise Disjoint` and the condition of
`Disjoint` on `List.toFinset`, in `Set` form.
-/

public section


open Finset

variable {α ι ι' : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] {r
  body: decidable_of_iff' (forall a in s, forall b in s, a != b -> r a b) Iff.rfl

中文:
实例 [DecidableEq
  签名: α] {r
  定义体: decidable_of_iff' (forall a in s, forall b in s, a != b -> r a b) Iff.rfl

Depends on / 依赖: Iff.rfl, decidable_of_iff
-/
instance [DecidableEq α] {r : α -> α -> Prop} [DecidableRel r] {s : Finset α} :
    Decidable ((s : Set α).Pairwise r) :=
  decidable_of_iff' (forall a in s, forall b in s, a != b -> r a b) Iff.rfl

/--
theorem `Finset.pairwiseDisjoint_range_singleton` / 定理 `Finset.pairwiseDisjoint_range_singleton`

English:
theorem Finset.pairwiseDisjoint_range_singleton
  proof: by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)

中文:
定理 Finset.pairwiseDisjoint_range_singleton
  证明: by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)

Depends on / 依赖: disjoint_singleton, ne_of_apply_ne
-/
theorem Finset.pairwiseDisjoint_range_singleton :
    (Set.range (singleton : α -> Finset α)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)

namespace Set

/--
theorem `PairwiseDisjoint.elim_finset` / 定理 `PairwiseDisjoint.elim_finset`

English:
theorem PairwiseDisjoint.elim_finset
  statement: {s : Set ι} {f : ι -> Finset α} (hs : s.PairwiseDisjoint f)
  proof: hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

中文:
定理 PairwiseDisjoint.elim_finset
  结论: {s : Set ι} {f : ι -> Finset α} (hs : s.PairwiseDisjoint f)
  证明: hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

Depends on / 依赖: Finset, Finset.not_disjoint_iff, hs.elim, not_disjoint_iff
-/
theorem PairwiseDisjoint.elim_finset {s : Set ι} {f : ι -> Finset α} (hs : s.PairwiseDisjoint f)
    {i j : ι} (hi : i in s) (hj : j in s) (a : α) (hai : a in f i) (haj : a in f j) : i = j :=
  hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

section SemilatticeInf

variable [SemilatticeInf α] [OrderBot α] {s : Finset ι} {f : ι -> α}

/--
theorem `PairwiseDisjoint.image_finset_of_le` / 定理 `PairwiseDisjoint.image_finset_of_le`

English:
theorem PairwiseDisjoint.image_finset_of_le
  statement: [DecidableEq ι] {s : Finset ι} {f : ι -> α}
  proof: by
  rw [coe_image]
  exact hs.image_of_le hf

中文:
定理 PairwiseDisjoint.image_finset_of_le
  结论: [DecidableEq ι] {s : Finset ι} {f : ι -> α}
  证明: by
  rw [coe_image]
  exact hs.image_of_le hf

Depends on / 依赖: coe_image, hs.image_of_le, image_of_le
-/
theorem PairwiseDisjoint.image_finset_of_le [DecidableEq ι] {s : Finset ι} {f : ι -> α}
    (hs : (s : Set ι).PairwiseDisjoint f) {g : ι -> ι} (hf : forall a, f (g a) <= f a) :
    (s.image g : Set ι).PairwiseDisjoint f := by
  rw [coe_image]
  exact hs.image_of_le hf

/--
theorem `PairwiseDisjoint.attach` / 定理 `PairwiseDisjoint.attach`

English:
theorem PairwiseDisjoint.attach
  given: (hs : (s : Set ι).PairwiseDisjoint f)
  proof: fun i _ j _ hij =>
hs i.2 j.2 mt Subtype.ext hij

中文:
定理 PairwiseDisjoint.attach
  条件: (hs : (s : Set ι).PairwiseDisjoint f)
  证明: fun i _ j _ hij =>
hs i.2 j.2 mt Subtype.ext hij
-/
theorem PairwiseDisjoint.attach (hs : (s : Set ι).PairwiseDisjoint f) :
    (s.attach : Set { x // x in s }).PairwiseDisjoint (f ∘ Subtype.val) := fun i _ j _ hij =>
hs i.2 j.2 mt Subtype.ext hij

end SemilatticeInf

variable [Lattice α] [OrderBot α]

/--
theorem `PairwiseDisjoint.biUnion_finset` / 定理 `PairwiseDisjoint.biUnion_finset`

English:
theorem PairwiseDisjoint.biUnion_finset
  statement: {s : Set ι'} {g : ι' -> Finset ι} {f : ι -> α}
  proof: by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (by rwa [hcd] at ha) hb hab
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)

中文:
定理 PairwiseDisjoint.biUnion_finset
  结论: {s : Set ι'} {g : ι' -> Finset ι} {f : ι -> α}
  证明: by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (by rwa [hcd] at ha) hb hab
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)

Depends on / 依赖: Finset, Finset.le_sup, Set.mem_iUnion, eq_or_ne, le_sup, mem_iUnion, ne_of_apply_ne, simp_rw
-/
theorem PairwiseDisjoint.biUnion_finset {s : Set ι'} {g : ι' -> Finset ι} {f : ι -> α}
    (hs : s.PairwiseDisjoint fun i' : ι' => (g i').sup f)
    (hg : forall i in s, (g i : Set ι).PairwiseDisjoint f) : (⋃ i in s, ↑(g i)).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (by rwa [hcd] at ha) hb hab
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)

end Set

namespace List

variable {β : Type*} [DecidableEq α] {r : α -> α -> Prop} {l : List α}

/--
theorem `pairwise_of_coe_toFinset_pairwise` / 定理 `pairwise_of_coe_toFinset_pairwise`

English:
theorem pairwise_of_coe_toFinset_pairwise
  given: (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup)
  proof: by
  rw [coe_toFinset] at hl
  exact hn.pairwise_of_set_pairwise hl

中文:
定理 pairwise_of_coe_toFinset_pairwise
  条件: (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup)
  证明: by
  rw [coe_toFinset] at hl
  exact hn.pairwise_of_set_pairwise hl

Depends on / 依赖: coe_toFinset, hn.pairwise_of_set_pairwise, pairwise_of_set_pairwise
-/
theorem pairwise_of_coe_toFinset_pairwise (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup) :
    l.Pairwise r := by
  rw [coe_toFinset] at hl
  exact hn.pairwise_of_set_pairwise hl

/--
theorem `pairwise_iff_coe_toFinset_pairwise` / 定理 `pairwise_iff_coe_toFinset_pairwise`

English:
theorem pairwise_iff_coe_toFinset_pairwise
  given: [Std.Symm r] (hn : l.Nodup)
  proof: by
  rw [coe_toFinset]; rw [hn.pairwise_coe]

中文:
定理 pairwise_iff_coe_toFinset_pairwise
  条件: [Std.Symm r] (hn : l.Nodup)
  证明: by
  rw [coe_toFinset]; rw [hn.pairwise_coe]

Depends on / 依赖: coe_toFinset, hn.pairwise_coe, pairwise_coe
-/
theorem pairwise_iff_coe_toFinset_pairwise [Std.Symm r] (hn : l.Nodup) :
    (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r := by
  rw [coe_toFinset]; rw [hn.pairwise_coe]

open scoped Function -- required for scoped `on` notation

/--
theorem `pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint` / 定理 `pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint`

English:
theorem pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint
  statement: {α ι} [PartialOrder α] [OrderBot α]
  proof: pairwise_of_coe_toFinset_pairwise hl hn

中文:
定理 pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint
  结论: {α ι} [PartialOrder α] [OrderBot α]
  证明: pairwise_of_coe_toFinset_pairwise hl hn

Depends on / 依赖: MulAction, MulAction.compHom, compHom, fast_instance, pairwise_of_coe_toFinset_pairwise, toMonoidHom, toRealHom, toRealHom.toMonoidHom
-/
theorem pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint {α ι} [PartialOrder α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι -> α} (hl : (l.toFinset : Set ι).PairwiseDisjoint f)
    (hn : l.Nodup) : l.Pairwise (_root_.Disjoint on f) :=
  pairwise_of_coe_toFinset_pairwise hl hn

/--
theorem `pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint` / 定理 `pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint`

English:
theorem pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
  statement: {α ι} [PartialOrder α] [OrderBot α]
  proof: pairwise_iff_coe_toFinset_pairwise hn

中文:
定理 pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
  结论: {α ι} [PartialOrder α] [OrderBot α]
  证明: pairwise_iff_coe_toFinset_pairwise hn

Depends on / 依赖: pairwise_iff_coe_toFinset_pairwise
-/
theorem pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint {α ι} [PartialOrder α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι -> α} (hn : l.Nodup) :
    (l.toFinset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (_root_.Disjoint on f) :=
  pairwise_iff_coe_toFinset_pairwise hn

end List
