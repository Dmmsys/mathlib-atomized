/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Relations holding pairwise

In this file we prove many facts about `Pairwise` and the set lattice.
-/

@[expose] public section


open Function Set Order

variable {α ι ι' : Type*} {κ : Sort*} {r : α -> α -> Prop}
section Pairwise

variable {f : ι -> α} {s : Set α}

namespace Set

-- TODO: fix naming inconsistency with the iUnion₂ theorems below.
/--
theorem `pairwise_iUnion` / 定理 `pairwise_iUnion`

English:
theorem pairwise_iUnion
  given: {f : κ -> Set α} (hd : Directed (· subseteq ·) f)
  proof: by
  constructor
  · intro H n
    exact Pairwise.mono (subset_iUnion _ _) H
  · intro H i hi j hj hij
    rcases mem_iUnion.1 hi with ⟨m, hm⟩
    rcases mem_iUnion.1 hj with ⟨n, hn⟩
    rcases hd m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij

中文:
定理 pairwise_iUnion
  条件: {f : κ -> 集合 α} (hd : Directed (· subseteq ·) f)
  证明: by
  constructor
  · intro H n
    exact Pairwise.mono (subset_iUnion _ _) H
  · intro H i hi j hj hij
    rcases mem_iUnion.1 hi with ⟨m, hm⟩
    rcases mem_iUnion.1 hj with ⟨n, hn⟩
    rcases hd m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij

Depends on / 依赖: Pairwise, Pairwise.mono, mem_iUnion, subset_iUnion
-/
theorem pairwise_iUnion {f : κ -> Set α} (hd : Directed (· subseteq ·) f) :
    (⋃ n, f n).Pairwise r ↔ forall n, (f n).Pairwise r := by
  constructor
  · intro H n
    exact Pairwise.mono (subset_iUnion _ _) H
  · intro H i hi j hj hij
    rcases mem_iUnion.1 hi with ⟨m, hm⟩
    rcases mem_iUnion.1 hj with ⟨n, hn⟩
    rcases hd m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij

-- TODO: harmonize explicitness of `r`
/--
theorem `pairwise_iUnion₂` / 定理 `pairwise_iUnion₂`

English:
theorem pairwise_iUnion₂
  statement: {s : Set (Set α)} (hd : DirectedOn (· subseteq ·) s)
  proof: by
  simp only [Set.Pairwise, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro x S hS hx y T hT hy hne
  obtain ⟨U, hU, hSU, hTU⟩ := hd S hS T hT
  exact h U hU (hSU hx) (hTU hy) hne

中文:
定理 pairwise_iUnion₂
  结论: {s : 集合 (集合 α)} (hd : DirectedOn (· subseteq ·) s)
  证明: by
  simp only [Set.Pairwise, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro x S hS hx y T hT hy hne
  obtain ⟨U, hU, hSU, hTU⟩ := hd S hS T hT
  exact h U hU (hSU hx) (hTU hy) hne

Depends on / 依赖: Pairwise, Set.Pairwise, and_imp, exists_prop, forall_exists_index, mem_iUnion
-/
theorem pairwise_iUnion₂ {s : Set (Set α)} (hd : DirectedOn (· subseteq ·) s)
    (r : α -> α -> Prop) (h : forall a in s, a.Pairwise r) : (⋃ a in s, a).Pairwise r := by
  simp only [Set.Pairwise, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro x S hS hx y T hT hy hne
  obtain ⟨U, hU, hSU, hTU⟩ := hd S hS T hT
  exact h U hU (hSU hx) (hTU hy) hne

/--
theorem `pairwise_iUnion₂_iff` / 定理 `pairwise_iUnion₂_iff`

English:
theorem pairwise_iUnion₂_iff
  given: {s : Set (Set α)} (hd : DirectedOn (· subseteq ·) s)
  proof: ⟨fun h a ha => h.mono subset_iUnion₂_of_subset a ha (by rfl), pairwise_iUnion₂ hd _⟩

中文:
定理 pairwise_iUnion₂_iff
  条件: {s : 集合 (集合 α)} (hd : DirectedOn (· subseteq ·) s)
  证明: ⟨fun h a ha => h.mono subset_iUnion₂_of_subset a ha (by rfl), pairwise_iUnion₂ hd _⟩

Depends on / 依赖: h.mono
-/
theorem pairwise_iUnion₂_iff {s : Set (Set α)} (hd : DirectedOn (· subseteq ·) s) :
    (⋃ a in s, a).Pairwise r ↔ forall a in s, a.Pairwise r :=
⟨fun h a ha => h.mono subset_iUnion₂_of_subset a ha (by rfl), pairwise_iUnion₂ hd _⟩

/--
theorem `pairwise_sUnion` / 定理 `pairwise_sUnion`

English:
theorem pairwise_sUnion
  given: {r : α -> α -> Prop} {s : Set (Set α)} (hd : DirectedOn (· subseteq ·) s)
  proof: by
  rw [sUnion_eq_iUnion]; rw [pairwise_iUnion hd.directed_val]; rw [SetCoe.forall]

中文:
定理 pairwise_sUnion
  条件: {r : α -> α -> 命题} {s : 集合 (集合 α)} (hd : DirectedOn (· subseteq ·) s)
  证明: by
  rw [sUnion_eq_iUnion]; rw [pairwise_iUnion hd.directed_val]; rw [SetCoe.forall]

Depends on / 依赖: SetCoe, SetCoe.forall, directed_val, hd.directed_val, pairwise_iUnion, sUnion_eq_iUnion
-/
theorem pairwise_sUnion {r : α -> α -> Prop} {s : Set (Set α)} (hd : DirectedOn (· subseteq ·) s) :
    (⋃₀ s).Pairwise r ↔ forall a in s, Set.Pairwise a r := by
  rw [sUnion_eq_iUnion]; rw [pairwise_iUnion hd.directed_val]; rw [SetCoe.forall]

end Set

end Pairwise

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s : Set ι} {f : ι -> α}

/--
theorem `pairwiseDisjoint_iUnion` / 定理 `pairwiseDisjoint_iUnion`

English:
theorem pairwiseDisjoint_iUnion
  given: {g : ι' -> Set ι} (h : Directed (· subseteq ·) g)
  proof: pairwise_iUnion h

中文:
定理 pairwiseDisjoint_iUnion
  条件: {g : ι' -> 集合 ι} (h : Directed (· subseteq ·) g)
  证明: pairwise_iUnion h

Depends on / 依赖: pairwise_iUnion
-/
theorem pairwiseDisjoint_iUnion {g : ι' -> Set ι} (h : Directed (· subseteq ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ forall ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_iUnion h

/--
theorem `pairwiseDisjoint_sUnion` / 定理 `pairwiseDisjoint_sUnion`

English:
theorem pairwiseDisjoint_sUnion
  given: {s : Set (Set ι)} (h : DirectedOn (· subseteq ·) s)
  proof: pairwise_sUnion h

中文:
定理 pairwiseDisjoint_sUnion
  条件: {s : 集合 (集合 ι)} (h : DirectedOn (· subseteq ·) s)
  证明: pairwise_sUnion h

Depends on / 依赖: pairwise_sUnion
-/
theorem pairwiseDisjoint_sUnion {s : Set (Set ι)} (h : DirectedOn (· subseteq ·) s) :
    (⋃₀ s).PairwiseDisjoint f ↔ forall ⦃a⦄, a in s -> Set.PairwiseDisjoint a f :=
  pairwise_sUnion h

end PartialOrderBot

section CompleteLattice

variable [CompleteLattice α] {s : Set ι} {t : Set ι'}

/--
theorem `PairwiseDisjoint.biUnion` / 定理 `PairwiseDisjoint.biUnion`

English:
theorem PairwiseDisjoint.biUnion
  statement: {s : Set ι'} {g : ι' -> Set ι} {f : ι -> α}
  proof: by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd ▸ ha) hb hab
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono
      (le_iSup₂ (f := fun i _ => f i) a ha)
      (le_i

中文:
定理 PairwiseDisjoint.biUnion
  结论: {s : 集合 ι'} {g : ι' -> 集合 ι} {f : ι -> α}
  证明: by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd ▸ ha) hb hab
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono
      (le_iSup₂ (f := fun i _ => f i) a ha)
      (le_i

Depends on / 依赖: Set.mem_iUnion, eq_or_ne, mem_iUnion, ne_of_apply_ne, simp_rw
-/
theorem PairwiseDisjoint.biUnion {s : Set ι'} {g : ι' -> Set ι} {f : ι -> α}
    (hs : s.PairwiseDisjoint fun i' : ι' => ⨆ i in g i', f i)
    (hg : forall i in s, (g i).PairwiseDisjoint f) : (⋃ i in s, g i).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd ▸ ha) hb hab
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono
      (le_iSup₂ (f := fun i _ => f i) a ha)
      (le_iSup₂ (f := fun i _ => f i) b hb)

/--
theorem `PairwiseDisjoint.prod_left` / 定理 `PairwiseDisjoint.prod_left`

English:
theorem PairwiseDisjoint.prod_left
  statement: {f : ι × ι' -> α}
  proof: by
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h
  rw [mem_prod] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht hi.2 hj.2 <| (Prod.mk_right_injective _).ne_iff.1 h).mono ?_ ?_
    · convert! le_iSup₂ (α := α) i hi.1; rfl
    · convert! le_iSup₂ (α := α) i hj.1; rfl
  · refine (hs hi.1 hj.1 hij).mono 

中文:
定理 PairwiseDisjoint.prod_left
  结论: {f : ι × ι' -> α}
  证明: by
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h
  rw [mem_prod] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht hi.2 hj.2 <| (Prod.mk_right_injective _).ne_iff.1 h).mono ?_ ?_
    · convert! le_iSup₂ (α := α) i hi.1; rfl
    · convert! le_iSup₂ (α := α) i hj.1; rfl
  · refine (hs hi.1 hj.1 hij).mono 

Depends on / 依赖: Prod.mk_right_injective, convert, eq_or_ne, mem_prod, mk_right_injective, ne_iff
-/
theorem PairwiseDisjoint.prod_left {f : ι × ι' -> α}
    (hs : s.PairwiseDisjoint fun i => ⨆ i' in t, f (i, i'))
    (ht : t.PairwiseDisjoint fun i' => ⨆ i in s, f (i, i')) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f := by
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h
  rw [mem_prod] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht hi.2 hj.2 <| (Prod.mk_right_injective _).ne_iff.1 h).mono ?_ ?_
    · convert! le_iSup₂ (α := α) i hi.1; rfl
    · convert! le_iSup₂ (α := α) i hj.1; rfl
  · refine (hs hi.1 hj.1 hij).mono ?_ ?_
    · convert! le_iSup₂ (α := α) i' hi.2; rfl
    · convert! le_iSup₂ (α := α) j' hj.2; rfl

end CompleteLattice

section Frame

variable [Frame α]

/--
theorem `pairwiseDisjoint_prod_left` / 定理 `pairwiseDisjoint_prod_left`

English:
theorem pairwiseDisjoint_prod_left
  given: {s : Set ι} {t : Set ι'} {f : ι × ι' -> α}
  proof: by
  refine
      ⟨fun h => ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩, fun h => h.1.prod_left h.2⟩ <;>
    simp_rw [Function.onFun, iSup_disjoint_iff, disjoint_iSup_iff] <;>
    intro i' hi' j' hj'
  · exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne Prod.fst hij)
  · exact

中文:
定理 pairwiseDisjoint_prod_left
  条件: {s : 集合 ι} {t : 集合 ι'} {f : ι × ι' -> α}
  证明: by
  refine
      ⟨fun h => ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩, fun h => h.1.prod_left h.2⟩ <;>
    simp_rw [Function.onFun, iSup_disjoint_iff, disjoint_iSup_iff] <;>
    intro i' hi' j' hj'
  · exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne Prod.fst hij)
  · exact

Depends on / 依赖: Function, Function.onFun, Prod.fst, Prod.snd, disjoint_iSup_iff, iSup_disjoint_iff, mk_mem_prod, ne_of_apply_ne, prod_left, simp_rw
-/
theorem pairwiseDisjoint_prod_left {s : Set ι} {t : Set ι'} {f : ι × ι' -> α} :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f ↔
      (s.PairwiseDisjoint fun i => ⨆ i' in t, f (i, i')) ∧
        t.PairwiseDisjoint fun i' => ⨆ i in s, f (i, i') := by
  refine
      ⟨fun h => ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩, fun h => h.1.prod_left h.2⟩ <;>
    simp_rw [Function.onFun, iSup_disjoint_iff, disjoint_iSup_iff] <;>
    intro i' hi' j' hj'
  · exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne Prod.fst hij)
  · exact h (mk_mem_prod hi' hi) (mk_mem_prod hj' hj) (ne_of_apply_ne Prod.snd hij)

end Frame

/--
theorem `biUnion_sdiff_biUnion_eq` / 定理 `biUnion_sdiff_biUnion_eq`

English:
theorem biUnion_sdiff_biUnion_eq
  given: {s t : Set ι} {f : ι -> Set α} (h : (s union t).PairwiseDisjoint f)
  proof: by
  refine
    (biUnion_sdiff_biUnion_subset f s t).antisymm
      (iUnion₂_subset fun i hi a ha => (mem_sdiff _).2 ⟨mem_biUnion hi.1 ha, ?_⟩)
  rw [mem_iUnion₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩

@[deprecated (since := "

中文:
定理 biUnion_sdiff_biUnion_eq
  条件: {s t : 集合 ι} {f : ι -> 集合 α} (h : (s union t).PairwiseDisjoint f)
  证明: by
  refine
    (biUnion_sdiff_biUnion_subset f s t).antisymm
      (iUnion₂_subset fun i hi a ha => (mem_sdiff _).2 ⟨mem_biUnion hi.1 ha, ?_⟩)
  rw [mem_iUnion₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩

@[deprecated (since := "

Depends on / 依赖: Or.inl, Or.inr, antisymm, biUnion_sdiff_biUnion_subset, le_bot, mem_biUnion, mem_sdiff, ne_of_mem_of_not_mem
-/
theorem biUnion_sdiff_biUnion_eq {s t : Set ι} {f : ι -> Set α} (h : (s union t).PairwiseDisjoint f) :
    ((⋃ i in s, f i) \ ⋃ i in t, f i) = ⋃ i in s \ t, f i := by
  refine
    (biUnion_sdiff_biUnion_subset f s t).antisymm
      (iUnion₂_subset fun i hi a ha => (mem_sdiff _).2 ⟨mem_biUnion hi.1 ha, ?_⟩)
  rw [mem_iUnion₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩

@[deprecated (since := "2026-06-03")] alias biUnion_diff_biUnion_eq := biUnion_sdiff_biUnion_eq


/--
Definition of `biUnionEqSigmaOfDisjoint` / `biUnionEqSigmaOfDisjoint` 的定义

English:
definition biUnionEqSigmaOfDisjoint
  signature: {s : Set ι} {f : ι -> Set α} (h : s.PairwiseDisjoint f)
  body: (Equiv.setCongr (biUnion_eq_iUnion _ _)).trans
unionEqSigmaOfDisjoint fun ⟨_i, hi⟩ ⟨_j, hj⟩ ne => h hi hj fun eq => ne Subtype.ext eq

@[simp]

中文:
定义 biUnionEqSigmaOfDisjoint
  签名: {s : 集合 ι} {f : ι -> 集合 α} (h : s.PairwiseDisjoint f)
  定义体: (Equiv.setCongr (biUnion_eq_iUnion _ _)).trans
unionEqSigmaOfDisjoint fun ⟨_i, hi⟩ ⟨_j, hj⟩ ne => h hi hj fun eq => ne Subtype.ext eq

@[simp]

Depends on / 依赖: Equiv.setCongr, Subtype, Subtype.ext, biUnion_eq_iUnion, setCongr, unionEqSigmaOfDisjoint
-/
noncomputable def biUnionEqSigmaOfDisjoint {s : Set ι} {f : ι -> Set α} (h : s.PairwiseDisjoint f) :
    (⋃ i in s, f i) ≃ Σ i : s, f i :=
(Equiv.setCongr (biUnion_eq_iUnion _ _)).trans
unionEqSigmaOfDisjoint fun ⟨_i, hi⟩ ⟨_j, hj⟩ ne => h hi hj fun eq => ne Subtype.ext eq

@[simp]
/--
lemma `coe_biUnionEqSigmaOfDisjoint_symm_apply` / 引理 `coe_biUnionEqSigmaOfDisjoint_symm_apply`

English:
lemma coe_biUnionEqSigmaOfDisjoint_symm_apply
  statement: {α ι : Type*} {s : Set ι}
  proof: by
  rfl

中文:
引理 coe_biUnionEqSigmaOfDisjoint_symm_apply
  结论: {α ι : 类型} {s : 集合 ι}
  证明: by
  rfl

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField, ResidueField, X.presheaf.stalk, presheaf
-/
lemma coe_biUnionEqSigmaOfDisjoint_symm_apply {α ι : Type*} {s : Set ι}
    {f : ι -> Set α} (h : s.PairwiseDisjoint f) (x : (i : s) × f i) :
    ((Set.biUnionEqSigmaOfDisjoint h).symm x : α) = x.2 := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `coe_snd_biUnionEqSigmaOfDisjoint` / 引理 `coe_snd_biUnionEqSigmaOfDisjoint`

English:
lemma coe_snd_biUnionEqSigmaOfDisjoint
  statement: {α ι : Type*} {s : Set ι}
  proof: by
  simp [biUnionEqSigmaOfDisjoint]

中文:
引理 coe_snd_biUnionEqSigmaOfDisjoint
  结论: {α ι : 类型} {s : 集合 ι}
  证明: by
  simp [biUnionEqSigmaOfDisjoint]

Depends on / 依赖: biUnionEqSigmaOfDisjoint
-/
lemma coe_snd_biUnionEqSigmaOfDisjoint {α ι : Type*} {s : Set ι}
    {f : ι -> Set α} (h : s.PairwiseDisjoint f) (x : ⋃ i in s, f i) :
    ((Set.biUnionEqSigmaOfDisjoint h x).snd : α) = x := by
  simp [biUnionEqSigmaOfDisjoint]

end Set

section

variable {f : ι -> Set α} {s t : Set ι}

/--
lemma `Set.pairwiseDisjoint_iff` / 引理 `Set.pairwiseDisjoint_iff`

English:
lemma Set.pairwiseDisjoint_iff
  proof: by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

中文:
引理 集合.pairwiseDisjoint_iff
  证明: by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

Depends on / 依赖: Function, Function.onFun, Pairwise, PairwiseDisjoint, Set.Pairwise, Set.PairwiseDisjoint, not_disjoint_iff_nonempty_inter, not_imp_comm
-/
lemma Set.pairwiseDisjoint_iff :
    s.PairwiseDisjoint f ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f i inter f j).Nonempty -> i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

/--
lemma `Set.pairwiseDisjoint_pair_insert` / 引理 `Set.pairwiseDisjoint_pair_insert`

English:
lemma Set.pairwiseDisjoint_pair_insert
  given: {s : Set α} {a : α} (ha : a ∉ s)
  proof: by
  rw [pairwiseDisjoint_iff]
  rintro i hi j hj
  have := insert_erase_invOn.2.injOn (notMem_subset hi ha) (notMem_subset hj ha)
  aesop (add simp [Set.Nonempty, Set.subset_def])

中文:
引理 集合.pairwiseDisjoint_pair_insert
  条件: {s : 集合 α} {a : α} (ha : a ∉ s)
  证明: by
  rw [pairwiseDisjoint_iff]
  rintro i hi j hj
  have := insert_erase_invOn.2.injOn (notMem_subset hi ha) (notMem_subset hj ha)
  aesop (add simp [Set.Nonempty, Set.subset_def])

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, Nonempty, Set.Nonempty, Set.subset_def, X.residue_surjective, epi_of_surjective, insert_erase_invOn, notMem_subset, pairwiseDisjoint_iff, residue_surjective, subset_def
-/
lemma Set.pairwiseDisjoint_pair_insert {s : Set α} {a : α} (ha : a ∉ s) :
    s.powerset.PairwiseDisjoint fun t => ({t, insert a t} : Set (Set α)) := by
  rw [pairwiseDisjoint_iff]
  rintro i hi j hj
  have := insert_erase_invOn.2.injOn (notMem_subset hi ha) (notMem_subset hj ha)
  aesop (add simp [Set.Nonempty, Set.subset_def])

/--
theorem `Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion` / 定理 `Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion`

English:
theorem Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion
  statement: (h₀ : (s union t).PairwiseDisjoint f)
  proof: by
  rintro i hi
  obtain ⟨a, hai⟩ := h₁ i hi
  obtain ⟨j, hj, haj⟩ := mem_iUnion₂.1 (h <| mem_iUnion₂_of_mem hi hai)
  rwa [h₀.eq (subset_union_left hi) (subset_union_right hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]

中文:
定理 集合.PairwiseDisjoint.subset_of_biUnion_subset_biUnion
  结论: (h₀ : (s union t).PairwiseDisjoint f)
  证明: by
  rintro i hi
  obtain ⟨a, hai⟩ := h₁ i hi
  obtain ⟨j, hj, haj⟩ := mem_iUnion₂.1 (h <| mem_iUnion₂_of_mem hi hai)
  rwa [h₀.eq (subset_union_left hi) (subset_union_right hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]

Depends on / 依赖: not_disjoint_iff, subset_union_left, subset_union_right
-/
theorem Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀ : (s union t).PairwiseDisjoint f)
    (h₁ : forall i in s, (f i).Nonempty) (h : ⋃ i in s, f i subseteq ⋃ i in t, f i) : s subseteq t := by
  rintro i hi
  obtain ⟨a, hai⟩ := h₁ i hi
  obtain ⟨j, hj, haj⟩ := mem_iUnion₂.1 (h <| mem_iUnion₂_of_mem hi hai)
  rwa [h₀.eq (subset_union_left hi) (subset_union_right hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]

/--
theorem `Pairwise.subset_of_biUnion_subset_biUnion` / 定理 `Pairwise.subset_of_biUnion_subset_biUnion`

English:
theorem Pairwise.subset_of_biUnion_subset_biUnion
  statement: (h₀ : Pairwise (Disjoint on f))
  proof: Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀.set_pairwise _) h₁ h

中文:
定理 两两.subset_of_biUnion_subset_biUnion
  结论: (h₀ : 两两 (Disjoint on f))
  证明: Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀.set_pairwise _) h₁ h

Depends on / 依赖: PairwiseDisjoint, Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion, set_pairwise, subset_of_biUnion_subset_biUnion
-/
theorem Pairwise.subset_of_biUnion_subset_biUnion (h₀ : Pairwise (Disjoint on f))
    (h₁ : forall i in s, (f i).Nonempty) (h : ⋃ i in s, f i subseteq ⋃ i in t, f i) : s subseteq t :=
  Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀.set_pairwise _) h₁ h

/--
theorem `Pairwise.biUnion_injective` / 定理 `Pairwise.biUnion_injective`

English:
theorem Pairwise.biUnion_injective
  given: (h₀ : Pairwise (Disjoint on f)) (h₁ : forall i, (f i).Nonempty)
  proof: fun _s _t h =>
((h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.subset).antisymm
(h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) h.superset

中文:
定理 两两.biUnion_injective
  条件: (h₀ : 两两 (Disjoint on f)) (h₁ : 对任意 i, (f i).非空)
  证明: fun _s _t h =>
((h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.subset).antisymm
(h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) h.superset
-/
theorem Pairwise.biUnion_injective (h₀ : Pairwise (Disjoint on f)) (h₁ : forall i, (f i).Nonempty) :
    Injective fun s : Set ι => ⋃ i in s, f i := fun _s _t h =>
((h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.subset).antisymm
(h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) h.superset

/--
theorem `pairwiseDisjoint_unique` / 定理 `pairwiseDisjoint_unique`

English:
theorem pairwiseDisjoint_unique
  statement: {y : α}
  proof: by
  refine existsUnique_of_exists_of_unique ?ex ?unique
  · simpa only [mem_iUnion, exists_prop] using hy
  · rintro i j ⟨his, hi⟩ ⟨hjs, hj⟩
exact h_disjoint.elim his hjs not_disjoint_iff.mpr ⟨y, ⟨hi, hj⟩⟩

中文:
定理 pairwiseDisjoint_unique
  结论: {y : α}
  证明: by
  refine existsUnique_of_exists_of_unique ?ex ?unique
  · simpa only [mem_iUnion, exists_prop] using hy
  · rintro i j ⟨his, hi⟩ ⟨hjs, hj⟩
exact h_disjoint.elim his hjs not_disjoint_iff.mpr ⟨y, ⟨hi, hj⟩⟩

Depends on / 依赖: existsUnique_of_exists_of_unique, exists_prop, h_disjoint, h_disjoint.elim, mem_iUnion, not_disjoint_iff, not_disjoint_iff.mpr, unique
-/
theorem pairwiseDisjoint_unique {y : α}
    (h_disjoint : PairwiseDisjoint s f)
    (hy : y in (⋃ i in s, f i)) : exists! i, i in s ∧ y in f i := by
  refine existsUnique_of_exists_of_unique ?ex ?unique
  · simpa only [mem_iUnion, exists_prop] using hy
  · rintro i j ⟨his, hi⟩ ⟨hjs, hj⟩
exact h_disjoint.elim his hjs not_disjoint_iff.mpr ⟨y, ⟨hi, hj⟩⟩

end
