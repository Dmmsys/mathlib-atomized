/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Baire spaces

A topological space is called a *Baire space*
if a countable intersection of dense open subsets is dense.
Baire theorems say that all completely metrizable spaces
and all locally compact regular spaces are Baire spaces.
We prove the theorems in `Mathlib/Topology/Baire/CompleteMetrizable`
and `Mathlib/Topology/Baire/LocallyCompactRegular`.

In this file we prove some lemmas about Baire spaces.

The good concept underlying the theorems is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We deduce this version from Baire property.
We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

We also prove that in Baire spaces, the `residual` sets are exactly those containing a dense Gδ set.
-/

public section


noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}

section BaireTheorem

variable [TopologicalSpace X]

/--
theorem `Set.Finite.dense_sInter` / 定理 `Set.Finite.dense_sInter`

English:
theorem Set.Finite.dense_sInter
  statement: {s : Set (Set X)} (hs : s.Finite)
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [sInter_empty]
  | insert ha hsf ih =>
    simp only [sInter_insert, forall_mem_insert] at hd ⊢
    refine hd.1.inter_of_isOpen_right ?_ (hsf.isOpen_sInter (fun y hy => ho y (Or.inr hy)))
    exact ih ((fun y hy => ho y (Or.in

中文:
定理 Set.Finite.dense_sInter
  结论: {s : Set (Set X)} (hs : s.Finite)
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [sInter_empty]
  | insert ha hsf ih =>
    simp only [sInter_insert, forall_mem_insert] at hd ⊢
    refine hd.1.inter_of_isOpen_right ?_ (hsf.isOpen_sInter (fun y hy => ho y (Or.inr hy)))
    exact ih ((fun y hy => ho y (Or.in

Depends on / 依赖: Finite, Or.inr, Set.Finite.induction_on, forall_mem_insert, hsf.isOpen_sInter, induction_on, insert, inter_of_isOpen_right, isOpen_sInter, sInter_empty, sInter_insert
-/
theorem Set.Finite.dense_sInter {s : Set (Set X)} (hs : s.Finite)
    (ho : forall t in s, IsOpen t) (hd : forall t in s, Dense t) : Dense (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [sInter_empty]
  | insert ha hsf ih =>
    simp only [sInter_insert, forall_mem_insert] at hd ⊢
    refine hd.1.inter_of_isOpen_right ?_ (hsf.isOpen_sInter (fun y hy => ho y (Or.inr hy)))
    exact ih ((fun y hy => ho y (Or.inr hy))) (fun y hy => hd.2 y hy)

/--
theorem `baire_of_finite` / 定理 `baire_of_finite`

English:
theorem baire_of_finite
  given: [Finite X]
  statement: BaireSpace X where
  proof: sInter_range f ▸ (toFinite (range f)).dense_sInter (by grind) (by grind)

中文:
定理 baire_of_finite
  条件: [Finite X]
  结论: BaireSpace X where
  证明: sInter_range f ▸ (toFinite (range f)).dense_sInter (by grind) (by grind)

Depends on / 依赖: dense_sInter, sInter_range, toFinite
-/
theorem baire_of_finite [Finite X] : BaireSpace X where
  baire_property f _ _ := sInter_range f ▸ (toFinite (range f)).dense_sInter (by grind) (by grind)

variable [BaireSpace X]

/--
theorem `dense_iInter_of_isOpen_nat` / 定理 `dense_iInter_of_isOpen_nat`

English:
theorem dense_iInter_of_isOpen_nat
  statement: {f : Nat -> Set X} (ho : forall n, IsOpen (f n))
  proof: BaireSpace.baire_property f ho hd

中文:
定理 dense_iInter_of_isOpen_nat
  结论: {f : 自然数 -> Set X} (ho : 对任意 n, IsOpen (f n))
  证明: BaireSpace.baire_property f ho hd

Depends on / 依赖: BaireSpace, BaireSpace.baire_property, baire_property
-/
theorem dense_iInter_of_isOpen_nat {f : Nat -> Set X} (ho : forall n, IsOpen (f n))
    (hd : forall n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd

/--
theorem `IsGδ.baireSpace_of_dense` / 定理 `IsGδ.baireSpace_of_dense`

English:
theorem IsGδ.baireSpace_of_dense
  given: {s : Set X} (hG : IsGδ s) (hd : Dense s)
  statement: BaireSpace s
  proof: by
  constructor
  intro f hof hdf
  obtain ⟨V, hV⟩ : exists V : Nat -> Set X, (forall n, IsOpen (V n)) ∧ s = ⋂ n, V n := eq_iInter_nat hG
  choose g hg1 hg2 hg3 using fun n => exists_open_dense_of_open_dense_subtype hd (hof n) (hdf n)
  have h_inter_dense : Dense (⋂ n, g n inter V n) := BaireSpace.

中文:
定理 IsGδ.baireSpace_of_dense
  条件: {s : Set X} (hG : IsGδ s) (hd : Dense s)
  结论: BaireSpace s
  证明: by
  constructor
  intro f hof hdf
  obtain ⟨V, hV⟩ : exists V : Nat -> Set X, (forall n, IsOpen (V n)) ∧ s = ⋂ n, V n := eq_iInter_nat hG
  choose g hg1 hg2 hg3 using fun n => exists_open_dense_of_open_dense_subtype hd (hof n) (hdf n)
  have h_inter_dense : Dense (⋂ n, g n inter V n) := BaireSpace.

Depends on / 依赖: BaireSpace, BaireSpace.baire_property, IsOpen, baire_property, eq_iInter_nat, exists_open_dense_of_open_dense_subtype, h_inter_dense, h_inter_eq, hd.mono, iInter_subset, inter_of_isOpen_left
-/
theorem IsGδ.baireSpace_of_dense {s : Set X} (hG : IsGδ s) (hd : Dense s) : BaireSpace s := by
  constructor
  intro f hof hdf
  obtain ⟨V, hV⟩ : exists V : Nat -> Set X, (forall n, IsOpen (V n)) ∧ s = ⋂ n, V n := eq_iInter_nat hG
  choose g hg1 hg2 hg3 using fun n => exists_open_dense_of_open_dense_subtype hd (hof n) (hdf n)
  have h_inter_dense : Dense (⋂ n, g n inter V n) := BaireSpace.baire_property (fun n => g n inter V n)
    (fun n => (hg1 n).inter (hV.1 n))
    (fun n => (hg2 n).inter_of_isOpen_left (hd.mono (by simp [hV.2, iInter_subset])) (hg1 n))
  have h_inter_eq : ⋂ n, g n inter V n = ⋂ n, f n := by ext; simp_all; grind
  exact Subtype.dense_iff.mpr fun a _ => h_inter_eq ▸ h_inter_dense a

/--
theorem `Topology.IsOpenEmbedding.baireSpace` / 定理 `Topology.IsOpenEmbedding.baireSpace`

English:
theorem Topology.IsOpenEmbedding.baireSpace
  statement: {Y : Type*} [TopologicalSpace Y] {p : Y -> X}
  proof: by
  constructor
  intro f hof hdf
  let s := range p
  let c := fun n : Nat => p '' f n union (closure s)ᶜ
  have c_open (n : Nat) : IsOpen (c n) := IsOpen.union (hp.isOpenMap (f n) (hof n))
    isClosed_closure.isOpen_compl
  have c_dense (n : Nat) : Dense (c n) := by
    rw [dense_iff_closure_eq]

中文:
定理 Topology.IsOpenEmbedding.baireSpace
  结论: {Y : 类型} [TopologicalSpace Y] {p : Y -> X}
  证明: by
  constructor
  intro f hof hdf
  let s := range p
  let c := fun n : Nat => p '' f n union (closure s)ᶜ
  have c_open (n : Nat) : IsOpen (c n) := IsOpen.union (hp.isOpenMap (f n) (hof n))
    isClosed_closure.isOpen_compl
  have c_dense (n : Nat) : Dense (c n) := by
    rw [dense_iff_closure_eq]

Depends on / 依赖: IsOpen, IsOpen.union, c_dense, c_open, closure, dense_iff_closure_eq, hp.isOpenMap, interior, isClosed_closure, isClosed_closure.isOpen_compl, isOpenMap, isOpen_compl, subset_antisymm_iff, subseteq
-/
theorem Topology.IsOpenEmbedding.baireSpace {Y : Type*} [TopologicalSpace Y] {p : Y -> X}
    (hp : Topology.IsOpenEmbedding p) : BaireSpace Y := by
  constructor
  intro f hof hdf
  let s := range p
  let c := fun n : Nat => p '' f n union (closure s)ᶜ
  have c_open (n : Nat) : IsOpen (c n) := IsOpen.union (hp.isOpenMap (f n) (hof n))
    isClosed_closure.isOpen_compl
  have c_dense (n : Nat) : Dense (c n) := by
    rw [dense_iff_closure_eq]; rw [subset_antisymm_iff]
    have : univ subseteq closure (c n) := calc
      _ subseteq (interior (closure s)) union (interior (closure s))ᶜ := by grind
      _ subseteq closure s union (interior (closure s))ᶜ := by gcongr; exact interior_subset
      _ subseteq closure (p '' f n) union (interior (closure s))ᶜ := union_subset_union
          (closure_minimal (hp.continuous.range_subset_closure_image_dense (hdf n))
          isClosed_closure) (subset_refl (interior (closure s))ᶜ)
      _ subseteq closure (p '' f n) union closure ((closure s)ᶜ) := union_subset_union (by simp) (by simp)
      _ = closure (c n) := closure_union.symm
    grind
  have c_inter_dense : Dense (⋂ n, c n) := dense_iInter_of_isOpen_nat c_open c_dense
  have c_inter_eq : ⋂ n, f n = p ⁻¹' (⋂ n, c n) := by
    ext x
    simp only [mem_iInter, mem_preimage, mem_union, mem_compl_iff, c]
    refine ⟨fun h i => by grind, fun h i => ?_⟩
    exact hp.injective.mem_set_image.mp (imp_iff_or_not.mpr (h i)
      (subset_closure (mem_range_self x)))
  exact c_inter_eq ▸ Dense.preimage c_inter_dense hp.isOpenMap

/--
theorem `IsOpen.baireSpace` / 定理 `IsOpen.baireSpace`

English:
theorem IsOpen.baireSpace
  given: {s : Set X} (hO : IsOpen s)
  statement: BaireSpace s
  proof: hO.isOpenEmbedding_subtypeVal.baireSpace

中文:
定理 IsOpen.baireSpace
  条件: {s : Set X} (hO : IsOpen s)
  结论: BaireSpace s
  证明: hO.isOpenEmbedding_subtypeVal.baireSpace

Depends on / 依赖: baireSpace, hO.isOpenEmbedding_subtypeVal.baireSpace, isOpenEmbedding_subtypeVal
-/
theorem IsOpen.baireSpace {s : Set X} (hO : IsOpen s) : BaireSpace s :=
  hO.isOpenEmbedding_subtypeVal.baireSpace

/--
theorem `IsOpenQuotientMap.baireSpace` / 定理 `IsOpenQuotientMap.baireSpace`

English:
theorem IsOpenQuotientMap.baireSpace
  statement: {Y : Type*} [TopologicalSpace Y] {f : X -> Y}
  proof: by
  constructor
  intro u hou hdu
  have := dense_iInter_of_isOpen_nat (fun n => hf.continuous.isOpen_preimage (u n) (hou n))
    (fun n => (IsOpenQuotientMap.dense_preimage_iff hf).mpr (hdu n))
  simp_all [← preimage_iInter, IsOpenQuotientMap.dense_preimage_iff]

中文:
定理 IsOpenQuotientMap.baireSpace
  结论: {Y : 类型} [TopologicalSpace Y] {f : X -> Y}
  证明: by
  constructor
  intro u hou hdu
  have := dense_iInter_of_isOpen_nat (fun n => hf.continuous.isOpen_preimage (u n) (hou n))
    (fun n => (IsOpenQuotientMap.dense_preimage_iff hf).mpr (hdu n))
  simp_all [← preimage_iInter, IsOpenQuotientMap.dense_preimage_iff]

Depends on / 依赖: IsOpenQuotientMap, IsOpenQuotientMap.dense_preimage_iff, continuous, dense_iInter_of_isOpen_nat, dense_preimage_iff, hf.continuous.isOpen_preimage, isOpen_preimage, preimage_iInter
-/
theorem IsOpenQuotientMap.baireSpace {Y : Type*} [TopologicalSpace Y] {f : X -> Y}
    (hf : IsOpenQuotientMap f) : BaireSpace Y := by
  constructor
  intro u hou hdu
  have := dense_iInter_of_isOpen_nat (fun n => hf.continuous.isOpen_preimage (u n) (hou n))
    (fun n => (IsOpenQuotientMap.dense_preimage_iff hf).mpr (hdu n))
  simp_all [← preimage_iInter, IsOpenQuotientMap.dense_preimage_iff]

/--
theorem `dense_sInter_of_isOpen` / 定理 `dense_sInter_of_isOpen`

English:
theorem dense_sInter_of_isOpen
  statement: {S : Set (Set X)} (ho : forall s in S, IsOpen s) (hS : S.Countable)
  proof: by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    exact dense_iInter_of_isOpen_nat (forall_mem_range.1 ho) (forall_mem_range.1 hd)

中文:
定理 dense_sInter_of_isOpen
  结论: {S : Set (Set X)} (ho : 对任意 s in S, IsOpen s) (hS : S.Countable)
  证明: by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    exact dense_iInter_of_isOpen_nat (forall_mem_range.1 ho) (forall_mem_range.1 hd)

Depends on / 依赖: S.eq_empty_or_nonempty, dense_iInter_of_isOpen_nat, eq_empty_or_nonempty, exists_eq_range, forall_mem_range, hS.exists_eq_range
-/
theorem dense_sInter_of_isOpen {S : Set (Set X)} (ho : forall s in S, IsOpen s) (hS : S.Countable)
    (hd : forall s in S, Dense s) : Dense (⋂₀ S) := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    exact dense_iInter_of_isOpen_nat (forall_mem_range.1 ho) (forall_mem_range.1 hd)

/--
theorem `dense_biInter_of_isOpen` / 定理 `dense_biInter_of_isOpen`

English:
theorem dense_biInter_of_isOpen
  statement: {S : Set α} {f : α -> Set X} (ho : forall s in S, IsOpen (f s))
  proof: by
  rw [← sInter_image]
  refine dense_sInter_of_isOpen ?_ (hS.image _) ?_ <;> rwa [forall_mem_image]

中文:
定理 dense_biInter_of_isOpen
  结论: {S : Set α} {f : α -> Set X} (ho : 对任意 s in S, IsOpen (f s))
  证明: by
  rw [← sInter_image]
  refine dense_sInter_of_isOpen ?_ (hS.image _) ?_ <;> rwa [forall_mem_image]

Depends on / 依赖: dense_sInter_of_isOpen, forall_mem_image, hS.image, sInter_image
-/
theorem dense_biInter_of_isOpen {S : Set α} {f : α -> Set X} (ho : forall s in S, IsOpen (f s))
    (hS : S.Countable) (hd : forall s in S, Dense (f s)) : Dense (⋂ s in S, f s) := by
  rw [← sInter_image]
  refine dense_sInter_of_isOpen ?_ (hS.image _) ?_ <;> rwa [forall_mem_image]

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable type. -/
@[wikidata Q1052678]
/--
theorem `dense_iInter_of_isOpen` / 定理 `dense_iInter_of_isOpen`

English:
theorem dense_iInter_of_isOpen
  statement: [Countable ι] {f : ι -> Set X} (ho : forall i, IsOpen (f i))
  proof: dense_sInter_of_isOpen (forall_mem_range.2 ho) (countable_range _) (forall_mem_range.2 hd)

中文:
定理 dense_iInter_of_isOpen
  结论: [Countable ι] {f : ι -> Set X} (ho : 对任意 i, IsOpen (f i))
  证明: dense_sInter_of_isOpen (forall_mem_range.2 ho) (countable_range _) (forall_mem_range.2 hd)

Depends on / 依赖: countable_range, dense_sInter_of_isOpen, forall_mem_range
-/
theorem dense_iInter_of_isOpen [Countable ι] {f : ι -> Set X} (ho : forall i, IsOpen (f i))
    (hd : forall i, Dense (f i)) : Dense (⋂ s, f s) :=
  dense_sInter_of_isOpen (forall_mem_range.2 ho) (countable_range _) (forall_mem_range.2 hd)

/--
theorem `mem_residual` / 定理 `mem_residual`

English:
theorem mem_residual
  given: {s : Set X}
  statement: s in residual X ↔ exists t subseteq s, IsGδ t ∧ Dense t
  proof: by
  constructor
  · rw [mem_residual_iff]
    rintro ⟨S, hSo, hSd, Sct, Ss⟩
    refine ⟨_, Ss, ⟨_, fun t ht => hSo _ ht, Sct, rfl⟩, ?_⟩
    exact dense_sInter_of_isOpen hSo Sct hSd
  rintro ⟨t, ts, ho, hd⟩
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts

中文:
定理 mem_residual
  条件: {s : Set X}
  结论: s in residual X ↔ 存在 t subseteq s, IsGδ t ∧ Dense t
  证明: by
  constructor
  · rw [mem_residual_iff]
    rintro ⟨S, hSo, hSd, Sct, Ss⟩
    refine ⟨_, Ss, ⟨_, fun t ht => hSo _ ht, Sct, rfl⟩, ?_⟩
    exact dense_sInter_of_isOpen hSo Sct hSd
  rintro ⟨t, ts, ho, hd⟩
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts

Depends on / 依赖: dense_sInter_of_isOpen, mem_of_superset, mem_residual_iff
-/
theorem mem_residual {s : Set X} : s in residual X ↔ exists t subseteq s, IsGδ t ∧ Dense t := by
  constructor
  · rw [mem_residual_iff]
    rintro ⟨S, hSo, hSd, Sct, Ss⟩
    refine ⟨_, Ss, ⟨_, fun t ht => hSo _ ht, Sct, rfl⟩, ?_⟩
    exact dense_sInter_of_isOpen hSo Sct hSd
  rintro ⟨t, ts, ho, hd⟩
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts

/--
theorem `eventually_residual` / 定理 `eventually_residual`

English:
theorem eventually_residual
  given: {p : X -> Prop}
  proof: by
  simp only [Filter.Eventually, mem_residual, subset_def, mem_ofPred_eq]
  tauto

中文:
定理 eventually_residual
  条件: {p : X -> 命题}
  证明: by
  simp only [Filter.Eventually, mem_residual, subset_def, mem_ofPred_eq]
  tauto

Depends on / 依赖: Eventually, Filter, Filter.Eventually, mem_ofPred_eq, mem_residual, subset_def
-/
theorem eventually_residual {p : X -> Prop} :
    (forallᶠ x in residual X, p x) ↔ exists t : Set X, IsGδ t ∧ Dense t ∧ forall x in t, p x := by
  simp only [Filter.Eventually, mem_residual, subset_def, mem_ofPred_eq]
  tauto

/--
theorem `dense_of_mem_residual` / 定理 `dense_of_mem_residual`

English:
theorem dense_of_mem_residual
  given: {s : Set X} (hs : s in residual X)
  statement: Dense s
  proof: let ⟨_, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts

中文:
定理 dense_of_mem_residual
  条件: {s : Set X} (hs : s in residual X)
  结论: Dense s
  证明: let ⟨_, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts

Depends on / 依赖: hd.mono, mem_residual
-/
theorem dense_of_mem_residual {s : Set X} (hs : s in residual X) : Dense s :=
  let ⟨_, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts

/--
theorem `not_isMeagre_of_isOpen` / 定理 `not_isMeagre_of_isOpen`

English:
theorem not_isMeagre_of_isOpen
  given: {s : Set X} (hs : IsOpen s) (hne : s.Nonempty)
  statement: ¬ IsMeagre s
  proof: by
  intro h
  obtain ⟨x, hx, hxc⟩ :=
    (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
  exact hxc hx

中文:
定理 not_isMeagre_of_isOpen
  条件: {s : Set X} (hs : IsOpen s) (hne : s.Nonempty)
  结论: ¬ IsMeagre s
  证明: by
  intro h
  obtain ⟨x, hx, hxc⟩ :=
    (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
  exact hxc hx

Depends on / 依赖: IsMeagre, dense_of_mem_residual, inter_open_nonempty
-/
theorem not_isMeagre_of_isOpen {s : Set X} (hs : IsOpen s) (hne : s.Nonempty) : ¬ IsMeagre s := by
  intro h
  obtain ⟨x, hx, hxc⟩ :=
    (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
  exact hxc hx

/--
theorem `dense_sInter_of_Gδ` / 定理 `dense_sInter_of_Gδ`

English:
theorem dense_sInter_of_Gδ
  statement: {S : Set (Set X)} (ho : forall s in S, IsGδ s) (hS : S.Countable)
  proof: dense_of_mem_residual ((countable_sInter_mem hS).mpr
    (fun _ hs => residual_of_dense_Gδ (ho _ hs) (hd _ hs)))

中文:
定理 dense_sInter_of_Gδ
  结论: {S : Set (Set X)} (ho : 对任意 s in S, IsGδ s) (hS : S.Countable)
  证明: dense_of_mem_residual ((countable_sInter_mem hS).mpr
    (fun _ hs => residual_of_dense_Gδ (ho _ hs) (hd _ hs)))

Depends on / 依赖: countable_sInter_mem, dense_of_mem_residual
-/
theorem dense_sInter_of_Gδ {S : Set (Set X)} (ho : forall s in S, IsGδ s) (hS : S.Countable)
    (hd : forall s in S, Dense s) : Dense (⋂₀ S) :=
  dense_of_mem_residual ((countable_sInter_mem hS).mpr
    (fun _ hs => residual_of_dense_Gδ (ho _ hs) (hd _ hs)))

/--
theorem `dense_iInter_of_Gδ` / 定理 `dense_iInter_of_Gδ`

English:
theorem dense_iInter_of_Gδ
  statement: [Countable ι] {f : ι -> Set X} (ho : forall s, IsGδ (f s))
  proof: dense_sInter_of_Gδ (forall_mem_range.2 ‹_›) (countable_range _) (forall_mem_range.2 ‹_›)

中文:
定理 dense_iInter_of_Gδ
  结论: [Countable ι] {f : ι -> Set X} (ho : 对任意 s, IsGδ (f s))
  证明: dense_sInter_of_Gδ (forall_mem_range.2 ‹_›) (countable_range _) (forall_mem_range.2 ‹_›)

Depends on / 依赖: countable_range, forall_mem_range
-/
theorem dense_iInter_of_Gδ [Countable ι] {f : ι -> Set X} (ho : forall s, IsGδ (f s))
    (hd : forall s, Dense (f s)) : Dense (⋂ s, f s) :=
  dense_sInter_of_Gδ (forall_mem_range.2 ‹_›) (countable_range _) (forall_mem_range.2 ‹_›)

/--
theorem `dense_biInter_of_Gδ` / 定理 `dense_biInter_of_Gδ`

English:
theorem dense_biInter_of_Gδ
  statement: {S : Set α} {f : forall x in S, Set X} (ho : forall s (H : s in S), IsGδ (f s H))
  proof: by
  rw [biInter_eq_iInter]
  have := hS.to_subtype
  exact dense_iInter_of_Gδ (fun s => ho s s.2) fun s => hd s s.2

中文:
定理 dense_biInter_of_Gδ
  结论: {S : Set α} {f : 对任意 x in S, Set X} (ho : 对任意 s (H : s in S), IsGδ (f s H))
  证明: by
  rw [biInter_eq_iInter]
  have := hS.to_subtype
  exact dense_iInter_of_Gδ (fun s => ho s s.2) fun s => hd s s.2

Depends on / 依赖: biInter_eq_iInter, hS.to_subtype, to_subtype
-/
theorem dense_biInter_of_Gδ {S : Set α} {f : forall x in S, Set X} (ho : forall s (H : s in S), IsGδ (f s H))
    (hS : S.Countable) (hd : forall s (H : s in S), Dense (f s H)) : Dense (⋂ s in S, f s ‹_›) := by
  rw [biInter_eq_iInter]
  have := hS.to_subtype
  exact dense_iInter_of_Gδ (fun s => ho s s.2) fun s => hd s s.2

/--
theorem `Dense.inter_of_Gδ` / 定理 `Dense.inter_of_Gδ`

English:
theorem Dense.inter_of_Gδ
  statement: {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
  proof: by
  rw [inter_eq_iInter]
  apply dense_iInter_of_Gδ <;> simp [Bool.forall_bool, *]

中文:
定理 Dense.inter_of_Gδ
  结论: {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
  证明: by
  rw [inter_eq_iInter]
  apply dense_iInter_of_Gδ <;> simp [Bool.forall_bool, *]

Depends on / 依赖: Bool.forall_bool, forall_bool, inter_eq_iInter
-/
theorem Dense.inter_of_Gδ {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
    (htc : Dense t) : Dense (s inter t) := by
  rw [inter_eq_iInter]
  apply dense_iInter_of_Gδ <;> simp [Bool.forall_bool, *]

/--
theorem `IsGδ.dense_iUnion_interior_of_closed` / 定理 `IsGδ.dense_iUnion_interior_of_closed`

English:
theorem IsGδ.dense_iUnion_interior_of_closed
  statement: [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s)
  proof: by
  let g i := (frontier (f i))ᶜ
  have hgo : forall i, IsOpen (g i) := fun i => isClosed_frontier.isOpen_compl
  have hgd : Dense (⋂ i, g i) := by
    refine dense_iInter_of_isOpen hgo fun i x => ?_
    rw [closure_compl]; rw [interior_frontier (hc _)]
    exact id
  refine (hd.inter_of_Gδ hs (.iI

中文:
定理 IsGδ.dense_iUnion_interior_of_closed
  结论: [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s)
  证明: by
  let g i := (frontier (f i))ᶜ
  have hgo : forall i, IsOpen (g i) := fun i => isClosed_frontier.isOpen_compl
  have hgd : Dense (⋂ i, g i) := by
    refine dense_iInter_of_isOpen hgo fun i x => ?_
    rw [closure_compl]; rw [interior_frontier (hc _)]
    exact id
  refine (hd.inter_of_Gδ hs (.iI

Depends on / 依赖: IsOpen, closure_compl, dense_iInter_of_isOpen, frontier, hd.inter_of_G, iInter_of_isOpen, interior_frontier, isClosed_frontier, isClosed_frontier.isOpen_compl, isOpen_compl, mem_iInter, mem_iUnion, self_sdiff_frontier
-/
theorem IsGδ.dense_iUnion_interior_of_closed [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s)
    {f : ι -> Set X} (hc : forall i, IsClosed (f i)) (hU : s subseteq ⋃ i, f i) :
    Dense (⋃ i, interior (f i)) := by
  let g i := (frontier (f i))ᶜ
  have hgo : forall i, IsOpen (g i) := fun i => isClosed_frontier.isOpen_compl
  have hgd : Dense (⋂ i, g i) := by
    refine dense_iInter_of_isOpen hgo fun i x => ?_
    rw [closure_compl]; rw [interior_frontier (hc _)]
    exact id
  refine (hd.inter_of_Gδ hs (.iInter_of_isOpen fun i => (hgo i)) hgd).mono ?_
  rintro x ⟨hxs, hxg⟩
  rw [mem_iInter] at hxg
  rcases mem_iUnion.1 (hU hxs) with ⟨i, hi⟩
  exact mem_iUnion.2 ⟨i, self_sdiff_frontier (f i) ▸ ⟨hi, hxg _⟩⟩

/--
theorem `IsGδ.dense_biUnion_interior_of_closed` / 定理 `IsGδ.dense_biUnion_interior_of_closed`

English:
theorem IsGδ.dense_biUnion_interior_of_closed
  statement: {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s)
  proof: by
  have := ht.to_subtype
  simp only [biUnion_eq_iUnion, SetCoe.forall'] at *
  exact hs.dense_iUnion_interior_of_closed hd hc hU

中文:
定理 IsGδ.dense_biUnion_interior_of_closed
  结论: {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s)
  证明: by
  have := ht.to_subtype
  simp only [biUnion_eq_iUnion, SetCoe.forall'] at *
  exact hs.dense_iUnion_interior_of_closed hd hc hU

Depends on / 依赖: SetCoe, SetCoe.forall, biUnion_eq_iUnion, dense_iUnion_interior_of_closed, hs.dense_iUnion_interior_of_closed, ht.to_subtype, to_subtype
-/
theorem IsGδ.dense_biUnion_interior_of_closed {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s)
    (ht : t.Countable) {f : α -> Set X} (hc : forall i in t, IsClosed (f i)) (hU : s subseteq ⋃ i in t, f i) :
    Dense (⋃ i in t, interior (f i)) := by
  have := ht.to_subtype
  simp only [biUnion_eq_iUnion, SetCoe.forall'] at *
  exact hs.dense_iUnion_interior_of_closed hd hc hU

/--
theorem `IsGδ.dense_sUnion_interior_of_closed` / 定理 `IsGδ.dense_sUnion_interior_of_closed`

English:
theorem IsGδ.dense_sUnion_interior_of_closed
  statement: {T : Set (Set X)} {s : Set X} (hs : IsGδ s)
  proof: hs.dense_biUnion_interior_of_closed hd hc hc' by rwa [← sUnion_eq_biUnion]

中文:
定理 IsGδ.dense_sUnion_interior_of_closed
  结论: {T : Set (Set X)} {s : Set X} (hs : IsGδ s)
  证明: hs.dense_biUnion_interior_of_closed hd hc hc' by rwa [← sUnion_eq_biUnion]

Depends on / 依赖: dense_biUnion_interior_of_closed, hs.dense_biUnion_interior_of_closed, sUnion_eq_biUnion
-/
theorem IsGδ.dense_sUnion_interior_of_closed {T : Set (Set X)} {s : Set X} (hs : IsGδ s)
    (hd : Dense s) (hc : T.Countable) (hc' : forall t in T, IsClosed t) (hU : s subseteq ⋃₀ T) :
    Dense (⋃ t in T, interior t) :=
hs.dense_biUnion_interior_of_closed hd hc hc' by rwa [← sUnion_eq_biUnion]

/--
theorem `dense_biUnion_interior_of_closed` / 定理 `dense_biUnion_interior_of_closed`

English:
theorem dense_biUnion_interior_of_closed
  statement: {S : Set α} {f : α -> Set X} (hc : forall s in S, IsClosed (f s))
  proof: IsGδ.univ.dense_biUnion_interior_of_closed dense_univ hS hc hU.ge

中文:
定理 dense_biUnion_interior_of_closed
  结论: {S : Set α} {f : α -> Set X} (hc : 对任意 s in S, IsClosed (f s))
  证明: IsGδ.univ.dense_biUnion_interior_of_closed dense_univ hS hc hU.ge

Depends on / 依赖: dense_biUnion_interior_of_closed, dense_univ, hU.ge, univ.dense_biUnion_interior_of_closed
-/
theorem dense_biUnion_interior_of_closed {S : Set α} {f : α -> Set X} (hc : forall s in S, IsClosed (f s))
    (hS : S.Countable) (hU : ⋃ s in S, f s = univ) : Dense (⋃ s in S, interior (f s)) :=
  IsGδ.univ.dense_biUnion_interior_of_closed dense_univ hS hc hU.ge

/--
theorem `dense_sUnion_interior_of_closed` / 定理 `dense_sUnion_interior_of_closed`

English:
theorem dense_sUnion_interior_of_closed
  statement: {S : Set (Set X)} (hc : forall s in S, IsClosed s)
  proof: IsGδ.univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge

中文:
定理 dense_sUnion_interior_of_closed
  结论: {S : Set (Set X)} (hc : 对任意 s in S, IsClosed s)
  证明: IsGδ.univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge

Depends on / 依赖: dense_sUnion_interior_of_closed, dense_univ, hU.ge, univ.dense_sUnion_interior_of_closed
-/
theorem dense_sUnion_interior_of_closed {S : Set (Set X)} (hc : forall s in S, IsClosed s)
    (hS : S.Countable) (hU : ⋃₀ S = univ) : Dense (⋃ s in S, interior s) :=
  IsGδ.univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge

/--
theorem `dense_iUnion_interior_of_closed` / 定理 `dense_iUnion_interior_of_closed`

English:
theorem dense_iUnion_interior_of_closed
  statement: [Countable ι] {f : ι -> Set X} (hc : forall i, IsClosed (f i))
  proof: IsGδ.univ.dense_iUnion_interior_of_closed dense_univ hc hU.ge

中文:
定理 dense_iUnion_interior_of_closed
  结论: [Countable ι] {f : ι -> Set X} (hc : 对任意 i, IsClosed (f i))
  证明: IsGδ.univ.dense_iUnion_interior_of_closed dense_univ hc hU.ge

Depends on / 依赖: dense_iUnion_interior_of_closed, dense_univ, hU.ge, univ.dense_iUnion_interior_of_closed
-/
theorem dense_iUnion_interior_of_closed [Countable ι] {f : ι -> Set X} (hc : forall i, IsClosed (f i))
    (hU : ⋃ i, f i = univ) : Dense (⋃ i, interior (f i)) :=
  IsGδ.univ.dense_iUnion_interior_of_closed dense_univ hc hU.ge

variable [Nonempty X]

/--
theorem `nonempty_interior_of_iUnion_of_closed` / 定理 `nonempty_interior_of_iUnion_of_closed`

English:
theorem nonempty_interior_of_iUnion_of_closed
  statement: [Countable ι] {f : ι -> Set X}
  proof: by
  simpa using (dense_iUnion_interior_of_closed hc hU).nonempty

中文:
定理 nonempty_interior_of_iUnion_of_closed
  结论: [Countable ι] {f : ι -> Set X}
  证明: by
  simpa using (dense_iUnion_interior_of_closed hc hU).nonempty

Depends on / 依赖: dense_iUnion_interior_of_closed, nonempty
-/
theorem nonempty_interior_of_iUnion_of_closed [Countable ι] {f : ι -> Set X}
    (hc : forall i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : exists i, (interior <| f i).Nonempty := by
  simpa using (dense_iUnion_interior_of_closed hc hU).nonempty

/--
theorem `not_isMeagre_of_isGδ_of_dense` / 定理 `not_isMeagre_of_isGδ_of_dense`

English:
theorem not_isMeagre_of_isGδ_of_dense
  given: {s : Set X} (hs : IsGδ s) (hd : Dense s)
  proof: by
  intro h
  rcases mem_residual.1 h with ⟨t, hts, htG, hd'⟩
  rcases (hd.inter_of_Gδ hs htG hd').nonempty with ⟨x, hx₁, hx₂⟩
  exact hts hx₂ hx₁

中文:
定理 not_isMeagre_of_isGδ_of_dense
  条件: {s : Set X} (hs : IsGδ s) (hd : Dense s)
  证明: by
  intro h
  rcases mem_residual.1 h with ⟨t, hts, htG, hd'⟩
  rcases (hd.inter_of_Gδ hs htG hd').nonempty with ⟨x, hx₁, hx₂⟩
  exact hts hx₂ hx₁

Depends on / 依赖: hd.inter_of_G, mem_residual, nonempty
-/
theorem not_isMeagre_of_isGδ_of_dense {s : Set X} (hs : IsGδ s) (hd : Dense s) :
    ¬ IsMeagre s := by
  intro h
  rcases mem_residual.1 h with ⟨t, hts, htG, hd'⟩
  rcases (hd.inter_of_Gδ hs htG hd').nonempty with ⟨x, hx₁, hx₂⟩
  exact hts hx₂ hx₁

/--
theorem `not_isMeagre_of_mem_residual` / 定理 `not_isMeagre_of_mem_residual`

English:
theorem not_isMeagre_of_mem_residual
  given: {s : Set X} (hs : s in residual X)
  proof: by
  rcases (mem_residual (X := X)).1 hs with ⟨t, ht_sub, htGδ, ht_dense⟩
  intro hs_meagre
  exact not_isMeagre_of_isGδ_of_dense (X := X) htGδ ht_dense (hs_meagre.mono ht_sub)

中文:
定理 not_isMeagre_of_mem_residual
  条件: {s : Set X} (hs : s in residual X)
  证明: by
  rcases (mem_residual (X := X)).1 hs with ⟨t, ht_sub, htGδ, ht_dense⟩
  intro hs_meagre
  exact not_isMeagre_of_isGδ_of_dense (X := X) htGδ ht_dense (hs_meagre.mono ht_sub)

Depends on / 依赖: hs_meagre, hs_meagre.mono, ht_dense, ht_sub, mem_residual
-/
theorem not_isMeagre_of_mem_residual {s : Set X} (hs : s in residual X) :
    ¬ IsMeagre s := by
  rcases (mem_residual (X := X)).1 hs with ⟨t, ht_sub, htGδ, ht_dense⟩
  intro hs_meagre
  exact not_isMeagre_of_isGδ_of_dense (X := X) htGδ ht_dense (hs_meagre.mono ht_sub)

end BaireTheorem
