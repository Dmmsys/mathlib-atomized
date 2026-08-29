/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Finite.Sigma
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact open covered sets

In this file we define the notion of a compact-open covered set with respect to a family of
maps `fᵢ : X i → S`. A set `U` is compact-open covered by the family `fᵢ` if it is the finite
union of images of compact open sets in the `X i`.

This notion is not interesting, if the `fᵢ` are open maps (see `IsCompactOpenCovered.of_isOpenMap`).

This is used to define the fpqc topology of schemes, there a cover is given by a family of flat
morphisms such that every compact open is compact-open covered.

## Main results

- `IsCompactOpenCovered.of_isOpenMap`: If all the `fᵢ` are open maps, then every compact open
  of `S` is compact-open covered.
-/

@[expose] public section

open TopologicalSpace Opens

/--
Definition of `IsCompactOpenCovered` / `IsCompactOpenCovered` 的定义

English:
definition IsCompactOpenCovered
  signature: {S ι : Type*} {X : ι -> Type*} (f : forall i, X i -> S)
  body: exists (s : Set ι) (_ : s.Finite) (V : forall i in s, Opens (X i)),
    (forall (i : ι) (h : i in s), IsCompact (V i h).1) ∧
    ⋃ (i : ι) (h : i in s), (f i) '' (V i h) = U

中文:
定义 IsCompactOpenCovered
  签名: {S ι : 类型} {X : ι -> 类型} (f : 对任意 i, X i -> S)
  定义体: exists (s : Set ι) (_ : s.Finite) (V : forall i in s, Opens (X i)),
    (forall (i : ι) (h : i in s), IsCompact (V i h).1) ∧
    ⋃ (i : ι) (h : i in s), (f i) '' (V i h) = U

Depends on / 依赖: Finite, IsCompact, s.Finite
-/
def IsCompactOpenCovered {S ι : Type*} {X : ι -> Type*} (f : forall i, X i -> S)
    [forall i, TopologicalSpace (X i)] (U : Set S) : Prop :=
  exists (s : Set ι) (_ : s.Finite) (V : forall i in s, Opens (X i)),
    (forall (i : ι) (h : i in s), IsCompact (V i h).1) ∧
    ⋃ (i : ι) (h : i in s), (f i) '' (V i h) = U

namespace IsCompactOpenCovered

variable {S ι : Type*} {X : ι -> Type*} {f : forall i, X i -> S} [forall i, TopologicalSpace (X i)] {U : Set S}

/--
lemma `empty` / 引理 `empty`

English:
lemma empty
  statement: IsCompactOpenCovered f ∅
  proof: ⟨∅, Set.finite_empty, fun _ _ => ⟨∅, isOpen_empty⟩, fun _ _ => isCompact_empty, by simp⟩

中文:
引理 empty
  结论: IsCompactOpenCovered f ∅
  证明: ⟨∅, Set.finite_empty, fun _ _ => ⟨∅, isOpen_empty⟩, fun _ _ => isCompact_empty, by simp⟩

Depends on / 依赖: Set.finite_empty, finite_empty, isCompact_empty, isOpen_empty
-/
lemma empty : IsCompactOpenCovered f ∅ :=
  ⟨∅, Set.finite_empty, fun _ _ => ⟨∅, isOpen_empty⟩, fun _ _ => isCompact_empty, by simp⟩

/--
lemma `iff_of_unique` / 引理 `iff_of_unique`

English:
lemma iff_of_unique
  given: [Unique ι]
  proof: by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ => ?_, fun ⟨V, hc, h⟩ => ?_⟩
  · cases s.eq_empty_or_singleton_of_unique <;> aesop
  · refine ⟨{default}, Set.finite_singleton _, fun i h => h ▸ V, fun i => ?_, by simpa⟩
    rintro rfl
    simpa

中文:
引理 iff_of_unique
  条件: [唯一 ι]
  证明: by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ => ?_, fun ⟨V, hc, h⟩ => ?_⟩
  · cases s.eq_empty_or_singleton_of_unique <;> aesop
  · refine ⟨{default}, Set.finite_singleton _, fun i h => h ▸ V, fun i => ?_, by simpa⟩
    rintro rfl
    simpa

Depends on / 依赖: Set.finite_singleton, eq_empty_or_singleton_of_unique, finite_singleton, s.eq_empty_or_singleton_of_unique
-/
lemma iff_of_unique [Unique ι] :
    IsCompactOpenCovered f U ↔ exists (V : Opens (X default)), IsCompact V.1 ∧ f default '' V.1 = U := by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ => ?_, fun ⟨V, hc, h⟩ => ?_⟩
  · cases s.eq_empty_or_singleton_of_unique <;> aesop
  · refine ⟨{default}, Set.finite_singleton _, fun i h => h ▸ V, fun i => ?_, by simpa⟩
    rintro rfl
    simpa

/--
lemma `id_iff_isOpen_and_isCompact` / 引理 `id_iff_isOpen_and_isCompact`

English:
lemma id_iff_isOpen_and_isCompact
  given: [TopologicalSpace S]
  proof: by
  rw [iff_of_unique]
  refine ⟨fun ⟨V, hV, heq⟩ => ?_, fun ⟨ho, hc⟩ => ⟨⟨U, ho⟩, hc, by simp⟩⟩
  simp only [id_eq, Set.image_id', carrier_eq_coe, ← heq] at heq ⊢
  exact ⟨V.2, hV⟩

中文:
引理 id_iff_isOpen_and_isCompact
  条件: [拓扑空间 S]
  证明: by
  rw [iff_of_unique]
  refine ⟨fun ⟨V, hV, heq⟩ => ?_, fun ⟨ho, hc⟩ => ⟨⟨U, ho⟩, hc, by simp⟩⟩
  simp only [id_eq, Set.image_id', carrier_eq_coe, ← heq] at heq ⊢
  exact ⟨V.2, hV⟩

Depends on / 依赖: Set.image_id, carrier_eq_coe, id_eq, iff_of_unique, image_id
-/
lemma id_iff_isOpen_and_isCompact [TopologicalSpace S] :
    IsCompactOpenCovered (fun _ : Unit => id) U ↔ IsOpen U ∧ IsCompact U := by
  rw [iff_of_unique]
  refine ⟨fun ⟨V, hV, heq⟩ => ?_, fun ⟨ho, hc⟩ => ⟨⟨U, ho⟩, hc, by simp⟩⟩
  simp only [id_eq, Set.image_id', carrier_eq_coe, ← heq] at heq ⊢
  exact ⟨V.2, hV⟩

/--
lemma `iff_isCompactOpenCovered_sigmaMk` / 引理 `iff_isCompactOpenCovered_sigmaMk`

English:
lemma iff_isCompactOpenCovered_sigmaMk
  proof: by
  classical
  rw [iff_of_unique (ι := Unit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ => ?_, fun ⟨V, hc, heq⟩ => ?_⟩
  · refine ⟨⟨s.sigma fun i => if h : i in s then V i h else ∅, isOpen_sigma_iff.mpr ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i in s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      exact Set.isCompact_sigma hs fun i => (by simp_all)
    · aesop
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i in s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (t := t) hi]
      exact isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi => ⟨t i, this i hi⟩, fun i _ => hc i, ?_⟩
    simp_rw [coe_mk, ← heq, ← heq', Set.image_sigma_eq_iUnion, Function.comp_apply]

中文:
引理 iff_isCompactOpenCovered_sigmaMk
  证明: by
  classical
  rw [iff_of_unique (ι := Unit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ => ?_, fun ⟨V, hc, heq⟩ => ?_⟩
  · refine ⟨⟨s.sigma fun i => if h : i in s then V i h else ∅, isOpen_sigma_iff.mpr ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i in s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      exact Set.isCompact_sigma hs fun i => (by simp_all)
    · aesop
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i in s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (t := t) hi]
      exact isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi => ⟨t i, this i hi⟩, fun i _ => hc i, ?_⟩
    simp_rw [coe_mk, ← heq, ← heq', Set.image_sigma_eq_iUnion, Function.comp_apply]

Depends on / 依赖: IsOpen, Set.isCompact_sigma, Set.mk_preimage_sigma, classical, hc.sigma_exists_finite_sigma_eq, iff_of_unique, isCompact_sigma, isOpen_sigma_iff, isOpen_sigma_iff.mpr, mk_preimage_sigma, s.sigma, sigma_exists_finite_sigma_eq
-/
lemma iff_isCompactOpenCovered_sigmaMk :
    IsCompactOpenCovered f U ↔
      IsCompactOpenCovered (fun (_ : Unit) (p : Σ i : ι, X i) => f p.1 p.2) U := by
  classical
  rw [iff_of_unique (ι := Unit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ => ?_, fun ⟨V, hc, heq⟩ => ?_⟩
  · refine ⟨⟨s.sigma fun i => if h : i in s then V i h else ∅, isOpen_sigma_iff.mpr ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i in s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      exact Set.isCompact_sigma hs fun i => (by simp_all)
    · aesop
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i in s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (t := t) hi]
      exact isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi => ⟨t i, this i hi⟩, fun i _ => hc i, ?_⟩
    simp_rw [coe_mk, ← heq, ← heq', Set.image_sigma_eq_iUnion, Function.comp_apply]

/--
lemma `of_iUnion_eq_of_finite` / 引理 `of_iUnion_eq_of_finite`

English:
lemma of_iUnion_eq_of_finite
  statement: {κ : Type*} [Finite κ] (s : κ -> Set S) (hs : ⋃ i, s i = U)
  proof: by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique]
  have (i : κ) : exists (V : Opens (Σ i, X i)), IsCompact V.1 ∧ (f _ ·.snd) '' V.1 = s i := by
    convert! H i; rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  choose V hVeq hVc using this
  exact ⟨⨆ i, V i, by simpa using isCompact_iUnion hVeq, by simp_all [Set.image_iUnion, ← hs]⟩

中文:
引理 of_iUnion_eq_of_finite
  结论: {κ : 类型} [有限 κ] (s : κ -> 集合 S) (hs : ⋃ i, s i = U)
  证明: by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique]
  have (i : κ) : exists (V : Opens (Σ i, X i)), IsCompact V.1 ∧ (f _ ·.snd) '' V.1 = s i := by
    convert! H i; rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  choose V hVeq hVc using this
  exact ⟨⨆ i, V i, by simpa using isCompact_iUnion hVeq, by simp_all [Set.image_iUnion, ← hs]⟩

Depends on / 依赖: IsCompact, Set.image_iUnion, convert, iff_isCompactOpenCovered_sigmaMk, iff_of_unique, image_iUnion, isCompact_iUnion
-/
lemma of_iUnion_eq_of_finite {κ : Type*} [Finite κ] (s : κ -> Set S) (hs : ⋃ i, s i = U)
    (H : forall i, IsCompactOpenCovered f (s i)) : IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique]
  have (i : κ) : exists (V : Opens (Σ i, X i)), IsCompact V.1 ∧ (f _ ·.snd) '' V.1 = s i := by
    convert! H i; rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  choose V hVeq hVc using this
  exact ⟨⨆ i, V i, by simpa using isCompact_iUnion hVeq, by simp_all [Set.image_iUnion, ← hs]⟩

/--
lemma `of_biUnion_eq_of_finite` / 引理 `of_biUnion_eq_of_finite`

English:
lemma of_biUnion_eq_of_finite
  statement: (s : Set (Set S)) (hs : ⋃ t in s, t = U) (hf : s.Finite)
  proof: by
  have := hf.to_subtype
  exact of_iUnion_eq_of_finite (fun i : s => i.1) (by simpa) (by simpa)

中文:
引理 of_biUnion_eq_of_finite
  结论: (s : 集合 (集合 S)) (hs : ⋃ t in s, t = U) (hf : s.有限)
  证明: by
  have := hf.to_subtype
  exact of_iUnion_eq_of_finite (fun i : s => i.1) (by simpa) (by simpa)

Depends on / 依赖: hf.to_subtype, of_iUnion_eq_of_finite, to_subtype
-/
lemma of_biUnion_eq_of_finite (s : Set (Set S)) (hs : ⋃ t in s, t = U) (hf : s.Finite)
    (H : forall t in s, IsCompactOpenCovered f t) : IsCompactOpenCovered f U := by
  have := hf.to_subtype
  exact of_iUnion_eq_of_finite (fun i : s => i.1) (by simpa) (by simpa)

/--
lemma `of_biUnion_eq_of_isCompact` / 引理 `of_biUnion_eq_of_isCompact`

English:
lemma of_biUnion_eq_of_isCompact
  statement: [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
  proof: by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun V : s => V.1) (fun V => V.1.2) (by simp [← hs])
  refine of_biUnion_eq_of_finite (SetLike.coe '' (t.image Subtype.val : Set (Opens S))) ?_ ?_ ?_
  · exact subset_antisymm (fun x h => by aesop) (subset_trans ht <| by simp)
  · exact Set.toFinite _
  · grind

中文:
引理 of_biUnion_eq_of_isCompact
  结论: [拓扑空间 S] {U : 集合 S} (hU : 是紧集 U)
  证明: by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun V : s => V.1) (fun V => V.1.2) (by simp [← hs])
  refine of_biUnion_eq_of_finite (SetLike.coe '' (t.image Subtype.val : Set (Opens S))) ?_ ?_ ?_
  · exact subset_antisymm (fun x h => by aesop) (subset_trans ht <| by simp)
  · exact Set.toFinite _
  · grind

Depends on / 依赖: Set.toFinite, SetLike, SetLike.coe, Subtype, Subtype.val, classical, elim_finite_subcover, hU.elim_finite_subcover, of_biUnion_eq_of_finite, subset_antisymm, subset_trans, t.image, toFinite
-/
lemma of_biUnion_eq_of_isCompact [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
    (s : Set (Opens S)) (hs : ⋃ t in s, t = U) (H : forall t in s, IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun V : s => V.1) (fun V => V.1.2) (by simp [← hs])
  refine of_biUnion_eq_of_finite (SetLike.coe '' (t.image Subtype.val : Set (Opens S))) ?_ ?_ ?_
  · exact subset_antisymm (fun x h => by aesop) (subset_trans ht <| by simp)
  · exact Set.toFinite _
  · grind

/--
lemma `of_isCompact_of_forall_exists_isCompactOpenCovered` / 引理 `of_isCompact_of_forall_exists_isCompactOpenCovered`

English:
lemma of_isCompact_of_forall_exists_isCompactOpenCovered
  statement: [TopologicalSpace S] {U : Set S}
  proof: by
  choose Us hU' hUx hUo hU'' using H
  refine of_biUnion_eq_of_isCompact hU { Us x h | (x : S) (h : x in U) } ?_ ?_
  · refine subset_antisymm (fun x => ?_) fun x hx => ?_
    · simp [Opens.forall]
      grind
    · simpa using ⟨⟨Us x hx, hUo _ _⟩, ⟨x, by simpa⟩, hUx _ _⟩
  · grind

中文:
引理 of_isCompact_of_对任意_存在_isCompactOpenCovered
  结论: [拓扑空间 S] {U : 集合 S}
  证明: by
  choose Us hU' hUx hUo hU'' using H
  refine of_biUnion_eq_of_isCompact hU { Us x h | (x : S) (h : x in U) } ?_ ?_
  · refine subset_antisymm (fun x => ?_) fun x hx => ?_
    · simp [Opens.forall]
      grind
    · simpa using ⟨⟨Us x hx, hUo _ _⟩, ⟨x, by simpa⟩, hUx _ _⟩
  · grind

Depends on / 依赖: Opens.forall, of_biUnion_eq_of_isCompact, subset_antisymm
-/
lemma of_isCompact_of_forall_exists_isCompactOpenCovered [TopologicalSpace S] {U : Set S}
    (hU : IsCompact U) (H : forall x in U, exists t subseteq U, x in t ∧ IsOpen t ∧ IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  choose Us hU' hUx hUo hU'' using H
  refine of_biUnion_eq_of_isCompact hU { Us x h | (x : S) (h : x in U) } ?_ ?_
  · refine subset_antisymm (fun x => ?_) fun x hx => ?_
    · simp [Opens.forall]
      grind
    · simpa using ⟨⟨Us x hx, hUo _ _⟩, ⟨x, by simpa⟩, hUx _ _⟩
  · grind

/--
lemma `image` / 引理 `image`

English:
lemma image
  given: {i : ι} (V : Opens (X i)) (hV : IsCompact (X := X i) V)
  proof: by
  refine ⟨{i}, Set.finite_singleton i, fun j hj => hj ▸ V, by rintro i rfl; simpa, by simp⟩

中文:
引理 像
  条件: {i : ι} (V : Opens (X i)) (hV : 是紧集 (X := X i) V)
  证明: by
  refine ⟨{i}, Set.finite_singleton i, fun j hj => hj ▸ V, by rintro i rfl; simpa, by simp⟩
-/
lemma image {i : ι} (V : Opens (X i)) (hV : IsCompact (X := X i) V) :
    IsCompactOpenCovered f (f i '' V) := by
  refine ⟨{i}, Set.finite_singleton i, fun j hj => hj ▸ V, by rintro i rfl; simpa, by simp⟩

/--
lemma `of_finite` / 引理 `of_finite`

English:
lemma of_finite
  statement: {U : Set S} {κ : Type*} [Finite κ] (a : κ -> ι) (V : forall k, Opens (X (a k)))
  proof: of_iUnion_eq_of_finite _ hU (fun _ => .image _ (hV _))

中文:
引理 of_finite
  结论: {U : 集合 S} {κ : 类型} [有限 κ] (a : κ -> ι) (V : 对任意 k, Opens (X (a k)))
  证明: of_iUnion_eq_of_finite _ hU (fun _ => .image _ (hV _))

Depends on / 依赖: of_iUnion_eq_of_finite
-/
lemma of_finite {U : Set S} {κ : Type*} [Finite κ] (a : κ -> ι) (V : forall k, Opens (X (a k)))
    (hV : forall k, IsCompact (V k).1) (hU : ⋃ k, f (a k) '' V k = U) :
    IsCompactOpenCovered f U :=
  of_iUnion_eq_of_finite _ hU (fun _ => .image _ (hV _))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_mem_of_isBasis` / 引理 `exists_mem_of_isBasis`

English:
lemma exists_mem_of_isBasis
  statement: {B : forall i, Set (Opens (X i))} (hB : forall i, IsBasis (B i))
  proof: by
  suffices h : exists (κ : Type _) (_ : Finite κ) (a : κ -> ι) (V : forall i, Opens (X (a i))),
      (forall i, V i in B (a i)) ∧ (forall i, IsCompact (V i).1) ∧ ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i => V _, fun i => hB _, ?_⟩
    simp [← hU, ← (Fintype.equivFin κ).symm.surjective.iUnion_comp, Function.comp_apply]
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  choose Us UsB hUsf hUs using fun i : s => (hB i.1).exists_finite_of_isCompact (hc i i.2)
  let σ := Σ i : s, Us i
  have : Finite s := hs
  have (i : _) : Finite (Us i) := hUsf i
  refine ⟨σ, inferInstance, fun i => i.1.1, fun i => i.2.1, fun i => UsB _ (by simp),
      fun _ => hBc _ _ (UsB _ (by simp)), ?_⟩
  rw [← hunion]
  ext x
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi, o, ho⟩ => by aesop, fun ⟨i, hi, h, hmem, heq⟩ => ?_⟩
  rw [hUs ⟨i]; rw [hi⟩]; rw [coe_sSup]; rw [Set.mem_iUnion] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq

中文:
引理 存在_mem_of_isBasis
  结论: {B : 对任意 i, 集合 (Opens (X i))} (hB : 对任意 i, 是基 (B i))
  证明: by
  suffices h : exists (κ : Type _) (_ : Finite κ) (a : κ -> ι) (V : forall i, Opens (X (a i))),
      (forall i, V i in B (a i)) ∧ (forall i, IsCompact (V i).1) ∧ ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i => V _, fun i => hB _, ?_⟩
    simp [← hU, ← (Fintype.equivFin κ).symm.surjective.iUnion_comp, Function.comp_apply]
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  choose Us UsB hUsf hUs using fun i : s => (hB i.1).exists_finite_of_isCompact (hc i i.2)
  let σ := Σ i : s, Us i
  have : Finite s := hs
  have (i : _) : Finite (Us i) := hUsf i
  refine ⟨σ, inferInstance, fun i => i.1.1, fun i => i.2.1, fun i => UsB _ (by simp),
      fun _ => hBc _ _ (UsB _ (by simp)), ?_⟩
  rw [← hunion]
  ext x
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi, o, ho⟩ => by aesop, fun ⟨i, hi, h, hmem, heq⟩ => ?_⟩
  rw [hUs ⟨i]; rw [hi⟩]; rw [coe_sSup]; rw [Set.mem_iUnion] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq

Depends on / 依赖: Finite, Fintype, Fintype.card, Fintype.equivFin, Function, Function.comp_apply, IsCompact, comp_apply, equivFin, hunion, iUnion_comp, nonempty_fintype, surjective, symm.surjective.iUnion_comp
-/
lemma exists_mem_of_isBasis {B : forall i, Set (Opens (X i))} (hB : forall i, IsBasis (B i))
    (hBc : forall (i : ι), forall U in B i, IsCompact U.1)
    {U : Set S} (hU : IsCompactOpenCovered f U) :
    exists (n : Nat) (a : Fin n -> ι) (V : forall i, Opens (X (a i))),
      (forall i, V i in B (a i)) ∧ ⋃ i, f (a i) '' V i = U := by
  suffices h : exists (κ : Type _) (_ : Finite κ) (a : κ -> ι) (V : forall i, Opens (X (a i))),
      (forall i, V i in B (a i)) ∧ (forall i, IsCompact (V i).1) ∧ ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i => V _, fun i => hB _, ?_⟩
    simp [← hU, ← (Fintype.equivFin κ).symm.surjective.iUnion_comp, Function.comp_apply]
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  choose Us UsB hUsf hUs using fun i : s => (hB i.1).exists_finite_of_isCompact (hc i i.2)
  let σ := Σ i : s, Us i
  have : Finite s := hs
  have (i : _) : Finite (Us i) := hUsf i
  refine ⟨σ, inferInstance, fun i => i.1.1, fun i => i.2.1, fun i => UsB _ (by simp),
      fun _ => hBc _ _ (UsB _ (by simp)), ?_⟩
  rw [← hunion]
  ext x
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi, o, ho⟩ => by aesop, fun ⟨i, hi, h, hmem, heq⟩ => ?_⟩
  rw [hUs ⟨i]; rw [hi⟩]; rw [coe_sSup]; rw [Set.mem_iUnion] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq

/--
lemma `of_finite_of_isSpectralMap` / 引理 `of_finite_of_isSpectralMap`

English:
lemma of_finite_of_isSpectralMap
  statement: [Finite ι] [TopologicalSpace S]
  proof: by
  refine ⟨.univ, Set.finite_univ, fun i _ => ⟨f i ⁻¹' U, hU.preimage (hf i).1⟩,
    fun i _ => hc.preimage_of_isOpen (hf i) hU, subset_antisymm (by simp) fun x hx => ?_⟩
  obtain ⟨i, y, rfl⟩ := hs x hx
  simpa using ⟨i, y, hx, rfl⟩

中文:
引理 of_finite_of_isSpectralMap
  结论: [有限 ι] [拓扑空间 S]
  证明: by
  refine ⟨.univ, Set.finite_univ, fun i _ => ⟨f i ⁻¹' U, hU.preimage (hf i).1⟩,
    fun i _ => hc.preimage_of_isOpen (hf i) hU, subset_antisymm (by simp) fun x hx => ?_⟩
  obtain ⟨i, y, rfl⟩ := hs x hx
  simpa using ⟨i, y, hx, rfl⟩

Depends on / 依赖: Set.finite_univ, finite_univ, hU.preimage, hc.preimage_of_isOpen, preimage, preimage_of_isOpen, subset_antisymm
-/
lemma of_finite_of_isSpectralMap [Finite ι] [TopologicalSpace S]
    (hf : forall i, IsSpectralMap (f i)) {U : Set S} (hs : forall x in U, exists i, x in Set.range (f i))
    (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  refine ⟨.univ, Set.finite_univ, fun i _ => ⟨f i ⁻¹' U, hU.preimage (hf i).1⟩,
    fun i _ => hc.preimage_of_isOpen (hf i) hU, subset_antisymm (by simp) fun x hx => ?_⟩
  obtain ⟨i, y, rfl⟩ := hs x hx
  simpa using ⟨i, y, hx, rfl⟩

/--
lemma `of_isOpenMap` / 引理 `of_isOpenMap`

English:
lemma of_isOpenMap
  statement: [TopologicalSpace S] [forall i, PrespectralSpace (X i)]
  proof: by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_prespectralSpace
      (continuous_sigma_iff.mpr hfc) (fun x hx => ?_) hU hc
  simpa using hs x hx

中文:
引理 of_isOpenMap
  结论: [拓扑空间 S] [对任意 i, Prespectral空间 (X i)]
  证明: by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_prespectralSpace
      (continuous_sigma_iff.mpr hfc) (fun x hx => ?_) hU hc
  simpa using hs x hx

Depends on / 依赖: continuous_sigma_iff, continuous_sigma_iff.mpr, exists_opens_image_eq_of_prespectralSpace, iff_isCompactOpenCovered_sigmaMk, iff_of_unique, isOpenMap_sigma, isOpenMap_sigma.mpr
-/
lemma of_isOpenMap [TopologicalSpace S] [forall i, PrespectralSpace (X i)]
    (hfc : forall i, Continuous (f i)) (h : forall i, IsOpenMap (f i))
    {U : Set S} (hs : forall x in U, exists i, x in Set.range (f i)) (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_prespectralSpace
      (continuous_sigma_iff.mpr hfc) (fun x hx => ?_) hU hc
  simpa using hs x hx

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  statement: [forall i, PrespectralSpace (X i)] [TopologicalSpace S]
  proof: by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique] at hU ⊢
  let p : (Σ i, Y i) -> (Σ i, X i) := Sigma.map a t
  have hcomp : (fun x => f x.1 x.2) ∘ p = fun x => g x.1 x.2 := by
    ext
    simp [hge, p, Sigma.map]
  have hp : Continuous p := Continuous.sigma_map ht
  have hf : Continuous (fun p : Σ i, X i => f p.1 p.2) := by simp [hf]
  obtain ⟨V, hV, heq⟩ := hU
  obtain ⟨K, hK, ho, hVK, hKU⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
(hV.image hp) (ho.preimage hf) by
    simp [← heq, ← Set.preimage_comp, hcomp, Set.subset_preimage_image]
  refine ⟨⟨K, ho⟩, hK, subset_antisymm (by simpa) ?_⟩
  rw [← heq]; rw [← hcomp]; rw [Set.image_comp]
  exact subset_trans (Set.image_mono hVK) (by simp)

中文:
引理 of_comp
  结论: [对任意 i, Prespectral空间 (X i)] [拓扑空间 S]
  证明: by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique] at hU ⊢
  let p : (Σ i, Y i) -> (Σ i, X i) := Sigma.map a t
  have hcomp : (fun x => f x.1 x.2) ∘ p = fun x => g x.1 x.2 := by
    ext
    simp [hge, p, Sigma.map]
  have hp : Continuous p := Continuous.sigma_map ht
  have hf : Continuous (fun p : Σ i, X i => f p.1 p.2) := by simp [hf]
  obtain ⟨V, hV, heq⟩ := hU
  obtain ⟨K, hK, ho, hVK, hKU⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
(hV.image hp) (ho.preimage hf) by
    simp [← heq, ← Set.preimage_comp, hcomp, Set.subset_preimage_image]
  refine ⟨⟨K, ho⟩, hK, subset_antisymm (by simpa) ?_⟩
  rw [← heq]; rw [← hcomp]; rw [Set.image_comp]
  exact subset_trans (Set.image_mono hVK) (by simp)

Depends on / 依赖: Continuous, Continuous.sigma_map, PrespectralSpace, PrespectralSpace.exists_isCompact_and_isOpen_between, Set.prei, Sigma.map, exists_isCompact_and_isOpen_between, hV.image, ho.preimage, iff_isCompactOpenCovered_sigmaMk, iff_of_unique, preimage, sigma_map
-/
lemma of_comp [forall i, PrespectralSpace (X i)] [TopologicalSpace S]
    {σ : Type*} {Y : σ -> Type*} [forall i, TopologicalSpace (Y i)]
    (g : forall i, Y i -> S) {a : σ -> ι} (t : forall i, Y i -> X (a i)) (ht : forall i, Continuous (t i))
    (hge : forall i, g i = f (a i) ∘ t i)
    (hf : forall i, Continuous (f i)) {U : Set S} (ho : IsOpen U) (hU : IsCompactOpenCovered g U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk]; rw [iff_of_unique] at hU ⊢
  let p : (Σ i, Y i) -> (Σ i, X i) := Sigma.map a t
  have hcomp : (fun x => f x.1 x.2) ∘ p = fun x => g x.1 x.2 := by
    ext
    simp [hge, p, Sigma.map]
  have hp : Continuous p := Continuous.sigma_map ht
  have hf : Continuous (fun p : Σ i, X i => f p.1 p.2) := by simp [hf]
  obtain ⟨V, hV, heq⟩ := hU
  obtain ⟨K, hK, ho, hVK, hKU⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
(hV.image hp) (ho.preimage hf) by
    simp [← heq, ← Set.preimage_comp, hcomp, Set.subset_preimage_image]
  refine ⟨⟨K, ho⟩, hK, subset_antisymm (by simpa) ?_⟩
  rw [← heq]; rw [← hcomp]; rw [Set.image_comp]
  exact subset_trans (Set.image_mono hVK) (by simp)

end IsCompactOpenCovered
