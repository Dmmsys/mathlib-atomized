/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets in uniform spaces

* `compactSpace_uniformity`: On a compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.

-/

public section

universe u v ua ub uc ud

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

section Compact

open Uniformity Set Filter UniformSpace
open scoped SetRel Topology

variable [UniformSpace α] {K : Set α}

/--
theorem `lebesgue_number_lemma` / 定理 `lebesgue_number_lemma`

English:
theorem lebesgue_number_lemma
  statement: {ι : Sort*} {U : ι -> Set α} (hK : IsCompact K)
  proof: by
  have : forall x in K, exists i, exists V in 𝓤 α, ball x (V ○ V) subseteq U i := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff]; rw [nhds_eq_comap_uniformity]; rw [← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.relComp monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx => ball x (W x hx)) (fun x hx => ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x in t, W x x.2, (biInter_finset_mem _).2 fun x _ => hW x x.2, fun x hx => ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz => hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩

中文:
定理 lebesgue_number_lemma
  结论: {ι : 类型层*} {U : ι -> 集合 α} (hK : 是紧集 K)
  证明: by
  have : forall x in K, exists i, exists V in 𝓤 α, ball x (V ○ V) subseteq U i := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff]; rw [nhds_eq_comap_uniformity]; rw [← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.relComp monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx => ball x (W x hx)) (fun x hx => ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x in t, W x x.2, (biInter_finset_mem _).2 fun x _ => hW x x.2, fun x hx => ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz => hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩

Depends on / 依赖: _comp_uniformity, ball_mem_nhds, basis_sets, elim_nhds_subcover, hK.elim_nhds_subcover, hcover, mem_iUnion, mem_iff, mem_nhds_iff, monotone_id, monotone_id.relComp, nhds_eq_comap_uniformity, relComp, subseteq
-/
theorem lebesgue_number_lemma {ι : Sort*} {U : ι -> Set α} (hK : IsCompact K)
    (hopen : forall i, IsOpen (U i)) (hcover : K subseteq ⋃ i, U i) :
    exists V in 𝓤 α, forall x in K, exists i, ball x V subseteq U i := by
  have : forall x in K, exists i, exists V in 𝓤 α, ball x (V ○ V) subseteq U i := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff]; rw [nhds_eq_comap_uniformity]; rw [← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.relComp monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx => ball x (W x hx)) (fun x hx => ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x in t, W x x.2, (biInter_finset_mem _).2 fun x _ => hW x x.2, fun x hx => ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz => hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩

/--
theorem `lebesgue_number_lemma_nhds'` / 定理 `lebesgue_number_lemma_nhds'`

English:
theorem lebesgue_number_lemma_nhds'
  statement: {U : (x : α) -> x in K -> Set α} (hK : IsCompact K)
  proof: by
  rcases lebesgue_number_lemma (U := fun x : K => interior (U x x.2)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

中文:
定理 lebesgue_number_lemma_nhds'
  结论: {U : (x : α) -> x in K -> 集合 α} (hK : 是紧集 K)
  证明: by
  rcases lebesgue_number_lemma (U := fun x : K => interior (U x x.2)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

Depends on / 依赖: V_uni, hy.trans, interior, interior_subset, isOpen_interior, lebesgue_number_lemma, mem_iUnion, mem_interior_iff_mem_nhds
-/
theorem lebesgue_number_lemma_nhds' {U : (x : α) -> x in K -> Set α} (hK : IsCompact K)
    (hU : forall x hx, U x hx in 𝓝 x) : exists V in 𝓤 α, forall x in K, exists y : K, ball x V subseteq U y y.2 := by
  rcases lebesgue_number_lemma (U := fun x : K => interior (U x x.2)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

/--
theorem `lebesgue_number_lemma_nhds` / 定理 `lebesgue_number_lemma_nhds`

English:
theorem lebesgue_number_lemma_nhds
  given: {U : α -> Set α} (hK : IsCompact K) (hU : forall x in K, U x in 𝓝 x)
  proof: by
  rcases lebesgue_number_lemma (U := fun x => interior (U x)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

中文:
定理 lebesgue_number_lemma_nhds
  条件: {U : α -> 集合 α} (hK : 是紧集 K) (hU : 对任意 x in K, U x in 𝓝 x)
  证明: by
  rcases lebesgue_number_lemma (U := fun x => interior (U x)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

Depends on / 依赖: V_uni, hy.trans, interior, interior_subset, isOpen_interior, lebesgue_number_lemma, mem_iUnion, mem_interior_iff_mem_nhds
-/
theorem lebesgue_number_lemma_nhds {U : α -> Set α} (hK : IsCompact K) (hU : forall x in K, U x in 𝓝 x) :
    exists V in 𝓤 α, forall x in K, exists y, ball x V subseteq U y := by
  rcases lebesgue_number_lemma (U := fun x => interior (U x)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

/--
theorem `lebesgue_number_lemma_nhdsWithin'` / 定理 `lebesgue_number_lemma_nhdsWithin'`

English:
theorem lebesgue_number_lemma_nhdsWithin'
  statement: {U : (x : α) -> x in K -> Set α} (hK : IsCompact K)
  proof: (lebesgue_number_lemma_nhds' hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

中文:
定理 lebesgue_number_lemma_nhdsWithin'
  结论: {U : (x : α) -> x in K -> 集合 α} (hK : 是紧集 K)
  证明: (lebesgue_number_lemma_nhds' hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

Depends on / 依赖: Filter, Filter.mem_inf_principal, V_uni, inter_subset, lebesgue_number_lemma_nhds, mem_inf_principal
-/
theorem lebesgue_number_lemma_nhdsWithin' {U : (x : α) -> x in K -> Set α} (hK : IsCompact K)
    (hU : forall x hx, U x hx in 𝓝[K] x) : exists V in 𝓤 α, forall x in K, exists y : K, ball x V inter K subseteq U y y.2 :=
  (lebesgue_number_lemma_nhds' hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

/--
theorem `lebesgue_number_lemma_nhdsWithin` / 定理 `lebesgue_number_lemma_nhdsWithin`

English:
theorem lebesgue_number_lemma_nhdsWithin
  statement: {U : α -> Set α} (hK : IsCompact K)
  proof: (lebesgue_number_lemma_nhds hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

中文:
定理 lebesgue_number_lemma_nhdsWithin
  结论: {U : α -> 集合 α} (hK : 是紧集 K)
  证明: (lebesgue_number_lemma_nhds hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

Depends on / 依赖: Filter, Filter.mem_inf_principal, V_uni, inter_subset, lebesgue_number_lemma_nhds, mem_inf_principal
-/
theorem lebesgue_number_lemma_nhdsWithin {U : α -> Set α} (hK : IsCompact K)
    (hU : forall x in K, U x in 𝓝[K] x) : exists V in 𝓤 α, forall x in K, exists y, ball x V inter K subseteq U y :=
  (lebesgue_number_lemma_nhds hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

/--
theorem `Filter.HasBasis.lebesgue_number_lemma` / 定理 `Filter.HasBasis.lebesgue_number_lemma`

English:
theorem Filter.HasBasis.lebesgue_number_lemma
  statement: {ι' ι : Sort*} {p : ι' -> Prop}
  proof: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx => (ht x hx).imp fun i hi => Subset.trans (ball_mono hst _) hi

中文:
定理 滤子.有基.lebesgue_number_lemma
  结论: {ι' ι : 类型层*} {p : ι' -> 命题}
  证明: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx => (ht x hx).imp fun i hi => Subset.trans (ball_mono hst _) hi
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma {ι' ι : Sort*} {p : ι' -> Prop}
    {V : ι' -> Set (α × α)} {U : ι -> Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hopen : forall j, IsOpen (U j)) (hcover : K subseteq ⋃ j, U j) :
    exists i, p i ∧ forall x in K, exists j, ball x (V i) subseteq U j := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx => (ht x hx).imp fun i hi => Subset.trans (ball_mono hst _) hi

/--
theorem `Filter.HasBasis.lebesgue_number_lemma_nhds'` / 定理 `Filter.HasBasis.lebesgue_number_lemma_nhds'`

English:
theorem Filter.HasBasis.lebesgue_number_lemma_nhds'
  statement: {ι' : Sort*} {p : ι' -> Prop}
  proof: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds' hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp fun y hy => Subset.trans (ball_mono hst _) hy

中文:
定理 滤子.有基.lebesgue_number_lemma_nhds'
  结论: {ι' : 类型层*} {p : ι' -> 命题}
  证明: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds' hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp fun y hy => Subset.trans (ball_mono hst _) hy
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhds' {ι' : Sort*} {p : ι' -> Prop}
    {V : ι' -> Set (α × α)} {U : (x : α) -> x in K -> Set α} (hbasis : (𝓤 α).HasBasis p V)
    (hK : IsCompact K) (hU : forall x hx, U x hx in 𝓝 x) :
    exists i, p i ∧ forall x in K, exists y : K, ball x (V i) subseteq U y y.2 := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds' hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp fun y hy => Subset.trans (ball_mono hst _) hy

/--
theorem `Filter.HasBasis.lebesgue_number_lemma_nhds` / 定理 `Filter.HasBasis.lebesgue_number_lemma_nhds`

English:
theorem Filter.HasBasis.lebesgue_number_lemma_nhds
  statement: {ι' : Sort*} {p : ι' -> Prop}
  proof: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp fun y hy => Subset.trans (ball_mono hst _) hy

中文:
定理 滤子.有基.lebesgue_number_lemma_nhds
  结论: {ι' : 类型层*} {p : ι' -> 命题}
  证明: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp fun y hy => Subset.trans (ball_mono hst _) hy
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhds {ι' : Sort*} {p : ι' -> Prop}
    {V : ι' -> Set (α × α)} {U : α -> Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hU : forall x in K, U x in 𝓝 x) : exists i, p i ∧ forall x in K, exists y, ball x (V i) subseteq U y := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp fun y hy => Subset.trans (ball_mono hst _) hy

/--
theorem `Filter.HasBasis.lebesgue_number_lemma_nhdsWithin'` / 定理 `Filter.HasBasis.lebesgue_number_lemma_nhdsWithin'`

English:
theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin'
  statement: {ι' : Sort*} {p : ι' -> Prop}
  proof: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin' hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp
    fun y hy => Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

中文:
定理 滤子.有基.lebesgue_number_lemma_nhdsWithin'
  结论: {ι' : 类型层*} {p : ι' -> 命题}
  证明: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin' hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp
    fun y hy => Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin' {ι' : Sort*} {p : ι' -> Prop}
    {V : ι' -> Set (α × α)} {U : (x : α) -> x in K -> Set α} (hbasis : (𝓤 α).HasBasis p V)
    (hK : IsCompact K) (hU : forall x hx, U x hx in 𝓝[K] x) :
    exists i, p i ∧ forall x in K, exists y : K, ball x (V i) inter K subseteq U y y.2 := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin' hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp
    fun y hy => Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

/--
theorem `Filter.HasBasis.lebesgue_number_lemma_nhdsWithin` / 定理 `Filter.HasBasis.lebesgue_number_lemma_nhdsWithin`

English:
theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin
  statement: {ι' : Sort*} {p : ι' -> Prop}
  proof: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp
    fun y hy => Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

中文:
定理 滤子.有基.lebesgue_number_lemma_nhdsWithin
  结论: {ι' : 类型层*} {p : ι' -> 命题}
  证明: by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp
    fun y hy => Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin {ι' : Sort*} {p : ι' -> Prop}
    {V : ι' -> Set (α × α)} {U : α -> Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hU : forall x in K, U x in 𝓝[K] x) : exists i, p i ∧ forall x in K, exists y, ball x (V i) inter K subseteq U y := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin hK hU)
  exact fun s t hst ht x hx => (ht x hx).imp
    fun y hy => Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

/--
theorem `lebesgue_number_lemma_sUnion` / 定理 `lebesgue_number_lemma_sUnion`

English:
theorem lebesgue_number_lemma_sUnion
  statement: {S : Set (Set α)}
  proof: by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover

中文:
定理 lebesgue_number_lemma_sUnion
  结论: {S : 集合 (集合 α)}
  证明: by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover

Depends on / 依赖: hcover, lebesgue_number_lemma, sUnion_eq_iUnion
-/
theorem lebesgue_number_lemma_sUnion {S : Set (Set α)}
    (hK : IsCompact K) (hopen : forall s in S, IsOpen s) (hcover : K subseteq ⋃₀ S) :
    exists V in 𝓤 α, forall x in K, exists s in S, ball x V subseteq s := by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover

/--
theorem `IsCompact.nhdsSet_basis_uniformity` / 定理 `IsCompact.nhdsSet_basis_uniformity`

English:
theorem IsCompact.nhdsSet_basis_uniformity
  statement: {p : ι -> Prop} {V : ι -> Set (α × α)}
  proof: by
    constructor
    · intro H
      have HKU : K subseteq ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : exists i, p i ∧ ⋃ x in K, ball x (V i) subseteq interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ => isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ => ?_) hi
exact ball_mem_nhds _ hbasis.mem_of_mem hpi

中文:
定理 是紧集.nhdsSet_basis_uniformity
  结论: {p : ι -> 命题} {V : ι -> 集合 (α × α)}
  证明: by
    constructor
    · intro H
      have HKU : K subseteq ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : exists i, p i ∧ ⋃ x in K, ball x (V i) subseteq interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ => isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ => ?_) hi
exact ball_mem_nhds _ hbasis.mem_of_mem hpi

Depends on / 依赖: bUnion_mem_nhdsSet, ball_mem_nhds, hbasis, hbasis.lebesgue_number_lemma, hbasis.mem_of_mem, hi.trans, iUnion_const, interior, interior_subset, isOpen_interior, lebesgue_number_lemma, mem_of_mem, mem_of_superset, subset_interior_iff_mem_nhdsSet, subseteq
-/
theorem IsCompact.nhdsSet_basis_uniformity {p : ι -> Prop} {V : ι -> Set (α × α)}
    (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis p fun i => ⋃ x in K, ball x (V i) where
  mem_iff' U := by
    constructor
    · intro H
      have HKU : K subseteq ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : exists i, p i ∧ ⋃ x in K, ball x (V i) subseteq interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ => isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ => ?_) hi
exact ball_mem_nhds _ hbasis.mem_of_mem hpi

-- TODO: move to a separate file, golf using the regularity of a uniform space.
/--
theorem `Disjoint.exists_uniform_thickening` / 定理 `Disjoint.exists_uniform_thickening`

English:
theorem Disjoint.exists_uniform_thickening
  statement: {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
  proof: by
  have : Bᶜ in 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hxa hxb) hb

中文:
定理 Disjoint.存在_uniform_thickening
  结论: {A B : 集合 α} (hA : 是紧集 A) (hB : 是闭集 B)
  证明: by
  have : Bᶜ in 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hxa hxb) hb

Depends on / 依赖: Filter, Filter.basis_sets, Set.disjoint_left.mpr, basis_sets, comp_symm_mem_uniformity_sets, disjoint_left, h.le_compl_right, hA.nhdsSet_basis_uniformity, hB.isOpen_compl.mem_nhdsSet.mpr, hVsymm, isOpen_compl, le_compl_right, mem_ball_symmetry, mem_comp_of_mem_ball, mem_iff, mem_nhdsSet, nhdsSet_basis_uniformity
-/
theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : exists V in 𝓤 α, Disjoint (⋃ x in A, ball x V) (⋃ x in B, ball x V) := by
  have : Bᶜ in 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hxa hxb) hb

/--
theorem `Disjoint.exists_uniform_thickening_of_basis` / 定理 `Disjoint.exists_uniform_thickening_of_basis`

English:
theorem Disjoint.exists_uniform_thickening_of_basis
  statement: {p : ι -> Prop} {s : ι -> Set (α × α)}
  proof: by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩

中文:
定理 Disjoint.存在_uniform_thickening_of_basis
  结论: {p : ι -> 命题} {s : ι -> 集合 (α × α)}
  证明: by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩

Depends on / 依赖: ball_mono, exists_uniform_thickening, h.exists_uniform_thickening, hU.mem_iff, hVAB.mono, mem_iff
-/
theorem Disjoint.exists_uniform_thickening_of_basis {p : ι -> Prop} {s : ι -> Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : exists i, p i ∧ Disjoint (⋃ x in A, ball x (s i)) (⋃ x in B, ball x (s i)) := by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩

/--
theorem `lebesgue_number_of_compact_open` / 定理 `lebesgue_number_of_compact_open`

English:
theorem lebesgue_number_of_compact_open
  statement: {K U : Set α} (hK : IsCompact K)
  proof: let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩

中文:
定理 lebesgue_number_of_compact_open
  结论: {K U : 集合 α} (hK : 是紧集 K)
  证明: let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩

Depends on / 依赖: hK.nhdsSet_basis_uniformity, hU.mem_nhdsSet, mem_iff, mem_nhdsSet, nhdsSet_basis_uniformity, uniformity_hasBasis_open
-/
theorem lebesgue_number_of_compact_open {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K subseteq U) : exists V in 𝓤 α, IsOpen V ∧ forall x in K, UniformSpace.ball x V subseteq U :=
  let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩


/--
theorem `nhdsSet_diagonal_eq_uniformity` / 定理 `nhdsSet_diagonal_eq_uniformity`

English:
theorem nhdsSet_diagonal_eq_uniformity
  given: [CompactSpace α]
  statement: 𝓝ˢ (diagonal α) = 𝓤 α
  proof: by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U in 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩

中文:
定理 nhdsSet_diagonal_eq_uniformity
  条件: [紧空间 α]
  结论: 𝓝ˢ (diagonal α) = 𝓤 α
  证明: by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U in 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩

Depends on / 依赖: HasBasis, antisymm, basis_sets, basis_sets.prod_self.comap, ge_iff, isCompact_diagonal, isCompact_diagonal.nhdsSet_basis_uniformity, mem_of_superset, nhdsSet_basis_uniformity, nhdsSet_diagonal_le_uniformity, nhdsSet_diagonal_le_uniformity.antisymm, prod_self, refl_mem_uniformity, uniformity_prod_eq_comap_prod
-/
theorem nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α := by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U in 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩

/--
theorem `compactSpace_uniformity` / 定理 `compactSpace_uniformity`

English:
theorem compactSpace_uniformity
  given: [CompactSpace α]
  statement: 𝓤 α = ⨆ x, 𝓝 (x, x)
  proof: nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)

中文:
定理 compactSpace_uniformity
  条件: [紧空间 α]
  结论: 𝓤 α = ⨆ x, 𝓝 (x, x)
  证明: nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)

Depends on / 依赖: nhdsSet_diagonal, nhdsSet_diagonal_eq_uniformity, nhdsSet_diagonal_eq_uniformity.symm.trans
-/
theorem compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x) :=
  nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)

/--
theorem `unique_uniformity_of_compact` / 定理 `unique_uniformity_of_compact`

English:
theorem unique_uniformity_of_compact
  statement: [t : TopologicalSpace γ] [CompactSpace γ]
  proof: by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u]; rw [compactSpace_uniformity]; rw [h]; rw [h']

中文:
定理 unique_uniformity_of_compact
  结论: [t : 拓扑空间 γ] [紧空间 γ]
  证明: by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u]; rw [compactSpace_uniformity]; rw [h]; rw [h']

Depends on / 依赖: CompactSpace, UniformSpace, UniformSpace.ext, compactSpace_uniformity, toTopologicalSpace, u.toTopologicalSpace
-/
theorem unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ]
    {u u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) :
    u = u' := by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u]; rw [compactSpace_uniformity]; rw [h]; rw [h']

end Compact

/--
theorem `IsClosed.relPreimage_of_isCompact` / 定理 `IsClosed.relPreimage_of_isCompact`

English:
theorem IsClosed.relPreimage_of_isCompact
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually] at hs ⊢
  simp_rw [Set.mem_compl_iff, SetRel.mem_preimage, not_exists, not_and]
exact fun y hy => ht.eventually_forall_of_forall_eventually fun x hx => hs _ hy _ hx

中文:
定理 是闭集.relPreimage_of_isCompact
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually] at hs ⊢
  simp_rw [Set.mem_compl_iff, SetRel.mem_preimage, not_exists, not_and]
exact fun y hy => ht.eventually_forall_of_forall_eventually fun x hx => hs _ hy _ hx

Depends on / 依赖: Set.mem_compl_iff, SetRel, SetRel.mem_preimage, eventually_forall_of_forall_eventually, ht.eventually_forall_of_forall_eventually, isOpen_compl_iff, isOpen_iff_eventually, mem_compl_iff, mem_preimage, not_and, not_exists, simp_rw
-/
theorem IsClosed.relPreimage_of_isCompact [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : IsCompact t) :
    IsClosed (s.preimage t) := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually] at hs ⊢
  simp_rw [Set.mem_compl_iff, SetRel.mem_preimage, not_exists, not_and]
exact fun y hy => ht.eventually_forall_of_forall_eventually fun x hx => hs _ hy _ hx

/--
theorem `IsClosed.relImage_of_isCompact` / 定理 `IsClosed.relImage_of_isCompact`

English:
theorem IsClosed.relImage_of_isCompact
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: hs.relInv.relPreimage_of_isCompact ht

中文:
定理 是闭集.relImage_of_isCompact
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: hs.relInv.relPreimage_of_isCompact ht

Depends on / 依赖: hs.relInv.relPreimage_of_isCompact, relInv, relPreimage_of_isCompact
-/
theorem IsClosed.relImage_of_isCompact [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : IsCompact t) :
    IsClosed (s.image t) :=
  hs.relInv.relPreimage_of_isCompact ht
