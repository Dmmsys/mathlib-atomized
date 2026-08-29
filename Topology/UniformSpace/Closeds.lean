/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.UniformSpace.UniformEmbedding

import Mathlib.Topology.UniformSpace.Compact

/-!
# Hausdorff uniformity

This file defines the Hausdorff uniformity on the types of closed subsets, compact subsets and
and nonempty compact subsets of a uniform space. This is the generalization of the uniformity
induced by the Hausdorff metric to hyperspaces of uniform spaces.
-/

@[expose] public section

open Topology
open scoped Uniformity Filter

variable {α β γ : Type*}

section hausdorffEntourage

open SetRel

/--
Definition of `hausdorffEntourage` / `hausdorffEntourage` 的定义

English:
definition hausdorffEntourage
  signature: (U : SetRel α α)
  body: {x | x.1 subseteq U.preimage x.2 ∧ x.2 subseteq U.image x.1}

中文:
定义 hausdorffEntourage
  签名: (U : SetRel α α)
  定义体: {x | x.1 subseteq U.preimage x.2 ∧ x.2 subseteq U.image x.1}

Depends on / 依赖: U.image, U.preimage, preimage, subseteq
-/
def hausdorffEntourage (U : SetRel α α) : SetRel (Set α) (Set α) :=
  {x | x.1 subseteq U.preimage x.2 ∧ x.2 subseteq U.image x.1}

/--
theorem `mem_hausdorffEntourage` / 定理 `mem_hausdorffEntourage`

English:
theorem mem_hausdorffEntourage
  given: (U : SetRel α α) (s t : Set α)
  proof: Iff.rfl

@[gcongr]

中文:
定理 mem_hausdorffEntourage
  条件: (U : SetRel α α) (s t : 集合 α)
  证明: Iff.rfl

@[gcongr]

Depends on / 依赖: Iff.rfl
-/
theorem mem_hausdorffEntourage (U : SetRel α α) (s t : Set α) :
    (s, t) in hausdorffEntourage U ↔ s subseteq U.preimage t ∧ t subseteq U.image s :=
  Iff.rfl

@[gcongr]
/--
theorem `hausdorffEntourage_mono` / 定理 `hausdorffEntourage_mono`

English:
theorem hausdorffEntourage_mono
  given: {U V : SetRel α α} (h : U subseteq V)
  proof: by
  unfold hausdorffEntourage
  gcongr

中文:
定理 hausdorffEntourage_mono
  条件: {U V : SetRel α α} (h : U subseteq V)
  证明: by
  unfold hausdorffEntourage
  gcongr

Depends on / 依赖: hausdorffEntourage
-/
theorem hausdorffEntourage_mono {U V : SetRel α α} (h : U subseteq V) :
    hausdorffEntourage U subseteq hausdorffEntourage V := by
  unfold hausdorffEntourage
  gcongr

/--
theorem `monotone_hausdorffEntourage` / 定理 `monotone_hausdorffEntourage`

English:
theorem monotone_hausdorffEntourage
  statement: Monotone (hausdorffEntourage (α := α))
  proof: fun _ _ => hausdorffEntourage_mono

@[simp]

中文:
定理 monotone_hausdorffEntourage
  结论: 递增 (hausdorffEntourage (α := α))
  证明: fun _ _ => hausdorffEntourage_mono

@[simp]
-/
theorem monotone_hausdorffEntourage : Monotone (hausdorffEntourage (α := α)) :=
  fun _ _ => hausdorffEntourage_mono

@[simp]
/--
theorem `hausdorffEntourage_id` / 定理 `hausdorffEntourage_id`

English:
theorem hausdorffEntourage_id
  statement: hausdorffEntourage (.id : SetRel α α) = .id
  proof: by
  simp_rw [hausdorffEntourage, preimage_id, image_id, ← subset_antisymm_iff, SetRel.id]

中文:
定理 hausdorffEntourage_id
  结论: hausdorffEntourage (.id : SetRel α α) = .id
  证明: by
  simp_rw [hausdorffEntourage, preimage_id, image_id, ← subset_antisymm_iff, SetRel.id]

Depends on / 依赖: SetRel, SetRel.id, hausdorffEntourage, image_id, preimage_id, simp_rw, subset_antisymm_iff
-/
theorem hausdorffEntourage_id : hausdorffEntourage (.id : SetRel α α) = .id := by
  simp_rw [hausdorffEntourage, preimage_id, image_id, ← subset_antisymm_iff, SetRel.id]

/--
Instance `isRefl_hausdorffEntourage` / 实例 `isRefl_hausdorffEntourage`

English:
instance isRefl_hausdorffEntourage
  signature: (U : SetRel α α) [U.IsRefl]
  body: ⟨fun _ => ⟨U.self_subset_preimage _, U.self_subset_image _⟩⟩

@[simp]

中文:
实例 isRefl_hausdorffEntourage
  签名: (U : SetRel α α) [U.IsRefl]
  定义体: ⟨fun _ => ⟨U.self_subset_preimage _, U.self_subset_image _⟩⟩

@[simp]

Depends on / 依赖: U.self_subset_image, U.self_subset_preimage, self_subset_image, self_subset_preimage
-/
instance isRefl_hausdorffEntourage (U : SetRel α α) [U.IsRefl] :
    (hausdorffEntourage U).IsRefl :=
  ⟨fun _ => ⟨U.self_subset_preimage _, U.self_subset_image _⟩⟩

@[simp]
/--
theorem `inv_hausdorffEntourage` / 定理 `inv_hausdorffEntourage`

English:
theorem inv_hausdorffEntourage
  given: (U : SetRel α α)
  proof: Set.ext fun _ => And.comm

中文:
定理 inv_hausdorffEntourage
  条件: (U : SetRel α α)
  证明: Set.ext fun _ => And.comm

Depends on / 依赖: And.comm, Set.ext
-/
theorem inv_hausdorffEntourage (U : SetRel α α) :
    (hausdorffEntourage U).inv = hausdorffEntourage U.inv :=
  Set.ext fun _ => And.comm

/--
Instance `isSymm_hausdorffEntourage` / 实例 `isSymm_hausdorffEntourage`

English:
instance isSymm_hausdorffEntourage
  signature: (U : SetRel α α) [U.IsSymm]
  body: by
  rw [← inv_eq_self_iff]; rw [inv_hausdorffEntourage]; rw [inv_eq_self]

中文:
实例 isSymm_hausdorffEntourage
  签名: (U : SetRel α α) [U.是Symm]
  定义体: by
  rw [← inv_eq_self_iff]; rw [inv_hausdorffEntourage]; rw [inv_eq_self]

Depends on / 依赖: inv_eq_self, inv_eq_self_iff, inv_hausdorffEntourage
-/
instance isSymm_hausdorffEntourage (U : SetRel α α) [U.IsSymm] :
    (hausdorffEntourage U).IsSymm := by
  rw [← inv_eq_self_iff]; rw [inv_hausdorffEntourage]; rw [inv_eq_self]

/--
theorem `hausdorffEntourage_comp` / 定理 `hausdorffEntourage_comp`

English:
theorem hausdorffEntourage_comp
  given: (U V : SetRel α α)
  proof: by
  apply subset_antisymm
  · intro ⟨s, t⟩ ⟨hst, hts⟩
    simp only [mem_comp, mem_hausdorffEntourage] at *
    refine ⟨U.image s inter V.preimage t, ⟨?_, Set.inter_subset_left⟩, ⟨Set.inter_subset_right, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, y, hxy, hyz⟩ := hst hx
      exact ⟨y, ⟨⟨x, hx, hxy⟩

中文:
定理 hausdorffEntourage_comp
  条件: (U V : SetRel α α)
  证明: by
  apply subset_antisymm
  · intro ⟨s, t⟩ ⟨hst, hts⟩
    simp only [mem_comp, mem_hausdorffEntourage] at *
    refine ⟨U.image s inter V.preimage t, ⟨?_, Set.inter_subset_left⟩, ⟨Set.inter_subset_right, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, y, hxy, hyz⟩ := hst hx
      exact ⟨y, ⟨⟨x, hx, hxy⟩

Depends on / 依赖: Set.inter_subset_left, Set.inter_subset_right, U.image, V.preimage, inter_subset_left, inter_subset_right, mem_comp, mem_hausdorffEntourage, preimage, preimage_comp, subset_antisymm
-/
theorem hausdorffEntourage_comp (U V : SetRel α α) :
    hausdorffEntourage (U ○ V) = hausdorffEntourage U ○ hausdorffEntourage V := by
  apply subset_antisymm
  · intro ⟨s, t⟩ ⟨hst, hts⟩
    simp only [mem_comp, mem_hausdorffEntourage] at *
    refine ⟨U.image s inter V.preimage t, ⟨?_, Set.inter_subset_left⟩, ⟨Set.inter_subset_right, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, y, hxy, hyz⟩ := hst hx
      exact ⟨y, ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩, hxy⟩
    · intro z hz
      obtain ⟨x, hx, y, hxy, hyz⟩ := hts hz
      exact ⟨y, ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩, hyz⟩
  · intro ⟨s₁, s₃⟩ ⟨s₂, ⟨h₁₂, h₂₁⟩, ⟨h₂₃, h₃₂⟩⟩
    simp only at *
    grw [mem_hausdorffEntourage, preimage_comp, ← h₂₃, ← h₁₂, image_comp, ← h₂₁, ← h₃₂]
    exact ⟨subset_rfl, subset_rfl⟩

/--
Instance `isTrans_hausdorffEntourage` / 实例 `isTrans_hausdorffEntourage`

English:
instance isTrans_hausdorffEntourage
  signature: (U : SetRel α α) [U.IsTrans]
  body: by
  grw [isTrans_iff_comp_subset_self, ← hausdorffEntourage_comp, comp_subset_self]

@[simp]

中文:
实例 isTrans_hausdorffEntourage
  签名: (U : SetRel α α) [U.是Trans]
  定义体: by
  grw [isTrans_iff_comp_subset_self, ← hausdorffEntourage_comp, comp_subset_self]

@[simp]

Depends on / 依赖: comp_subset_self, hausdorffEntourage_comp, isTrans_iff_comp_subset_self
-/
instance isTrans_hausdorffEntourage (U : SetRel α α) [U.IsTrans] :
    (hausdorffEntourage U).IsTrans := by
  grw [isTrans_iff_comp_subset_self, ← hausdorffEntourage_comp, comp_subset_self]

@[simp]
/--
theorem `singleton_mem_hausdorffEntourage` / 定理 `singleton_mem_hausdorffEntourage`

English:
theorem singleton_mem_hausdorffEntourage
  given: (U : SetRel α α) (x y : α)
  proof: by
  simp [hausdorffEntourage]

中文:
定理 singleton_mem_hausdorffEntourage
  条件: (U : SetRel α α) (x y : α)
  证明: by
  simp [hausdorffEntourage]

Depends on / 依赖: hausdorffEntourage
-/
theorem singleton_mem_hausdorffEntourage (U : SetRel α α) (x y : α) :
    ({x}, {y}) in hausdorffEntourage U ↔ (x, y) in U := by
  simp [hausdorffEntourage]

/--
theorem `union_mem_hausdorffEntourage` / 定理 `union_mem_hausdorffEntourage`

English:
theorem union_mem_hausdorffEntourage
  statement: (U : SetRel α α) {s₁ s₂ t₁ t₂ : Set α}
  proof: by
  grind [mem_hausdorffEntourage, preimage_union, image_union]

中文:
定理 union_mem_hausdorffEntourage
  结论: (U : SetRel α α) {s₁ s₂ t₁ t₂ : 集合 α}
  证明: by
  grind [mem_hausdorffEntourage, preimage_union, image_union]

Depends on / 依赖: image_union, mem_hausdorffEntourage, preimage_union
-/
theorem union_mem_hausdorffEntourage (U : SetRel α α) {s₁ s₂ t₁ t₂ : Set α}
    (h₁ : (s₁, t₁) in hausdorffEntourage U) (h₂ : (s₂, t₂) in hausdorffEntourage U) :
    (s₁ union s₂, t₁ union t₂) in hausdorffEntourage U := by
  grind [mem_hausdorffEntourage, preimage_union, image_union]

/--
theorem `TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage` / 定理 `TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage`

English:
theorem TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage
  statement: [UniformSpace α]
  proof: by
  obtain ⟨t, ht₁, ht₂⟩ := hs _ (symm_le_uniformity hU)
  lift t to Finset α using ht₁
  classical
  refine ⟨{x in t | exists y in s, (x, y) in U}, ?_⟩
  rw [Finset.coe_filter]
  refine ⟨fun _ h => h.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht₂ hx)
  exact ⟨y, ⟨hy, x, hx, hx

中文:
定理 全有界.存在_prodMk_finset_mem_hausdorffEntourage
  结论: [一致空间 α]
  证明: by
  obtain ⟨t, ht₁, ht₂⟩ := hs _ (symm_le_uniformity hU)
  lift t to Finset α using ht₁
  classical
  refine ⟨{x in t | exists y in s, (x, y) in U}, ?_⟩
  rw [Finset.coe_filter]
  refine ⟨fun _ h => h.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht₂ hx)
  exact ⟨y, ⟨hy, x, hx, hx

Depends on / 依赖: Finset, Finset.coe_filter, Set.mem_iUnion, classical, coe_filter, symm_le_uniformity
-/
theorem TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage [UniformSpace α]
    {s : Set α} (hs : TotallyBounded s) {U : SetRel α α} (hU : U in 𝓤 α) :
    exists t : Finset α, (↑t, s) in hausdorffEntourage U := by
  obtain ⟨t, ht₁, ht₂⟩ := hs _ (symm_le_uniformity hU)
  lift t to Finset α using ht₁
  classical
  refine ⟨{x in t | exists y in s, (x, y) in U}, ?_⟩
  rw [Finset.coe_filter]
  refine ⟨fun _ h => h.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht₂ hx)
  exact ⟨y, ⟨hy, x, hx, hxy⟩, hxy⟩

/--
theorem `prod_mem_hausdorffEntourage_entourageProd` / 定理 `prod_mem_hausdorffEntourage_entourageProd`

English:
theorem prod_mem_hausdorffEntourage_entourageProd
  proof: by
  simp only [mem_hausdorffEntourage] at *
  grind [preimage_entourageProd_prod, image_entourageProd_prod]

中文:
定理 prod_mem_hausdorffEntourage_entourageProd
  证明: by
  simp only [mem_hausdorffEntourage] at *
  grind [preimage_entourageProd_prod, image_entourageProd_prod]

Depends on / 依赖: image_entourageProd_prod, mem_hausdorffEntourage, preimage_entourageProd_prod
-/
theorem prod_mem_hausdorffEntourage_entourageProd
    (U₁ : SetRel α α) (U₂ : SetRel β β) {s₁ t₁ : Set α} {s₂ t₂ : Set β}
    (h₁ : (s₁, t₁) in hausdorffEntourage U₁) (h₂ : (s₂, t₂) in hausdorffEntourage U₂) :
    (s₁ ×ˢ s₂, t₁ ×ˢ t₂) in hausdorffEntourage (entourageProd U₁ U₂) := by
  simp only [mem_hausdorffEntourage] at *
  grind [preimage_entourageProd_prod, image_entourageProd_prod]

end hausdorffEntourage

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

variable (α) in
/--
Definition of `UniformSpace.hausdorff` / `UniformSpace.hausdorff` 的定义

English:
abbreviation UniformSpace.hausdorff
  signature: : UniformSpace (Set α)
  body: .ofCore
  { uniformity := (𝓤 α).lift' hausdorffEntourage
    refl := by
      simp_rw [Filter.principal_le_lift', SetRel.id_subset_iff]
      intro (U : SetRel α α) hU
      have := isRefl_of_mem_uniformity hU
      exact isRefl_hausdorffEntourage U
    symm :=
      Filter.tendsto_lift'.mpr fun U h

中文:
缩写 一致空间.hausdorff
  签名: : 一致空间 (集合 α)
  定义体: .ofCore
  { uniformity := (𝓤 α).lift' hausdorffEntourage
    refl := by
      simp_rw [Filter.principal_le_lift', SetRel.id_subset_iff]
      intro (U : SetRel α α) hU
      have := isRefl_of_mem_uniformity hU
      exact isRefl_hausdorffEntourage U
    symm :=
      Filter.tendsto_lift'.mpr fun U h
-/
protected abbrev UniformSpace.hausdorff : UniformSpace (Set α) := .ofCore
  { uniformity := (𝓤 α).lift' hausdorffEntourage
    refl := by
      simp_rw [Filter.principal_le_lift', SetRel.id_subset_iff]
      intro (U : SetRel α α) hU
      have := isRefl_of_mem_uniformity hU
      exact isRefl_hausdorffEntourage U
    symm :=
      Filter.tendsto_lift'.mpr fun U hU => Filter.mem_of_superset
        (Filter.mem_lift' (symm_le_uniformity hU)) (inv_hausdorffEntourage U).symm.subset
    comp := by
      rw [Filter.le_lift']
      intro U hU
      obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
      refine Filter.mem_of_superset (Filter.mem_lift' (Filter.mem_lift' hV)) ?_
      grw [← hausdorffEntourage_comp, hVU] }

attribute [local instance] UniformSpace.hausdorff

/--
theorem `Filter.HasBasis.uniformity_hausdorff` / 定理 `Filter.HasBasis.uniformity_hausdorff`

English:
theorem Filter.HasBasis.uniformity_hausdorff
  proof: h.lift' monotone_hausdorffEntourage

中文:
定理 滤子.有基.uniformity_hausdorff
  证明: h.lift' monotone_hausdorffEntourage

Depends on / 依赖: h.lift, monotone_hausdorffEntourage
-/
theorem Filter.HasBasis.uniformity_hausdorff
    {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Set α)).HasBasis p (hausdorffEntourage ∘ s) :=
  h.lift' monotone_hausdorffEntourage

namespace UniformSpace.hausdorff

/--
theorem `isOpen_inter_nonempty_of_isOpen` / 定理 `isOpen_inter_nonempty_of_isOpen`

English:
theorem isOpen_inter_nonempty_of_isOpen
  given: {U : Set α} (hU : IsOpen U)
  proof: by
  rw [isOpen_iff_mem_nhds]
  intro s ⟨x, hx₁, hx₂⟩
  rw [← hU.mem_nhds_iff]; rw [mem_nhds_iff] at hx₂
  obtain ⟨V, hV, hVU⟩ := hx₂
  rw [mem_nhds_iff]
  refine ⟨_, Filter.mem_lift' hV, ?_⟩
  rintro s' ⟨hs', -⟩
  obtain ⟨y, hy, hxy⟩ := hs' hx₁
  exact ⟨y, hy, hVU hxy⟩

中文:
定理 isOpen_inter_nonempty_of_isOpen
  条件: {U : 集合 α} (hU : 是开集 U)
  证明: by
  rw [isOpen_iff_mem_nhds]
  intro s ⟨x, hx₁, hx₂⟩
  rw [← hU.mem_nhds_iff]; rw [mem_nhds_iff] at hx₂
  obtain ⟨V, hV, hVU⟩ := hx₂
  rw [mem_nhds_iff]
  refine ⟨_, Filter.mem_lift' hV, ?_⟩
  rintro s' ⟨hs', -⟩
  obtain ⟨y, hy, hxy⟩ := hs' hx₁
  exact ⟨y, hy, hVU hxy⟩

Depends on / 依赖: Filter, Filter.mem_lift, hU.mem_nhds_iff, isOpen_iff_mem_nhds, mem_lift, mem_nhds_iff
-/
theorem isOpen_inter_nonempty_of_isOpen {U : Set α} (hU : IsOpen U) :
    IsOpen {s | (s inter U).Nonempty} := by
  rw [isOpen_iff_mem_nhds]
  intro s ⟨x, hx₁, hx₂⟩
  rw [← hU.mem_nhds_iff]; rw [mem_nhds_iff] at hx₂
  obtain ⟨V, hV, hVU⟩ := hx₂
  rw [mem_nhds_iff]
  refine ⟨_, Filter.mem_lift' hV, ?_⟩
  rintro s' ⟨hs', -⟩
  obtain ⟨y, hy, hxy⟩ := hs' hx₁
  exact ⟨y, hy, hVU hxy⟩

/--
theorem `_root_.IsClosed.powerset_hausdorff` / 定理 `_root_.IsClosed.powerset_hausdorff`

English:
theorem _root_.IsClosed.powerset_hausdorff
  given: {F : Set α} (hF : IsClosed F)
  proof: by
  simp_rw [Set.powerset, ← isOpen_compl_iff, Set.compl_ofPred, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen hF.isOpen_compl

中文:
定理 _root_.是闭集.powerset_hausdorff
  条件: {F : 集合 α} (hF : 是闭集 F)
  证明: by
  simp_rw [Set.powerset, ← isOpen_compl_iff, Set.compl_ofPred, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen hF.isOpen_compl

Depends on / 依赖: Set.compl_ofPred, Set.inter_compl_nonempty_iff, Set.powerset, compl_ofPred, hF.isOpen_compl, inter_compl_nonempty_iff, isOpen_compl, isOpen_compl_iff, isOpen_inter_nonempty_of_isOpen, powerset, simp_rw
-/
theorem _root_.IsClosed.powerset_hausdorff {F : Set α} (hF : IsClosed F) :
    IsClosed F.powerset := by
  simp_rw [Set.powerset, ← isOpen_compl_iff, Set.compl_ofPred, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen hF.isOpen_compl

/--
theorem `isClopen_singleton_empty` / 定理 `isClopen_singleton_empty`

English:
theorem isClopen_singleton_empty
  statement: IsClopen {(∅ : Set α)}
  proof: by
  constructor
  · rw [← Set.powerset_empty]
    exact isClosed_empty.powerset_hausdorff
  · simp_rw [isOpen_iff_mem_nhds, Set.mem_singleton_iff, forall_eq, nhds_eq_uniformity]
    filter_upwards [Filter.mem_lift' <| Filter.mem_lift' Filter.univ_mem] with F ⟨_, hF⟩
    simpa using hF

中文:
定理 isClopen_singleton_empty
  结论: IsClopen {(∅ : 集合 α)}
  证明: by
  constructor
  · rw [← Set.powerset_empty]
    exact isClosed_empty.powerset_hausdorff
  · simp_rw [isOpen_iff_mem_nhds, Set.mem_singleton_iff, forall_eq, nhds_eq_uniformity]
    filter_upwards [Filter.mem_lift' <| Filter.mem_lift' Filter.univ_mem] with F ⟨_, hF⟩
    simpa using hF

Depends on / 依赖: Filter, Filter.mem_lift, Filter.univ_mem, Set.mem_singleton_iff, Set.powerset_empty, filter_upwards, forall_eq, isClosed_empty, isClosed_empty.powerset_hausdorff, isOpen_iff_mem_nhds, mem_lift, mem_singleton_iff, nhds_eq_uniformity, powerset_empty, powerset_hausdorff, simp_rw, univ_mem
-/
theorem isClopen_singleton_empty : IsClopen {(∅ : Set α)} := by
  constructor
  · rw [← Set.powerset_empty]
    exact isClosed_empty.powerset_hausdorff
  · simp_rw [isOpen_iff_mem_nhds, Set.mem_singleton_iff, forall_eq, nhds_eq_uniformity]
    filter_upwards [Filter.mem_lift' <| Filter.mem_lift' Filter.univ_mem] with F ⟨_, hF⟩
    simpa using hF

/--
theorem `isUniformEmbedding_singleton` / 定理 `isUniformEmbedding_singleton`

English:
theorem isUniformEmbedding_singleton
  statement: IsUniformEmbedding ({·} : α -> Set α) where
  proof: Set.singleton_injective
  comap_uniformity := by
    change Filter.comap _ (Filter.lift' _ _) = _
    simp_rw [Filter.comap_lift'_eq, Function.comp_def, Set.preimage,
      singleton_mem_hausdorffEntourage]
    exact Filter.lift'_id

中文:
定理 isUniformEmbedding_singleton
  结论: 是一致嵌入 ({·} : α -> 集合 α) where
  证明: Set.singleton_injective
  comap_uniformity := by
    change Filter.comap _ (Filter.lift' _ _) = _
    simp_rw [Filter.comap_lift'_eq, Function.comp_def, Set.preimage,
      singleton_mem_hausdorffEntourage]
    exact Filter.lift'_id

Depends on / 依赖: Set.singleton_injective, singleton_injective
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> Set α) where
  injective := Set.singleton_injective
  comap_uniformity := by
    change Filter.comap _ (Filter.lift' _ _) = _
    simp_rw [Filter.comap_lift'_eq, Function.comp_def, Set.preimage,
      singleton_mem_hausdorffEntourage]
    exact Filter.lift'_id

/--
theorem `isClosedEmbedding_singleton` / 定理 `isClosedEmbedding_singleton`

English:
theorem isClosedEmbedding_singleton
  given: [T0Space α]
  proof: isUniformEmbedding_singleton.isEmbedding
  isClosed_range :=
    TopologicalSpace.isClosed_range_singleton
      isClopen_singleton_empty.isOpen
      isOpen_inter_nonempty_of_isOpen

中文:
定理 isClosedEmbedding_singleton
  条件: [T0空间 α]
  证明: isUniformEmbedding_singleton.isEmbedding
  isClosed_range :=
    TopologicalSpace.isClosed_range_singleton
      isClopen_singleton_empty.isOpen
      isOpen_inter_nonempty_of_isOpen

Depends on / 依赖: isEmbedding, isUniformEmbedding_singleton, isUniformEmbedding_singleton.isEmbedding
-/
theorem isClosedEmbedding_singleton [T0Space α] :
    Topology.IsClosedEmbedding ({·} : α -> Set α) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range :=
    TopologicalSpace.isClosed_range_singleton
      isClopen_singleton_empty.isOpen
      isOpen_inter_nonempty_of_isOpen

/--
theorem `uniformContinuous_union` / 定理 `uniformContinuous_union`

English:
theorem uniformContinuous_union
  statement: UniformContinuous (fun x : Set α × Set α => x.1 union x.2)
  proof: by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hU)]
    with _ ⟨h₁, h₂⟩ using union_mem_hausdorffEntourage U h₁ h₂

中文:
定理 uniformContinuous_union
  结论: 一致连续 (fun x : 集合 α × 集合 α => x.1 union x.2)
  证明: by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hU)]
    with _ ⟨h₁, h₂⟩ using union_mem_hausdorffEntourage U h₁ h₂

Depends on / 依赖: Filter, Filter.mem_lift, Filter.tendsto_lift, entourageProd_mem_uniformity, filter_upwards, mem_lift, tendsto_lift, union_mem_hausdorffEntourage
-/
theorem uniformContinuous_union : UniformContinuous (fun x : Set α × Set α => x.1 union x.2) := by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hU)]
    with _ ⟨h₁, h₂⟩ using union_mem_hausdorffEntourage U h₁ h₂

/--
theorem `uniformContinuous_prod` / 定理 `uniformContinuous_prod`

English:
theorem uniformContinuous_prod
  statement: UniformContinuous (fun x : Set α × Set β => x.1 ×ˢ x.2)
  proof: by
.lift' monotone_hausdorffEntourage refine (𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets
.tendsto_right_iff.mpr fun ⟨U, V⟩ ⟨hU, hV⟩ => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hV)]
    with ⟨⟨s₁, s₂⟩, ⟨t₁, t₂⟩⟩ ⟨h₁, h₂⟩ using prod_mem_hausdorffE

中文:
定理 uniformContinuous_prod
  结论: 一致连续 (fun x : 集合 α × 集合 β => x.1 ×ˢ x.2)
  证明: by
.lift' monotone_hausdorffEntourage refine (𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets
.tendsto_right_iff.mpr fun ⟨U, V⟩ ⟨hU, hV⟩ => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hV)]
    with ⟨⟨s₁, s₂⟩, ⟨t₁, t₂⟩⟩ ⟨h₁, h₂⟩ using prod_mem_hausdorffE

Depends on / 依赖: Filter, Filter.mem_lift, basis_sets, basis_sets.uniformity_prod, entourageProd_mem_uniformity, filter_upwards, mem_lift, monotone_hausdorffEntourage, prod_mem_hausdorffEntourage_entourageProd, tendsto_right_iff, tendsto_right_iff.mpr, uniformity_prod
-/
theorem uniformContinuous_prod : UniformContinuous (fun x : Set α × Set β => x.1 ×ˢ x.2) := by
.lift' monotone_hausdorffEntourage refine (𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets
.tendsto_right_iff.mpr fun ⟨U, V⟩ ⟨hU, hV⟩ => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hV)]
    with ⟨⟨s₁, s₂⟩, ⟨t₁, t₂⟩⟩ ⟨h₁, h₂⟩ using prod_mem_hausdorffEntourage_entourageProd U V h₁ h₂

/--
theorem `uniformContinuous_closure` / 定理 `uniformContinuous_closure`

English:
theorem uniformContinuous_closure
  statement: UniformContinuous (closure (X := α))
  proof: by
  simp_rw [UniformContinuous, (𝓤 α).basis_sets.uniformity_hausdorff.tendsto_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id, mem_hausdorffEntourage]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp 

中文:
定理 uniformContinuous_closure
  结论: 一致连续 (closure (X := α))
  证明: by
  simp_rw [UniformContinuous, (𝓤 α).basis_sets.uniformity_hausdorff.tendsto_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id, mem_hausdorffEntourage]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp 

Depends on / 依赖: Function, Function.comp_id, SetRel, SetRel.image_comp, SetRel.preimage_comp, UniformContinuous, basis_sets, basis_sets.uniformity_hausdorff, basis_sets.uniformity_hausdorff.tendsto_iff, closure_subset_image, closure_subset_preimage, comp_id, comp_mem_uniformity_sets, image_comp, mem_hausdorffEntourage, preimage_comp, simp_rw, subset_closure, tendsto_iff, uniformity_hausdorff
-/
theorem uniformContinuous_closure : UniformContinuous (closure (X := α)) := by
  simp_rw [UniformContinuous, (𝓤 α).basis_sets.uniformity_hausdorff.tendsto_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id, mem_hausdorffEntourage]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp only at *
  constructor
  · grw [closure_subset_preimage hV s, hst, ← subset_closure, ← hVU, SetRel.preimage_comp]
  · grw [closure_subset_image hV t, hts, ← subset_closure, ← hVU, SetRel.image_comp]

@[fun_prop]
/--
theorem `continuous_closure` / 定理 `continuous_closure`

English:
theorem continuous_closure
  statement: Continuous (closure (X := α))
  proof: uniformContinuous_closure.continuous

中文:
定理 continuous_closure
  结论: 连续 (closure (X := α))
  证明: uniformContinuous_closure.continuous
-/
theorem continuous_closure : Continuous (closure (X := α)) :=
  uniformContinuous_closure.continuous

/--
theorem `isUniformInducing_closure` / 定理 `isUniformInducing_closure`

English:
theorem isUniformInducing_closure
  statement: IsUniformInducing (closure (X := α))
  proof: by
refine ⟨le_antisymm ?_ Filter.map_le_iff_le_comap.mp uniformContinuous_closure⟩
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.le_basis_iff
    (𝓤 α).basis_sets.uniformity_hausdorff]; rw [Function.comp_id]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  re

中文:
定理 isUniformInducing_closure
  结论: 是UniformInducing (closure (X := α))
  证明: by
refine ⟨le_antisymm ?_ Filter.map_le_iff_le_comap.mp uniformContinuous_closure⟩
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.le_basis_iff
    (𝓤 α).basis_sets.uniformity_hausdorff]; rw [Function.comp_id]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  re

Depends on / 依赖: Filter, Filter.map_le_iff_le_comap.mp, Function, Function.comp_id, SetRel, SetRel.preimage_comp, basis_sets, basis_sets.uniformity_hausdorff, basis_sets.uniformity_hausdorff.comap, closure_subset_preimage, comp_id, comp_mem_uniformity_sets, le_antisymm, le_basis_iff, map_le_iff_le_comap, mem_hausdorffEntourage, preimage_comp, subset_c, subset_closure, uniformContinuous_closure
-/
theorem isUniformInducing_closure : IsUniformInducing (closure (X := α)) := by
refine ⟨le_antisymm ?_ Filter.map_le_iff_le_comap.mp uniformContinuous_closure⟩
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.le_basis_iff
    (𝓤 α).basis_sets.uniformity_hausdorff]; rw [Function.comp_id]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp only [mem_hausdorffEntourage] at *
  constructor
  · grw [subset_closure (s := s), hst, closure_subset_preimage hV t, ← hVU, SetRel.preimage_comp]
  · grw [subset_closure (s := t), hts, closure_subset_image hV s, ← hVU, SetRel.image_comp]

/--
theorem `nhds_closure` / 定理 `nhds_closure`

English:
theorem nhds_closure
  given: (s : Set α)
  statement: 𝓝 (closure s) = 𝓝 s
  proof: by
  simp_rw +singlePass [isUniformInducing_closure.isInducing.nhds_eq_comap, closure_closure]

中文:
定理 nhds_closure
  条件: (s : 集合 α)
  结论: 𝓝 (closure s) = 𝓝 s
  证明: by
  simp_rw +singlePass [isUniformInducing_closure.isInducing.nhds_eq_comap, closure_closure]

Depends on / 依赖: closure_closure, isInducing, isUniformInducing_closure, isUniformInducing_closure.isInducing.nhds_eq_comap, nhds_eq_comap, simp_rw, singlePass
-/
theorem nhds_closure (s : Set α) : 𝓝 (closure s) = 𝓝 s := by
  simp_rw +singlePass [isUniformInducing_closure.isInducing.nhds_eq_comap, closure_closure]

/--
theorem `isClosed_setOfPred_totallyBounded` / 定理 `isClosed_setOfPred_totallyBounded`

English:
theorem isClosed_setOfPred_totallyBounded
  statement: IsClosed {s : Set α | TotallyBounded s}
  proof: by
  simp_rw [isClosed_iff_frequently, nhds_eq_comap_uniformity]
  intro s hs U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.frequently_iff] at hs
  obtain ⟨t, ⟨hst : s subseteq V.preimage t, -⟩, ht⟩ := hs V hV
  obtain ⟨

中文:
定理 isClosed_setOfPred_totallyBounded
  结论: 是闭集 {s : 集合 α | 全有界 s}
  证明: by
  simp_rw [isClosed_iff_frequently, nhds_eq_comap_uniformity]
  intro s hs U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.frequently_iff] at hs
  obtain ⟨t, ⟨hst : s subseteq V.preimage t, -⟩, ht⟩ := hs V hV
  obtain ⟨

Depends on / 依赖: Set.subset_def, SetRel, V.preimage, basis_sets, basis_sets.uniformity_hausdorff.comap, comp_mem_uniformity_sets, frequently_iff, isClosed_iff_frequently, nhds_eq_comap_uniformity, preimage, simp_rw, subset_def, subseteq, uniformity_hausdorff
-/
theorem isClosed_setOfPred_totallyBounded : IsClosed {s : Set α | TotallyBounded s} := by
  simp_rw [isClosed_iff_frequently, nhds_eq_comap_uniformity]
  intro s hs U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.frequently_iff] at hs
  obtain ⟨t, ⟨hst : s subseteq V.preimage t, -⟩, ht⟩ := hs V hV
  obtain ⟨u, hu, htu⟩ := ht V hV
  refine ⟨u, hu, ?_⟩
  grw [hst, htu, ← hVU]
  simp [Set.subset_def]
  grind

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_totallyBounded := isClosed_setOfPred_totallyBounded

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteUniformity
  signature: α] : DiscreteUniformity (Set α)
  body: by
  rw [discreteUniformity_iff_setRelId_mem_uniformity]
  convert! Filter.mem_lift' (DiscreteUniformity.relId_mem_uniformity α)
  rw [hausdorffEntourage_id]

中文:
实例 [DiscreteUniformity
  签名: α] : DiscreteUniformity (集合 α)
  定义体: by
  rw [discreteUniformity_iff_setRelId_mem_uniformity]
  convert! Filter.mem_lift' (DiscreteUniformity.relId_mem_uniformity α)
  rw [hausdorffEntourage_id]

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.relId_mem_uniformity, Filter, Filter.mem_lift, convert, discreteUniformity_iff_setRelId_mem_uniformity, hausdorffEntourage_id, mem_lift, relId_mem_uniformity
-/
instance [DiscreteUniformity α] : DiscreteUniformity (Set α) := by
  rw [discreteUniformity_iff_setRelId_mem_uniformity]
  convert! Filter.mem_lift' (DiscreteUniformity.relId_mem_uniformity α)
  rw [hausdorffEntourage_id]

end UniformSpace.hausdorff

/--
theorem `UniformContinuous.image_hausdorff` / 定理 `UniformContinuous.image_hausdorff`

English:
theorem UniformContinuous.image_hausdorff
  given: {f : α -> β} (hf : UniformContinuous f)
  proof: by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [Filter.mem_lift' (hf hU)] with ⟨s, t⟩ ⟨h₁, h₂⟩
  simp_rw [mem_hausdorffEntourage, Set.image_subset_iff]
  exact ⟨h₁.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩,
    h₂.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.me

中文:
定理 一致连续.image_hausdorff
  条件: {f : α -> β} (hf : 一致连续 f)
  证明: by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [Filter.mem_lift' (hf hU)] with ⟨s, t⟩ ⟨h₁, h₂⟩
  simp_rw [mem_hausdorffEntourage, Set.image_subset_iff]
  exact ⟨h₁.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩,
    h₂.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.me

Depends on / 依赖: Filter, Filter.mem_lift, Filter.tendsto_lift, Set.image_subset_iff, Set.mem_image_of_mem, filter_upwards, image_subset_iff, mem_hausdorffEntourage, mem_image_of_mem, mem_lift, simp_rw, tendsto_lift
-/
theorem UniformContinuous.image_hausdorff {f : α -> β} (hf : UniformContinuous f) :
    UniformContinuous (f '' ·) := by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [Filter.mem_lift' (hf hU)] with ⟨s, t⟩ ⟨h₁, h₂⟩
  simp_rw [mem_hausdorffEntourage, Set.image_subset_iff]
  exact ⟨h₁.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩,
    h₂.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩⟩

/--
theorem `IsUniformInducing.image_hausdorff` / 定理 `IsUniformInducing.image_hausdorff`

English:
theorem IsUniformInducing.image_hausdorff
  given: {f : α -> β} (hf : IsUniformInducing f)
  proof: by
  constructor
  change Filter.comap _ (Filter.lift' _ _) = Filter.lift' _ _
  rw [Filter.comap_lift'_eq]; rw [← hf.comap_uniformity]; rw [Filter.comap_lift'_eq2 monotone_hausdorffEntourage]
  congr with U ⟨s, t⟩
  simp only [Function.comp, hausdorffEntourage, SetRel.preimage, SetRel.image, Set.pr

中文:
定理 是UniformInducing.image_hausdorff
  条件: {f : α -> β} (hf : 是UniformInducing f)
  证明: by
  constructor
  change Filter.comap _ (Filter.lift' _ _) = Filter.lift' _ _
  rw [Filter.comap_lift'_eq]; rw [← hf.comap_uniformity]; rw [Filter.comap_lift'_eq2 monotone_hausdorffEntourage]
  congr with U ⟨s, t⟩
  simp only [Function.comp, hausdorffEntourage, SetRel.preimage, SetRel.image, Set.pr

Depends on / 依赖: Filter, Filter.comap, Filter.comap_lift, Filter.lift, Function, Function.comp, Set.exists_mem_image, Set.image_subset_iff, Set.mem_ofPred, Set.preimage, SetRel, SetRel.image, SetRel.preimage, _eq2, comap_lift, comap_uniformity, exists_mem_image, hausdorffEntourage, hf.comap_uniformity, image_subset_iff
-/
theorem IsUniformInducing.image_hausdorff {f : α -> β} (hf : IsUniformInducing f) :
    IsUniformInducing (f '' ·) := by
  constructor
  change Filter.comap _ (Filter.lift' _ _) = Filter.lift' _ _
  rw [Filter.comap_lift'_eq]; rw [← hf.comap_uniformity]; rw [Filter.comap_lift'_eq2 monotone_hausdorffEntourage]
  congr with U ⟨s, t⟩
  simp only [Function.comp, hausdorffEntourage, SetRel.preimage, SetRel.image, Set.preimage,
    Set.mem_ofPred, Set.image_subset_iff, Set.exists_mem_image]

/--
theorem `IsUniformEmbedding.image_hausdorff` / 定理 `IsUniformEmbedding.image_hausdorff`

English:
theorem IsUniformEmbedding.image_hausdorff
  given: {f : α -> β} (hf : IsUniformEmbedding f)
  proof: hf.isUniformInducing.image_hausdorff
  injective := hf.injective.image_injective

中文:
定理 是一致嵌入.image_hausdorff
  条件: {f : α -> β} (hf : 是一致嵌入 f)
  证明: hf.isUniformInducing.image_hausdorff
  injective := hf.injective.image_injective

Depends on / 依赖: hf.isUniformInducing.image_hausdorff, image_hausdorff, isUniformInducing
-/
theorem IsUniformEmbedding.image_hausdorff {f : α -> β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f '' ·) where
  __ := hf.isUniformInducing.image_hausdorff
  injective := hf.injective.image_injective

/--
theorem `TotallyBounded.powerset_hausdorff` / 定理 `TotallyBounded.powerset_hausdorff`

English:
theorem TotallyBounded.powerset_hausdorff
  given: {t : Set α} (ht : TotallyBounded t)
  proof: by
  simp_rw [(𝓤 α).basis_sets.uniformity_hausdorff.totallyBounded_iff, Function.comp_id,
    Set.powerset, Set.ofPred_subset, Set.mem_iUnion]
  intro (U : SetRel α α) hU
  obtain ⟨u, hu, ht⟩ := ht U hU
  refine ⟨u.powerset, hu.powerset, fun s hs => ⟨u inter U.image s, by grind, fun x hx => ?_,
    

中文:
定理 全有界.powerset_hausdorff
  条件: {t : 集合 α} (ht : 全有界 t)
  证明: by
  simp_rw [(𝓤 α).basis_sets.uniformity_hausdorff.totallyBounded_iff, Function.comp_id,
    Set.powerset, Set.ofPred_subset, Set.mem_iUnion]
  intro (U : SetRel α α) hU
  obtain ⟨u, hu, ht⟩ := ht U hU
  refine ⟨u.powerset, hu.powerset, fun s hs => ⟨u inter U.image s, by grind, fun x hx => ?_,
    

Depends on / 依赖: Function, Function.comp_id, Set.mem_iUnion, Set.ofPred_subset, Set.powerset, SetRel, U.image, basis_sets, basis_sets.uniformity_hausdorff.totallyBounded_iff, comp_id, hu.powerset, mem_iUnion, ofPred_subset, powerset, simp_rw, totallyBounded_iff, u.powerset, uniformity_hausdorff
-/
theorem TotallyBounded.powerset_hausdorff {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded t.powerset := by
  simp_rw [(𝓤 α).basis_sets.uniformity_hausdorff.totallyBounded_iff, Function.comp_id,
    Set.powerset, Set.ofPred_subset, Set.mem_iUnion]
  intro (U : SetRel α α) hU
  obtain ⟨u, hu, ht⟩ := ht U hU
  refine ⟨u.powerset, hu.powerset, fun s hs => ⟨u inter U.image s, by grind, fun x hx => ?_,
    fun x ⟨_, hx⟩ => hx⟩⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (hs hx))
  exact ⟨y, ⟨hy, ⟨x, hx, hxy⟩⟩, hxy⟩

/--
theorem `TotallyBounded.nhds_vietoris_le_nhds_hausdorff` / 定理 `TotallyBounded.nhds_vietoris_le_nhds_hausdorff`

English:
theorem TotallyBounded.nhds_vietoris_le_nhds_hausdorff
  given: {s : Set α} (hs : TotallyBounded s)
  proof: by
  open UniformSpace TopologicalSpace.vietoris in
  simp_rw [nhds_eq_comap_uniformity,
.ge_iff, Function.comp_id, .comap _ uniformity_hasBasis_open.uniformity_hausdorff
    hausdorffEntourage, Set.preimage_ofPred_eq, Set.ofPred_and]
  intro U ⟨hU₁, hU₂⟩
  have : U.IsRefl := ⟨fun _ => refl_mem_unif

中文:
定理 全有界.nhds_vietoris_le_nhds_hausdorff
  条件: {s : 集合 α} (hs : 全有界 s)
  证明: by
  open UniformSpace TopologicalSpace.vietoris in
  simp_rw [nhds_eq_comap_uniformity,
.ge_iff, Function.comp_id, .comap _ uniformity_hasBasis_open.uniformity_hausdorff
    hausdorffEntourage, Set.preimage_ofPred_eq, Set.ofPred_and]
  intro U ⟨hU₁, hU₂⟩
  have : U.IsRefl := ⟨fun _ => refl_mem_unif

Depends on / 依赖: Filter, Filter.inter_mem, Function, Function.comp_id, IsRefl, Set.ofPred_and, Set.preimage_ofPred_eq, SetRel, SetRel.self_subset_image, TopologicalSpace, TopologicalSpace.vietoris, U.IsRefl, UniformSpace, comp_id, comp_open_symm_mem_uniform, ge_iff, hausdorffEntourage, inter_mem, mem_nhds, nhds_eq_comap_uniformity
-/
theorem TotallyBounded.nhds_vietoris_le_nhds_hausdorff {s : Set α} (hs : TotallyBounded s) :
    @nhds _ (.vietoris α) s <= 𝓝 s := by
  open UniformSpace TopologicalSpace.vietoris in
  simp_rw [nhds_eq_comap_uniformity,
.ge_iff, Function.comp_id, .comap _ uniformity_hasBasis_open.uniformity_hausdorff
    hausdorffEntourage, Set.preimage_ofPred_eq, Set.ofPred_and]
  intro U ⟨hU₁, hU₂⟩
  have : U.IsRefl := ⟨fun _ => refl_mem_uniformity hU₁⟩
  let := TopologicalSpace.vietoris α
refine Filter.inter_mem ?_ hU₂.relImage.powerset_vietoris.mem_nhds
    SetRel.self_subset_image _
  obtain ⟨V : SetRel α α, hV₁, hV₂, _, hVU⟩ := comp_open_symm_mem_uniformity_sets hU₁
  obtain ⟨t, ht₁, ht₂⟩ := hs.exists_prodMk_finset_mem_hausdorffEntourage hV₁
  dsimp only at ht₁ ht₂
  filter_upwards [(Filter.eventually_all_finset t).mpr fun x hx =>
.eventually_mem (ht₁ hx)] isOpen_inter_nonempty_of_isOpen (isOpen_ball x hV₂)
    with u (hu : ↑t subseteq V.preimage ↑u)
  grw [ht₂, ← SetRel.preimage_eq_image, hu, ← hVU, SetRel.preimage_comp]

/--
theorem `IsCompact.nhds_hausdorff_eq_nhds_vietoris` / 定理 `IsCompact.nhds_hausdorff_eq_nhds_vietoris`

English:
theorem IsCompact.nhds_hausdorff_eq_nhds_vietoris
  given: {s : Set α} (hs : IsCompact s)
  proof: by
  refine le_antisymm ?_ hs.totallyBounded.nhds_vietoris_le_nhds_hausdorff
  simp_rw [TopologicalSpace.nhds_generateFrom, le_iInf₂_iff, Filter.le_principal_iff]
  rintro _ ⟨hs', (⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)⟩
  · obtain ⟨V : SetRel α α, hV₁, hV₂⟩ :=
.mem_iff.mp (hU.mem_nhdsSet.mpr hs') hs.nhdsSet_

中文:
定理 是紧集.nhds_hausdorff_eq_nhds_vietoris
  条件: {s : 集合 α} (hs : 是紧集 s)
  证明: by
  refine le_antisymm ?_ hs.totallyBounded.nhds_vietoris_le_nhds_hausdorff
  simp_rw [TopologicalSpace.nhds_generateFrom, le_iInf₂_iff, Filter.le_principal_iff]
  rintro _ ⟨hs', (⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)⟩
  · obtain ⟨V : SetRel α α, hV₁, hV₂⟩ :=
.mem_iff.mp (hU.mem_nhdsSet.mpr hs') hs.nhdsSet_

Depends on / 依赖: Filter, Filter.le_principal_iff, Filter.mem_lift, Set.mem_biUnion, SetRel, TopologicalSpace, TopologicalSpace.nhds_generateFrom, UniformSpace, UniformSpace.ball_mem_nhds, UniformSpace.haus, ball_mem_nhds, basis_sets, filter_upwards, hU.mem_nhdsSet.mpr, hs.nhdsSet_basis_uniformity, hs.totallyBounded.nhds_vietoris_le_nhds_hausdorff, ht.trans, le_antisymm, le_principal_iff, mem_biUnion
-/
theorem IsCompact.nhds_hausdorff_eq_nhds_vietoris {s : Set α} (hs : IsCompact s) :
    𝓝 s = @nhds _ (.vietoris α) s := by
  refine le_antisymm ?_ hs.totallyBounded.nhds_vietoris_le_nhds_hausdorff
  simp_rw [TopologicalSpace.nhds_generateFrom, le_iInf₂_iff, Filter.le_principal_iff]
  rintro _ ⟨hs', (⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)⟩
  · obtain ⟨V : SetRel α α, hV₁, hV₂⟩ :=
.mem_iff.mp (hU.mem_nhdsSet.mpr hs') hs.nhdsSet_basis_uniformity (𝓤 α).basis_sets
    filter_upwards [UniformSpace.ball_mem_nhds _ (Filter.mem_lift' hV₁)]
      with t ⟨_, ht⟩
exact ht.trans fun x ⟨y, hy, hxy⟩ => hV₂ Set.mem_biUnion hy hxy
  · exact (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hU).mem_nhds hs'

namespace UniformSpace.hausdorff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] : CompactSpace (Set α) where
  body: by
    rw [isCompact_iff_ultrafilter_le_nhds]
    rintro f -
    let := TopologicalSpace.vietoris α
    -- `f.lim` is the limit of `f` in the Vietoris topology
    refine ⟨closure f.lim, Set.mem_univ _, ?_⟩
    grw [isClosed_closure.isCompact.nhds_hausdorff_eq_nhds_vietoris,
      ← TopologicalSpace

中文:
实例 [紧空间
  签名: α] : 紧空间 (集合 α) where
  定义体: by
    rw [isCompact_iff_ultrafilter_le_nhds]
    rintro f -
    let := TopologicalSpace.vietoris α
    -- `f.lim` is the limit of `f` in the Vietoris topology
    refine ⟨closure f.lim, Set.mem_univ _, ?_⟩
    grw [isClosed_closure.isCompact.nhds_hausdorff_eq_nhds_vietoris,
      ← TopologicalSpace

Depends on / 依赖: TopologicalSpace, TopologicalSpace.vietoris, isCompact_iff_ultrafilter_le_nhds, vietoris
-/
instance [CompactSpace α] : CompactSpace (Set α) where
  isCompact_univ := by
    rw [isCompact_iff_ultrafilter_le_nhds]
    rintro f -
    let := TopologicalSpace.vietoris α
    -- `f.lim` is the limit of `f` in the Vietoris topology
    refine ⟨closure f.lim, Set.mem_univ _, ?_⟩
    grw [isClosed_closure.isCompact.nhds_hausdorff_eq_nhds_vietoris,
      ← TopologicalSpace.vietoris.specializes_closure.nhds_le_nhds, f.le_nhds_lim]

end UniformSpace.hausdorff

namespace TopologicalSpace.Closeds

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace (Closeds α)
  body: .comap (↑) (.hausdorff α)

中文:
实例 uniformSpace
  签名: : 一致空间 (Closeds α)
  定义体: .comap (↑) (.hausdorff α)

Depends on / 依赖: hausdorff
-/
instance uniformSpace : UniformSpace (Closeds α) :=
  .comap (↑) (.hausdorff α)

/--
theorem `uniformity_def` / 定理 `uniformity_def`

English:
theorem uniformity_def
  proof: rfl

中文:
定理 uniformity_def
  证明: rfl
-/
theorem uniformity_def :
    𝓤 (Closeds α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl

/--
theorem `_root_.Filter.HasBasis.uniformity_closeds` / 定理 `_root_.Filter.HasBasis.uniformity_closeds`

English:
theorem _root_.Filter.HasBasis.uniformity_closeds
  proof: h.uniformity_hausdorff.comap _

中文:
定理 _root_.滤子.有基.uniformity_closeds
  证明: h.uniformity_hausdorff.comap _

Depends on / 依赖: h.uniformity_hausdorff.comap, uniformity_hausdorff
-/
theorem _root_.Filter.HasBasis.uniformity_closeds
    {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Closeds α)).HasBasis p (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _

/--
theorem `isUniformEmbedding_coe` / 定理 `isUniformEmbedding_coe`

English:
theorem isUniformEmbedding_coe
  statement: IsUniformEmbedding ((↑) : Closeds α -> Set α) where
  proof: SetLike.coe_injective
  comap_uniformity := rfl

中文:
定理 isUniformEmbedding_coe
  结论: 是一致嵌入 ((↑) : Closeds α -> 集合 α) where
  证明: SetLike.coe_injective
  comap_uniformity := rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Closeds α -> Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl

/--
theorem `uniformContinuous_coe` / 定理 `uniformContinuous_coe`

English:
theorem uniformContinuous_coe
  statement: UniformContinuous ((↑) : Closeds α -> Set α)
  proof: isUniformEmbedding_coe.uniformContinuous

中文:
定理 uniformContinuous_coe
  结论: 一致连续 ((↑) : Closeds α -> 集合 α)
  证明: isUniformEmbedding_coe.uniformContinuous

Depends on / 依赖: isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : Closeds α -> Set α) :=
  isUniformEmbedding_coe.uniformContinuous

/--
theorem `isOpen_inter_nonempty_of_isOpen` / 定理 `isOpen_inter_nonempty_of_isOpen`

English:
theorem isOpen_inter_nonempty_of_isOpen
  given: {s : Set α} (hs : IsOpen s)
  proof: isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)

中文:
定理 isOpen_inter_nonempty_of_isOpen
  条件: {s : 集合 α} (hs : 是开集 s)
  证明: isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen, hausdorff, isOpen_induced, isOpen_inter_nonempty_of_isOpen
-/
theorem isOpen_inter_nonempty_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsOpen {t : Closeds α | ((t : Set α) inter s).Nonempty} :=
  isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)

/--
theorem `isClosed_subsets_of_isClosed` / 定理 `isClosed_subsets_of_isClosed`

English:
theorem isClosed_subsets_of_isClosed
  given: {s : Set α} (hs : IsClosed s)
  proof: isClosed_induced hs.powerset_hausdorff

中文:
定理 isClosed_subsets_of_isClosed
  条件: {s : 集合 α} (hs : 是闭集 s)
  证明: isClosed_induced hs.powerset_hausdorff

Depends on / 依赖: hs.powerset_hausdorff, isClosed_induced, powerset_hausdorff
-/
theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : Closeds α | (t : Set α) subseteq s} :=
  isClosed_induced hs.powerset_hausdorff

/--
theorem `isClopen_singleton_bot` / 定理 `isClopen_singleton_bot`

English:
theorem isClopen_singleton_bot
  statement: IsClopen {(⊥ : Closeds α)}
  proof: by
  convert! UniformSpace.hausdorff.isClopen_singleton_empty.preimage uniformContinuous_coe.continuous
  ext; simp

中文:
定理 isClopen_singleton_bot
  结论: IsClopen {(⊥ : Closeds α)}
  证明: by
  convert! UniformSpace.hausdorff.isClopen_singleton_empty.preimage uniformContinuous_coe.continuous
  ext; simp

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.isClopen_singleton_empty.preimage, continuous, convert, hausdorff, isClopen_singleton_empty, preimage, uniformContinuous_coe, uniformContinuous_coe.continuous
-/
theorem isClopen_singleton_bot : IsClopen {(⊥ : Closeds α)} := by
  convert! UniformSpace.hausdorff.isClopen_singleton_empty.preimage uniformContinuous_coe.continuous
  ext; simp

/--
theorem `totallyBounded_subsets_of_totallyBounded` / 定理 `totallyBounded_subsets_of_totallyBounded`

English:
theorem totallyBounded_subsets_of_totallyBounded
  given: {t : Set α} (ht : TotallyBounded t)
  proof: totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

中文:
定理 totallyBounded_subsets_of_totallyBounded
  条件: {t : 集合 α} (ht : 全有界 t)
  证明: totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

Depends on / 依赖: ht.powerset_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.isUniformInducing, isUniformInducing, powerset_hausdorff, totallyBounded_preimage
-/
theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {F : Closeds α | ↑F subseteq t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

/--
theorem `isClosed_setOfPred_totallyBounded` / 定理 `isClosed_setOfPred_totallyBounded`

English:
theorem isClosed_setOfPred_totallyBounded
  statement: IsClosed {s : Closeds α | TotallyBounded (s : Set α)}
  proof: UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded.preimage uniformContinuous_coe.continuous

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_totallyBounded := isClosed_setOfPred_totallyBounded

中文:
定理 isClosed_setOfPred_totallyBounded
  结论: 是闭集 {s : Closeds α | 全有界 (s : 集合 α)}
  证明: UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded.preimage uniformContinuous_coe.continuous

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_totallyBounded := isClosed_setOfPred_totallyBounded

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded.preimage, continuous, hausdorff, isClosed_setOfPred_totallyBounded, preimage, uniformContinuous_coe, uniformContinuous_coe.continuous
-/
theorem isClosed_setOfPred_totallyBounded : IsClosed {s : Closeds α | TotallyBounded (s : Set α)} :=
  UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded.preimage uniformContinuous_coe.continuous

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_totallyBounded := isClosed_setOfPred_totallyBounded

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteUniformity
  signature: α] : DiscreteUniformity (Closeds α)
  body: isUniformEmbedding_coe.discreteUniformity

中文:
实例 [DiscreteUniformity
  签名: α] : DiscreteUniformity (Closeds α)
  定义体: isUniformEmbedding_coe.discreteUniformity

Depends on / 依赖: discreteUniformity, isUniformEmbedding_coe, isUniformEmbedding_coe.discreteUniformity
-/
instance [DiscreteUniformity α] : DiscreteUniformity (Closeds α) :=
  isUniformEmbedding_coe.discreteUniformity

section T0Space

variable [T0Space α]

/--
theorem `isUniformEmbedding_singleton` / 定理 `isUniformEmbedding_singleton`

English:
theorem isUniformEmbedding_singleton
  statement: IsUniformEmbedding ({·} : α -> Closeds α)
  proof: isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

中文:
定理 isUniformEmbedding_singleton
  结论: 是一致嵌入 ({·} : α -> Closeds α)
  证明: isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.isUniformEmbedding_singleton, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.of_comp_iff.mp, isUniformEmbedding_singleton, of_comp_iff
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> Closeds α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

/--
theorem `uniformContinuous_singleton` / 定理 `uniformContinuous_singleton`

English:
theorem uniformContinuous_singleton
  statement: UniformContinuous ({·} : α -> Closeds α)
  proof: isUniformEmbedding_singleton.uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_singleton
  结论: 一致连续 ({·} : α -> Closeds α)
  证明: isUniformEmbedding_singleton.uniformContinuous

@[fun_prop]

Depends on / 依赖: isUniformEmbedding_singleton, isUniformEmbedding_singleton.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_singleton : UniformContinuous ({·} : α -> Closeds α) :=
  isUniformEmbedding_singleton.uniformContinuous

@[fun_prop]
/--
theorem `isEmbedding_singleton` / 定理 `isEmbedding_singleton`

English:
theorem isEmbedding_singleton
  statement: IsEmbedding ({·} : α -> Closeds α)
  proof: isUniformEmbedding_singleton.isEmbedding

@[fun_prop]

中文:
定理 isEmbedding_singleton
  结论: 是嵌入 ({·} : α -> Closeds α)
  证明: isUniformEmbedding_singleton.isEmbedding

@[fun_prop]

Depends on / 依赖: isEmbedding, isUniformEmbedding_singleton, isUniformEmbedding_singleton.isEmbedding
-/
theorem isEmbedding_singleton : IsEmbedding ({·} : α -> Closeds α) :=
  isUniformEmbedding_singleton.isEmbedding

@[fun_prop]
/--
theorem `continuous_singleton` / 定理 `continuous_singleton`

English:
theorem continuous_singleton
  statement: Continuous ({·} : α -> Closeds α)
  proof: isEmbedding_singleton.continuous

@[fun_prop]

中文:
定理 continuous_singleton
  结论: 连续 ({·} : α -> Closeds α)
  证明: isEmbedding_singleton.continuous

@[fun_prop]

Depends on / 依赖: continuous, isEmbedding_singleton, isEmbedding_singleton.continuous
-/
theorem continuous_singleton : Continuous ({·} : α -> Closeds α) :=
  isEmbedding_singleton.continuous

@[fun_prop]
/--
theorem `isClosedEmbedding_singleton` / 定理 `isClosedEmbedding_singleton`

English:
theorem isClosedEmbedding_singleton
  statement: Topology.IsClosedEmbedding ({·} : α -> Closeds α) where
  proof: isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← SetLike.coe_injective.preimage_image (s := Set.range ({·}))]; rw [← Set.range_comp]
    exact UniformSpace.hausdorff.isClosedEmbedding_singleton.isClosed_range.preimage
      uniformContinuous_coe.continuous

@[simp]

中文:
定理 isClosedEmbedding_singleton
  结论: 拓扑.是闭嵌入 ({·} : α -> Closeds α) where
  证明: isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← SetLike.coe_injective.preimage_image (s := Set.range ({·}))]; rw [← Set.range_comp]
    exact UniformSpace.hausdorff.isClosedEmbedding_singleton.isClosed_range.preimage
      uniformContinuous_coe.continuous

@[simp]

Depends on / 依赖: isEmbedding, isUniformEmbedding_singleton, isUniformEmbedding_singleton.isEmbedding
-/
theorem isClosedEmbedding_singleton : Topology.IsClosedEmbedding ({·} : α -> Closeds α) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← SetLike.coe_injective.preimage_image (s := Set.range ({·}))]; rw [← Set.range_comp]
    exact UniformSpace.hausdorff.isClosedEmbedding_singleton.isClosed_range.preimage
      uniformContinuous_coe.continuous

@[simp]
/--
theorem `discreteUniformity_iff` / 定理 `discreteUniformity_iff`

English:
theorem discreteUniformity_iff
  statement: DiscreteUniformity (Closeds α) ↔ DiscreteUniformity α
  proof: ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

中文:
定理 discreteUniformity_iff
  结论: DiscreteUniformity (Closeds α) ↔ DiscreteUniformity α
  证明: ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

Depends on / 依赖: discreteUniformity, isUniformEmbedding_singleton, isUniformEmbedding_singleton.discreteUniformity
-/
theorem discreteUniformity_iff : DiscreteUniformity (Closeds α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

end T0Space

/--
theorem `uniformContinuous_sup` / 定理 `uniformContinuous_sup`

English:
theorem uniformContinuous_sup
  statement: UniformContinuous (fun x : Closeds α × Closeds α => x.1 ⊔ x.2)
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

中文:
定理 uniformContinuous_sup
  结论: 一致连续 (fun x : Closeds α × Closeds α => x.1 ⊔ x.2)
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.uniformContinuous_union.comp, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, prodMap, uniformContinuous_coe, uniformContinuous_coe.prodMap, uniformContinuous_iff, uniformContinuous_union
-/
theorem uniformContinuous_sup : UniformContinuous (fun x : Closeds α × Closeds α => x.1 ⊔ x.2) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

/--
theorem `_root_.UniformContinuous.sup_closeds` / 定理 `_root_.UniformContinuous.sup_closeds`

English:
theorem _root_.UniformContinuous.sup_closeds
  proof: uniformContinuous_sup.comp hf.prodMk hg

中文:
定理 _root_.一致连续.sup_closeds
  证明: uniformContinuous_sup.comp hf.prodMk hg

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_sup, uniformContinuous_sup.comp
-/
theorem _root_.UniformContinuous.sup_closeds
    {f g : α -> Closeds β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
uniformContinuous_sup.comp hf.prodMk hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSup (Closeds α)
  body: ⟨uniformContinuous_sup.continuous⟩

中文:
实例 :
  签名: 余ntinuousSup (Closeds α)
  定义体: ⟨uniformContinuous_sup.continuous⟩

Depends on / 依赖: continuous, uniformContinuous_sup, uniformContinuous_sup.continuous
-/
instance : ContinuousSup (Closeds α) :=
  ⟨uniformContinuous_sup.continuous⟩

/--
theorem `uniformContinuous_prod` / 定理 `uniformContinuous_prod`

English:
theorem uniformContinuous_prod
  statement: UniformContinuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2)
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

中文:
定理 uniformContinuous_prod
  结论: 一致连续 (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2)
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.uniformContinuous_prod.comp, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, prodMap, uniformContinuous_coe, uniformContinuous_coe.prodMap, uniformContinuous_iff, uniformContinuous_prod
-/
theorem uniformContinuous_prod : UniformContinuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

/--
theorem `_root_.UniformContinuous.prod_closeds` / 定理 `_root_.UniformContinuous.prod_closeds`

English:
theorem _root_.UniformContinuous.prod_closeds
  statement: {f : α -> Closeds β} {g : α -> Closeds γ}
  proof: uniformContinuous_prod.comp (hf.prodMk hg)

@[fun_prop]

中文:
定理 _root_.一致连续.prod_closeds
  结论: {f : α -> Closeds β} {g : α -> Closeds γ}
  证明: uniformContinuous_prod.comp (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_prod, uniformContinuous_prod.comp
-/
theorem _root_.UniformContinuous.prod_closeds {f : α -> Closeds β} {g : α -> Closeds γ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ×ˢ g x) :=
  uniformContinuous_prod.comp (hf.prodMk hg)

@[fun_prop]
/--
theorem `continuous_prod` / 定理 `continuous_prod`

English:
theorem continuous_prod
  statement: Continuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2)
  proof: uniformContinuous_prod.continuous

中文:
定理 continuous_prod
  结论: 连续 (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2)
  证明: uniformContinuous_prod.continuous

Depends on / 依赖: continuous, uniformContinuous_prod, uniformContinuous_prod.continuous
-/
theorem continuous_prod : Continuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2) :=
  uniformContinuous_prod.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T0Space (Closeds α)
  body: by
  suffices forall F₁ F₂ : Closeds α, Inseparable F₁ F₂ -> F₁ <= F₂ from
    ⟨fun F₁ F₂ h => le_antisymm (this F₁ F₂ h) (this F₂ F₁ h.symm)⟩
  refine fun F₁ F₂ h x hx₁ => isClosed_iff_frequently.mp F₂.isClosed _ ?_
  rw [nhds_eq_comap_uniformity]; rw [Filter.frequently_comap]; rw [Filter.frequentl

中文:
实例 :
  签名: T0空间 (Closeds α)
  定义体: by
  suffices forall F₁ F₂ : Closeds α, Inseparable F₁ F₂ -> F₁ <= F₂ from
    ⟨fun F₁ F₂ h => le_antisymm (this F₁ F₂ h) (this F₂ F₁ h.symm)⟩
  refine fun F₁ F₂ h x hx₁ => isClosed_iff_frequently.mp F₂.isClosed _ ?_
  rw [nhds_eq_comap_uniformity]; rw [Filter.frequently_comap]; rw [Filter.frequentl

Depends on / 依赖: Closeds, Filter, Filter.frequently_comap, Filter.frequently_iff, Filter.mem_lift, Filter.preimage_mem_comap, Inseparable, SetRel, U.preimage, frequently_comap, frequently_iff, h.nhds_le_uniformity, h.symm, isClosed, isClosed_iff_frequently, isClosed_iff_frequently.mp, le_antisymm, mem_lift, mem_of_mem_nhds, nhds_eq_comap_uniformity
-/
instance : T0Space (Closeds α) := by
  suffices forall F₁ F₂ : Closeds α, Inseparable F₁ F₂ -> F₁ <= F₂ from
    ⟨fun F₁ F₂ h => le_antisymm (this F₁ F₂ h) (this F₂ F₁ h.symm)⟩
  refine fun F₁ F₂ h x hx₁ => isClosed_iff_frequently.mp F₂.isClosed _ ?_
  rw [nhds_eq_comap_uniformity]; rw [Filter.frequently_comap]; rw [Filter.frequently_iff]
  intro (U : SetRel α α) hU
  obtain ⟨h : (F₁ : Set α) subseteq U.preimage F₂, -⟩ :=
mem_of_mem_nhds h.nhds_le_uniformity Filter.preimage_mem_comap Filter.mem_lift' hU
  obtain ⟨y, hy, hxy⟩ := h hx₁
  exact ⟨(x, y), hxy, y, rfl, hy⟩

/--
theorem `isUniformInducing_closure` / 定理 `isUniformInducing_closure`

English:
theorem isUniformInducing_closure
  statement: IsUniformInducing (Closeds.closure (α := α))
  proof: isUniformEmbedding_coe.isUniformInducing.of_comp_iff.mp
    UniformSpace.hausdorff.isUniformInducing_closure

中文:
定理 isUniformInducing_closure
  结论: 是UniformInducing (Closeds.closure (α := α))
  证明: isUniformEmbedding_coe.isUniformInducing.of_comp_iff.mp
    UniformSpace.hausdorff.isUniformInducing_closure
-/
theorem isUniformInducing_closure : IsUniformInducing (Closeds.closure (α := α)) :=
  isUniformEmbedding_coe.isUniformInducing.of_comp_iff.mp
    UniformSpace.hausdorff.isUniformInducing_closure

/--
theorem `uniformContinuous_closure` / 定理 `uniformContinuous_closure`

English:
theorem uniformContinuous_closure
  statement: UniformContinuous (Closeds.closure (α := α))
  proof: isUniformInducing_closure.uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_closure
  结论: 一致连续 (Closeds.closure (α := α))
  证明: isUniformInducing_closure.uniformContinuous

@[fun_prop]
-/
theorem uniformContinuous_closure : UniformContinuous (Closeds.closure (α := α)) :=
  isUniformInducing_closure.uniformContinuous

@[fun_prop]
/--
theorem `continuous_closure` / 定理 `continuous_closure`

English:
theorem continuous_closure
  statement: Continuous (Closeds.closure (α := α))
  proof: uniformContinuous_closure.continuous

中文:
定理 continuous_closure
  结论: 连续 (Closeds.closure (α := α))
  证明: uniformContinuous_closure.continuous
-/
theorem continuous_closure : Continuous (Closeds.closure (α := α)) :=
  uniformContinuous_closure.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] : CompactSpace (Closeds α) where
  body: by simpa [gi.l_surjective.range_eq]
    using isCompact_univ.image continuous_closure

@[simp]

中文:
实例 [紧空间
  签名: α] : 紧空间 (Closeds α) where
  定义体: by simpa [gi.l_surjective.range_eq]
    using isCompact_univ.image continuous_closure

@[simp]

Depends on / 依赖: continuous_closure, gi.l_surjective.range_eq, isCompact_univ, isCompact_univ.image, l_surjective, range_eq
-/
instance [CompactSpace α] : CompactSpace (Closeds α) where
  isCompact_univ := by simpa [gi.l_surjective.range_eq]
    using isCompact_univ.image continuous_closure

@[simp]
/--
theorem `compactSpace_iff` / 定理 `compactSpace_iff`

English:
theorem compactSpace_iff
  statement: CompactSpace (Closeds α) ↔ CompactSpace α
  proof: by
  refine ⟨fun _ => compactSpace_of_finite_subfamily_closed fun {ι} F hF₁ hF₂ => ?_,
    fun _ => inferInstance⟩
  have := isClopen_singleton_bot.compl.isClosed.isCompact.elim_finite_subfamily_closed
    (fun i => {C : Closeds α | ↑C subseteq F i})
    (fun i => isClosed_subsets_of_isClosed (hF₁ i

中文:
定理 compactSpace_iff
  结论: 紧空间 (Closeds α) ↔ 紧空间 α
  证明: by
  refine ⟨fun _ => compactSpace_of_finite_subfamily_closed fun {ι} F hF₁ hF₂ => ?_,
    fun _ => inferInstance⟩
  have := isClopen_singleton_bot.compl.isClosed.isCompact.elim_finite_subfamily_closed
    (fun i => {C : Closeds α | ↑C subseteq F i})
    (fun i => isClosed_subsets_of_isClosed (hF₁ i

Depends on / 依赖: Closeds, Set.disjoint_compl_left_iff_subset, Set.disjoint_iff_inter_eq_empty, Set.ofPred_eq_eq_singleton, Set.ofPred_forall, Set.subset_empty_iff, Set.subset_iInter_iff, coe_eq_empty, compactSpace_of_finite_subfamily_closed, disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty, elim_finite_subfamily_closed, isClopen_singleton_bot, isClopen_singleton_bot.compl.isClosed.isCompact.elim_finite_subfamily_closed, isClosed, isClosed_subsets_of_isClosed, isCompact, ofPred_eq_eq_singleton, ofPred_forall, simp_rw
-/
theorem compactSpace_iff : CompactSpace (Closeds α) ↔ CompactSpace α := by
  refine ⟨fun _ => compactSpace_of_finite_subfamily_closed fun {ι} F hF₁ hF₂ => ?_,
    fun _ => inferInstance⟩
  have := isClopen_singleton_bot.compl.isClosed.isCompact.elim_finite_subfamily_closed
    (fun i => {C : Closeds α | ↑C subseteq F i})
    (fun i => isClosed_subsets_of_isClosed (hF₁ i))
  simp_rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset,
    ← Set.ofPred_forall, ← Set.subset_iInter_iff, hF₂, Set.subset_empty_iff, coe_eq_empty,
    Set.ofPred_eq_eq_singleton] at this
  obtain ⟨s, hs⟩ := this .rfl
  specialize @hs ⟨⋂ i in s, F i, isClosed_biInter fun i _ => hF₁ i⟩ .rfl
  exact ⟨s, congr($hs)⟩

@[simp]
/--
theorem `noncompactSpace_iff` / 定理 `noncompactSpace_iff`

English:
theorem noncompactSpace_iff
  statement: NoncompactSpace (Closeds α) ↔ NoncompactSpace α
  proof: by
  simp_rw [← not_compactSpace_iff, compactSpace_iff]

中文:
定理 noncompactSpace_iff
  结论: Noncompact空间 (Closeds α) ↔ Noncompact空间 α
  证明: by
  simp_rw [← not_compactSpace_iff, compactSpace_iff]

Depends on / 依赖: compactSpace_iff, not_compactSpace_iff, simp_rw
-/
theorem noncompactSpace_iff : NoncompactSpace (Closeds α) ↔ NoncompactSpace α := by
  simp_rw [← not_compactSpace_iff, compactSpace_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoncompactSpace
  signature: α] : NoncompactSpace (Closeds α)
  body: noncompactSpace_iff.mpr ‹_›

中文:
实例 [Noncompact空间
  签名: α] : Noncompact空间 (Closeds α)
  定义体: noncompactSpace_iff.mpr ‹_›

Depends on / 依赖: noncompactSpace_iff, noncompactSpace_iff.mpr
-/
instance [NoncompactSpace α] : NoncompactSpace (Closeds α) :=
  noncompactSpace_iff.mpr ‹_›

end TopologicalSpace.Closeds

namespace TopologicalSpace.Compacts

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace (Compacts α)
  body: .replaceTopology (.comap (↑) (.hausdorff α)) ext_nhds fun K => by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

中文:
实例 uniformSpace
  签名: : 一致空间 (余mpacts α)
  定义体: .replaceTopology (.comap (↑) (.hausdorff α)) ext_nhds fun K => by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

Depends on / 依赖: K.isCompact.nhds_hausdorff_eq_nhds_vietoris, ext_nhds, hausdorff, isCompact, nhds_hausdorff_eq_nhds_vietoris, nhds_induced, replaceTopology, simp_rw
-/
instance uniformSpace : UniformSpace (Compacts α) :=
.replaceTopology (.comap (↑) (.hausdorff α)) ext_nhds fun K => by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

/--
theorem `uniformity_def` / 定理 `uniformity_def`

English:
theorem uniformity_def
  proof: rfl

中文:
定理 uniformity_def
  证明: rfl
-/
theorem uniformity_def :
    𝓤 (Compacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl

/--
theorem `_root_.Filter.HasBasis.uniformity_compacts` / 定理 `_root_.Filter.HasBasis.uniformity_compacts`

English:
theorem _root_.Filter.HasBasis.uniformity_compacts
  proof: h.uniformity_hausdorff.comap _

中文:
定理 _root_.滤子.有基.uniformity_compacts
  证明: h.uniformity_hausdorff.comap _

Depends on / 依赖: h.uniformity_hausdorff.comap, uniformity_hausdorff
-/
theorem _root_.Filter.HasBasis.uniformity_compacts
    {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Compacts α)).HasBasis p (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _

/--
theorem `isUniformEmbedding_coe` / 定理 `isUniformEmbedding_coe`

English:
theorem isUniformEmbedding_coe
  statement: IsUniformEmbedding ((↑) : Compacts α -> Set α) where
  proof: SetLike.coe_injective
  comap_uniformity := rfl

中文:
定理 isUniformEmbedding_coe
  结论: 是一致嵌入 ((↑) : 余mpacts α -> 集合 α) where
  证明: SetLike.coe_injective
  comap_uniformity := rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Compacts α -> Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl

/--
theorem `uniformContinuous_coe` / 定理 `uniformContinuous_coe`

English:
theorem uniformContinuous_coe
  statement: UniformContinuous ((↑) : Compacts α -> Set α)
  proof: isUniformEmbedding_coe.uniformContinuous

中文:
定理 uniformContinuous_coe
  结论: 一致连续 ((↑) : 余mpacts α -> 集合 α)
  证明: isUniformEmbedding_coe.uniformContinuous

Depends on / 依赖: isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : Compacts α -> Set α) :=
  isUniformEmbedding_coe.uniformContinuous

/--
theorem `isUniformEmbedding_toCloseds` / 定理 `isUniformEmbedding_toCloseds`

English:
theorem isUniformEmbedding_toCloseds
  given: [T2Space α]
  statement: IsUniformEmbedding (toCloseds (α := α)) where
  proof: toCloseds_injective
  comap_uniformity := Filter.comap_comap

中文:
定理 isUniformEmbedding_toCloseds
  条件: [T2空间 α]
  结论: 是一致嵌入 (toCloseds (α := α)) where
  证明: toCloseds_injective
  comap_uniformity := Filter.comap_comap
-/
theorem isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_comap

/--
theorem `uniformContinuous_toCloseds` / 定理 `uniformContinuous_toCloseds`

English:
theorem uniformContinuous_toCloseds
  given: [T2Space α]
  statement: UniformContinuous (toCloseds (α := α))
  proof: isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_toCloseds
  条件: [T2空间 α]
  结论: 一致连续 (toCloseds (α := α))
  证明: isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
-/
theorem uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
/--
theorem `isEmbedding_toCloseds` / 定理 `isEmbedding_toCloseds`

English:
theorem isEmbedding_toCloseds
  given: [T2Space α]
  statement: IsEmbedding (toCloseds (α := α))
  proof: isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]

中文:
定理 isEmbedding_toCloseds
  条件: [T2空间 α]
  结论: 是嵌入 (toCloseds (α := α))
  证明: isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
-/
theorem isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
/--
theorem `continuous_toCloseds` / 定理 `continuous_toCloseds`

English:
theorem continuous_toCloseds
  given: [T2Space α]
  statement: Continuous (toCloseds (α := α))
  proof: uniformContinuous_toCloseds.continuous

@[fun_prop]

中文:
定理 continuous_toCloseds
  条件: [T2空间 α]
  结论: 连续 (toCloseds (α := α))
  证明: uniformContinuous_toCloseds.continuous

@[fun_prop]
-/
theorem continuous_toCloseds [T2Space α] : Continuous (toCloseds (α := α)) :=
  uniformContinuous_toCloseds.continuous

@[fun_prop]
/--
theorem `isClosedEmbedding_toCloseds` / 定理 `isClosedEmbedding_toCloseds`

English:
theorem isClosedEmbedding_toCloseds
  given: [T2Space α] [CompleteSpace α]
  proof: isEmbedding_toCloseds
  isClosed_range := by
    convert! Closeds.isClosed_setOfPred_totallyBounded
    exact subset_antisymm
      (Set.range_subset_iff.mpr fun K => K.isCompact.totallyBounded)
      (fun K hK => ⟨⟨K, hK.isCompact_of_isClosed K.isClosed⟩, rfl⟩)

中文:
定理 isClosedEmbedding_toCloseds
  条件: [T2空间 α] [完备空间 α]
  证明: isEmbedding_toCloseds
  isClosed_range := by
    convert! Closeds.isClosed_setOfPred_totallyBounded
    exact subset_antisymm
      (Set.range_subset_iff.mpr fun K => K.isCompact.totallyBounded)
      (fun K hK => ⟨⟨K, hK.isCompact_of_isClosed K.isClosed⟩, rfl⟩)
-/
theorem isClosedEmbedding_toCloseds [T2Space α] [CompleteSpace α] :
    IsClosedEmbedding (toCloseds (α := α)) where
  __ := isEmbedding_toCloseds
  isClosed_range := by
    convert! Closeds.isClosed_setOfPred_totallyBounded
    exact subset_antisymm
      (Set.range_subset_iff.mpr fun K => K.isCompact.totallyBounded)
      (fun K hK => ⟨⟨K, hK.isCompact_of_isClosed K.isClosed⟩, rfl⟩)

/--
theorem `totallyBounded_subsets_of_totallyBounded` / 定理 `totallyBounded_subsets_of_totallyBounded`

English:
theorem totallyBounded_subsets_of_totallyBounded
  given: {t : Set α} (ht : TotallyBounded t)
  proof: totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

中文:
定理 totallyBounded_subsets_of_totallyBounded
  条件: {t : 集合 α} (ht : 全有界 t)
  证明: totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

Depends on / 依赖: ht.powerset_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.isUniformInducing, isUniformInducing, powerset_hausdorff, totallyBounded_preimage
-/
theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {K : Compacts α | ↑K subseteq t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

/--
theorem `isUniformEmbedding_singleton` / 定理 `isUniformEmbedding_singleton`

English:
theorem isUniformEmbedding_singleton
  statement: IsUniformEmbedding ({·} : α -> Compacts α)
  proof: isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

中文:
定理 isUniformEmbedding_singleton
  结论: 是一致嵌入 ({·} : α -> 余mpacts α)
  证明: isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.isUniformEmbedding_singleton, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.of_comp_iff.mp, isUniformEmbedding_singleton, of_comp_iff
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> Compacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

/--
theorem `uniformContinuous_singleton` / 定理 `uniformContinuous_singleton`

English:
theorem uniformContinuous_singleton
  statement: UniformContinuous ({·} : α -> Compacts α)
  proof: isUniformEmbedding_singleton.uniformContinuous

中文:
定理 uniformContinuous_singleton
  结论: 一致连续 ({·} : α -> 余mpacts α)
  证明: isUniformEmbedding_singleton.uniformContinuous

Depends on / 依赖: isUniformEmbedding_singleton, isUniformEmbedding_singleton.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_singleton : UniformContinuous ({·} : α -> Compacts α) :=
  isUniformEmbedding_singleton.uniformContinuous

/--
theorem `uniformContinuous_sup` / 定理 `uniformContinuous_sup`

English:
theorem uniformContinuous_sup
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

中文:
定理 uniformContinuous_sup
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.uniformContinuous_union.comp, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, prodMap, uniformContinuous_coe, uniformContinuous_coe.prodMap, uniformContinuous_iff, uniformContinuous_union
-/
theorem uniformContinuous_sup :
    UniformContinuous (fun x : Compacts α × Compacts α => x.1 ⊔ x.2) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

/--
theorem `_root_.UniformContinuous.sup_compacts` / 定理 `_root_.UniformContinuous.sup_compacts`

English:
theorem _root_.UniformContinuous.sup_compacts
  proof: uniformContinuous_sup.comp hf.prodMk hg

中文:
定理 _root_.一致连续.sup_compacts
  证明: uniformContinuous_sup.comp hf.prodMk hg

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_sup, uniformContinuous_sup.comp
-/
theorem _root_.UniformContinuous.sup_compacts
    {f g : α -> Compacts β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
uniformContinuous_sup.comp hf.prodMk hg

/--
theorem `uniformContinuous_prod` / 定理 `uniformContinuous_prod`

English:
theorem uniformContinuous_prod
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

中文:
定理 uniformContinuous_prod
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.uniformContinuous_prod.comp, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, prodMap, uniformContinuous_coe, uniformContinuous_coe.prodMap, uniformContinuous_iff, uniformContinuous_prod
-/
theorem uniformContinuous_prod :
    UniformContinuous (fun x : Compacts α × Compacts β => x.1 ×ˢ x.2) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

/--
theorem `_root_.UniformContinuous.prod_compacts` / 定理 `_root_.UniformContinuous.prod_compacts`

English:
theorem _root_.UniformContinuous.prod_compacts
  statement: {f : α -> Compacts β} {g : α -> Compacts γ}
  proof: uniformContinuous_prod.comp (hf.prodMk hg)

中文:
定理 _root_.一致连续.prod_compacts
  结论: {f : α -> 余mpacts β} {g : α -> 余mpacts γ}
  证明: uniformContinuous_prod.comp (hf.prodMk hg)

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_prod, uniformContinuous_prod.comp
-/
theorem _root_.UniformContinuous.prod_compacts {f : α -> Compacts β} {g : α -> Compacts γ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ×ˢ g x) :=
  uniformContinuous_prod.comp (hf.prodMk hg)

/--
theorem `_root_.UniformContinuous.compacts_map` / 定理 `_root_.UniformContinuous.compacts_map`

English:
theorem _root_.UniformContinuous.compacts_map
  given: {f : α -> β} (hf : UniformContinuous f)
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr hf.image_hausdorff.comp uniformContinuous_coe

中文:
定理 _root_.一致连续.compacts_map
  条件: {f : α -> β} (hf : 一致连续 f)
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr hf.image_hausdorff.comp uniformContinuous_coe

Depends on / 依赖: hf.image_hausdorff.comp, image_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, uniformContinuous_coe, uniformContinuous_iff
-/
theorem _root_.UniformContinuous.compacts_map {f : α -> β} (hf : UniformContinuous f) :
    UniformContinuous (Compacts.map f hf.continuous) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr hf.image_hausdorff.comp uniformContinuous_coe

/--
theorem `_root_.IsUniformInducing.compacts_map` / 定理 `_root_.IsUniformInducing.compacts_map`

English:
theorem _root_.IsUniformInducing.compacts_map
  given: {f : α -> β} (hf : IsUniformInducing f)
  proof: .of_comp hf.uniformContinuous.compacts_map uniformContinuous_coe
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

中文:
定理 _root_.是UniformInducing.compacts_map
  条件: {f : α -> β} (hf : 是UniformInducing f)
  证明: .of_comp hf.uniformContinuous.compacts_map uniformContinuous_coe
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

Depends on / 依赖: compacts_map, hf.image_hausdorff.comp, hf.uniformContinuous.compacts_map, image_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.isUniformInducing, isUniformInducing, of_comp, uniformContinuous, uniformContinuous_coe
-/
theorem _root_.IsUniformInducing.compacts_map {f : α -> β} (hf : IsUniformInducing f) :
    IsUniformInducing (Compacts.map f hf.uniformContinuous.continuous) :=
.of_comp hf.uniformContinuous.compacts_map uniformContinuous_coe
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

/--
theorem `_root_.IsUniformEmbedding.compacts_map` / 定理 `_root_.IsUniformEmbedding.compacts_map`

English:
theorem _root_.IsUniformEmbedding.compacts_map
  given: {f : α -> β} (hf : IsUniformEmbedding f)
  proof: hf.isUniformInducing.compacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

中文:
定理 _root_.是一致嵌入.compacts_map
  条件: {f : α -> β} (hf : 是一致嵌入 f)
  证明: hf.isUniformInducing.compacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

Depends on / 依赖: compacts_map, hf.isUniformInducing.compacts_map, isUniformInducing
-/
theorem _root_.IsUniformEmbedding.compacts_map {f : α -> β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (Compacts.map f hf.uniformContinuous.continuous) where
  __ := hf.isUniformInducing.compacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteUniformity
  signature: α] : DiscreteUniformity (Compacts α)
  body: isUniformEmbedding_coe.discreteUniformity

@[simp]

中文:
实例 [DiscreteUniformity
  签名: α] : DiscreteUniformity (余mpacts α)
  定义体: isUniformEmbedding_coe.discreteUniformity

@[simp]

Depends on / 依赖: discreteUniformity, isUniformEmbedding_coe, isUniformEmbedding_coe.discreteUniformity
-/
instance [DiscreteUniformity α] : DiscreteUniformity (Compacts α) :=
  isUniformEmbedding_coe.discreteUniformity

@[simp]
/--
theorem `discreteUniformity_iff` / 定理 `discreteUniformity_iff`

English:
theorem discreteUniformity_iff
  statement: DiscreteUniformity (Compacts α) ↔ DiscreteUniformity α
  proof: ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

中文:
定理 discreteUniformity_iff
  结论: DiscreteUniformity (余mpacts α) ↔ DiscreteUniformity α
  证明: ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

Depends on / 依赖: discreteUniformity, isUniformEmbedding_singleton, isUniformEmbedding_singleton.discreteUniformity
-/
theorem discreteUniformity_iff : DiscreteUniformity (Compacts α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: α] : CompleteSpace (Compacts α)
  body: by
  refine ⟨fun {f} ⟨_, hf⟩ => ?_⟩
  grw [← Filter.curry_le_prod, (𝓤 α).basis_sets.uniformity_compacts.ge_iff] at hf
  change forall {U} (hU : U in 𝓤 α), forallᶠ K in f, forallᶠ K' in f, (↑K, ↑K') in hausdorffEntourage U at hf
  let l : Filter α := f.lift' fun s => ⋃ K in s, K
  have hl : l.Totally

中文:
实例 [完备空间
  签名: α] : 完备空间 (余mpacts α)
  定义体: by
  refine ⟨fun {f} ⟨_, hf⟩ => ?_⟩
  grw [← Filter.curry_le_prod, (𝓤 α).basis_sets.uniformity_compacts.ge_iff] at hf
  change forall {U} (hU : U in 𝓤 α), forallᶠ K in f, forallᶠ K' in f, (↑K, ↑K') in hausdorffEntourage U at hf
  let l : Filter α := f.lift' fun s => ⋃ K in s, K
  have hl : l.Totally

Depends on / 依赖: Filter, Filter.curry_le_prod, K.isCompact.totallyBounded, SetRel, TotallyBounded, basis_sets, basis_sets.uniformity_compacts.ge_iff, comp_mem_uniformity_sets, curry_le_prod, f.lift, ge_iff, hausdorffEntourage, isCompact, l.TotallyBounded, symm_le_uniformity, totallyBounded, uniformity_compacts
-/
instance [CompleteSpace α] : CompleteSpace (Compacts α) := by
  refine ⟨fun {f} ⟨_, hf⟩ => ?_⟩
  grw [← Filter.curry_le_prod, (𝓤 α).basis_sets.uniformity_compacts.ge_iff] at hf
  change forall {U} (hU : U in 𝓤 α), forallᶠ K in f, forallᶠ K' in f, (↑K, ↑K') in hausdorffEntourage U at hf
  let l : Filter α := f.lift' fun s => ⋃ K in s, K
  have hl : l.TotallyBounded := by
    intro U hU
    obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
.exists obtain ⟨K, hK⟩ := hf (symm_le_uniformity hV)
    obtain ⟨t, ht₁, ht₂⟩ := K.isCompact.totallyBounded V hV
    rw [← SetRel.preimage_eq_biUnion] at ht₂
    refine ⟨t, ht₁, Filter.mem_of_superset (Filter.mem_lift' hK) ?_⟩
    rw [Set.iUnion₂_subset_iff]
    intro K' ⟨_, (hK' : ↑K' subseteq V.preimage K)⟩
    grw [← hVU, SetRel.preimage_comp, ← ht₂, hK']
  let L : Compacts α := ⟨{x | ClusterPt x l}, hl.isCompact_setOfPred_clusterPt⟩
  exists L
  simp_rw [nhds_eq_comap_uniformity']
  rw [uniformity_hasBasis_closed.uniformity_compacts.comap _ |>.ge_iff]
  intro U ⟨hU₁, hU₂⟩
  filter_upwards [hf hU₁] with K hK
  simp_rw [Set.mem_preimage, Prod.map, id, mem_hausdorffEntourage]
  constructor
  · intro x hx
    set lx := l ⊓ 𝓟 (UniformSpace.ball x U) with le_def
    have hlx : lx.TotallyBounded := hl.mono inf_le_left
    have : lx.NeBot := by
      rw [le_def]; rw [Filter.lift'_inf_principal_eq]; rw [Filter.lift'_neBot_iff fun _ _ h =>
Set.inter_subset_inter_left _ Set.biUnion_subset_biUnion_left h]
      intro s hs
obtain ⟨K', ⟨h₁, -⟩, h₂⟩ := Filter.nonempty_of_mem Filter.inter_mem hK hs
      obtain ⟨y, hy, hxy⟩ := h₁ hx
      exact ⟨y, Set.mem_iUnion₂_of_mem h₂ hy, hxy⟩
    obtain ⟨y, hy⟩ := hlx.exists_clusterPt
    have hy₁ : ClusterPt y l := .of_inf_left hy
    have hy₂ : ClusterPt y (𝓟 (UniformSpace.ball x U)) := .of_inf_right hy
    rw [← mem_closure_iff_clusterPt]; rw [(UniformSpace.isClosed_ball x hU₂).closure_eq] at hy₂
    exact ⟨y, hy₁, hy₂⟩
  · intro x (hx : ClusterPt x l)
    rw [← (hU₂.relImage_of_isCompact K.isCompact).closure_eq]; rw [mem_closure_iff_clusterPt]
    refine hx.mono ?_
    rw [Filter.le_principal_iff]
    refine Filter.mem_of_superset (Filter.mem_lift' hK) ?_
    rw [Set.iUnion₂_subset_iff]
    exact fun _ ⟨_, h⟩ => h

end TopologicalSpace.Compacts

namespace TopologicalSpace.NonemptyCompacts

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace (NonemptyCompacts α)
  body: .replaceTopology (.comap (↑) (.hausdorff α)) ext_nhds fun K => by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

中文:
实例 uniformSpace
  签名: : 一致空间 (NonemptyCompacts α)
  定义体: .replaceTopology (.comap (↑) (.hausdorff α)) ext_nhds fun K => by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

Depends on / 依赖: K.isCompact.nhds_hausdorff_eq_nhds_vietoris, ext_nhds, hausdorff, isCompact, nhds_hausdorff_eq_nhds_vietoris, nhds_induced, replaceTopology, simp_rw
-/
instance uniformSpace : UniformSpace (NonemptyCompacts α) :=
.replaceTopology (.comap (↑) (.hausdorff α)) ext_nhds fun K => by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

/--
theorem `uniformity_def` / 定理 `uniformity_def`

English:
theorem uniformity_def
  proof: rfl

中文:
定理 uniformity_def
  证明: rfl
-/
theorem uniformity_def :
    𝓤 (NonemptyCompacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl

/--
theorem `_root_.Filter.HasBasis.uniformity_nonemptyCompacts` / 定理 `_root_.Filter.HasBasis.uniformity_nonemptyCompacts`

English:
theorem _root_.Filter.HasBasis.uniformity_nonemptyCompacts
  proof: h.uniformity_hausdorff.comap _

中文:
定理 _root_.滤子.有基.uniformity_nonemptyCompacts
  证明: h.uniformity_hausdorff.comap _

Depends on / 依赖: h.uniformity_hausdorff.comap, uniformity_hausdorff
-/
theorem _root_.Filter.HasBasis.uniformity_nonemptyCompacts
    {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (NonemptyCompacts α)).HasBasis p
      (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _

/--
theorem `isUniformEmbedding_coe` / 定理 `isUniformEmbedding_coe`

English:
theorem isUniformEmbedding_coe
  statement: IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where
  proof: SetLike.coe_injective
  comap_uniformity := rfl

中文:
定理 isUniformEmbedding_coe
  结论: 是一致嵌入 ((↑) : NonemptyCompacts α -> 集合 α) where
  证明: SetLike.coe_injective
  comap_uniformity := rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl

/--
theorem `uniformContinuous_coe` / 定理 `uniformContinuous_coe`

English:
theorem uniformContinuous_coe
  statement: UniformContinuous ((↑) : NonemptyCompacts α -> Set α)
  proof: isUniformEmbedding_coe.uniformContinuous

中文:
定理 uniformContinuous_coe
  结论: 一致连续 ((↑) : NonemptyCompacts α -> 集合 α)
  证明: isUniformEmbedding_coe.uniformContinuous

Depends on / 依赖: isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : NonemptyCompacts α -> Set α) :=
  isUniformEmbedding_coe.uniformContinuous

/--
theorem `isUniformEmbedding_toCloseds` / 定理 `isUniformEmbedding_toCloseds`

English:
theorem isUniformEmbedding_toCloseds
  given: [T2Space α]
  statement: IsUniformEmbedding (toCloseds (α := α)) where
  proof: toCloseds_injective
  comap_uniformity := Filter.comap_comap

中文:
定理 isUniformEmbedding_toCloseds
  条件: [T2空间 α]
  结论: 是一致嵌入 (toCloseds (α := α)) where
  证明: toCloseds_injective
  comap_uniformity := Filter.comap_comap
-/
theorem isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_comap

/--
theorem `uniformContinuous_toCloseds` / 定理 `uniformContinuous_toCloseds`

English:
theorem uniformContinuous_toCloseds
  given: [T2Space α]
  statement: UniformContinuous (toCloseds (α := α))
  proof: isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_toCloseds
  条件: [T2空间 α]
  结论: 一致连续 (toCloseds (α := α))
  证明: isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
-/
theorem uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
/--
theorem `isEmbedding_toCloseds` / 定理 `isEmbedding_toCloseds`

English:
theorem isEmbedding_toCloseds
  given: [T2Space α]
  statement: IsEmbedding (toCloseds (α := α))
  proof: isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]

中文:
定理 isEmbedding_toCloseds
  条件: [T2空间 α]
  结论: 是嵌入 (toCloseds (α := α))
  证明: isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
-/
theorem isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
/--
theorem `continuous_toCloseds` / 定理 `continuous_toCloseds`

English:
theorem continuous_toCloseds
  given: [T2Space α]
  statement: Continuous (toCloseds (α := α))
  proof: uniformContinuous_toCloseds.continuous

@[fun_prop]

中文:
定理 continuous_toCloseds
  条件: [T2空间 α]
  结论: 连续 (toCloseds (α := α))
  证明: uniformContinuous_toCloseds.continuous

@[fun_prop]
-/
theorem continuous_toCloseds [T2Space α] : Continuous (toCloseds (α := α)) :=
  uniformContinuous_toCloseds.continuous

@[fun_prop]
/--
theorem `isClosedEmbedding_toCloseds` / 定理 `isClosedEmbedding_toCloseds`

English:
theorem isClosedEmbedding_toCloseds
  given: [T2Space α] [CompleteSpace α]
  proof: Compacts.isClosedEmbedding_toCloseds.comp isClosedEmbedding_toCompacts

中文:
定理 isClosedEmbedding_toCloseds
  条件: [T2空间 α] [完备空间 α]
  证明: Compacts.isClosedEmbedding_toCloseds.comp isClosedEmbedding_toCompacts
-/
theorem isClosedEmbedding_toCloseds [T2Space α] [CompleteSpace α] :
    IsClosedEmbedding (toCloseds (α := α)) :=
  Compacts.isClosedEmbedding_toCloseds.comp isClosedEmbedding_toCompacts

/--
theorem `isUniformEmbedding_toCompacts` / 定理 `isUniformEmbedding_toCompacts`

English:
theorem isUniformEmbedding_toCompacts
  statement: IsUniformEmbedding (toCompacts (α := α)) where
  proof: toCompacts_injective
  comap_uniformity := Filter.comap_comap

中文:
定理 isUniformEmbedding_toCompacts
  结论: 是一致嵌入 (toCompacts (α := α)) where
  证明: toCompacts_injective
  comap_uniformity := Filter.comap_comap
-/
theorem isUniformEmbedding_toCompacts : IsUniformEmbedding (toCompacts (α := α)) where
  injective := toCompacts_injective
  comap_uniformity := Filter.comap_comap

/--
theorem `uniformContinuous_toCompacts` / 定理 `uniformContinuous_toCompacts`

English:
theorem uniformContinuous_toCompacts
  statement: UniformContinuous (toCompacts (α := α))
  proof: isUniformEmbedding_toCompacts.uniformContinuous

中文:
定理 uniformContinuous_toCompacts
  结论: 一致连续 (toCompacts (α := α))
  证明: isUniformEmbedding_toCompacts.uniformContinuous
-/
theorem uniformContinuous_toCompacts : UniformContinuous (toCompacts (α := α)) :=
  isUniformEmbedding_toCompacts.uniformContinuous

/--
theorem `totallyBounded_subsets_of_totallyBounded` / 定理 `totallyBounded_subsets_of_totallyBounded`

English:
theorem totallyBounded_subsets_of_totallyBounded
  given: {t : Set α} (ht : TotallyBounded t)
  proof: totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

中文:
定理 totallyBounded_subsets_of_totallyBounded
  条件: {t : 集合 α} (ht : 全有界 t)
  证明: totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

Depends on / 依赖: ht.powerset_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.isUniformInducing, isUniformInducing, powerset_hausdorff, totallyBounded_preimage
-/
theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {K : NonemptyCompacts α | ↑K subseteq t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

/--
theorem `isUniformEmbedding_singleton` / 定理 `isUniformEmbedding_singleton`

English:
theorem isUniformEmbedding_singleton
  statement: IsUniformEmbedding ({·} : α -> NonemptyCompacts α)
  proof: isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

中文:
定理 isUniformEmbedding_singleton
  结论: 是一致嵌入 ({·} : α -> NonemptyCompacts α)
  证明: isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.isUniformEmbedding_singleton, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.of_comp_iff.mp, isUniformEmbedding_singleton, of_comp_iff
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> NonemptyCompacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

/--
theorem `uniformContinuous_singleton` / 定理 `uniformContinuous_singleton`

English:
theorem uniformContinuous_singleton
  statement: UniformContinuous ({·} : α -> NonemptyCompacts α)
  proof: isUniformEmbedding_singleton.uniformContinuous

中文:
定理 uniformContinuous_singleton
  结论: 一致连续 ({·} : α -> NonemptyCompacts α)
  证明: isUniformEmbedding_singleton.uniformContinuous

Depends on / 依赖: isUniformEmbedding_singleton, isUniformEmbedding_singleton.uniformContinuous, uniformContinuous
-/
theorem uniformContinuous_singleton : UniformContinuous ({·} : α -> NonemptyCompacts α) :=
  isUniformEmbedding_singleton.uniformContinuous

/--
theorem `uniformContinuous_sup` / 定理 `uniformContinuous_sup`

English:
theorem uniformContinuous_sup
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

中文:
定理 uniformContinuous_sup
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.uniformContinuous_union.comp, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, prodMap, uniformContinuous_coe, uniformContinuous_coe.prodMap, uniformContinuous_iff, uniformContinuous_union
-/
theorem uniformContinuous_sup :
    UniformContinuous (fun x : NonemptyCompacts α × NonemptyCompacts α => x.1 ⊔ x.2) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_union.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

/--
theorem `_root_.UniformContinuous.sup_nonemptyCompacts` / 定理 `_root_.UniformContinuous.sup_nonemptyCompacts`

English:
theorem _root_.UniformContinuous.sup_nonemptyCompacts
  proof: uniformContinuous_sup.comp hf.prodMk hg

中文:
定理 _root_.一致连续.sup_nonemptyCompacts
  证明: uniformContinuous_sup.comp hf.prodMk hg

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_sup, uniformContinuous_sup.comp
-/
theorem _root_.UniformContinuous.sup_nonemptyCompacts
    {f g : α -> NonemptyCompacts β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
uniformContinuous_sup.comp hf.prodMk hg

/--
theorem `uniformContinuous_prod` / 定理 `uniformContinuous_prod`

English:
theorem uniformContinuous_prod
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

中文:
定理 uniformContinuous_prod
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

Depends on / 依赖: UniformSpace, UniformSpace.hausdorff.uniformContinuous_prod.comp, hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, prodMap, uniformContinuous_coe, uniformContinuous_coe.prodMap, uniformContinuous_iff, uniformContinuous_prod
-/
theorem uniformContinuous_prod :
    UniformContinuous (fun x : NonemptyCompacts α × NonemptyCompacts β => x.1 ×ˢ x.2) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr
UniformSpace.hausdorff.uniformContinuous_prod.comp
      uniformContinuous_coe.prodMap uniformContinuous_coe

/--
theorem `_root_.UniformContinuous.prod_nonemptyCompacts` / 定理 `_root_.UniformContinuous.prod_nonemptyCompacts`

English:
theorem _root_.UniformContinuous.prod_nonemptyCompacts
  proof: uniformContinuous_prod.comp (hf.prodMk hg)

中文:
定理 _root_.一致连续.prod_nonemptyCompacts
  证明: uniformContinuous_prod.comp (hf.prodMk hg)

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_prod, uniformContinuous_prod.comp
-/
theorem _root_.UniformContinuous.prod_nonemptyCompacts
    {f : α -> NonemptyCompacts β} {g : α -> NonemptyCompacts γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous (fun x => f x ×ˢ g x) :=
  uniformContinuous_prod.comp (hf.prodMk hg)

/--
theorem `_root_.UniformContinuous.nonemptyCompacts_map` / 定理 `_root_.UniformContinuous.nonemptyCompacts_map`

English:
theorem _root_.UniformContinuous.nonemptyCompacts_map
  given: {f : α -> β} (hf : UniformContinuous f)
  proof: isUniformEmbedding_coe.uniformContinuous_iff.mpr hf.image_hausdorff.comp uniformContinuous_coe

中文:
定理 _root_.一致连续.nonemptyCompacts_map
  条件: {f : α -> β} (hf : 一致连续 f)
  证明: isUniformEmbedding_coe.uniformContinuous_iff.mpr hf.image_hausdorff.comp uniformContinuous_coe

Depends on / 依赖: hf.image_hausdorff.comp, image_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous_iff.mpr, uniformContinuous_coe, uniformContinuous_iff
-/
theorem _root_.UniformContinuous.nonemptyCompacts_map {f : α -> β} (hf : UniformContinuous f) :
    UniformContinuous (NonemptyCompacts.map f hf.continuous) :=
isUniformEmbedding_coe.uniformContinuous_iff.mpr hf.image_hausdorff.comp uniformContinuous_coe

/--
theorem `_root_.IsUniformInducing.nonemptyCompacts_map` / 定理 `_root_.IsUniformInducing.nonemptyCompacts_map`

English:
theorem _root_.IsUniformInducing.nonemptyCompacts_map
  given: {f : α -> β} (hf : IsUniformInducing f)
  proof: .of_comp hf.uniformContinuous.nonemptyCompacts_map uniformContinuous_coe
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

中文:
定理 _root_.是UniformInducing.nonemptyCompacts_map
  条件: {f : α -> β} (hf : 是UniformInducing f)
  证明: .of_comp hf.uniformContinuous.nonemptyCompacts_map uniformContinuous_coe
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

Depends on / 依赖: hf.image_hausdorff.comp, hf.uniformContinuous.nonemptyCompacts_map, image_hausdorff, isUniformEmbedding_coe, isUniformEmbedding_coe.isUniformInducing, isUniformInducing, nonemptyCompacts_map, of_comp, uniformContinuous, uniformContinuous_coe
-/
theorem _root_.IsUniformInducing.nonemptyCompacts_map {f : α -> β} (hf : IsUniformInducing f) :
    IsUniformInducing (NonemptyCompacts.map f hf.uniformContinuous.continuous) :=
.of_comp hf.uniformContinuous.nonemptyCompacts_map uniformContinuous_coe
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

/--
theorem `_root_.IsUniformEmbedding.nonemptyCompacts_map` / 定理 `_root_.IsUniformEmbedding.nonemptyCompacts_map`

English:
theorem _root_.IsUniformEmbedding.nonemptyCompacts_map
  given: {f : α -> β} (hf : IsUniformEmbedding f)
  proof: hf.isUniformInducing.nonemptyCompacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

中文:
定理 _root_.是一致嵌入.nonemptyCompacts_map
  条件: {f : α -> β} (hf : 是一致嵌入 f)
  证明: hf.isUniformInducing.nonemptyCompacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

Depends on / 依赖: hf.isUniformInducing.nonemptyCompacts_map, isUniformInducing, nonemptyCompacts_map
-/
theorem _root_.IsUniformEmbedding.nonemptyCompacts_map {f : α -> β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (NonemptyCompacts.map f hf.uniformContinuous.continuous) where
  __ := hf.isUniformInducing.nonemptyCompacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteUniformity
  signature: α] : DiscreteUniformity (NonemptyCompacts α)
  body: isUniformEmbedding_coe.discreteUniformity

@[simp]

中文:
实例 [DiscreteUniformity
  签名: α] : DiscreteUniformity (NonemptyCompacts α)
  定义体: isUniformEmbedding_coe.discreteUniformity

@[simp]

Depends on / 依赖: discreteUniformity, isUniformEmbedding_coe, isUniformEmbedding_coe.discreteUniformity
-/
instance [DiscreteUniformity α] : DiscreteUniformity (NonemptyCompacts α) :=
  isUniformEmbedding_coe.discreteUniformity

@[simp]
/--
theorem `discreteUniformity_iff` / 定理 `discreteUniformity_iff`

English:
theorem discreteUniformity_iff
  statement: DiscreteUniformity (NonemptyCompacts α) ↔ DiscreteUniformity α
  proof: ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

中文:
定理 discreteUniformity_iff
  结论: DiscreteUniformity (NonemptyCompacts α) ↔ DiscreteUniformity α
  证明: ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

Depends on / 依赖: discreteUniformity, isUniformEmbedding_singleton, isUniformEmbedding_singleton.discreteUniformity
-/
theorem discreteUniformity_iff : DiscreteUniformity (NonemptyCompacts α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: α] : CompleteSpace (NonemptyCompacts α)
  body: isUniformEmbedding_toCompacts.completeSpace isClosedEmbedding_toCompacts.isClosed_range.isComplete

@[simp]

中文:
实例 [完备空间
  签名: α] : 完备空间 (NonemptyCompacts α)
  定义体: isUniformEmbedding_toCompacts.completeSpace isClosedEmbedding_toCompacts.isClosed_range.isComplete

@[simp]

Depends on / 依赖: completeSpace, isClosedEmbedding_toCompacts, isClosedEmbedding_toCompacts.isClosed_range.isComplete, isClosed_range, isComplete, isUniformEmbedding_toCompacts, isUniformEmbedding_toCompacts.completeSpace
-/
instance [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  isUniformEmbedding_toCompacts.completeSpace isClosedEmbedding_toCompacts.isClosed_range.isComplete

@[simp]
/--
theorem `completeSpace_iff` / 定理 `completeSpace_iff`

English:
theorem completeSpace_iff
  statement: CompleteSpace (NonemptyCompacts α) ↔ CompleteSpace α
  proof: by
  refine ⟨fun _ => ⟨fun {f} hf => ?_⟩, fun _ => inferInstance⟩
obtain ⟨K, hK⟩ := CompleteSpace.complete hf.map uniformContinuous_singleton
  obtain ⟨x, hx⟩ := K.nonempty
  exists x
  rw [(nhds_basis_opens x).ge_iff]
  intro U ⟨hxU, hU⟩
  filter_upwards [hK <| (isOpen_inter_nonempty_of_isOpen hU).

中文:
定理 completeSpace_iff
  结论: 完备空间 (NonemptyCompacts α) ↔ 完备空间 α
  证明: by
  refine ⟨fun _ => ⟨fun {f} hf => ?_⟩, fun _ => inferInstance⟩
obtain ⟨K, hK⟩ := CompleteSpace.complete hf.map uniformContinuous_singleton
  obtain ⟨x, hx⟩ := K.nonempty
  exists x
  rw [(nhds_basis_opens x).ge_iff]
  intro U ⟨hxU, hU⟩
  filter_upwards [hK <| (isOpen_inter_nonempty_of_isOpen hU).

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, K.nonempty, complete, filter_upwards, ge_iff, hf.map, isOpen_inter_nonempty_of_isOpen, mem_nhds, nhds_basis_opens, nonempty, uniformContinuous_singleton
-/
theorem completeSpace_iff : CompleteSpace (NonemptyCompacts α) ↔ CompleteSpace α := by
  refine ⟨fun _ => ⟨fun {f} hf => ?_⟩, fun _ => inferInstance⟩
obtain ⟨K, hK⟩ := CompleteSpace.complete hf.map uniformContinuous_singleton
  obtain ⟨x, hx⟩ := K.nonempty
  exists x
  rw [(nhds_basis_opens x).ge_iff]
  intro U ⟨hxU, hU⟩
  filter_upwards [hK <| (isOpen_inter_nonempty_of_isOpen hU).mem_nhds ⟨x, hx, hxU⟩]
  simp

@[simp]
/--
theorem `_root_.TopologicalSpace.Compacts.completeSpace_iff` / 定理 `_root_.TopologicalSpace.Compacts.completeSpace_iff`

English:
theorem _root_.TopologicalSpace.Compacts.completeSpace_iff
  proof: NonemptyCompacts.completeSpace_iff.mp
      NonemptyCompacts.isUniformEmbedding_toCompacts.completeSpace
        isClosedEmbedding_toCompacts.isClosed_range.isComplete
  mpr _ := inferInstance

中文:
定理 _root_.拓扑空间.余mpacts.completeSpace_iff
  证明: NonemptyCompacts.completeSpace_iff.mp
      NonemptyCompacts.isUniformEmbedding_toCompacts.completeSpace
        isClosedEmbedding_toCompacts.isClosed_range.isComplete
  mpr _ := inferInstance

Depends on / 依赖: NonemptyCompacts, NonemptyCompacts.completeSpace_iff.mp, NonemptyCompacts.isUniformEmbedding_toCompacts.completeSpace, completeSpace, completeSpace_iff, isClosedEmbedding_toCompacts, isClosedEmbedding_toCompacts.isClosed_range.isComplete, isClosed_range, isComplete, isUniformEmbedding_toCompacts
-/
theorem _root_.TopologicalSpace.Compacts.completeSpace_iff :
    CompleteSpace (Compacts α) ↔ CompleteSpace α where
  mp _ :=
NonemptyCompacts.completeSpace_iff.mp
      NonemptyCompacts.isUniformEmbedding_toCompacts.completeSpace
        isClosedEmbedding_toCompacts.isClosed_range.isComplete
  mpr _ := inferInstance

end TopologicalSpace.NonemptyCompacts
