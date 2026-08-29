/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
module

public import Mathlib.Dynamics.Flow

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `atTop`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notation

The `omegaLimit` scope provides the localised notation `ω` for
`omegaLimit`, as well as `ω⁺` and `ω⁻` for `omegaLimit atTop` and
`omegaLimit atBot` respectively for when the acting monoid is
endowed with an order.
-/

@[expose] public section


open Set Function Filter Topology

/-!
### Definition and notation
-/
section omegaLimit

variable {τ : Type*} {α : Type*} {β : Type*} {ι : Type*}

/--
Definition of `omegaLimit` / `omegaLimit` 的定义

English:
definition omegaLimit
  signature: [TopologicalSpace β] (f : Filter τ) (ϕ : τ -> α -> β) (s : Set α)
  body: ⋂ u in f, closure (image2 ϕ u s)

@[inherit_doc]
scoped[omegaLimit] notation "ω" => omegaLimit

中文:
定义 omegaLimit
  签名: [拓扑空间 β] (f : 滤子 τ) (ϕ : τ -> α -> β) (s : 集合 α)
  定义体: ⋂ u in f, closure (image2 ϕ u s)

@[inherit_doc]
scoped[omegaLimit] notation "ω" => omegaLimit

Depends on / 依赖: closure, image2
-/
def omegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ -> α -> β) (s : Set α) : Set β :=
  ⋂ u in f, closure (image2 ϕ u s)

@[inherit_doc]
scoped[omegaLimit] notation "ω" => omegaLimit

/-- The ω-limit w.r.t. `Filter.atTop`. -/
scoped[omegaLimit] notation "ω⁺" => omegaLimit Filter.atTop

/-- The ω-limit w.r.t. `Filter.atBot`. -/
scoped[omegaLimit] notation "ω⁻" => omegaLimit Filter.atBot

variable [TopologicalSpace β]
variable (f : Filter τ) (ϕ : τ -> α -> β) (s s₁ s₂ : Set α)

/-!
### Elementary properties
-/
open omegaLimit

/--
theorem `omegaLimit_def` / 定理 `omegaLimit_def`

English:
theorem omegaLimit_def
  statement: ω f ϕ s = ⋂ u in f, closure (image2 ϕ u s)
  proof: rfl

中文:
定理 omegaLimit_def
  结论: ω f ϕ s = ⋂ u in f, closure (image2 ϕ u s)
  证明: rfl
-/
theorem omegaLimit_def : ω f ϕ s = ⋂ u in f, closure (image2 ϕ u s) := rfl

/--
theorem `omegaLimit_subset_of_tendsto` / 定理 `omegaLimit_subset_of_tendsto`

English:
theorem omegaLimit_subset_of_tendsto
  given: {m : τ -> τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂)
  proof: by
  refine iInter₂_mono' fun u hu => ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)

中文:
定理 omegaLimit_subset_of_tendsto
  条件: {m : τ -> τ} {f₁ f₂ : 滤子 τ} (hf : 收敛 m f₁ f₂)
  证明: by
  refine iInter₂_mono' fun u hu => ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)

Depends on / 依赖: Subset, Subset.rfl, closure_mono, image2_image_left, image2_subset, image_preimage_subset, tendsto_def, tendsto_def.mp
-/
theorem omegaLimit_subset_of_tendsto {m : τ -> τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x => ϕ (m t) x) s subseteq ω f₂ ϕ s := by
  refine iInter₂_mono' fun u hu => ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)

/--
theorem `omegaLimit_mono_left` / 定理 `omegaLimit_mono_left`

English:
theorem omegaLimit_mono_left
  given: {f₁ f₂ : Filter τ} (hf : f₁ <= f₂)
  statement: ω f₁ ϕ s subseteq ω f₂ ϕ s
  proof: omegaLimit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)

中文:
定理 omegaLimit_mono_left
  条件: {f₁ f₂ : 滤子 τ} (hf : f₁ <= f₂)
  结论: ω f₁ ϕ s subseteq ω f₂ ϕ s
  证明: omegaLimit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)

Depends on / 依赖: omegaLimit_subset_of_tendsto, tendsto_id
-/
theorem omegaLimit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ <= f₂) : ω f₁ ϕ s subseteq ω f₂ ϕ s :=
  omegaLimit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)

/--
theorem `omegaLimit_mono_right` / 定理 `omegaLimit_mono_right`

English:
theorem omegaLimit_mono_right
  given: {s₁ s₂ : Set α} (hs : s₁ subseteq s₂)
  statement: ω f ϕ s₁ subseteq ω f ϕ s₂
  proof: iInter₂_mono fun _u _hu => closure_mono (image2_subset Subset.rfl hs)

中文:
定理 omegaLimit_mono_right
  条件: {s₁ s₂ : 集合 α} (hs : s₁ subseteq s₂)
  结论: ω f ϕ s₁ subseteq ω f ϕ s₂
  证明: iInter₂_mono fun _u _hu => closure_mono (image2_subset Subset.rfl hs)

Depends on / 依赖: Subset, Subset.rfl, closure_mono, image2_subset
-/
theorem omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ subseteq s₂) : ω f ϕ s₁ subseteq ω f ϕ s₂ :=
  iInter₂_mono fun _u _hu => closure_mono (image2_subset Subset.rfl hs)

/--
theorem `isClosed_omegaLimit` / 定理 `isClosed_omegaLimit`

English:
theorem isClosed_omegaLimit
  statement: IsClosed (ω f ϕ s)
  proof: isClosed_iInter fun _u => isClosed_iInter fun _hu => isClosed_closure

中文:
定理 isClosed_omegaLimit
  结论: 是闭集 (ω f ϕ s)
  证明: isClosed_iInter fun _u => isClosed_iInter fun _hu => isClosed_closure

Depends on / 依赖: isClosed_closure, isClosed_iInter
-/
theorem isClosed_omegaLimit : IsClosed (ω f ϕ s) :=
  isClosed_iInter fun _u => isClosed_iInter fun _hu => isClosed_closure

/--
theorem `mapsTo_omegaLimit'` / 定理 `mapsTo_omegaLimit'`

English:
theorem mapsTo_omegaLimit'
  statement: {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ -> α -> β}
  proof: by
  simp only [omegaLimit_def, mem_iInter, MapsTo]
  intro y hy u hu
  refine map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_mem_image2.2 fun t ht x hx => ?_)
  calc
    ϕ' t (ga x) in image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)
.symm _ = gb (ϕ t x) := ht.2 hx

中文:
定理 mapsTo_omegaLimit'
  结论: {α' β' : 类型} [拓扑空间 β'] {f : 滤子 τ} {ϕ : τ -> α -> β}
  证明: by
  simp only [omegaLimit_def, mem_iInter, MapsTo]
  intro y hy u hu
  refine map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_mem_image2.2 fun t ht x hx => ?_)
  calc
    ϕ' t (ga x) in image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)
.symm _ = gb (ϕ t x) := ht.2 hx

Depends on / 依赖: MapsTo, forall_mem_image2, image2, inter_mem, map_mem_closure, mem_iInter, mem_image2_of_mem, omegaLimit_def
-/
theorem mapsTo_omegaLimit' {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ -> α -> β}
    {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β -> β'}
    (hg : forallᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') := by
  simp only [omegaLimit_def, mem_iInter, MapsTo]
  intro y hy u hu
  refine map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_mem_image2.2 fun t ht x hx => ?_)
  calc
    ϕ' t (ga x) in image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)
.symm _ = gb (ϕ t x) := ht.2 hx

/--
theorem `mapsTo_omegaLimit` / 定理 `mapsTo_omegaLimit`

English:
theorem mapsTo_omegaLimit
  statement: {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ -> α -> β}
  proof: mapsTo_omegaLimit' _ hs (Eventually.of_forall fun t x _hx => hg t x) hgc

中文:
定理 mapsTo_omegaLimit
  结论: {α' β' : 类型} [拓扑空间 β'] {f : 滤子 τ} {ϕ : τ -> α -> β}
  证明: mapsTo_omegaLimit' _ hs (Eventually.of_forall fun t x _hx => hg t x) hgc

Depends on / 依赖: Eventually, Eventually.of_forall, mapsTo_omegaLimit, of_forall
-/
theorem mapsTo_omegaLimit {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ -> α -> β}
    {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β -> β'}
    (hg : forall t x, gb (ϕ t x) = ϕ' t (ga x)) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') :=
  mapsTo_omegaLimit' _ hs (Eventually.of_forall fun t x _hx => hg t x) hgc

/--
theorem `omegaLimit_image_eq` / 定理 `omegaLimit_image_eq`

English:
theorem omegaLimit_image_eq
  given: {α' : Type*} (ϕ : τ -> α' -> β) (f : Filter τ) (g : α -> α')
  proof: by simp only [omegaLimit, image2_image_right]

中文:
定理 omegaLimit_image_eq
  条件: {α' : 类型} (ϕ : τ -> α' -> β) (f : 滤子 τ) (g : α -> α')
  证明: by simp only [omegaLimit, image2_image_right]

Depends on / 依赖: image2_image_right, omegaLimit
-/
theorem omegaLimit_image_eq {α' : Type*} (ϕ : τ -> α' -> β) (f : Filter τ) (g : α -> α') :
    ω f ϕ (g '' s) = ω f (fun t x => ϕ t (g x)) s := by simp only [omegaLimit, image2_image_right]

/--
theorem `omegaLimit_preimage_subset` / 定理 `omegaLimit_preimage_subset`

English:
theorem omegaLimit_preimage_subset
  statement: {α' : Type*} (ϕ : τ -> α' -> β) (s : Set α') (f : Filter τ)
  proof: mapsTo_omegaLimit _ (mapsTo_preimage _ _) (fun _t _x => rfl) continuous_id

中文:
定理 omegaLimit_preimage_subset
  结论: {α' : 类型} (ϕ : τ -> α' -> β) (s : 集合 α') (f : 滤子 τ)
  证明: mapsTo_omegaLimit _ (mapsTo_preimage _ _) (fun _t _x => rfl) continuous_id

Depends on / 依赖: continuous_id, mapsTo_omegaLimit, mapsTo_preimage
-/
theorem omegaLimit_preimage_subset {α' : Type*} (ϕ : τ -> α' -> β) (s : Set α') (f : Filter τ)
    (g : α -> α') : ω f (fun t x => ϕ t (g x)) (g ⁻¹' s) subseteq ω f ϕ s :=
  mapsTo_omegaLimit _ (mapsTo_preimage _ _) (fun _t _x => rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/

/--
theorem `mem_omegaLimit_iff_frequently` / 定理 `mem_omegaLimit_iff_frequently`

English:
theorem mem_omegaLimit_iff_frequently
  given: (y : β)
  proof: by
  simp_rw [frequently_iff, omegaLimit_def, mem_iInter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, ht, _, hx, rfl⟩
    exact ⟨_, ht, _, hx, by rwa [mem_preimage]⟩
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, ht, _, hx, rfl⟩

中文:
定理 mem_omegaLimit_iff_frequently
  条件: (y : β)
  证明: by
  simp_rw [frequently_iff, omegaLimit_def, mem_iInter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, ht, _, hx, rfl⟩
    exact ⟨_, ht, _, hx, by rwa [mem_preimage]⟩
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, ht, _, hx, rfl⟩

Depends on / 依赖: frequently_iff, mem_closure_iff_nhds, mem_iInter, mem_preimage, omegaLimit_def, simp_rw
-/
theorem mem_omegaLimit_iff_frequently (y : β) :
    y in ω f ϕ s ↔ forall n in 𝓝 y, existsᶠ t in f, (s inter ϕ t ⁻¹' n).Nonempty := by
  simp_rw [frequently_iff, omegaLimit_def, mem_iInter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, ht, _, hx, rfl⟩
    exact ⟨_, ht, _, hx, by rwa [mem_preimage]⟩
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, ht, _, hx, rfl⟩

/--
theorem `mem_omegaLimit_iff_frequently₂` / 定理 `mem_omegaLimit_iff_frequently₂`

English:
theorem mem_omegaLimit_iff_frequently₂
  given: (y : β)
  proof: by
  simp_rw [mem_omegaLimit_iff_frequently, image_inter_nonempty_iff]

中文:
定理 mem_omegaLimit_iff_frequently₂
  条件: (y : β)
  证明: by
  simp_rw [mem_omegaLimit_iff_frequently, image_inter_nonempty_iff]

Depends on / 依赖: image_inter_nonempty_iff, mem_omegaLimit_iff_frequently, simp_rw
-/
theorem mem_omegaLimit_iff_frequently₂ (y : β) :
    y in ω f ϕ s ↔ forall n in 𝓝 y, existsᶠ t in f, (ϕ t '' s inter n).Nonempty := by
  simp_rw [mem_omegaLimit_iff_frequently, image_inter_nonempty_iff]

/--
theorem `mem_omegaLimit_singleton_iff_mapClusterPt` / 定理 `mem_omegaLimit_singleton_iff_mapClusterPt`

English:
theorem mem_omegaLimit_singleton_iff_mapClusterPt
  given: (x : α) (y : β)
  proof: by
  simp_rw [mem_omegaLimit_iff_frequently, mapClusterPt_iff_frequently, singleton_inter_nonempty,
    mem_preimage]

@[deprecated (since := "2026-03-31")]
alias mem_omegaLimit_singleton_iff_map_cluster_point := mem_omegaLimit_singleton_iff_mapClusterPt

中文:
定理 mem_omegaLimit_singleton_iff_mapClusterPt
  条件: (x : α) (y : β)
  证明: by
  simp_rw [mem_omegaLimit_iff_frequently, mapClusterPt_iff_frequently, singleton_inter_nonempty,
    mem_preimage]

@[deprecated (since := "2026-03-31")]
alias mem_omegaLimit_singleton_iff_map_cluster_point := mem_omegaLimit_singleton_iff_mapClusterPt

Depends on / 依赖: mapClusterPt_iff_frequently, mem_omegaLimit_iff_frequently, mem_preimage, simp_rw, singleton_inter_nonempty
-/
theorem mem_omegaLimit_singleton_iff_mapClusterPt (x : α) (y : β) :
    y in ω f ϕ {x} ↔ MapClusterPt y f fun t => ϕ t x := by
  simp_rw [mem_omegaLimit_iff_frequently, mapClusterPt_iff_frequently, singleton_inter_nonempty,
    mem_preimage]

@[deprecated (since := "2026-03-31")]
alias mem_omegaLimit_singleton_iff_map_cluster_point := mem_omegaLimit_singleton_iff_mapClusterPt


/--
theorem `omegaLimit_inter` / 定理 `omegaLimit_inter`

English:
theorem omegaLimit_inter
  statement: ω f ϕ (s₁ inter s₂) subseteq ω f ϕ s₁ inter ω f ϕ s₂
  proof: subset_inter (omegaLimit_mono_right _ _ inter_subset_left)
    (omegaLimit_mono_right _ _ inter_subset_right)

中文:
定理 omegaLimit_inter
  结论: ω f ϕ (s₁ inter s₂) subseteq ω f ϕ s₁ inter ω f ϕ s₂
  证明: subset_inter (omegaLimit_mono_right _ _ inter_subset_left)
    (omegaLimit_mono_right _ _ inter_subset_right)

Depends on / 依赖: inter_subset_left, inter_subset_right, omegaLimit_mono_right, subset_inter
-/
theorem omegaLimit_inter : ω f ϕ (s₁ inter s₂) subseteq ω f ϕ s₁ inter ω f ϕ s₂ :=
  subset_inter (omegaLimit_mono_right _ _ inter_subset_left)
    (omegaLimit_mono_right _ _ inter_subset_right)

/--
theorem `omegaLimit_iInter` / 定理 `omegaLimit_iInter`

English:
theorem omegaLimit_iInter
  given: (p : ι -> Set α)
  statement: ω f ϕ (⋂ i, p i) subseteq ⋂ i, ω f ϕ (p i)
  proof: subset_iInter fun _i => omegaLimit_mono_right _ _ (iInter_subset _ _)

中文:
定理 omegaLimit_i整数er
  条件: (p : ι -> 集合 α)
  结论: ω f ϕ (⋂ i, p i) subseteq ⋂ i, ω f ϕ (p i)
  证明: subset_iInter fun _i => omegaLimit_mono_right _ _ (iInter_subset _ _)

Depends on / 依赖: iInter_subset, omegaLimit_mono_right, subset_iInter
-/
theorem omegaLimit_iInter (p : ι -> Set α) : ω f ϕ (⋂ i, p i) subseteq ⋂ i, ω f ϕ (p i) :=
  subset_iInter fun _i => omegaLimit_mono_right _ _ (iInter_subset _ _)

/--
theorem `omegaLimit_union` / 定理 `omegaLimit_union`

English:
theorem omegaLimit_union
  statement: ω f ϕ (s₁ union s₂) = ω f ϕ s₁ union ω f ϕ s₂
  proof: by
  ext y; constructor
  · simp only [mem_union, mem_omegaLimit_iff_frequently, union_inter_distrib_right, union_nonempty,
      frequently_or_distrib]
    contrapose!
    simp only [← subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine ⟨n₁ inter n₂, inter_mem hn₁ hn₂, h₁.mono fun t => ?_, h₂.mono fun t => ?_⟩
    exacts [Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_left,
Subset.trans inter_subset_inter_right _ preimage_mono inter_subset_right]
  · rintro (hy | hy)
    exacts [omegaLimit_mono_right _ _ subset_union_left hy,
      omegaLimit_mono_right _ _ subset_union_right hy]

中文:
定理 omegaLimit_union
  结论: ω f ϕ (s₁ union s₂) = ω f ϕ s₁ union ω f ϕ s₂
  证明: by
  ext y; constructor
  · simp only [mem_union, mem_omegaLimit_iff_frequently, union_inter_distrib_right, union_nonempty,
      frequently_or_distrib]
    contrapose!
    simp only [← subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine ⟨n₁ inter n₂, inter_mem hn₁ hn₂, h₁.mono fun t => ?_, h₂.mono fun t => ?_⟩
    exacts [Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_left,
Subset.trans inter_subset_inter_right _ preimage_mono inter_subset_right]
  · rintro (hy | hy)
    exacts [omegaLimit_mono_right _ _ subset_union_left hy,
      omegaLimit_mono_right _ _ subset_union_right hy]

Depends on / 依赖: Subset, Subset.trans, contrapose, exacts, frequently_or_distrib, inter_mem, inter_subset_inter_right, inter_subset_left, inter_subset_right, mem_omegaLimit_iff_frequently, mem_union, omegaL, preimage_mono, subset_empty_iff, union_inter_distrib_right, union_nonempty
-/
theorem omegaLimit_union : ω f ϕ (s₁ union s₂) = ω f ϕ s₁ union ω f ϕ s₂ := by
  ext y; constructor
  · simp only [mem_union, mem_omegaLimit_iff_frequently, union_inter_distrib_right, union_nonempty,
      frequently_or_distrib]
    contrapose!
    simp only [← subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine ⟨n₁ inter n₂, inter_mem hn₁ hn₂, h₁.mono fun t => ?_, h₂.mono fun t => ?_⟩
    exacts [Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_left,
Subset.trans inter_subset_inter_right _ preimage_mono inter_subset_right]
  · rintro (hy | hy)
    exacts [omegaLimit_mono_right _ _ subset_union_left hy,
      omegaLimit_mono_right _ _ subset_union_right hy]

/--
theorem `omegaLimit_iUnion` / 定理 `omegaLimit_iUnion`

English:
theorem omegaLimit_iUnion
  given: (p : ι -> Set α)
  statement: ⋃ i, ω f ϕ (p i) subseteq ω f ϕ (⋃ i, p i)
  proof: by
  rw [iUnion_subset_iff]
  exact fun i => omegaLimit_mono_right _ _ (subset_iUnion _ _)

中文:
定理 omegaLimit_iUnion
  条件: (p : ι -> 集合 α)
  结论: ⋃ i, ω f ϕ (p i) subseteq ω f ϕ (⋃ i, p i)
  证明: by
  rw [iUnion_subset_iff]
  exact fun i => omegaLimit_mono_right _ _ (subset_iUnion _ _)

Depends on / 依赖: iUnion_subset_iff, omegaLimit_mono_right, subset_iUnion
-/
theorem omegaLimit_iUnion (p : ι -> Set α) : ⋃ i, ω f ϕ (p i) subseteq ω f ϕ (⋃ i, p i) := by
  rw [iUnion_subset_iff]
  exact fun i => omegaLimit_mono_right _ _ (subset_iUnion _ _)


/--
theorem `omegaLimit_eq_iInter` / 定理 `omegaLimit_eq_iInter`

English:
theorem omegaLimit_eq_iInter
  statement: ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s)
  proof: biInter_eq_iInter _ _

中文:
定理 omegaLimit_eq_i整数er
  结论: ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s)
  证明: biInter_eq_iInter _ _

Depends on / 依赖: biInter_eq_iInter
-/
theorem omegaLimit_eq_iInter : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s) :=
  biInter_eq_iInter _ _

/--
theorem `omegaLimit_eq_biInter_inter` / 定理 `omegaLimit_eq_biInter_inter`

English:
theorem omegaLimit_eq_biInter_inter
  given: {v : Set τ} (hv : v in f)
  proof: Subset.antisymm (iInter₂_mono' fun u hu => ⟨u inter v, inter_mem hu hv, Subset.rfl⟩)
    (iInter₂_mono fun _u _hu => closure_mono <| image2_subset inter_subset_left Subset.rfl)

中文:
定理 omegaLimit_eq_bi整数er_inter
  条件: {v : 集合 τ} (hv : v in f)
  证明: Subset.antisymm (iInter₂_mono' fun u hu => ⟨u inter v, inter_mem hu hv, Subset.rfl⟩)
    (iInter₂_mono fun _u _hu => closure_mono <| image2_subset inter_subset_left Subset.rfl)

Depends on / 依赖: Subset, Subset.antisymm, Subset.rfl, antisymm, closure_mono, image2_subset, inter_mem, inter_subset_left
-/
theorem omegaLimit_eq_biInter_inter {v : Set τ} (hv : v in f) :
    ω f ϕ s = ⋂ u in f, closure (image2 ϕ (u inter v) s) :=
  Subset.antisymm (iInter₂_mono' fun u hu => ⟨u inter v, inter_mem hu hv, Subset.rfl⟩)
    (iInter₂_mono fun _u _hu => closure_mono <| image2_subset inter_subset_left Subset.rfl)

/--
theorem `omegaLimit_eq_iInter_inter` / 定理 `omegaLimit_eq_iInter_inter`

English:
theorem omegaLimit_eq_iInter_inter
  given: {v : Set τ} (hv : v in f)
  proof: by
  rw [omegaLimit_eq_biInter_inter _ _ _ hv]
  apply biInter_eq_iInter

中文:
定理 omegaLimit_eq_i整数er_inter
  条件: {v : 集合 τ} (hv : v in f)
  证明: by
  rw [omegaLimit_eq_biInter_inter _ _ _ hv]
  apply biInter_eq_iInter

Depends on / 依赖: biInter_eq_iInter, omegaLimit_eq_biInter_inter
-/
theorem omegaLimit_eq_iInter_inter {v : Set τ} (hv : v in f) :
    ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ (u inter v) s) := by
  rw [omegaLimit_eq_biInter_inter _ _ _ hv]
  apply biInter_eq_iInter

/--
theorem `omegaLimit_subset_closure_image2` / 定理 `omegaLimit_subset_closure_image2`

English:
theorem omegaLimit_subset_closure_image2
  given: {u : Set τ} (hu : u in f)
  proof: by
  rw [omegaLimit_eq_iInter]
  intro _ hx
  rw [mem_iInter] at hx
  exact hx ⟨u, hu⟩

@[deprecated (since := "2026-03-31")]
alias omegaLimit_subset_closure_fw_image := omegaLimit_subset_closure_image2

中文:
定理 omegaLimit_subset_closure_image2
  条件: {u : 集合 τ} (hu : u in f)
  证明: by
  rw [omegaLimit_eq_iInter]
  intro _ hx
  rw [mem_iInter] at hx
  exact hx ⟨u, hu⟩

@[deprecated (since := "2026-03-31")]
alias omegaLimit_subset_closure_fw_image := omegaLimit_subset_closure_image2

Depends on / 依赖: mem_iInter, omegaLimit_eq_iInter
-/
theorem omegaLimit_subset_closure_image2 {u : Set τ} (hu : u in f) :
    ω f ϕ s subseteq closure (image2 ϕ u s) := by
  rw [omegaLimit_eq_iInter]
  intro _ hx
  rw [mem_iInter] at hx
  exact hx ⟨u, hu⟩

@[deprecated (since := "2026-03-31")]
alias omegaLimit_subset_closure_fw_image := omegaLimit_subset_closure_image2

-- An instance with better keys
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited f.sets
  body: Filter.inhabitedMem

中文:
实例 :
  签名: 可居 f.sets
  定义体: Filter.inhabitedMem

Depends on / 依赖: Filter, Filter.inhabitedMem, inhabitedMem
-/
instance : Inhabited f.sets := Filter.inhabitedMem

/-!
### ω-limits and compactness
-/

/--
theorem `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'` / 定理 `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'`

English:
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'
  statement: {c : Set β}
  proof: by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) :=
    (hc₁.of_isClosed_subset isClosed_closure hv₂).diff hn₁
  let j u := (closure (image2 ϕ (u inter v) s))ᶜ
  have hj₁ : forall u in f, IsOpen (j u) := fun _ _ => isOpen_compl_iff.mpr isClosed_closure
  have hj₂ : k \ n subseteq ⋃ u in f, j u := by
    have : ⋃ u in f, j u = ⋃ u : (↥f.sets), j u := biUnion_eq_iUnion _ _
    rw [this]; rw [sdiff_subset_comm]; rw [sdiff_iUnion]
    rw [omegaLimit_eq_iInter_inter _ _ _ hv₁] at hn₂
    simp_rw [j, sdiff_compl]
    rw [← inter_iInter]
    exact Subset.trans inter_subset_right hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : forall u in g, u in f, hg₂, hg₃⟩
  let w := (⋂ u in g, u) inter v
  have hw₂ : w in f := by simpa [w, *]
  have hw₃ : k \ n subseteq (closure (image2 ϕ w s))ᶜ := by
    apply Subset.trans hg₃
    simp only [j, iUnion_subset_iff, compl_subset_compl]
    intro u hu
    unfold w
    gcongr
    refine iInter_subset_of_subset u (iInter_subset_of_subset hu ?_)
    all_goals exact Subset.rfl
  have hw₄ : kᶜ subseteq (closure (image2 ϕ w s))ᶜ := by
    simp only [compl_subset_compl]
    exact closure_mono (image2_subset inter_subset_right Subset.rfl)
  have hnc : nᶜ subseteq k \ n union kᶜ := by rw [union_comm, ← inter_subset, sdiff_eq, inter_comm]
  have hw : closure (image2 ϕ w s) subseteq n :=
    compl_subset_compl.mp (Subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩

中文:
定理 eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'
  结论: {c : 集合 β}
  证明: by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) :=
    (hc₁.of_isClosed_subset isClosed_closure hv₂).diff hn₁
  let j u := (closure (image2 ϕ (u inter v) s))ᶜ
  have hj₁ : forall u in f, IsOpen (j u) := fun _ _ => isOpen_compl_iff.mpr isClosed_closure
  have hj₂ : k \ n subseteq ⋃ u in f, j u := by
    have : ⋃ u in f, j u = ⋃ u : (↥f.sets), j u := biUnion_eq_iUnion _ _
    rw [this]; rw [sdiff_subset_comm]; rw [sdiff_iUnion]
    rw [omegaLimit_eq_iInter_inter _ _ _ hv₁] at hn₂
    simp_rw [j, sdiff_compl]
    rw [← inter_iInter]
    exact Subset.trans inter_subset_right hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : forall u in g, u in f, hg₂, hg₃⟩
  let w := (⋂ u in g, u) inter v
  have hw₂ : w in f := by simpa [w, *]
  have hw₃ : k \ n subseteq (closure (image2 ϕ w s))ᶜ := by
    apply Subset.trans hg₃
    simp only [j, iUnion_subset_iff, compl_subset_compl]
    intro u hu
    unfold w
    gcongr
    refine iInter_subset_of_subset u (iInter_subset_of_subset hu ?_)
    all_goals exact Subset.rfl
  have hw₄ : kᶜ subseteq (closure (image2 ϕ w s))ᶜ := by
    simp only [compl_subset_compl]
    exact closure_mono (image2_subset inter_subset_right Subset.rfl)
  have hnc : nᶜ subseteq k \ n union kᶜ := by rw [union_comm, ← inter_subset, sdiff_eq, inter_comm]
  have hw : closure (image2 ϕ w s) subseteq n :=
    compl_subset_compl.mp (Subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩

Depends on / 依赖: IsCompact, IsOpen, biUnion_eq_iUnion, closure, f.sets, image2, isClosed_closure, isOpen_compl_iff, isOpen_compl_iff.mpr, of_isClosed_subset, omegaLimit_eq_iInter_inter, sdiff_iUnion, sdiff_subset_comm, subseteq
-/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : exists v in f, closure (image2 ϕ v s) subseteq c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s subseteq n) : exists u in f, closure (image2 ϕ u s) subseteq n := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) :=
    (hc₁.of_isClosed_subset isClosed_closure hv₂).diff hn₁
  let j u := (closure (image2 ϕ (u inter v) s))ᶜ
  have hj₁ : forall u in f, IsOpen (j u) := fun _ _ => isOpen_compl_iff.mpr isClosed_closure
  have hj₂ : k \ n subseteq ⋃ u in f, j u := by
    have : ⋃ u in f, j u = ⋃ u : (↥f.sets), j u := biUnion_eq_iUnion _ _
    rw [this]; rw [sdiff_subset_comm]; rw [sdiff_iUnion]
    rw [omegaLimit_eq_iInter_inter _ _ _ hv₁] at hn₂
    simp_rw [j, sdiff_compl]
    rw [← inter_iInter]
    exact Subset.trans inter_subset_right hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : forall u in g, u in f, hg₂, hg₃⟩
  let w := (⋂ u in g, u) inter v
  have hw₂ : w in f := by simpa [w, *]
  have hw₃ : k \ n subseteq (closure (image2 ϕ w s))ᶜ := by
    apply Subset.trans hg₃
    simp only [j, iUnion_subset_iff, compl_subset_compl]
    intro u hu
    unfold w
    gcongr
    refine iInter_subset_of_subset u (iInter_subset_of_subset hu ?_)
    all_goals exact Subset.rfl
  have hw₄ : kᶜ subseteq (closure (image2 ϕ w s))ᶜ := by
    simp only [compl_subset_compl]
    exact closure_mono (image2_subset inter_subset_right Subset.rfl)
  have hnc : nᶜ subseteq k \ n union kᶜ := by rw [union_comm, ← inter_subset, sdiff_eq, inter_comm]
  have hw : closure (image2 ϕ w s) subseteq n :=
    compl_subset_compl.mp (Subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩

/--
theorem `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset` / 定理 `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset`

English:
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
  statement: [T2Space β]
  proof: eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun _t => id) hc₁.isClosed⟩ hn₁ hn₂

中文:
定理 eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
  结论: [T2空间 β]
  证明: eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun _t => id) hc₁.isClosed⟩ hn₁ hn₂

Depends on / 依赖: closure_minimal, eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset, image2_subset_iff, isClosed
-/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : forallᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s subseteq n) : exists u in f, closure (image2 ϕ u s) subseteq n :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun _t => id) hc₁.isClosed⟩ hn₁ hn₂

/--
theorem `eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset` / 定理 `eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset`

English:
theorem eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
  statement: [T2Space β]
  proof: by
  rcases eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset f ϕ s hc₁
      hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx => ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

中文:
定理 eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
  结论: [T2空间 β]
  证明: by
  rcases eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset f ϕ s hc₁
      hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx => ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

Depends on / 依赖: eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset, hu_mem, mem_image2_of_mem, mem_of_superset, subset_closure
-/
theorem eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : forallᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s subseteq n) : forallᶠ t in f, MapsTo (ϕ t) s n := by
  rcases eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset f ϕ s hc₁
      hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx => ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

/--
theorem `eventually_closure_subset_of_isOpen_of_omegaLimit_subset` / 定理 `eventually_closure_subset_of_isOpen_of_omegaLimit_subset`

English:
theorem eventually_closure_subset_of_isOpen_of_omegaLimit_subset
  statement: [CompactSpace β] {v : Set β}
  proof: eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' _ _ _
    isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂

中文:
定理 eventually_closure_subset_of_isOpen_of_omegaLimit_subset
  结论: [紧空间 β] {v : 集合 β}
  证明: eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' _ _ _
    isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂

Depends on / 依赖: eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset, isCompact_univ, subset_univ, univ_mem
-/
theorem eventually_closure_subset_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s subseteq v) : exists u in f, closure (image2 ϕ u s) subseteq v :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' _ _ _
    isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂

/--
theorem `eventually_mapsTo_of_isOpen_of_omegaLimit_subset` / 定理 `eventually_mapsTo_of_isOpen_of_omegaLimit_subset`

English:
theorem eventually_mapsTo_of_isOpen_of_omegaLimit_subset
  statement: [CompactSpace β] {v : Set β}
  proof: by
  rcases eventually_closure_subset_of_isOpen_of_omegaLimit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx => ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

中文:
定理 eventually_mapsTo_of_isOpen_of_omegaLimit_subset
  结论: [紧空间 β] {v : 集合 β}
  证明: by
  rcases eventually_closure_subset_of_isOpen_of_omegaLimit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx => ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

Depends on / 依赖: eventually_closure_subset_of_isOpen_of_omegaLimit_subset, hu_mem, mem_image2_of_mem, mem_of_superset, subset_closure
-/
theorem eventually_mapsTo_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s subseteq v) : forallᶠ t in f, MapsTo (ϕ t) s v := by
  rcases eventually_closure_subset_of_isOpen_of_omegaLimit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx => ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

/--
theorem `nonempty_omegaLimit_of_isCompact_absorbing` / 定理 `nonempty_omegaLimit_of_isCompact_absorbing`

English:
theorem nonempty_omegaLimit_of_isCompact_absorbing
  statement: [NeBot f] {c : Set β} (hc₁ : IsCompact c)
  proof: by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omegaLimit_eq_iInter_inter _ _ _ hv₁]
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ inter u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals exact closure_mono (image2_subset (inter_subset_inter_left _ (by simp)) Subset.rfl)
  · intro u
    have hn : (image2 ϕ (u inter v) s).Nonempty :=
      Nonempty.image2 (Filter.nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
  · intro
    apply hc₁.of_isClosed_subset isClosed_closure
    grw [inter_subset_right, hv₂]
  · exact fun _ => isClosed_closure

中文:
定理 nonempty_omegaLimit_of_isCompact_absorbing
  结论: [NeBot f] {c : 集合 β} (hc₁ : 是紧集 c)
  证明: by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omegaLimit_eq_iInter_inter _ _ _ hv₁]
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ inter u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals exact closure_mono (image2_subset (inter_subset_inter_left _ (by simp)) Subset.rfl)
  · intro u
    have hn : (image2 ϕ (u inter v) s).Nonempty :=
      Nonempty.image2 (Filter.nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
  · intro
    apply hc₁.of_isClosed_subset isClosed_closure
    grw [inter_subset_right, hv₂]
  · exact fun _ => isClosed_closure

Depends on / 依赖: Filter, Filter.nonempty_of_mem, IsCompact, IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed, Nonempty, Nonempty.image2, Subset, Subset.rfl, all_goals, closure_mono, hn.mono, image2, image2_subset, inter_mem, inter_subset_inter_left, nonempty_iInter_of_directed_nonempty_isCompact_isClosed, nonempty_of_mem, of_isClose, omegaLimit_eq_iInter_inter, subset_closure
-/
theorem nonempty_omegaLimit_of_isCompact_absorbing [NeBot f] {c : Set β} (hc₁ : IsCompact c)
    (hc₂ : exists v in f, closure (image2 ϕ v s) subseteq c) (hs : s.Nonempty) : (ω f ϕ s).Nonempty := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omegaLimit_eq_iInter_inter _ _ _ hv₁]
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ inter u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals exact closure_mono (image2_subset (inter_subset_inter_left _ (by simp)) Subset.rfl)
  · intro u
    have hn : (image2 ϕ (u inter v) s).Nonempty :=
      Nonempty.image2 (Filter.nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
  · intro
    apply hc₁.of_isClosed_subset isClosed_closure
    grw [inter_subset_right, hv₂]
  · exact fun _ => isClosed_closure

/--
theorem `nonempty_omegaLimit` / 定理 `nonempty_omegaLimit`

English:
theorem nonempty_omegaLimit
  given: [CompactSpace β] [NeBot f] (hs : s.Nonempty)
  statement: (ω f ϕ s).Nonempty
  proof: nonempty_omegaLimit_of_isCompact_absorbing _ _ _ isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

中文:
定理 nonempty_omegaLimit
  条件: [紧空间 β] [NeBot f] (hs : s.非空)
  结论: (ω f ϕ s).非空
  证明: nonempty_omegaLimit_of_isCompact_absorbing _ _ _ isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

Depends on / 依赖: isCompact_univ, nonempty_omegaLimit_of_isCompact_absorbing, subset_univ, univ_mem
-/
theorem nonempty_omegaLimit [CompactSpace β] [NeBot f] (hs : s.Nonempty) : (ω f ϕ s).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing _ _ _ isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

end omegaLimit

/-!
### ω-limits of flows by a monoid
-/
namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddMonoid τ] {α : Type*}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/--
theorem `isInvariant_omegaLimit` / 定理 `isInvariant_omegaLimit`

English:
theorem isInvariant_omegaLimit
  given: (hf : forall t, Tendsto (t + ·) f f)
  statement: IsInvariant ϕ (ω f ϕ s)
  proof: by
  refine fun t => MapsTo.mono_right ?_ (omegaLimit_subset_of_tendsto ϕ s (hf t))
  exact
    mapsTo_omegaLimit _ (mapsTo_id _) (fun t' x => (ϕ.map_add _ _ _).symm)
      (continuous_const.flow ϕ continuous_id)

中文:
定理 isInvariant_omegaLimit
  条件: (hf : 对任意 t, 收敛 (t + ·) f f)
  结论: 是不变 ϕ (ω f ϕ s)
  证明: by
  refine fun t => MapsTo.mono_right ?_ (omegaLimit_subset_of_tendsto ϕ s (hf t))
  exact
    mapsTo_omegaLimit _ (mapsTo_id _) (fun t' x => (ϕ.map_add _ _ _).symm)
      (continuous_const.flow ϕ continuous_id)

Depends on / 依赖: MapsTo, MapsTo.mono_right, continuous_const, continuous_const.flow, continuous_id, map_add, mapsTo_id, mapsTo_omegaLimit, mono_right, omegaLimit_subset_of_tendsto
-/
theorem isInvariant_omegaLimit (hf : forall t, Tendsto (t + ·) f f) : IsInvariant ϕ (ω f ϕ s) := by
  refine fun t => MapsTo.mono_right ?_ (omegaLimit_subset_of_tendsto ϕ s (hf t))
  exact
    mapsTo_omegaLimit _ (mapsTo_id _) (fun t' x => (ϕ.map_add _ _ _).symm)
      (continuous_const.flow ϕ continuous_id)

/--
theorem `omegaLimit_image_subset` / 定理 `omegaLimit_image_subset`

English:
theorem omegaLimit_image_subset
  given: (t : τ) (ht : Tendsto (· + t) f f)
  proof: by
  simp only [omegaLimit_image_eq, ← map_add]
  exact omegaLimit_subset_of_tendsto ϕ s ht

中文:
定理 omegaLimit_image_subset
  条件: (t : τ) (ht : 收敛 (· + t) f f)
  证明: by
  simp only [omegaLimit_image_eq, ← map_add]
  exact omegaLimit_subset_of_tendsto ϕ s ht

Depends on / 依赖: map_add, omegaLimit_image_eq, omegaLimit_subset_of_tendsto
-/
theorem omegaLimit_image_subset (t : τ) (ht : Tendsto (· + t) f f) :
    ω f ϕ (ϕ t '' s) subseteq ω f ϕ s := by
  simp only [omegaLimit_image_eq, ← map_add]
  exact omegaLimit_subset_of_tendsto ϕ s ht

end Flow

/-!
### ω-limits of flows by a group
-/
namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddCommGroup τ] {α : Type*}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp]
/--
theorem `omegaLimit_image_eq` / 定理 `omegaLimit_image_eq`

English:
theorem omegaLimit_image_eq
  given: (hf : forall t, Tendsto (· + t) f f) (t : τ)
  statement: ω f ϕ (ϕ t '' s) = ω f ϕ s
  proof: Subset.antisymm (omegaLimit_image_subset _ _ _ _ (hf t))
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' ϕ t '' s) := by simp [image_image, ← map_add]
      _ subseteq ω f ϕ (ϕ t '' s) := omegaLimit_image_subset _ _ _ _ (hf _)

中文:
定理 omegaLimit_image_eq
  条件: (hf : 对任意 t, 收敛 (· + t) f f) (t : τ)
  结论: ω f ϕ (ϕ t '' s) = ω f ϕ s
  证明: Subset.antisymm (omegaLimit_image_subset _ _ _ _ (hf t))
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' ϕ t '' s) := by simp [image_image, ← map_add]
      _ subseteq ω f ϕ (ϕ t '' s) := omegaLimit_image_subset _ _ _ _ (hf _)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, image_image, map_add, omegaLimit_image_subset, subseteq
-/
theorem omegaLimit_image_eq (hf : forall t, Tendsto (· + t) f f) (t : τ) : ω f ϕ (ϕ t '' s) = ω f ϕ s :=
Subset.antisymm (omegaLimit_image_subset _ _ _ _ (hf t))
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' ϕ t '' s) := by simp [image_image, ← map_add]
      _ subseteq ω f ϕ (ϕ t '' s) := omegaLimit_image_subset _ _ _ _ (hf _)

/--
theorem `omegaLimit_omegaLimit` / 定理 `omegaLimit_omegaLimit`

English:
theorem omegaLimit_omegaLimit
  given: (hf : forall t, Tendsto (t + ·) f f)
  statement: ω f ϕ (ω f ϕ s) subseteq ω f ϕ s
  proof: by
  simp only [subset_def, mem_omegaLimit_iff_frequently₂, frequently_iff]
  intro _ h n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, _ht₁, ht₂⟩
  have l₁ : (ω f ϕ s inter o).Nonempty :=
    ht₂.mono
      (inter_subset_inter_left _
        ((isInvariant_iff_image _ _).mp (isInvariant_omegaLimit _ _ _ hf) _))
  have l₂ : (closure (image2 ϕ u s) inter o).Nonempty :=
    l₁.mono fun b hb => ⟨omegaLimit_subset_closure_image2 _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o inter image2 ϕ u s).Nonempty := by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, hr, _, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩

中文:
定理 omegaLimit_omegaLimit
  条件: (hf : 对任意 t, 收敛 (t + ·) f f)
  结论: ω f ϕ (ω f ϕ s) subseteq ω f ϕ s
  证明: by
  simp only [subset_def, mem_omegaLimit_iff_frequently₂, frequently_iff]
  intro _ h n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, _ht₁, ht₂⟩
  have l₁ : (ω f ϕ s inter o).Nonempty :=
    ht₂.mono
      (inter_subset_inter_left _
        ((isInvariant_iff_image _ _).mp (isInvariant_omegaLimit _ _ _ hf) _))
  have l₂ : (closure (image2 ϕ u s) inter o).Nonempty :=
    l₁.mono fun b hb => ⟨omegaLimit_subset_closure_image2 _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o inter image2 ϕ u s).Nonempty := by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, hr, _, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, Nonempty, closure, frequently_iff, image2, inter_subset_inter_left, isInvariant_iff_image, isInvariant_omegaLimit, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp, omegaLimit_subset_closure_image2, subset_def
-/
theorem omegaLimit_omegaLimit (hf : forall t, Tendsto (t + ·) f f) : ω f ϕ (ω f ϕ s) subseteq ω f ϕ s := by
  simp only [subset_def, mem_omegaLimit_iff_frequently₂, frequently_iff]
  intro _ h n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, _ht₁, ht₂⟩
  have l₁ : (ω f ϕ s inter o).Nonempty :=
    ht₂.mono
      (inter_subset_inter_left _
        ((isInvariant_iff_image _ _).mp (isInvariant_omegaLimit _ _ _ hf) _))
  have l₂ : (closure (image2 ϕ u s) inter o).Nonempty :=
    l₁.mono fun b hb => ⟨omegaLimit_subset_closure_image2 _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o inter image2 ϕ u s).Nonempty := by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, hr, _, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩

end Flow
