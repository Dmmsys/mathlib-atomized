/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.SetAccumulate
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Ultrafilter
public import Mathlib.Topology.Defs.Ultrafilter

/-!
# Compact sets and compact spaces

## Main results

* `isCompact_univ_pi`: **Tychonov's theorem** - an arbitrary product of compact sets
  is compact.

* `isCompact_generateFrom`: **Alexander's subbasis theorem** - suppose `X` is a topological space
  with a subbasis `S` and `s` is a subset of `X`, then `s` is compact if for any open cover of `s`
  with all elements taken from `S`, there is a finite subcover.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace Function

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X -> Y}

-- compact sets
section Compact

/--
lemma `IsCompact.exists_clusterPt` / 引理 `IsCompact.exists_clusterPt`

English:
lemma IsCompact.exists_clusterPt
  given: (hs : IsCompact s) {f : Filter X} [NeBot f] (hf : f <= 𝓟 s)
  proof: hs hf

中文:
引理 是紧集.存在_clusterPt
  条件: (hs : 是紧集 s) {f : 滤子 X} [NeBot f] (hf : f <= 𝓟 s)
  证明: hs hf
-/
lemma IsCompact.exists_clusterPt (hs : IsCompact s) {f : Filter X} [NeBot f] (hf : f <= 𝓟 s) :
    exists x in s, ClusterPt x f := hs hf

/--
lemma `IsCompact.exists_mapClusterPt` / 引理 `IsCompact.exists_mapClusterPt`

English:
lemma IsCompact.exists_mapClusterPt
  statement: {ι : Type*} (hs : IsCompact s) {f : Filter ι} [NeBot f]
  proof: hs hf

中文:
引理 是紧集.存在_mapClusterPt
  结论: {ι : 类型} (hs : 是紧集 s) {f : 滤子 ι} [NeBot f]
  证明: hs hf
-/
lemma IsCompact.exists_mapClusterPt {ι : Type*} (hs : IsCompact s) {f : Filter ι} [NeBot f]
    {u : ι -> X} (hf : Filter.map u f <= 𝓟 s) :
    exists x in s, MapClusterPt x f u := hs hf

/--
lemma `IsCompact.exists_clusterPt_of_frequently` / 引理 `IsCompact.exists_clusterPt_of_frequently`

English:
lemma IsCompact.exists_clusterPt_of_frequently
  statement: {l : Filter X} (hs : IsCompact s)
  proof: let ⟨a, has, ha⟩ := @hs _ (frequently_mem_iff_neBot.mp hl) inf_le_right
  ⟨a, has, ha.mono inf_le_left⟩

中文:
引理 是紧集.存在_clusterPt_of_frequently
  结论: {l : 滤子 X} (hs : 是紧集 s)
  证明: let ⟨a, has, ha⟩ := @hs _ (frequently_mem_iff_neBot.mp hl) inf_le_right
  ⟨a, has, ha.mono inf_le_left⟩

Depends on / 依赖: frequently_mem_iff_neBot, frequently_mem_iff_neBot.mp, ha.mono, inf_le_left, inf_le_right
-/
lemma IsCompact.exists_clusterPt_of_frequently {l : Filter X} (hs : IsCompact s)
    (hl : existsᶠ x in l, x in s) : exists a in s, ClusterPt a l :=
  let ⟨a, has, ha⟩ := @hs _ (frequently_mem_iff_neBot.mp hl) inf_le_right
  ⟨a, has, ha.mono inf_le_left⟩

/--
lemma `IsCompact.exists_mapClusterPt_of_frequently` / 引理 `IsCompact.exists_mapClusterPt_of_frequently`

English:
lemma IsCompact.exists_mapClusterPt_of_frequently
  statement: {l : Filter ι} {f : ι -> X} (hs : IsCompact s)
  proof: hs.exists_clusterPt_of_frequently hf

中文:
引理 是紧集.存在_mapClusterPt_of_frequently
  结论: {l : 滤子 ι} {f : ι -> X} (hs : 是紧集 s)
  证明: hs.exists_clusterPt_of_frequently hf

Depends on / 依赖: exists_clusterPt_of_frequently, hs.exists_clusterPt_of_frequently
-/
lemma IsCompact.exists_mapClusterPt_of_frequently {l : Filter ι} {f : ι -> X} (hs : IsCompact s)
    (hf : existsᶠ x in l, f x in s) : exists a in s, MapClusterPt a l f :=
  hs.exists_clusterPt_of_frequently hf

/--
theorem `IsCompact.compl_mem_sets` / 定理 `IsCompact.compl_mem_sets`

English:
theorem IsCompact.compl_mem_sets
  given: (hs : IsCompact s) {f : Filter X} (hf : forall x in s, sᶜ in 𝓝 x ⊓ f)
  proof: by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

中文:
定理 是紧集.compl_mem_sets
  条件: (hs : 是紧集 s) {f : 滤子 X} (hf : 对任意 x in s, sᶜ in 𝓝 x ⊓ f)
  证明: by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

Depends on / 依赖: compl_compl, contrapose, inf_assoc, inf_le_right, notMem_iff_inf_principal_compl
-/
theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter X} (hf : forall x in s, sᶜ in 𝓝 x ⊓ f) :
    sᶜ in f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

/--
theorem `IsCompact.compl_mem_sets_of_nhdsWithin` / 定理 `IsCompact.compl_mem_sets_of_nhdsWithin`

English:
theorem IsCompact.compl_mem_sets_of_nhdsWithin
  statement: (hs : IsCompact s) {f : Filter X}
  proof: by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

中文:
定理 是紧集.compl_mem_sets_of_nhdsWithin
  结论: (hs : 是紧集 s) {f : 滤子 X}
  证明: by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

Depends on / 依赖: compl_mem_sets, hs.compl_mem_sets, mem_inf_of_inter, mem_inf_principal, replace
-/
theorem IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter X}
    (hf : forall x in s, exists t in 𝓝[s] x, tᶜ in f) : sᶜ in f := by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
/--
theorem `IsCompact.induction_on` / 定理 `IsCompact.induction_on`

English:
theorem IsCompact.induction_on
  statement: (hs : IsCompact s) {p : Set X -> Prop} (he : p ∅)
  proof: by
  let f : Filter X := comk p he (fun _t ht _s hsub => hmono hsub ht) (fun _s hs _t ht => hunion hs ht)
  have : sᶜ in f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

中文:
定理 是紧集.induction_on
  结论: (hs : 是紧集 s) {p : 集合 X -> 命题} (he : p ∅)
  证明: by
  let f : Filter X := comk p he (fun _t ht _s hsub => hmono hsub ht) (fun _s hs _t ht => hunion hs ht)
  have : sᶜ in f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

Depends on / 依赖: Filter, compl_compl, compl_mem_sets_of_nhdsWithin, hs.compl_mem_sets_of_nhdsWithin, hunion
-/
theorem IsCompact.induction_on (hs : IsCompact s) {p : Set X -> Prop} (he : p ∅)
    (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hunion : forall ⦃s t⦄, p s -> p t -> p (s union t))
    (hnhds : forall x in s, exists t in 𝓝[s] x, p t) : p s := by
  let f : Filter X := comk p he (fun _t ht _s hsub => hmono hsub ht) (fun _s hs _t ht => hunion hs ht)
  have : sᶜ in f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a compact set and a closed set is a compact set. -/
@[compactness .]
/--
theorem `IsCompact.inter_right` / 定理 `IsCompact.inter_right`

English:
theorem IsCompact.inter_right
  given: (hs : IsCompact s) (ht : IsClosed t)
  statement: IsCompact (s inter t)
  proof: by
  intro f hnf hstf
  obtain ⟨x, hsx, hx⟩ : exists x in s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 inter_subset_left))
have : x in t := ht.mem_of_nhdsWithin_neBot
hx.mono le_trans hstf (le_principal_iff.2 inter_subset_right)
  exact ⟨x, ⟨hsx, this⟩, hx⟩

中文:
定理 是紧集.inter_right
  条件: (hs : 是紧集 s) (ht : 是闭集 t)
  结论: 是紧集 (s inter t)
  证明: by
  intro f hnf hstf
  obtain ⟨x, hsx, hx⟩ : exists x in s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 inter_subset_left))
have : x in t := ht.mem_of_nhdsWithin_neBot
hx.mono le_trans hstf (le_principal_iff.2 inter_subset_right)
  exact ⟨x, ⟨hsx, this⟩, hx⟩

Depends on / 依赖: ClusterPt, ht.mem_of_nhdsWithin_neBot, hx.mono, inter_subset_left, inter_subset_right, le_principal_iff, le_trans, mem_of_nhdsWithin_neBot
-/
theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s inter t) := by
  intro f hnf hstf
  obtain ⟨x, hsx, hx⟩ : exists x in s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 inter_subset_left))
have : x in t := ht.mem_of_nhdsWithin_neBot
hx.mono le_trans hstf (le_principal_iff.2 inter_subset_right)
  exact ⟨x, ⟨hsx, this⟩, hx⟩

/-- The intersection of a closed set and a compact set is a compact set. -/
@[compactness .]
/--
theorem `IsCompact.inter_left` / 定理 `IsCompact.inter_left`

English:
theorem IsCompact.inter_left
  given: (ht : IsCompact t) (hs : IsClosed s)
  statement: IsCompact (s inter t)
  proof: inter_comm t s ▸ ht.inter_right hs

中文:
定理 是紧集.inter_left
  条件: (ht : 是紧集 t) (hs : 是闭集 s)
  结论: 是紧集 (s inter t)
  证明: inter_comm t s ▸ ht.inter_right hs

Depends on / 依赖: ht.inter_right, inter_comm, inter_right
-/
theorem IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s inter t) :=
  inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a compact set and an open set is a compact set. -/
@[compactness .]
/--
theorem `IsCompact.diff` / 定理 `IsCompact.diff`

English:
theorem IsCompact.diff
  given: (hs : IsCompact s) (ht : IsOpen t)
  statement: IsCompact (s \ t)
  proof: hs.inter_right (isClosed_compl_iff.mpr ht)

中文:
定理 是紧集.diff
  条件: (hs : 是紧集 s) (ht : 是开集 t)
  结论: 是紧集 (s \ t)
  证明: hs.inter_right (isClosed_compl_iff.mpr ht)

Depends on / 依赖: hs.inter_right, inter_right, isClosed_compl_iff, isClosed_compl_iff.mpr
-/
theorem IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/--
theorem `IsCompact.of_isClosed_subset` / 定理 `IsCompact.of_isClosed_subset`

English:
theorem IsCompact.of_isClosed_subset
  given: (hs : IsCompact s) (ht : IsClosed t) (h : t subseteq s)
  proof: inter_eq_self_of_subset_right h ▸ hs.inter_right ht

@[compactness .]

中文:
定理 是紧集.of_isClosed_subset
  条件: (hs : 是紧集 s) (ht : 是闭集 t) (h : t subseteq s)
  证明: inter_eq_self_of_subset_right h ▸ hs.inter_right ht

@[compactness .]

Depends on / 依赖: hs.inter_right, inter_eq_self_of_subset_right, inter_right
-/
theorem IsCompact.of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t subseteq s) :
    IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht

@[compactness .]
/--
theorem `IsCompact.image_of_continuousOn` / 定理 `IsCompact.image_of_continuousOn`

English:
theorem IsCompact.image_of_continuousOn
  given: {f : X -> Y} (hs : IsCompact s) (hf : ContinuousOn f s)
  proof: by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : exists x in s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

中文:
定理 是紧集.image_of_continuousOn
  条件: {f : X -> Y} (hs : 是紧集 s) (hf : ContinuousOn f s)
  证明: by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : exists x in s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

Depends on / 依赖: ClusterPt, Tendsto, comap_inf_principal_neBot_of_image_mem, convert, hx.neBot, inf_le_right, l.comap, le_principal_iff, mem_image_of_mem, nhdsWithin, tendsto_comap, this.neBot
-/
theorem IsCompact.image_of_continuousOn {f : X -> Y} (hs : IsCompact s) (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : exists x in s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

/--
theorem `IsCompact.image` / 定理 `IsCompact.image`

English:
theorem IsCompact.image
  given: {f : X -> Y} (hs : IsCompact s) (hf : Continuous f)
  statement: IsCompact (f '' s)
  proof: hs.image_of_continuousOn hf.continuousOn

中文:
定理 是紧集.像
  条件: {f : X -> Y} (hs : 是紧集 s) (hf : 连续 f)
  结论: 是紧集 (f '' s)
  证明: hs.image_of_continuousOn hf.continuousOn

Depends on / 依赖: continuousOn, hf.continuousOn, hs.image_of_continuousOn, image_of_continuousOn
-/
theorem IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn

/--
theorem `IsCompact.adherence_nhdset` / 定理 `IsCompact.adherence_nhdset`

English:
theorem IsCompact.adherence_nhdset
  statement: {f : Filter X} (hs : IsCompact s) (hf₂ : f <= 𝓟 s)
  proof: Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ != ⊥) =>
let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ inf_le_of_left_le hf₂
    have : x in t := ht₂ x hx hfx.of_inf_left
    have : tᶜ inter t in 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x != ⊥ := hfx.of_inf_right.ne
    absurd A this

中文:
定理 是紧集.adherence_nhdset
  结论: {f : 滤子 X} (hs : 是紧集 s) (hf₂ : f <= 𝓟 s)
  证明: Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ != ⊥) =>
let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ inf_le_of_left_le hf₂
    have : x in t := ht₂ x hx hfx.of_inf_left
    have : tᶜ inter t in 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x != ⊥ := hfx.of_inf_right.ne
    absurd A this

Depends on / 依赖: Classical, Classical.by_cases, ClusterPt, IsOpen, IsOpen.mem_nhds, absurd, compl_inter_self, empty_mem_iff_bot, hfx.of_inf_left, hfx.of_inf_right.ne, inf_le_of_left_le, inter_mem_nhdsWithin, mem_nhds, mem_of_eq_bot, of_inf_left, of_inf_right
-/
theorem IsCompact.adherence_nhdset {f : Filter X} (hs : IsCompact s) (hf₂ : f <= 𝓟 s)
    (ht₁ : IsOpen t) (ht₂ : forall x in s, ClusterPt x f -> x in t) : t in f :=
  Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ != ⊥) =>
let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ inf_le_of_left_le hf₂
    have : x in t := ht₂ x hx hfx.of_inf_left
    have : tᶜ inter t in 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x != ⊥ := hfx.of_inf_right.ne
    absurd A this

/--
theorem `isCompact_iff_ultrafilter_le_nhds` / 定理 `isCompact_iff_ultrafilter_le_nhds`

English:
theorem isCompact_iff_ultrafilter_le_nhds
  proof: by
  refine (forall_neBot_le_iff ?_).trans ?_
  · rintro f g hle ⟨x, hxs, hxf⟩
    exact ⟨x, hxs, hxf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds

中文:
定理 isCompact_iff_ultrafilter_le_nhds
  证明: by
  refine (forall_neBot_le_iff ?_).trans ?_
  · rintro f g hle ⟨x, hxs, hxf⟩
    exact ⟨x, hxs, hxf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds

Depends on / 依赖: Ultrafilter, Ultrafilter.clusterPt_iff, clusterPt_iff, forall_neBot_le_iff, hxf.mono
-/
theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact s ↔ forall f : Ultrafilter X, ↑f <= 𝓟 s -> exists x in s, ↑f <= 𝓝 x := by
  refine (forall_neBot_le_iff ?_).trans ?_
  · rintro f g hle ⟨x, hxs, hxf⟩
    exact ⟨x, hxs, hxf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds

/--
theorem `isCompact_iff_ultrafilter_le_nhds'` / 定理 `isCompact_iff_ultrafilter_le_nhds'`

English:
theorem isCompact_iff_ultrafilter_le_nhds'
  proof: by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

中文:
定理 isCompact_iff_ultrafilter_le_nhds'
  证明: by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

Depends on / 依赖: Ultrafilter, Ultrafilter.mem_coe, isCompact_iff_ultrafilter_le_nhds, le_principal_iff, mem_coe
-/
theorem isCompact_iff_ultrafilter_le_nhds' :
    IsCompact s ↔ forall f : Ultrafilter X, s in f -> exists x in s, ↑f <= 𝓝 x := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

/--
lemma `IsCompact.le_nhdsSet_of_clusterPt` / 引理 `IsCompact.le_nhdsSet_of_clusterPt`

English:
lemma IsCompact.le_nhdsSet_of_clusterPt
  statement: (hs : IsCompact s) {l : Filter X} {s' : Set X}
  proof: by
  refine le_iff_ultrafilter.2 fun f hf => ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  grw [hx]
  refine nhds_le_nhdsSet ?_
  exact h x hxs (.mono (.of_le_nhds hx) hf)

中文:
引理 是紧集.le_nhdsSet_of_clusterPt
  结论: (hs : 是紧集 s) {l : 滤子 X} {s' : 集合 X}
  证明: by
  refine le_iff_ultrafilter.2 fun f hf => ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  grw [hx]
  refine nhds_le_nhdsSet ?_
  exact h x hxs (.mono (.of_le_nhds hx) hf)

Depends on / 依赖: hs.ultrafilter_le_nhds, le_iff_ultrafilter, nhds_le_nhdsSet, of_le_nhds, ultrafilter_le_nhds
-/
lemma IsCompact.le_nhdsSet_of_clusterPt (hs : IsCompact s) {l : Filter X} {s' : Set X}
    (hmem : s in l) (h : forall x in s, ClusterPt x l -> x in s') : l <= 𝓝ˢ s' := by
  refine le_iff_ultrafilter.2 fun f hf => ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  grw [hx]
  refine nhds_le_nhdsSet ?_
  exact h x hxs (.mono (.of_le_nhds hx) hf)

/--
lemma `IsCompact.le_nhds_of_unique_clusterPt` / 引理 `IsCompact.le_nhds_of_unique_clusterPt`

English:
lemma IsCompact.le_nhds_of_unique_clusterPt
  statement: (hs : IsCompact s) {l : Filter X} {y : X}
  proof: by
  rw [← nhdsSet_singleton]
  exact hs.le_nhdsSet_of_clusterPt hmem h

中文:
引理 是紧集.le_nhds_of_unique_clusterPt
  结论: (hs : 是紧集 s) {l : 滤子 X} {y : X}
  证明: by
  rw [← nhdsSet_singleton]
  exact hs.le_nhdsSet_of_clusterPt hmem h

Depends on / 依赖: hs.le_nhdsSet_of_clusterPt, le_nhdsSet_of_clusterPt, nhdsSet_singleton
-/
lemma IsCompact.le_nhds_of_unique_clusterPt (hs : IsCompact s) {l : Filter X} {y : X}
    (hmem : s in l) (h : forall x in s, ClusterPt x l -> x = y) : l <= 𝓝 y := by
  rw [← nhdsSet_singleton]
  exact hs.le_nhdsSet_of_clusterPt hmem h

/--
lemma `IsCompact.tendsto_nhdsSet_of_mapClusterPt` / 引理 `IsCompact.tendsto_nhdsSet_of_mapClusterPt`

English:
lemma IsCompact.tendsto_nhdsSet_of_mapClusterPt
  statement: {Y} {l : Filter Y} {s' : Set X} {f : Y -> X}
  proof: hs.le_nhdsSet_of_clusterPt (mem_map.2 hmem) h

中文:
引理 是紧集.tendsto_nhdsSet_of_mapClusterPt
  结论: {Y} {l : 滤子 Y} {s' : 集合 X} {f : Y -> X}
  证明: hs.le_nhdsSet_of_clusterPt (mem_map.2 hmem) h

Depends on / 依赖: hs.le_nhdsSet_of_clusterPt, le_nhdsSet_of_clusterPt, mem_map
-/
lemma IsCompact.tendsto_nhdsSet_of_mapClusterPt {Y} {l : Filter Y} {s' : Set X} {f : Y -> X}
    (hs : IsCompact s) (hmem : forallᶠ x in l, f x in s) (h : forall x in s, MapClusterPt x l f -> x in s') :
    Tendsto f l (𝓝ˢ s') :=
  hs.le_nhdsSet_of_clusterPt (mem_map.2 hmem) h

/--
lemma `IsCompact.tendsto_nhds_of_unique_mapClusterPt` / 引理 `IsCompact.tendsto_nhds_of_unique_mapClusterPt`

English:
lemma IsCompact.tendsto_nhds_of_unique_mapClusterPt
  statement: {Y} {l : Filter Y} {y : X} {f : Y -> X}
  proof: by
  rw [← nhdsSet_singleton]
  exact hs.tendsto_nhdsSet_of_mapClusterPt hmem h

中文:
引理 是紧集.tendsto_nhds_of_unique_mapClusterPt
  结论: {Y} {l : 滤子 Y} {y : X} {f : Y -> X}
  证明: by
  rw [← nhdsSet_singleton]
  exact hs.tendsto_nhdsSet_of_mapClusterPt hmem h

Depends on / 依赖: hs.tendsto_nhdsSet_of_mapClusterPt, nhdsSet_singleton, tendsto_nhdsSet_of_mapClusterPt
-/
lemma IsCompact.tendsto_nhds_of_unique_mapClusterPt {Y} {l : Filter Y} {y : X} {f : Y -> X}
    (hs : IsCompact s) (hmem : forallᶠ x in l, f x in s) (h : forall x in s, MapClusterPt x l f -> x = y) :
    Tendsto f l (𝓝 y) := by
  rw [← nhdsSet_singleton]
  exact hs.tendsto_nhdsSet_of_mapClusterPt hmem h

/--
theorem `IsCompact.elim_directed_cover` / 定理 `IsCompact.elim_directed_cover`

English:
theorem IsCompact.elim_directed_cover
  statement: {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
  proof: hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩

中文:
定理 是紧集.elim_directed_cover
  结论: {ι : 类型v} [hι : 非空 ι] (hs : 是紧集 s)
  证明: hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩

Depends on / 依赖: IsCompact, IsCompact.induction_on, IsOpen, IsOpen.mem_nhds, Subset, Subset.refl, Subset.trans, empty_subset, hs.trans, induction_on, mem_iUnion, mem_nhds, mem_nhdsWithin_of_mem_nhds, union_subset
-/
theorem IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
    (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i) (hdU : Directed (· subseteq ·) U) :
    exists i, s subseteq U i :=
  hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩

/--
theorem `IsCompact.elim_finite_subcover` / 定理 `IsCompact.elim_finite_subcover`

English:
theorem IsCompact.elim_finite_subcover
  statement: {ι : Type v} (hs : IsCompact s) (U : ι -> Set X)
  proof: hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

中文:
定理 是紧集.elim_finite_subcover
  结论: {ι : 类型v} (hs : 是紧集 s) (U : ι -> 集合 X)
  证明: hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

Depends on / 依赖: biUnion_subset_biUnion_left, directed_of_isDirected_le, elim_directed_cover, hs.elim_directed_cover, iUnion_eq_iUnion_finset, isOpen_biUnion
-/
theorem IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι -> Set X)
    (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i) : exists t : Finset ι, s subseteq ⋃ i in t, U i :=
  hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

/--
lemma `IsCompact.elim_nhds_subcover_nhdsSet'` / 引理 `IsCompact.elim_nhds_subcover_nhdsSet'`

English:
lemma IsCompact.elim_nhds_subcover_nhdsSet'
  statement: (hs : IsCompact s) (U : forall x in s, Set X)
  proof: by
  rcases hs.elim_finite_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior)
fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 hU _ _⟩ with ⟨t, hst⟩
  refine ⟨t, mem_nhdsSet_iff_forall.2 fun x hx => ?_⟩
  rcases mem_iUnion₂.1 (hst hx) with ⟨y, hyt, hy⟩
  refine mem_of_superset ?_ (subset_biUnion_of_mem hyt)
  exact mem_interior_iff_mem_nhds.1 hy

中文:
引理 是紧集.elim_nhds_subcover_nhdsSet'
  结论: (hs : 是紧集 s) (U : 对任意 x in s, 集合 X)
  证明: by
  rcases hs.elim_finite_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior)
fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 hU _ _⟩ with ⟨t, hst⟩
  refine ⟨t, mem_nhdsSet_iff_forall.2 fun x hx => ?_⟩
  rcases mem_iUnion₂.1 (hst hx) with ⟨y, hyt, hy⟩
  refine mem_of_superset ?_ (subset_biUnion_of_mem hyt)
  exact mem_interior_iff_mem_nhds.1 hy

Depends on / 依赖: elim_finite_subcover, hs.elim_finite_subcover, interior, isOpen_interior, mem_iUnion, mem_interior_iff_mem_nhds, mem_nhdsSet_iff_forall, mem_of_superset, subset_biUnion_of_mem
-/
lemma IsCompact.elim_nhds_subcover_nhdsSet' (hs : IsCompact s) (U : forall x in s, Set X)
    (hU : forall x hx, U x hx in 𝓝 x) : exists t : Finset s, (⋃ x in t, U x.1 x.2) in 𝓝ˢ s := by
  rcases hs.elim_finite_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior)
fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 hU _ _⟩ with ⟨t, hst⟩
  refine ⟨t, mem_nhdsSet_iff_forall.2 fun x hx => ?_⟩
  rcases mem_iUnion₂.1 (hst hx) with ⟨y, hyt, hy⟩
  refine mem_of_superset ?_ (subset_biUnion_of_mem hyt)
  exact mem_interior_iff_mem_nhds.1 hy

/--
lemma `IsCompact.elim_nhds_subcover_nhdsSet` / 引理 `IsCompact.elim_nhds_subcover_nhdsSet`

English:
lemma IsCompact.elim_nhds_subcover_nhdsSet
  statement: (hs : IsCompact s) {U : X -> Set X}
  proof: by
  let ⟨t, ht⟩ := hs.elim_nhds_subcover_nhdsSet' (fun x _ => U x) hU
  classical
  exact ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩

中文:
引理 是紧集.elim_nhds_subcover_nhdsSet
  结论: (hs : 是紧集 s) {U : X -> 集合 X}
  证明: by
  let ⟨t, ht⟩ := hs.elim_nhds_subcover_nhdsSet' (fun x _ => U x) hU
  classical
  exact ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩

Depends on / 依赖: Finset, Finset.mem_image, Finset.set_biUnion_finset_image, classical, elim_nhds_subcover_nhdsSet, hs.elim_nhds_subcover_nhdsSet, mem_image, set_biUnion_finset_image, t.image
-/
lemma IsCompact.elim_nhds_subcover_nhdsSet (hs : IsCompact s) {U : X -> Set X}
    (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (forall x in t, x in s) ∧ (⋃ x in t, U x) in 𝓝ˢ s := by
  let ⟨t, ht⟩ := hs.elim_nhds_subcover_nhdsSet' (fun x _ => U x) hU
  classical
  exact ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩

/--
theorem `IsCompact.elim_nhds_subcover'` / 定理 `IsCompact.elim_nhds_subcover'`

English:
theorem IsCompact.elim_nhds_subcover'
  statement: (hs : IsCompact s) (U : forall x in s, Set X)
  proof: (hs.elim_nhds_subcover_nhdsSet' U hU).imp fun _ => subset_of_mem_nhdsSet

中文:
定理 是紧集.elim_nhds_subcover'
  结论: (hs : 是紧集 s) (U : 对任意 x in s, 集合 X)
  证明: (hs.elim_nhds_subcover_nhdsSet' U hU).imp fun _ => subset_of_mem_nhdsSet

Depends on / 依赖: elim_nhds_subcover_nhdsSet, hs.elim_nhds_subcover_nhdsSet, subset_of_mem_nhdsSet
-/
theorem IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : forall x in s, Set X)
    (hU : forall x (hx : x in s), U x ‹x in s› in 𝓝 x) : exists t : Finset s, s subseteq ⋃ x in t, U (x : s) x.2 :=
  (hs.elim_nhds_subcover_nhdsSet' U hU).imp fun _ => subset_of_mem_nhdsSet

/--
theorem `IsCompact.elim_nhds_subcover` / 定理 `IsCompact.elim_nhds_subcover`

English:
theorem IsCompact.elim_nhds_subcover
  given: (hs : IsCompact s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x)
  proof: (hs.elim_nhds_subcover_nhdsSet hU).imp fun _ h => h.imp_right subset_of_mem_nhdsSet

中文:
定理 是紧集.elim_nhds_subcover
  条件: (hs : 是紧集 s) (U : X -> 集合 X) (hU : 对任意 x in s, U x in 𝓝 x)
  证明: (hs.elim_nhds_subcover_nhdsSet hU).imp fun _ h => h.imp_right subset_of_mem_nhdsSet

Depends on / 依赖: elim_nhds_subcover_nhdsSet, h.imp_right, hs.elim_nhds_subcover_nhdsSet, imp_right, subset_of_mem_nhdsSet
-/
theorem IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) :
    exists t : Finset X, (forall x in t, x in s) ∧ s subseteq ⋃ x in t, U x :=
  (hs.elim_nhds_subcover_nhdsSet hU).imp fun _ h => h.imp_right subset_of_mem_nhdsSet

/--
theorem `IsCompact.elim_nhdsWithin_subcover'` / 定理 `IsCompact.elim_nhdsWithin_subcover'`

English:
theorem IsCompact.elim_nhdsWithin_subcover'
  statement: (hs : IsCompact s) (U : forall x in s, Set X)
  proof: by
  choose V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover' V V_nhds).imp fun t ht =>
    subset_trans ?_ (iUnion₂_mono fun x _ => hV x x.2)
  simpa [← iUnion_inter, ← iUnion_coe_set]

中文:
定理 是紧集.elim_nhdsWithin_subcover'
  结论: (hs : 是紧集 s) (U : 对任意 x in s, 集合 X)
  证明: by
  choose V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover' V V_nhds).imp fun t ht =>
    subset_trans ?_ (iUnion₂_mono fun x _ => hV x x.2)
  simpa [← iUnion_inter, ← iUnion_coe_set]

Depends on / 依赖: V_nhds, elim_nhds_subcover, hs.elim_nhds_subcover, iUnion_coe_set, iUnion_inter, mem_nhdsWithin_iff_exists_mem_nhds_inter, subset_trans
-/
theorem IsCompact.elim_nhdsWithin_subcover' (hs : IsCompact s) (U : forall x in s, Set X)
    (hU : forall x (hx : x in s), U x hx in 𝓝[s] x) : exists t : Finset s, s subseteq ⋃ x in t, U x x.2 := by
  choose V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover' V V_nhds).imp fun t ht =>
    subset_trans ?_ (iUnion₂_mono fun x _ => hV x x.2)
  simpa [← iUnion_inter, ← iUnion_coe_set]

/--
theorem `IsCompact.elim_nhdsWithin_subcover` / 定理 `IsCompact.elim_nhdsWithin_subcover`

English:
theorem IsCompact.elim_nhdsWithin_subcover
  statement: (hs : IsCompact s) (U : X -> Set X)
  proof: by
  choose! V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover V V_nhds).imp fun t ⟨t_sub_s, ht⟩ =>
    ⟨t_sub_s, subset_trans ?_ (iUnion₂_mono fun x hx => hV x (t_sub_s x hx))⟩
  simpa [← iUnion_inter]

中文:
定理 是紧集.elim_nhdsWithin_subcover
  结论: (hs : 是紧集 s) (U : X -> 集合 X)
  证明: by
  choose! V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover V V_nhds).imp fun t ⟨t_sub_s, ht⟩ =>
    ⟨t_sub_s, subset_trans ?_ (iUnion₂_mono fun x hx => hV x (t_sub_s x hx))⟩
  simpa [← iUnion_inter]

Depends on / 依赖: V_nhds, elim_nhds_subcover, hs.elim_nhds_subcover, iUnion_inter, mem_nhdsWithin_iff_exists_mem_nhds_inter, subset_trans, t_sub_s
-/
theorem IsCompact.elim_nhdsWithin_subcover (hs : IsCompact s) (U : X -> Set X)
    (hU : forall x in s, U x in 𝓝[s] x) : exists t : Finset X, (forall x in t, x in s) ∧ s subseteq ⋃ x in t, U x := by
  choose! V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover V V_nhds).imp fun t ⟨t_sub_s, ht⟩ =>
    ⟨t_sub_s, subset_trans ?_ (iUnion₂_mono fun x hx => hV x (t_sub_s x hx))⟩
  simpa [← iUnion_inter]

/--
theorem `IsCompact.disjoint_nhdsSet_left` / 定理 `IsCompact.disjoint_nhdsSet_left`

English:
theorem IsCompact.disjoint_nhdsSet_left
  given: {l : Filter X} (hs : IsCompact s)
  proof: by
refine ⟨fun h x hx => h.mono_left nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x in t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]; rw [biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)

中文:
定理 是紧集.disjoint_nhdsSet_left
  条件: {l : 滤子 X} (hs : 是紧集 s)
  证明: by
refine ⟨fun h x hx => h.mono_left nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x in t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]; rw [biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)

Depends on / 依赖: biInter_finset_mem, disjoint_iff_left, elim_nhds_subcover, h.mono_left, hasBasis_nhdsSet, hs.elim_nhds_subcover, isOpen_biUnion, mem_nhds, mono_left, nhds_basis_opens, nhds_le_nhdsSet
-/
theorem IsCompact.disjoint_nhdsSet_left {l : Filter X} (hs : IsCompact s) :
    Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l := by
refine ⟨fun h x hx => h.mono_left nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x in t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]; rw [biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)

/--
theorem `IsCompact.disjoint_nhdsSet_right` / 定理 `IsCompact.disjoint_nhdsSet_right`

English:
theorem IsCompact.disjoint_nhdsSet_right
  given: {l : Filter X} (hs : IsCompact s)
  proof: by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

中文:
定理 是紧集.disjoint_nhdsSet_right
  条件: {l : 滤子 X} (hs : 是紧集 s)
  证明: by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

Depends on / 依赖: disjoint_comm, disjoint_nhdsSet_left, hs.disjoint_nhdsSet_left
-/
theorem IsCompact.disjoint_nhdsSet_right {l : Filter X} (hs : IsCompact s) :
    Disjoint l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

-- TODO: reformulate using `Disjoint`
/--
theorem `IsCompact.elim_directed_family_closed` / 定理 `IsCompact.elim_directed_family_closed`

English:
theorem IsCompact.elim_directed_family_closed
  statement: {ι : Type v} [Nonempty ι] (hs : IsCompact s)
  proof: let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ t) (fun i => (htc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! hst)
      (hdt.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! ht⟩

中文:
定理 是紧集.elim_directed_family_closed
  结论: {ι : 类型v} [非空 ι] (hs : 是紧集 s)
  证明: let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ t) (fun i => (htc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! hst)
      (hdt.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! ht⟩

Depends on / 依赖: compl_subset_compl, compl_subset_compl.mpr, elim_directed_cover, eq_empty_iff_forall_notMem, exists_prop, hdt.mono_comp, hs.elim_directed_cover, isOpen_compl, mem_compl_iff, mem_iInter, mem_iUnion, mem_inter_iff, mono_comp, not_and, not_forall, subset_def
-/
theorem IsCompact.elim_directed_family_closed {ι : Type v} [Nonempty ι] (hs : IsCompact s)
    (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst : (s inter ⋂ i, t i) = ∅)
    (hdt : Directed (· ⊇ ·) t) : exists i : ι, s inter t i = ∅ :=
  let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ t) (fun i => (htc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! hst)
      (hdt.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! ht⟩

-- TODO: reformulate using `Disjoint`
/--
theorem `IsCompact.elim_finite_subfamily_closed` / 定理 `IsCompact.elim_finite_subfamily_closed`

English:
theorem IsCompact.elim_finite_subfamily_closed
  statement: {ι : Type v} (hs : IsCompact s)
  proof: hs.elim_directed_family_closed _ (fun _ => isClosed_biInter fun _ _ => htc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h => biInter_subset_biInter_left h)

中文:
定理 是紧集.elim_finite_subfamily_closed
  结论: {ι : 类型v} (hs : 是紧集 s)
  证明: hs.elim_directed_family_closed _ (fun _ => isClosed_biInter fun _ _ => htc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h => biInter_subset_biInter_left h)

Depends on / 依赖: biInter_subset_biInter_left, directed_of_isDirected_le, elim_directed_family_closed, hs.elim_directed_family_closed, iInter_eq_iInter_finset, isClosed_biInter
-/
theorem IsCompact.elim_finite_subfamily_closed {ι : Type v} (hs : IsCompact s)
    (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst : (s inter ⋂ i, t i) = ∅) :
    exists u : Finset ι, (s inter ⋂ i in u, t i) = ∅ :=
  hs.elim_directed_family_closed _ (fun _ => isClosed_biInter fun _ _ => htc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h => biInter_subset_biInter_left h)

/--
theorem `IsCompact.inter_iInter_nonempty` / 定理 `IsCompact.inter_iInter_nonempty`

English:
theorem IsCompact.inter_iInter_nonempty
  statement: {ι : Type v} (hs : IsCompact s) (t : ι -> Set X)
  proof: by
  contrapose! hst
  exact hs.elim_finite_subfamily_closed t htc hst

中文:
定理 是紧集.inter_i整数er_nonempty
  结论: {ι : 类型v} (hs : 是紧集 s) (t : ι -> 集合 X)
  证明: by
  contrapose! hst
  exact hs.elim_finite_subfamily_closed t htc hst

Depends on / 依赖: contrapose, elim_finite_subfamily_closed, hs.elim_finite_subfamily_closed
-/
theorem IsCompact.inter_iInter_nonempty {ι : Type v} (hs : IsCompact s) (t : ι -> Set X)
    (htc : forall i, IsClosed (t i)) (hst : forall u : Finset ι, (s inter ⋂ i in u, t i).Nonempty) :
    (s inter ⋂ i, t i).Nonempty := by
  contrapose! hst
  exact hs.elim_finite_subfamily_closed t htc hst

/--
lemma `IsCompact.nonempty_inter_sInter` / 引理 `IsCompact.nonempty_inter_sInter`

English:
lemma IsCompact.nonempty_inter_sInter
  statement: (hs : IsCompact s) {t : Set (Set X)}
  proof: by
  rw [Set.sInter_eq_iInter]
  refine hs.inter_iInter_nonempty _ (fun i => ht _ i.2) fun a => ?_
  simpa using h (Subtype.val '' (a : Set t)) (by simp) (a.finite_toSet.image _)

中文:
引理 是紧集.nonempty_inter_s整数er
  结论: (hs : 是紧集 s) {t : 集合 (集合 X)}
  证明: by
  rw [Set.sInter_eq_iInter]
  refine hs.inter_iInter_nonempty _ (fun i => ht _ i.2) fun a => ?_
  simpa using h (Subtype.val '' (a : Set t)) (by simp) (a.finite_toSet.image _)

Depends on / 依赖: Set.sInter_eq_iInter, Subtype, Subtype.val, a.finite_toSet.image, finite_toSet, hs.inter_iInter_nonempty, inter_iInter_nonempty, sInter_eq_iInter
-/
lemma IsCompact.nonempty_inter_sInter (hs : IsCompact s) {t : Set (Set X)}
    (ht : forall a in t, IsClosed a) (h : forall a subseteq t, a.Finite -> (s inter ⋂₀ a).Nonempty) :
    (s inter ⋂₀ t).Nonempty := by
  rw [Set.sInter_eq_iInter]
  refine hs.inter_iInter_nonempty _ (fun i => ht _ i.2) fun a => ?_
  simpa using h (Subtype.val '' (a : Set t)) (by simp) (a.finite_toSet.image _)

/--
lemma `CompactSpace.nonempty_sInter` / 引理 `CompactSpace.nonempty_sInter`

English:
lemma CompactSpace.nonempty_sInter
  statement: [CompactSpace X] {s : Set (Set X)} (hsc : forall t in s, IsClosed t)
  proof: by
  simpa using isCompact_univ.nonempty_inter_sInter hsc (by simpa using hs)

中文:
引理 紧空间.nonempty_s整数er
  结论: [紧空间 X] {s : 集合 (集合 X)} (hsc : 对任意 t in s, 是闭集 t)
  证明: by
  simpa using isCompact_univ.nonempty_inter_sInter hsc (by simpa using hs)

Depends on / 依赖: isCompact_univ, isCompact_univ.nonempty_inter_sInter, nonempty_inter_sInter
-/
lemma CompactSpace.nonempty_sInter [CompactSpace X] {s : Set (Set X)} (hsc : forall t in s, IsClosed t)
    (hs : forall t subseteq s, t.Finite -> (⋂₀ t).Nonempty) : (⋂₀ s).Nonempty := by
  simpa using isCompact_univ.nonempty_inter_sInter hsc (by simpa using hs)

/--
theorem `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` / 定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`

English:
theorem IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  proof: by
  let i₀ := hι.some
  suffices (t i₀ inter ⋂ i, t i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at htn ⊢
  apply mt ((htc i₀).elim_directed_family_closed t htcl)
  push Not
  simp only [← nonempty_iff_ne_empty] at htn ⊢
  refine ⟨htd, fun i => ?_⟩
  rcases htd i₀ i with ⟨j, hji₀, hji⟩
  exact (htn j).mono (subset_inter hji₀ hji)

中文:
定理 是紧集.nonempty_i整数er_of_directed_nonempty_isCompact_isClosed
  证明: by
  let i₀ := hι.some
  suffices (t i₀ inter ⋂ i, t i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at htn ⊢
  apply mt ((htc i₀).elim_directed_family_closed t htcl)
  push Not
  simp only [← nonempty_iff_ne_empty] at htn ⊢
  refine ⟨htd, fun i => ?_⟩
  rcases htd i₀ i with ⟨j, hji₀, hji⟩
  exact (htn j).mono (subset_inter hji₀ hji)

Depends on / 依赖: Nonempty, elim_directed_family_closed, iInter_subset, inter_eq_right, inter_eq_right.mpr, nonempty_iff_ne_empty, subset_inter
-/
theorem IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    {ι : Type v} [hι : Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)
    (htn : forall i, (t i).Nonempty) (htc : forall i, IsCompact (t i)) (htcl : forall i, IsClosed (t i)) :
    (⋂ i, t i).Nonempty := by
  let i₀ := hι.some
  suffices (t i₀ inter ⋂ i, t i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at htn ⊢
  apply mt ((htc i₀).elim_directed_family_closed t htcl)
  push Not
  simp only [← nonempty_iff_ne_empty] at htn ⊢
  refine ⟨htd, fun i => ?_⟩
  rcases htd i₀ i with ⟨j, hji₀, hji⟩
  exact (htn j).mono (subset_inter hji₀ hji)

/--
theorem `IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed` / 定理 `IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed`

English:
theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
  proof: by
  rw [sInter_eq_iInter]
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (DirectedOn.directed_val hSd) (fun i => hSn i i.2) (fun i => hSc i i.2) (fun i => hScl i i.2)

中文:
定理 是紧集.nonempty_s整数er_of_directed_nonempty_isCompact_isClosed
  证明: by
  rw [sInter_eq_iInter]
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (DirectedOn.directed_val hSd) (fun i => hSn i i.2) (fun i => hSc i i.2) (fun i => hScl i i.2)

Depends on / 依赖: DirectedOn, DirectedOn.directed_val, IsCompact, IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed, directed_val, nonempty_iInter_of_directed_nonempty_isCompact_isClosed, sInter_eq_iInter
-/
theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    {S : Set (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) (hSn : forall U in S, U.Nonempty)
    (hSc : forall U in S, IsCompact U) (hScl : forall U in S, IsClosed U) : (⋂₀ S).Nonempty := by
  rw [sInter_eq_iInter]
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (DirectedOn.directed_val hSd) (fun i => hSn i i.2) (fun i => hSc i i.2) (fun i => hScl i i.2)

/--
theorem `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` / 定理 `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`

English:
theorem IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  statement: (t : Nat -> Set X)
  proof: have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
have : forall i, t i subseteq t 0 := fun i => tmono Nat.zero_le i
  have htc : forall i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

中文:
定理 是紧集.nonempty_i整数er_of_sequence_nonempty_isCompact_isClosed
  结论: (t : 自然数 -> 集合 X)
  证明: have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
have : forall i, t i subseteq t 0 := fun i => tmono Nat.zero_le i
  have htc : forall i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

Depends on / 依赖: Antitone, Directed, IsCompact, IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed, Nat.zero_le, antitone_nat_of_succ_le, directed_ge, ht0.of_isClosed_subset, nonempty_iInter_of_directed_nonempty_isCompact_isClosed, of_isClosed_subset, subseteq, tmono.directed_ge, zero_le
-/
theorem IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : Nat -> Set X)
    (htd : forall i, t (i + 1) subseteq t i) (htn : forall i, (t i).Nonempty) (ht0 : IsCompact (t 0))
    (htcl : forall i, IsClosed (t i)) : (⋂ i, t i).Nonempty :=
  have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
have : forall i, t i subseteq t 0 := fun i => tmono Nat.zero_le i
  have htc : forall i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

/--
theorem `IsCompact.elim_finite_subcover_image` / 定理 `IsCompact.elim_finite_subcover_image`

English:
theorem IsCompact.elim_finite_subcover_image
  statement: {b : Set ι} {c : ι -> Set X} (hs : IsCompact s)
  proof: by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b -> Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

中文:
定理 是紧集.elim_finite_subcover_image
  结论: {b : 集合 ι} {c : ι -> 集合 X} (hs : 是紧集 s)
  证明: by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b -> Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

Depends on / 依赖: Subtype, Subtype.forall, Subtype.val, biUnion_eq_iUnion, biUnion_image, d.finite_toSet.image, elim_finite_subcover, finite_toSet, hs.elim_finite_subcover
-/
theorem IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι -> Set X} (hs : IsCompact s)
    (hc₁ : forall i in b, IsOpen (c i)) (hc₂ : s subseteq ⋃ i in b, c i) :
    exists b', b' subseteq b ∧ Set.Finite b' ∧ s subseteq ⋃ i in b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b -> Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

/--
theorem `isCompact_of_finite_subcover` / 定理 `isCompact_of_finite_subcover`

English:
theorem isCompact_of_finite_subcover
  proof: fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_notMem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm]; rw [compl_iInter₂]
  simpa only [compl_compl]

中文:
定理 isCompact_of_finite_subcover
  证明: fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_notMem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm]; rw [compl_iInter₂]
  simpa only [compl_compl]

Depends on / 依赖: ClusterPt, SetCoe, SetCoe.forall, biInter_finset_mem, compl_compl, compl_notMem, contrapose, disjoint_iff, disjoint_iff_left, le_principal_iff, mem_iUnion, mem_of_superset, nhds_basis_opens, not_neBot, subset_compl_comm
-/
theorem isCompact_of_finite_subcover
    (h : forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) ->
      exists t : Finset ι, s subseteq ⋃ i in t, U i) :
    IsCompact s := fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_notMem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm]; rw [compl_iInter₂]
  simpa only [compl_compl]

-- TODO: reformulate using `Disjoint`
/--
theorem `isCompact_of_finite_subfamily_closed` / 定理 `isCompact_of_finite_subfamily_closed`

English:
theorem isCompact_of_finite_subfamily_closed
  proof: isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset]; rw [compl_iUnion]; rw [disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

中文:
定理 isCompact_of_finite_subfamily_closed
  证明: isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset]; rw [compl_iUnion]; rw [disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

Depends on / 依赖: compl_iUnion, disjoint_compl_right_iff_subset, disjoint_iff, isClosed_compl, isCompact_of_finite_subcover
-/
theorem isCompact_of_finite_subfamily_closed
    (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ ->
      exists u : Finset ι, (s inter ⋂ i in u, t i) = ∅) :
    IsCompact s :=
  isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset]; rw [compl_iUnion]; rw [disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/--
theorem `isCompact_iff_finite_subcover` / 定理 `isCompact_iff_finite_subcover`

English:
theorem isCompact_iff_finite_subcover
  proof: ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

中文:
定理 isCompact_iff_finite_subcover
  证明: ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

Depends on / 依赖: elim_finite_subcover, hs.elim_finite_subcover, isCompact_of_finite_subcover
-/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ forall {ι : Type u} (U : ι -> Set X),
      (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) -> exists t : Finset ι, s subseteq ⋃ i in t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

/--
theorem `isCompact_iff_finite_subfamily_closed` / 定理 `isCompact_iff_finite_subfamily_closed`

English:
theorem isCompact_iff_finite_subfamily_closed
  proof: ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩

中文:
定理 isCompact_iff_finite_subfamily_closed
  证明: ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩

Depends on / 依赖: elim_finite_subfamily_closed, hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed
-/
theorem isCompact_iff_finite_subfamily_closed :
    IsCompact s ↔ forall {ι : Type u} (t : ι -> Set X),
      (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ -> exists u : Finset ι, (s inter ⋂ i in u, t i) = ∅ :=
  ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩

/--
theorem `IsCompact.mem_nhdsSet_prod_of_forall` / 定理 `IsCompact.mem_nhdsSet_prod_of_forall`

English:
theorem IsCompact.mem_nhdsSet_prod_of_forall
  statement: {K : Set X} {Y} {l : Filter Y} {s : Set (X × Y)}
  proof: by
  refine hK.induction_on (by simp) (fun t t' ht hs => ?_) (fun t t' ht ht' => ?_) fun x hx => ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv

中文:
定理 是紧集.mem_nhdsSet_prod_of_对任意
  结论: {K : 集合 X} {Y} {l : 滤子 Y} {s : 集合 (X × Y)}
  证明: by
  refine hK.induction_on (by simp) (fun t t' ht hs => ?_) (fun t t' ht ht' => ?_) fun x hx => ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv

Depends on / 依赖: Subset, Subset.rfl, basis_sets, hK.induction_on, huo.mem_nhds, huo.mem_nhdsSet, induction_on, l.basis_sets, le_rfl, mem_iff, mem_nhds, mem_nhdsSet, mem_of_superset, nhdsSet_mono, nhdsWithin_le_nhds, nhds_basis_opens, prod_mem_prod, prod_mono, sup_prod
-/
theorem IsCompact.mem_nhdsSet_prod_of_forall {K : Set X} {Y} {l : Filter Y} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : forall x in K, s in 𝓝 x ×ˢ l) : s in (𝓝ˢ K) ×ˢ l := by
  refine hK.induction_on (by simp) (fun t t' ht hs => ?_) (fun t t' ht ht' => ?_) fun x hx => ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv

/--
theorem `IsCompact.nhdsSet_prod_eq_biSup` / 定理 `IsCompact.nhdsSet_prod_eq_biSup`

English:
theorem IsCompact.nhdsSet_prod_eq_biSup
  given: {K : Set X} (hK : IsCompact K) {Y} (l : Filter Y)
  proof: le_antisymm (fun s hs => hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun _ hx => prod_mono (nhds_le_nhdsSet hx) le_rfl)

中文:
定理 是紧集.nhdsSet_prod_eq_biSup
  条件: {K : 集合 X} (hK : 是紧集 K) {Y} (l : 滤子 Y)
  证明: le_antisymm (fun s hs => hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun _ hx => prod_mono (nhds_le_nhdsSet hx) le_rfl)

Depends on / 依赖: hK.mem_nhdsSet_prod_of_forall, le_antisymm, le_rfl, mem_nhdsSet_prod_of_forall, nhds_le_nhdsSet, prod_mono
-/
theorem IsCompact.nhdsSet_prod_eq_biSup {K : Set X} (hK : IsCompact K) {Y} (l : Filter Y) :
    (𝓝ˢ K) ×ˢ l = ⨆ x in K, 𝓝 x ×ˢ l :=
  le_antisymm (fun s hs => hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun _ hx => prod_mono (nhds_le_nhdsSet hx) le_rfl)

/--
theorem `IsCompact.prod_nhdsSet_eq_biSup` / 定理 `IsCompact.prod_nhdsSet_eq_biSup`

English:
theorem IsCompact.prod_nhdsSet_eq_biSup
  given: {K : Set Y} (hK : IsCompact K) {X} (l : Filter X)
  proof: by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

中文:
定理 是紧集.prod_nhdsSet_eq_biSup
  条件: {K : 集合 Y} (hK : 是紧集 K) {X} (l : 滤子 X)
  证明: by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

Depends on / 依赖: hK.nhdsSet_prod_eq_biSup, map_iSup, nhdsSet_prod_eq_biSup, prod_comm
-/
theorem IsCompact.prod_nhdsSet_eq_biSup {K : Set Y} (hK : IsCompact K) {X} (l : Filter X) :
    l ×ˢ (𝓝ˢ K) = ⨆ y in K, l ×ˢ 𝓝 y := by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

/--
theorem `IsCompact.mem_prod_nhdsSet_of_forall` / 定理 `IsCompact.mem_prod_nhdsSet_of_forall`

English:
theorem IsCompact.mem_prod_nhdsSet_of_forall
  statement: {K : Set Y} {X} {l : Filter X} {s : Set (X × Y)}
  proof: (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

中文:
定理 是紧集.mem_prod_nhdsSet_of_对任意
  结论: {K : 集合 Y} {X} {l : 滤子 X} {s : 集合 (X × Y)}
  证明: (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

Depends on / 依赖: hK.prod_nhdsSet_eq_biSup, prod_nhdsSet_eq_biSup
-/
theorem IsCompact.mem_prod_nhdsSet_of_forall {K : Set Y} {X} {l : Filter X} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : forall y in K, s in l ×ˢ 𝓝 y) : s in l ×ˢ 𝓝ˢ K :=
  (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

-- TODO: Is there a way to prove directly the `inf` version and then deduce the `Prod` one ?
-- That would seem a bit more natural.
/--
theorem `IsCompact.nhdsSet_inf_eq_biSup` / 定理 `IsCompact.nhdsSet_inf_eq_biSup`

English:
theorem IsCompact.nhdsSet_inf_eq_biSup
  given: {K : Set X} (hK : IsCompact K) (l : Filter X)
  proof: by
  have : forall f : Filter X, f ⊓ l = comap Function.diag (f ×ˢ l) := fun f => by
    simpa only [comap_prod] using! congrArg₂ (· ⊓ ·) comap_id.symm comap_id.symm
  simp_rw [this, ← comap_iSup, hK.nhdsSet_prod_eq_biSup]

中文:
定理 是紧集.nhdsSet_inf_eq_biSup
  条件: {K : 集合 X} (hK : 是紧集 K) (l : 滤子 X)
  证明: by
  have : forall f : Filter X, f ⊓ l = comap Function.diag (f ×ˢ l) := fun f => by
    simpa only [comap_prod] using! congrArg₂ (· ⊓ ·) comap_id.symm comap_id.symm
  simp_rw [this, ← comap_iSup, hK.nhdsSet_prod_eq_biSup]

Depends on / 依赖: Filter, Function, Function.diag, comap_iSup, comap_id, comap_id.symm, comap_prod, hK.nhdsSet_prod_eq_biSup, nhdsSet_prod_eq_biSup, simp_rw
-/
theorem IsCompact.nhdsSet_inf_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    (𝓝ˢ K) ⊓ l = ⨆ x in K, 𝓝 x ⊓ l := by
  have : forall f : Filter X, f ⊓ l = comap Function.diag (f ×ˢ l) := fun f => by
    simpa only [comap_prod] using! congrArg₂ (· ⊓ ·) comap_id.symm comap_id.symm
  simp_rw [this, ← comap_iSup, hK.nhdsSet_prod_eq_biSup]

/--
theorem `IsCompact.inf_nhdsSet_eq_biSup` / 定理 `IsCompact.inf_nhdsSet_eq_biSup`

English:
theorem IsCompact.inf_nhdsSet_eq_biSup
  given: {K : Set X} (hK : IsCompact K) (l : Filter X)
  proof: by
  simp only [inf_comm l, hK.nhdsSet_inf_eq_biSup]

中文:
定理 是紧集.inf_nhdsSet_eq_biSup
  条件: {K : 集合 X} (hK : 是紧集 K) (l : 滤子 X)
  证明: by
  simp only [inf_comm l, hK.nhdsSet_inf_eq_biSup]

Depends on / 依赖: hK.nhdsSet_inf_eq_biSup, inf_comm, nhdsSet_inf_eq_biSup
-/
theorem IsCompact.inf_nhdsSet_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    l ⊓ (𝓝ˢ K) = ⨆ x in K, l ⊓ 𝓝 x := by
  simp only [inf_comm l, hK.nhdsSet_inf_eq_biSup]

/--
theorem `IsCompact.mem_nhdsSet_inf_of_forall` / 定理 `IsCompact.mem_nhdsSet_inf_of_forall`

English:
theorem IsCompact.mem_nhdsSet_inf_of_forall
  statement: {K : Set X} {l : Filter X} {s : Set X}
  proof: (hK.nhdsSet_inf_eq_biSup l).symm ▸ by simpa using hs

中文:
定理 是紧集.mem_nhdsSet_inf_of_对任意
  结论: {K : 集合 X} {l : 滤子 X} {s : 集合 X}
  证明: (hK.nhdsSet_inf_eq_biSup l).symm ▸ by simpa using hs

Depends on / 依赖: hK.nhdsSet_inf_eq_biSup, nhdsSet_inf_eq_biSup
-/
theorem IsCompact.mem_nhdsSet_inf_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : forall x in K, s in 𝓝 x ⊓ l) : s in (𝓝ˢ K) ⊓ l :=
  (hK.nhdsSet_inf_eq_biSup l).symm ▸ by simpa using hs

/--
theorem `IsCompact.mem_inf_nhdsSet_of_forall` / 定理 `IsCompact.mem_inf_nhdsSet_of_forall`

English:
theorem IsCompact.mem_inf_nhdsSet_of_forall
  statement: {K : Set X} {l : Filter X} {s : Set X}
  proof: (hK.inf_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

中文:
定理 是紧集.mem_inf_nhdsSet_of_对任意
  结论: {K : 集合 X} {l : 滤子 X} {s : 集合 X}
  证明: (hK.inf_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

Depends on / 依赖: hK.inf_nhdsSet_eq_biSup, inf_nhdsSet_eq_biSup
-/
theorem IsCompact.mem_inf_nhdsSet_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : forall y in K, s in l ⊓ 𝓝 y) : s in l ⊓ 𝓝ˢ K :=
  (hK.inf_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

/--
theorem `IsCompact.eventually_forall_of_forall_eventually` / 定理 `IsCompact.eventually_forall_of_forall_eventually`

English:
theorem IsCompact.eventually_forall_of_forall_eventually
  statement: {x₀ : X} {K : Set Y} (hK : IsCompact K)
  proof: by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h => h.self_of_nhdsSet

@[compactness ., grind .]

中文:
定理 是紧集.eventually_对任意_of_对任意_eventually
  结论: {x₀ : X} {K : 集合 Y} (hK : 是紧集 K)
  证明: by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h => h.self_of_nhdsSet

@[compactness ., grind .]

Depends on / 依赖: eventually_iSup, h.self_of_nhdsSet, hK.prod_nhdsSet_eq_biSup, hP.curry.mono, nhds_prod_eq, prod_nhdsSet_eq_biSup, self_of_nhdsSet
-/
theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : X} {K : Set Y} (hK : IsCompact K)
    {P : X -> Y -> Prop} (hP : forall y in K, forallᶠ z : X × Y in 𝓝 (x₀, y), P z.1 z.2) :
    forallᶠ x in 𝓝 x₀, forall y in K, P x y := by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h => h.self_of_nhdsSet

@[compactness ., grind .]
/--
theorem `isCompact_empty` / 定理 `isCompact_empty`

English:
theorem isCompact_empty
  statement: IsCompact (∅ : Set X)
  proof: fun _f hnf hsf =>
Not.elim hnf.ne empty_mem_iff_bot.1 le_principal_iff.1 hsf

@[compactness ., grind .]

中文:
定理 isCompact_empty
  结论: 是紧集 (∅ : 集合 X)
  证明: fun _f hnf hsf =>
Not.elim hnf.ne empty_mem_iff_bot.1 le_principal_iff.1 hsf

@[compactness ., grind .]
-/
theorem isCompact_empty : IsCompact (∅ : Set X) := fun _f hnf hsf =>
Not.elim hnf.ne empty_mem_iff_bot.1 le_principal_iff.1 hsf

@[compactness ., grind .]
/--
theorem `isCompact_singleton` / 定理 `isCompact_singleton`

English:
theorem isCompact_singleton
  given: {x : X}
  statement: IsCompact ({x} : Set X)
  proof: fun _ hf hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

中文:
定理 isCompact_singleton
  条件: {x : X}
  结论: 是紧集 ({x} : 集合 X)
  证明: fun _ hf hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩
-/
theorem isCompact_singleton {x : X} : IsCompact ({x} : Set X) := fun _ hf hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

/--
theorem `Set.Subsingleton.isCompact` / 定理 `Set.Subsingleton.isCompact`

English:
theorem Set.Subsingleton.isCompact
  given: (hs : s.Subsingleton)
  statement: IsCompact s
  proof: Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton

中文:
定理 集合.子单例.isCompact
  条件: (hs : s.子单例)
  结论: 是紧集 s
  证明: Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton

Depends on / 依赖: Subsingleton, Subsingleton.induction_on, induction_on, isCompact_empty, isCompact_singleton
-/
theorem Set.Subsingleton.isCompact (hs : s.Subsingleton) : IsCompact s :=
  Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton

/--
theorem `Set.Finite.isCompact_biUnion` / 定理 `Set.Finite.isCompact_biUnion`

English:
theorem Set.Finite.isCompact_biUnion
  statement: {s : Set ι} {f : ι -> Set X} (hs : s.Finite)
  proof: isCompact_iff_ultrafilter_le_nhds'.2 fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩

中文:
定理 集合.有限.isCompact_biUnion
  结论: {s : 集合 ι} {f : ι -> 集合 X} (hs : s.有限)
  证明: isCompact_iff_ultrafilter_le_nhds'.2 fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩

Depends on / 依赖: Ultrafilter, Ultrafilter.finite_biUnion_mem_iff, finite_biUnion_mem_iff, isCompact_iff_ultrafilter_le_nhds, le_principal_iff, ultrafilter_le_nhds
-/
theorem Set.Finite.isCompact_biUnion {s : Set ι} {f : ι -> Set X} (hs : s.Finite)
    (hf : forall i in s, IsCompact (f i)) : IsCompact (⋃ i in s, f i) :=
  isCompact_iff_ultrafilter_le_nhds'.2 fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩

/--
theorem `Finset.isCompact_biUnion` / 定理 `Finset.isCompact_biUnion`

English:
theorem Finset.isCompact_biUnion
  given: (s : Finset ι) {f : ι -> Set X} (hf : forall i in s, IsCompact (f i))
  proof: s.finite_toSet.isCompact_biUnion hf

@[compactness .]

中文:
定理 有限集.isCompact_biUnion
  条件: (s : 有限集 ι) {f : ι -> 集合 X} (hf : 对任意 i in s, 是紧集 (f i))
  证明: s.finite_toSet.isCompact_biUnion hf

@[compactness .]

Depends on / 依赖: finite_toSet, isCompact_biUnion, s.finite_toSet.isCompact_biUnion
-/
theorem Finset.isCompact_biUnion (s : Finset ι) {f : ι -> Set X} (hf : forall i in s, IsCompact (f i)) :
    IsCompact (⋃ i in s, f i) :=
  s.finite_toSet.isCompact_biUnion hf

@[compactness .]
/--
theorem `isCompact_accumulate` / 定理 `isCompact_accumulate`

English:
theorem isCompact_accumulate
  given: {K : Nat -> Set X} (hK : forall n, IsCompact (K n)) (n : Nat)
  proof: (finite_le_nat n).isCompact_biUnion fun k _ => hK k

@[compactness .]

中文:
定理 isCompact_accumulate
  条件: {K : 自然数 -> 集合 X} (hK : 对任意 n, 是紧集 (K n)) (n : 自然数)
  证明: (finite_le_nat n).isCompact_biUnion fun k _ => hK k

@[compactness .]

Depends on / 依赖: finite_le_nat, isCompact_biUnion
-/
theorem isCompact_accumulate {K : Nat -> Set X} (hK : forall n, IsCompact (K n)) (n : Nat) :
    IsCompact (accumulate K n) :=
  (finite_le_nat n).isCompact_biUnion fun k _ => hK k

@[compactness .]
/--
theorem `Set.Finite.isCompact_sUnion` / 定理 `Set.Finite.isCompact_sUnion`

English:
theorem Set.Finite.isCompact_sUnion
  given: {S : Set (Set X)} (hf : S.Finite) (hc : forall s in S, IsCompact s)
  proof: by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

@[compactness .]

中文:
定理 集合.有限.isCompact_sUnion
  条件: {S : 集合 (集合 X)} (hf : S.有限) (hc : 对任意 s in S, 是紧集 s)
  证明: by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

@[compactness .]

Depends on / 依赖: hf.isCompact_biUnion, isCompact_biUnion, sUnion_eq_biUnion
-/
theorem Set.Finite.isCompact_sUnion {S : Set (Set X)} (hf : S.Finite) (hc : forall s in S, IsCompact s) :
    IsCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

@[compactness .]
/--
theorem `isCompact_iUnion` / 定理 `isCompact_iUnion`

English:
theorem isCompact_iUnion
  given: {ι : Sort*} {f : ι -> Set X} [Finite ι] (h : forall i, IsCompact (f i))
  proof: (finite_range f).isCompact_sUnion forall_mem_range.2 h

中文:
定理 isCompact_iUnion
  条件: {ι : 类型层*} {f : ι -> 集合 X} [有限 ι] (h : 对任意 i, 是紧集 (f i))
  证明: (finite_range f).isCompact_sUnion forall_mem_range.2 h

Depends on / 依赖: finite_range, forall_mem_range, isCompact_sUnion
-/
theorem isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite ι] (h : forall i, IsCompact (f i)) :
    IsCompact (⋃ i, f i) :=
(finite_range f).isCompact_sUnion forall_mem_range.2 h

/--
theorem `Set.Finite.isCompact` / 定理 `Set.Finite.isCompact`

English:
theorem Set.Finite.isCompact
  given: (hs : s.Finite)
  statement: IsCompact s
  proof: biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton

中文:
定理 集合.有限.isCompact
  条件: (hs : s.有限)
  结论: 是紧集 s
  证明: biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton
-/
@[simp, compactness .] theorem Set.Finite.isCompact (hs : s.Finite) : IsCompact s :=
  biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton

/--
theorem `Set.sUnion_isCompact_eq_univ` / 定理 `Set.sUnion_isCompact_eq_univ`

English:
theorem Set.sUnion_isCompact_eq_univ
  statement: ⋃₀ {(s : Set X) | IsCompact s} = univ
  proof: eq_univ_of_forall fun x => ⟨{x}, by simp⟩

中文:
定理 集合.sUnion_isCompact_eq_univ
  结论: ⋃₀ {(s : 集合 X) | 是紧集 s} = univ
  证明: eq_univ_of_forall fun x => ⟨{x}, by simp⟩
-/
@[simp] theorem Set.sUnion_isCompact_eq_univ : ⋃₀ {(s : Set X) | IsCompact s} = univ :=
eq_univ_of_forall fun x => ⟨{x}, by simp⟩

/--
theorem `IsCompact.finite_of_discrete` / 定理 `IsCompact.finite_of_discrete`

English:
theorem IsCompact.finite_of_discrete
  given: [DiscreteTopology X] (hs : IsCompact s)
  statement: s.Finite
  proof: by
  have : forall x : X, ({x} : Set X) in 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst

中文:
定理 是紧集.finite_of_discrete
  条件: [离散拓扑 X] (hs : 是紧集 s)
  结论: s.有限
  证明: by
  have : forall x : X, ({x} : Set X) in 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst

Depends on / 依赖: biUnion_of_singleton, elim_nhds_subcover, finite_toSet, hs.elim_nhds_subcover, nhds_discrete, set_biUnion_coe, subset, t.finite_toSet.subset, t.set_biUnion_coe
-/
theorem IsCompact.finite_of_discrete [DiscreteTopology X] (hs : IsCompact s) : s.Finite := by
  have : forall x : X, ({x} : Set X) in 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst

/--
theorem `isCompact_iff_finite` / 定理 `isCompact_iff_finite`

English:
theorem isCompact_iff_finite
  given: [DiscreteTopology X]
  statement: IsCompact s ↔ s.Finite
  proof: ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩

@[compactness .]

中文:
定理 isCompact_iff_finite
  条件: [离散拓扑 X]
  结论: 是紧集 s ↔ s.有限
  证明: ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩

@[compactness .]

Depends on / 依赖: finite_of_discrete, h.finite_of_discrete, h.isCompact, isCompact
-/
theorem isCompact_iff_finite [DiscreteTopology X] : IsCompact s ↔ s.Finite :=
  ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩

@[compactness .]
/--
theorem `IsCompact.union` / 定理 `IsCompact.union`

English:
theorem IsCompact.union
  given: (hs : IsCompact s) (ht : IsCompact t)
  statement: IsCompact (s union t)
  proof: by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption

@[compactness .]

中文:
定理 是紧集.union
  条件: (hs : 是紧集 s) (ht : 是紧集 t)
  结论: 是紧集 (s union t)
  证明: by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption

@[compactness .]

Depends on / 依赖: isCompact_iUnion, union_eq_iUnion
-/
theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s union t) := by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption

@[compactness .]
/--
theorem `IsCompact.insert` / 定理 `IsCompact.insert`

English:
theorem IsCompact.insert
  given: (hs : IsCompact s) (a)
  statement: IsCompact (insert a s)
  proof: isCompact_singleton.union hs

中文:
定理 是紧集.insert
  条件: (hs : 是紧集 s) (a)
  结论: 是紧集 (insert a s)
  证明: isCompact_singleton.union hs
-/
protected theorem IsCompact.insert (hs : IsCompact s) (a) : IsCompact (insert a s) :=
  isCompact_singleton.union hs

-- TODO: reformulate using `𝓝ˢ`
/--
theorem `exists_subset_nhds_of_isCompact'` / 定理 `exists_subset_nhds_of_isCompact'`

English:
theorem exists_subset_nhds_of_isCompact'
  statement: [Nonempty ι] {V : ι -> Set X}
  proof: by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices exists i, V i subseteq W from this.imp fun i hi => hi.trans hWU
  by_contra! H
  replace H : forall i, (V i inter Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i inter Wᶜ).Nonempty := by
    refine
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun i j => ?_) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine ⟨k, ⟨fun x => ?_, fun x => ?_⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i subseteq W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction

omit [TopologicalSpace X] in

中文:
定理 存在_subset_nhds_of_isCompact'
  结论: [非空 ι] {V : ι -> 集合 X}
  证明: by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices exists i, V i subseteq W from this.imp fun i hi => hi.trans hWU
  by_contra! H
  replace H : forall i, (V i inter Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i inter Wᶜ).Nonempty := by
    refine
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun i j => ?_) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine ⟨k, ⟨fun x => ?_, fun x => ?_⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i subseteq W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction

omit [TopologicalSpace X] in

Depends on / 依赖: IsCompact, IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed, Nonempty, Set.inter_compl_nonempty_iff.mpr, W_op, W_op.isClosed_compl, exists_open_set_nhds, hV_closed, hV_cpct, hi.trans, inter_compl_nonempty_iff, inter_right, isClosed_compl, nonempty_iInter_of_directed_nonempty_isCompact_isClosed, replace, subseteq, this.imp
-/
theorem exists_subset_nhds_of_isCompact' [Nonempty ι] {V : ι -> Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : forall i, IsCompact (V i)) (hV_closed : forall i, IsClosed (V i))
    {U : Set X} (hU : forall x in ⋂ i, V i, U in 𝓝 x) : exists i, V i subseteq U := by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices exists i, V i subseteq W from this.imp fun i hi => hi.trans hWU
  by_contra! H
  replace H : forall i, (V i inter Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i inter Wᶜ).Nonempty := by
    refine
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun i j => ?_) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine ⟨k, ⟨fun x => ?_, fun x => ?_⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i subseteq W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction

omit [TopologicalSpace X] in
/--
theorem `isCompact_generateFrom` / 定理 `isCompact_generateFrom`

English:
theorem isCompact_generateFrom
  statement: [T : TopologicalSpace X]
  proof: by
  rw [isCompact_iff_ultrafilter_le_nhds']; rw [hTS]
  intro F hsF
  by_contra hF
  have hSF : forall x in s, exists t, x in t ∧ t in S ∧ t ∉ F := by simpa [nhds_generateFrom] using hF
  choose! U hxU hSU hUF using hSF
  obtain ⟨Q, hQU, hQ, hsQ⟩ := h (U '' s) (by simpa [Set.subset_def])
    (fun x hx => Set.mem_sUnion_of_mem (hxU _ hx) (by grind))
  have : forall s in Q, s ∉ F := fun s hsQ => (hQU hsQ).choose_spec.2 ▸ hUF _ (hQU hsQ).choose_spec.1
  have hQF : ⋂₀ (compl '' Q) in F.sets := by simpa [Filter.biInter_mem hQ, F.compl_mem_iff_notMem]
  have : ⋃₀ Q ∉ F := by
    simpa [-Set.sInter_image, ← Set.compl_sUnion, hsQ, F.compl_mem_iff_notMem] using hQF
  exact this (F.mem_of_superset hsF hsQ)

omit [TopologicalSpace X] in

中文:
定理 isCompact_generateFrom
  结论: [T : 拓扑空间 X]
  证明: by
  rw [isCompact_iff_ultrafilter_le_nhds']; rw [hTS]
  intro F hsF
  by_contra hF
  have hSF : forall x in s, exists t, x in t ∧ t in S ∧ t ∉ F := by simpa [nhds_generateFrom] using hF
  choose! U hxU hSU hUF using hSF
  obtain ⟨Q, hQU, hQ, hsQ⟩ := h (U '' s) (by simpa [Set.subset_def])
    (fun x hx => Set.mem_sUnion_of_mem (hxU _ hx) (by grind))
  have : forall s in Q, s ∉ F := fun s hsQ => (hQU hsQ).choose_spec.2 ▸ hUF _ (hQU hsQ).choose_spec.1
  have hQF : ⋂₀ (compl '' Q) in F.sets := by simpa [Filter.biInter_mem hQ, F.compl_mem_iff_notMem]
  have : ⋃₀ Q ∉ F := by
    simpa [-Set.sInter_image, ← Set.compl_sUnion, hsQ, F.compl_mem_iff_notMem] using hQF
  exact this (F.mem_of_superset hsF hsQ)

omit [TopologicalSpace X] in

Depends on / 依赖: F.sets, Filter, Filter.biInter, Set.mem_sUnion_of_mem, Set.subset_def, biInter, choose_spec, isCompact_iff_ultrafilter_le_nhds, mem_sUnion_of_mem, nhds_generateFrom, subset_def
-/
theorem isCompact_generateFrom [T : TopologicalSpace X]
    {S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X}
    (h : forall P subseteq S, s subseteq ⋃₀ P -> exists Q subseteq P, Q.Finite ∧ s subseteq ⋃₀ Q) :
    IsCompact s := by
  rw [isCompact_iff_ultrafilter_le_nhds']; rw [hTS]
  intro F hsF
  by_contra hF
  have hSF : forall x in s, exists t, x in t ∧ t in S ∧ t ∉ F := by simpa [nhds_generateFrom] using hF
  choose! U hxU hSU hUF using hSF
  obtain ⟨Q, hQU, hQ, hsQ⟩ := h (U '' s) (by simpa [Set.subset_def])
    (fun x hx => Set.mem_sUnion_of_mem (hxU _ hx) (by grind))
  have : forall s in Q, s ∉ F := fun s hsQ => (hQU hsQ).choose_spec.2 ▸ hUF _ (hQU hsQ).choose_spec.1
  have hQF : ⋂₀ (compl '' Q) in F.sets := by simpa [Filter.biInter_mem hQ, F.compl_mem_iff_notMem]
  have : ⋃₀ Q ∉ F := by
    simpa [-Set.sInter_image, ← Set.compl_sUnion, hsQ, F.compl_mem_iff_notMem] using hQF
  exact this (F.mem_of_superset hsF hsQ)

omit [TopologicalSpace X] in
/--
theorem `isCompact_generateFrom'` / 定理 `isCompact_generateFrom'`

English:
theorem isCompact_generateFrom'
  statement: [T : TopologicalSpace X]
  proof: isCompact_generateFrom hTS fun P hP hs =>
    have ⟨J, hJ, cover⟩ := h P (fun a => ⟨a.1, hP a.2⟩) (sUnion_eq_iUnion ▸ hs)
    ⟨(·.1) '' J, ⟨by simp, hJ.image _, by aesop⟩⟩

中文:
定理 isCompact_generateFrom'
  结论: [T : 拓扑空间 X]
  证明: isCompact_generateFrom hTS fun P hP hs =>
    have ⟨J, hJ, cover⟩ := h P (fun a => ⟨a.1, hP a.2⟩) (sUnion_eq_iUnion ▸ hs)
    ⟨(·.1) '' J, ⟨by simp, hJ.image _, by aesop⟩⟩

Depends on / 依赖: hJ.image, isCompact_generateFrom, sUnion_eq_iUnion
-/
theorem isCompact_generateFrom' [T : TopologicalSpace X]
    {S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X}
    (h : forall (ι : Type u) (U : ι -> S), s subseteq ⋃ i, U i -> exists J : Set ι, J.Finite ∧ s subseteq ⋃ i in J, U i) :
    IsCompact s :=
  isCompact_generateFrom hTS fun P hP hs =>
    have ⟨J, hJ, cover⟩ := h P (fun a => ⟨a.1, hP a.2⟩) (sUnion_eq_iUnion ▸ hs)
    ⟨(·.1) '' J, ⟨by simp, hJ.image _, by aesop⟩⟩

namespace Filter

/--
theorem `hasBasis_cocompact` / 定理 `hasBasis_cocompact`

English:
theorem hasBasis_cocompact
  statement: (cocompact X).HasBasis IsCompact compl
  proof: hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s union t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isCompact_empty⟩

中文:
定理 hasBasis_cocompact
  结论: (cocompact X).有基 是紧集 compl
  证明: hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s union t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isCompact_empty⟩

Depends on / 依赖: compl_subset_compl, hasBasis_biInf_principal, hs.union, isCompact_empty, subset_union_left, subset_union_right
-/
theorem hasBasis_cocompact : (cocompact X).HasBasis IsCompact compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s union t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isCompact_empty⟩

/--
theorem `mem_cocompact` / 定理 `mem_cocompact`

English:
theorem mem_cocompact
  statement: s in cocompact X ↔ exists t, IsCompact t ∧ tᶜ subseteq s
  proof: hasBasis_cocompact.mem_iff

中文:
定理 mem_cocompact
  结论: s in cocompact X ↔ 存在 t, 是紧集 t ∧ tᶜ subseteq s
  证明: hasBasis_cocompact.mem_iff

Depends on / 依赖: hasBasis_cocompact, hasBasis_cocompact.mem_iff, mem_iff
-/
theorem mem_cocompact : s in cocompact X ↔ exists t, IsCompact t ∧ tᶜ subseteq s :=
  hasBasis_cocompact.mem_iff

/--
theorem `mem_cocompact'` / 定理 `mem_cocompact'`

English:
theorem mem_cocompact'
  statement: s in cocompact X ↔ exists t, IsCompact t ∧ sᶜ subseteq t
  proof: mem_cocompact.trans exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

中文:
定理 mem_cocompact'
  结论: s in cocompact X ↔ 存在 t, 是紧集 t ∧ sᶜ subseteq t
  证明: mem_cocompact.trans exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

Depends on / 依赖: and_congr_right, compl_subset_comm, exists_congr, mem_cocompact, mem_cocompact.trans
-/
theorem mem_cocompact' : s in cocompact X ↔ exists t, IsCompact t ∧ sᶜ subseteq t :=
mem_cocompact.trans exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

/--
theorem `_root_.IsCompact.compl_mem_cocompact` / 定理 `_root_.IsCompact.compl_mem_cocompact`

English:
theorem _root_.IsCompact.compl_mem_cocompact
  given: (hs : IsCompact s)
  statement: sᶜ in Filter.cocompact X
  proof: hasBasis_cocompact.mem_of_mem hs

中文:
定理 _root_.是紧集.compl_mem_cocompact
  条件: (hs : 是紧集 s)
  结论: sᶜ in 滤子.cocompact X
  证明: hasBasis_cocompact.mem_of_mem hs

Depends on / 依赖: hasBasis_cocompact, hasBasis_cocompact.mem_of_mem, mem_of_mem
-/
theorem _root_.IsCompact.compl_mem_cocompact (hs : IsCompact s) : sᶜ in Filter.cocompact X :=
  hasBasis_cocompact.mem_of_mem hs

/--
theorem `cocompact_le_cofinite` / 定理 `cocompact_le_cofinite`

English:
theorem cocompact_le_cofinite
  statement: cocompact X <= cofinite
  proof: fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact

中文:
定理 cocompact_le_cofinite
  结论: cocompact X <= cofinite
  证明: fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact
-/
theorem cocompact_le_cofinite : cocompact X <= cofinite := fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact

/--
theorem `cocompact_eq_cofinite` / 定理 `cocompact_eq_cofinite`

English:
theorem cocompact_eq_cofinite
  given: (X : Type*) [TopologicalSpace X] [DiscreteTopology X]
  proof: by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]

中文:
定理 cocompact_eq_cofinite
  条件: (X : 类型) [拓扑空间 X] [离散拓扑 X]
  证明: by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]

Depends on / 依赖: cocompact, eq_biInf, hasBasis_cofinite, hasBasis_cofinite.eq_biInf, isCompact_iff_finite
-/
theorem cocompact_eq_cofinite (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    cocompact X = cofinite := by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]

/--
theorem `disjoint_cocompact_left` / 定理 `disjoint_cocompact_left`

English:
theorem disjoint_cocompact_left
  given: (f : Filter X)
  proof: by
  simp_rw [hasBasis_cocompact.disjoint_iff_left, compl_compl]
  tauto

中文:
定理 disjoint_cocompact_left
  条件: (f : 滤子 X)
  证明: by
  simp_rw [hasBasis_cocompact.disjoint_iff_left, compl_compl]
  tauto

Depends on / 依赖: compl_compl, disjoint_iff_left, hasBasis_cocompact, hasBasis_cocompact.disjoint_iff_left, simp_rw
-/
theorem disjoint_cocompact_left (f : Filter X) :
    Disjoint (Filter.cocompact X) f ↔ exists K in f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_left, compl_compl]
  tauto

/--
theorem `disjoint_cocompact_right` / 定理 `disjoint_cocompact_right`

English:
theorem disjoint_cocompact_right
  given: (f : Filter X)
  proof: by
  simp_rw [hasBasis_cocompact.disjoint_iff_right, compl_compl]
  tauto

中文:
定理 disjoint_cocompact_right
  条件: (f : 滤子 X)
  证明: by
  simp_rw [hasBasis_cocompact.disjoint_iff_right, compl_compl]
  tauto

Depends on / 依赖: compl_compl, disjoint_iff_right, hasBasis_cocompact, hasBasis_cocompact.disjoint_iff_right, simp_rw
-/
theorem disjoint_cocompact_right (f : Filter X) :
    Disjoint f (Filter.cocompact X) ↔ exists K in f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_right, compl_compl]
  tauto

/--
theorem `Tendsto.isCompact_insert_range_of_cocompact` / 定理 `Tendsto.isCompact_insert_range_of_cocompact`

English:
theorem Tendsto.isCompact_insert_range_of_cocompact
  statement: {f : X -> Y} {y}
  proof: by
  intro l hne hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K in l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
exact ⟨y, Or.inr image_subset_range _ _ hy, hyl⟩

中文:
定理 收敛.isCompact_insert_range_of_cocompact
  结论: {f : X -> Y} {y}
  证明: by
  intro l hne hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K in l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
exact ⟨y, Or.inr image_subset_range _ _ hy, hyl⟩

Depends on / 依赖: ClusterPt, Or.inl, clusterPt_iff_nonempty, exacts, filter_upwards, hd.le_bot, le_bot, le_principal_iff, mem_cocompact, mem_image_of_mem, mem_of_mem_nhds, not_disjoint_iff_nonempty_inter, not_forall, not_not
-/
theorem Tendsto.isCompact_insert_range_of_cocompact {f : X -> Y} {y}
    (hf : Tendsto f (cocompact X) (𝓝 y)) (hfc : Continuous f) : IsCompact (insert y (range f)) := by
  intro l hne hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K in l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
exact ⟨y, Or.inr image_subset_range _ _ hy, hyl⟩

/--
theorem `Tendsto.isCompact_insert_range_of_cofinite` / 定理 `Tendsto.isCompact_insert_range_of_cofinite`

English:
theorem Tendsto.isCompact_insert_range_of_cofinite
  given: {f : ι -> X} {x} (hf : Tendsto f cofinite (𝓝 x))
  proof: by
  let : TopologicalSpace ι := ⊥; have h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology

中文:
定理 收敛.isCompact_insert_range_of_cofinite
  条件: {f : ι -> X} {x} (hf : 收敛 f cofinite (𝓝 x))
  证明: by
  let : TopologicalSpace ι := ⊥; have h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology

Depends on / 依赖: DiscreteTopology, TopologicalSpace, cocompact_eq_cofinite, continuous_of_discreteTopology, hf.isCompact_insert_range_of_cocompact, isCompact_insert_range_of_cocompact
-/
theorem Tendsto.isCompact_insert_range_of_cofinite {f : ι -> X} {x} (hf : Tendsto f cofinite (𝓝 x)) :
    IsCompact (insert x (range f)) := by
  let : TopologicalSpace ι := ⊥; have h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology

/--
theorem `Tendsto.isCompact_insert_range` / 定理 `Tendsto.isCompact_insert_range`

English:
theorem Tendsto.isCompact_insert_range
  given: {f : Nat -> X} {x} (hf : Tendsto f atTop (𝓝 x))
  proof: Filter.Tendsto.isCompact_insert_range_of_cofinite Nat.cofinite_eq_atTop.symm ▸ hf

中文:
定理 收敛.isCompact_insert_range
  条件: {f : 自然数 -> X} {x} (hf : 收敛 f atTop (𝓝 x))
  证明: Filter.Tendsto.isCompact_insert_range_of_cofinite Nat.cofinite_eq_atTop.symm ▸ hf

Depends on / 依赖: Filter, Filter.Tendsto.isCompact_insert_range_of_cofinite, Nat.cofinite_eq_atTop.symm, Tendsto, cofinite_eq_atTop, isCompact_insert_range_of_cofinite
-/
theorem Tendsto.isCompact_insert_range {f : Nat -> X} {x} (hf : Tendsto f atTop (𝓝 x)) :
    IsCompact (insert x (range f)) :=
Filter.Tendsto.isCompact_insert_range_of_cofinite Nat.cofinite_eq_atTop.symm ▸ hf

/--
theorem `hasBasis_coclosedCompact` / 定理 `hasBasis_coclosedCompact`

English:
theorem hasBasis_coclosedCompact
  proof: by
  simp only [Filter.coclosedCompact, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s union t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

中文:
定理 hasBasis_coclosedCompact
  证明: by
  simp only [Filter.coclosedCompact, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s union t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

Depends on / 依赖: Filter, Filter.coclosedCompact, coclosedCompact, compl_subset_compl, hasBasis_biInf_principal, iInf_and, isClosed_empty, isCompact_empty, subset_union_left, subset_union_right
-/
theorem hasBasis_coclosedCompact :
    (Filter.coclosedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl := by
  simp only [Filter.coclosedCompact, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s union t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

/--
theorem `mem_coclosedCompact_iff` / 定理 `mem_coclosedCompact_iff`

English:
theorem mem_coclosedCompact_iff
  proof: by
  refine hasBasis_coclosedCompact.mem_iff.trans ⟨?_, fun h => ?_⟩
  · rintro ⟨t, ⟨htcl, htco⟩, hst⟩
exact htco.of_isClosed_subset isClosed_closure
      closure_minimal (compl_subset_comm.2 hst) htcl
  · exact ⟨closure sᶜ, ⟨isClosed_closure, h⟩, compl_subset_comm.2 subset_closure⟩

中文:
定理 mem_coclosedCompact_iff
  证明: by
  refine hasBasis_coclosedCompact.mem_iff.trans ⟨?_, fun h => ?_⟩
  · rintro ⟨t, ⟨htcl, htco⟩, hst⟩
exact htco.of_isClosed_subset isClosed_closure
      closure_minimal (compl_subset_comm.2 hst) htcl
  · exact ⟨closure sᶜ, ⟨isClosed_closure, h⟩, compl_subset_comm.2 subset_closure⟩

Depends on / 依赖: closure, closure_minimal, compl_subset_comm, hasBasis_coclosedCompact, hasBasis_coclosedCompact.mem_iff.trans, htco.of_isClosed_subset, isClosed_closure, mem_iff, of_isClosed_subset, subset_closure
-/
theorem mem_coclosedCompact_iff :
    s in coclosedCompact X ↔ IsCompact (closure sᶜ) := by
  refine hasBasis_coclosedCompact.mem_iff.trans ⟨?_, fun h => ?_⟩
  · rintro ⟨t, ⟨htcl, htco⟩, hst⟩
exact htco.of_isClosed_subset isClosed_closure
      closure_minimal (compl_subset_comm.2 hst) htcl
  · exact ⟨closure sᶜ, ⟨isClosed_closure, h⟩, compl_subset_comm.2 subset_closure⟩

/--
theorem `compl_mem_coclosedCompact` / 定理 `compl_mem_coclosedCompact`

English:
theorem compl_mem_coclosedCompact
  statement: sᶜ in coclosedCompact X ↔ IsCompact (closure s)
  proof: by
  rw [mem_coclosedCompact_iff]; rw [compl_compl]

中文:
定理 compl_mem_coclosedCompact
  结论: sᶜ in coclosedCompact X ↔ 是紧集 (closure s)
  证明: by
  rw [mem_coclosedCompact_iff]; rw [compl_compl]

Depends on / 依赖: compl_compl, mem_coclosedCompact_iff
-/
theorem compl_mem_coclosedCompact : sᶜ in coclosedCompact X ↔ IsCompact (closure s) := by
  rw [mem_coclosedCompact_iff]; rw [compl_compl]

/--
theorem `cocompact_le_coclosedCompact` / 定理 `cocompact_le_coclosedCompact`

English:
theorem cocompact_le_coclosedCompact
  statement: cocompact X <= coclosedCompact X
  proof: iInf_mono fun _ => le_iInf fun _ => le_rfl

中文:
定理 cocompact_le_coclosedCompact
  结论: cocompact X <= coclosedCompact X
  证明: iInf_mono fun _ => le_iInf fun _ => le_rfl

Depends on / 依赖: iInf_mono, le_iInf, le_rfl
-/
theorem cocompact_le_coclosedCompact : cocompact X <= coclosedCompact X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

end Filter

/--
theorem `IsCompact.compl_mem_coclosedCompact_of_isClosed` / 定理 `IsCompact.compl_mem_coclosedCompact_of_isClosed`

English:
theorem IsCompact.compl_mem_coclosedCompact_of_isClosed
  given: (hs : IsCompact s) (hs' : IsClosed s)
  proof: hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩

中文:
定理 是紧集.compl_mem_coclosedCompact_of_isClosed
  条件: (hs : 是紧集 s) (hs' : 是闭集 s)
  证明: hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩

Depends on / 依赖: hasBasis_coclosedCompact, hasBasis_coclosedCompact.mem_of_mem, mem_of_mem
-/
theorem IsCompact.compl_mem_coclosedCompact_of_isClosed (hs : IsCompact s) (hs' : IsClosed s) :
    sᶜ in Filter.coclosedCompact X :=
  hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩

namespace Bornology

variable (X) in
/-- Sets that are contained in a compact set form a bornology. Its `cobounded` filter is
`Filter.cocompact`. See also `Bornology.relativelyCompact` the bornology of sets with compact
closure. -/
@[instance_reducible]
/--
Definition of `inCompact` / `inCompact` 的定义

English:
definition inCompact
  signature: : Bornology X where
  body: Filter.cocompact X
  le_cofinite := Filter.cocompact_le_cofinite

中文:
定义 inCompact
  签名: : 有界结构 X where
  定义体: Filter.cocompact X
  le_cofinite := Filter.cocompact_le_cofinite

Depends on / 依赖: Filter, Filter.cocompact, cocompact
-/
def inCompact : Bornology X where
  cobounded := Filter.cocompact X
  le_cofinite := Filter.cocompact_le_cofinite

/--
theorem `inCompact.isBounded_iff` / 定理 `inCompact.isBounded_iff`

English:
theorem inCompact.isBounded_iff
  statement: @IsBounded _ (inCompact X) s ↔ exists t, IsCompact t ∧ s subseteq t
  proof: by
  change sᶜ in Filter.cocompact X ↔ _
  rw [Filter.mem_cocompact]
  simp

中文:
定理 inCompact.isBounded_iff
  结论: @IsBounded _ (inCompact X) s ↔ 存在 t, 是紧集 t ∧ s subseteq t
  证明: by
  change sᶜ in Filter.cocompact X ↔ _
  rw [Filter.mem_cocompact]
  simp

Depends on / 依赖: Filter, Filter.cocompact, Filter.mem_cocompact, cocompact, mem_cocompact
-/
theorem inCompact.isBounded_iff : @IsBounded _ (inCompact X) s ↔ exists t, IsCompact t ∧ s subseteq t := by
  change sᶜ in Filter.cocompact X ↔ _
  rw [Filter.mem_cocompact]
  simp

/--
lemma `isBounded_image_of_isLocallyBounded_of_isCompact` / 引理 `isBounded_image_of_isLocallyBounded_of_isCompact`

English:
lemma isBounded_image_of_isLocallyBounded_of_isCompact
  statement: {Y : Type*}
  proof: by
  choose U hU using hf
  obtain ⟨I, hI⟩ := hs.elim_nhds_subcover U (fun x _ => (hU x).1)
  have : f '' ⋃ x in I, U x = ⋃ x in I, f '' U x := by simp [Set.image_iUnion₂]
  exact ((isBounded_biUnion_finset I).2 fun i _ => (hU i).2).subset (this ▸ Set.image_mono hI.2)

中文:
引理 isBounded_image_of_isLocallyBounded_of_isCompact
  结论: {Y : 类型}
  证明: by
  choose U hU using hf
  obtain ⟨I, hI⟩ := hs.elim_nhds_subcover U (fun x _ => (hU x).1)
  have : f '' ⋃ x in I, U x = ⋃ x in I, f '' U x := by simp [Set.image_iUnion₂]
  exact ((isBounded_biUnion_finset I).2 fun i _ => (hU i).2).subset (this ▸ Set.image_mono hI.2)

Depends on / 依赖: Set.image_iUnion, Set.image_mono, elim_nhds_subcover, hs.elim_nhds_subcover, image_mono, isBounded_biUnion_finset, subset
-/
lemma isBounded_image_of_isLocallyBounded_of_isCompact {Y : Type*}
    [Bornology Y] {s : Set X} (hs : IsCompact s) {f : X -> Y}
    (hf : forall x, exists t in 𝓝 x, IsBounded (f '' t)) :
    IsBounded (f '' s) := by
  choose U hU using hf
  obtain ⟨I, hI⟩ := hs.elim_nhds_subcover U (fun x _ => (hU x).1)
  have : f '' ⋃ x in I, U x = ⋃ x in I, f '' U x := by simp [Set.image_iUnion₂]
  exact ((isBounded_biUnion_finset I).2 fun i _ => (hU i).2).subset (this ▸ Set.image_mono hI.2)

end Bornology

/--
theorem `IsCompact.nhdsSet_prod_eq` / 定理 `IsCompact.nhdsSet_prod_eq`

English:
theorem IsCompact.nhdsSet_prod_eq
  given: {t : Set Y} (hs : IsCompact s) (ht : IsCompact t)
  proof: by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]

中文:
定理 是紧集.nhdsSet_prod_eq
  条件: {t : 集合 Y} (hs : 是紧集 s) (ht : 是紧集 t)
  证明: by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]

Depends on / 依赖: biSup_prod, hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, nhdsSet_prod_eq_biSup, nhds_prod_eq, prod_nhdsSet_eq_biSup, sSup_image, simp_rw
-/
theorem IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t := by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]

/--
theorem `nhdsSet_prod_le_of_disjoint_cocompact` / 定理 `nhdsSet_prod_le_of_disjoint_cocompact`

English:
theorem nhdsSet_prod_le_of_disjoint_cocompact
  statement: {f : Filter Y} (hs : IsCompact s)
  proof: by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    𝓝ˢ s ×ˢ f
    _ <= 𝓝ˢ s ×ˢ 𝓟 K := Filter.prod_mono_right _ (Filter.le_principal_iff.mpr hKf)
    _ <= 𝓝ˢ s ×ˢ 𝓝ˢ K := Filter.prod_mono_right _ principal_le_nhdsSet
    _ = 𝓝ˢ (s ×ˢ K) := (hs.nhdsSet_prod_eq hK).symm
    _ <= 𝓝ˢ (s ×ˢ Set.univ) := nhdsSet_mono (prod_mono_right le_top)

中文:
定理 nhdsSet_prod_le_of_disjoint_cocompact
  结论: {f : 滤子 Y} (hs : 是紧集 s)
  证明: by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    𝓝ˢ s ×ˢ f
    _ <= 𝓝ˢ s ×ˢ 𝓟 K := Filter.prod_mono_right _ (Filter.le_principal_iff.mpr hKf)
    _ <= 𝓝ˢ s ×ˢ 𝓝ˢ K := Filter.prod_mono_right _ principal_le_nhdsSet
    _ = 𝓝ˢ (s ×ˢ K) := (hs.nhdsSet_prod_eq hK).symm
    _ <= 𝓝ˢ (s ×ˢ Set.univ) := nhdsSet_mono (prod_mono_right le_top)

Depends on / 依赖: Filter, Filter.le_principal_iff.mpr, Filter.prod_mono_right, Set.univ, disjoint_cocompact_right, hs.nhdsSet_prod_eq, le_principal_iff, le_top, nhdsSet_mono, nhdsSet_prod_eq, principal_le_nhdsSet, prod_mono_right
-/
theorem nhdsSet_prod_le_of_disjoint_cocompact {f : Filter Y} (hs : IsCompact s)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝ˢ s ×ˢ f <= 𝓝ˢ (s ×ˢ Set.univ) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    𝓝ˢ s ×ˢ f
    _ <= 𝓝ˢ s ×ˢ 𝓟 K := Filter.prod_mono_right _ (Filter.le_principal_iff.mpr hKf)
    _ <= 𝓝ˢ s ×ˢ 𝓝ˢ K := Filter.prod_mono_right _ principal_le_nhdsSet
    _ = 𝓝ˢ (s ×ˢ K) := (hs.nhdsSet_prod_eq hK).symm
    _ <= 𝓝ˢ (s ×ˢ Set.univ) := nhdsSet_mono (prod_mono_right le_top)

/--
theorem `prod_nhdsSet_le_of_disjoint_cocompact` / 定理 `prod_nhdsSet_le_of_disjoint_cocompact`

English:
theorem prod_nhdsSet_le_of_disjoint_cocompact
  statement: {t : Set Y} {f : Filter X} (ht : IsCompact t)
  proof: by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    f ×ˢ 𝓝ˢ t
    _ <= (𝓟 K) ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ (Filter.le_principal_iff.mpr hKf)
    _ <= 𝓝ˢ K ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ principal_le_nhdsSet
    _ = 𝓝ˢ (K ×ˢ t) := (hK.nhdsSet_prod_eq ht).symm
    _ <= 𝓝ˢ (Set.univ ×ˢ t) := nhdsSet_mono (prod_mono_left le_top)

中文:
定理 prod_nhdsSet_le_of_disjoint_cocompact
  结论: {t : 集合 Y} {f : 滤子 X} (ht : 是紧集 t)
  证明: by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    f ×ˢ 𝓝ˢ t
    _ <= (𝓟 K) ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ (Filter.le_principal_iff.mpr hKf)
    _ <= 𝓝ˢ K ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ principal_le_nhdsSet
    _ = 𝓝ˢ (K ×ˢ t) := (hK.nhdsSet_prod_eq ht).symm
    _ <= 𝓝ˢ (Set.univ ×ˢ t) := nhdsSet_mono (prod_mono_left le_top)

Depends on / 依赖: Filter, Filter.le_principal_iff.mpr, Filter.prod_mono_left, Set.univ, disjoint_cocompact_right, hK.nhdsSet_prod_eq, le_principal_iff, le_top, nhdsSet_mono, nhdsSet_prod_eq, principal_le_nhdsSet, prod_mono_left
-/
theorem prod_nhdsSet_le_of_disjoint_cocompact {t : Set Y} {f : Filter X} (ht : IsCompact t)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝ˢ t <= 𝓝ˢ (Set.univ ×ˢ t) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    f ×ˢ 𝓝ˢ t
    _ <= (𝓟 K) ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ (Filter.le_principal_iff.mpr hKf)
    _ <= 𝓝ˢ K ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ principal_le_nhdsSet
    _ = 𝓝ˢ (K ×ˢ t) := (hK.nhdsSet_prod_eq ht).symm
    _ <= 𝓝ˢ (Set.univ ×ˢ t) := nhdsSet_mono (prod_mono_left le_top)

/--
theorem `nhds_prod_le_of_disjoint_cocompact` / 定理 `nhds_prod_le_of_disjoint_cocompact`

English:
theorem nhds_prod_le_of_disjoint_cocompact
  statement: {f : Filter Y} (x : X)
  proof: by
  simpa using nhdsSet_prod_le_of_disjoint_cocompact isCompact_singleton hf

中文:
定理 nhds_prod_le_of_disjoint_cocompact
  结论: {f : 滤子 Y} (x : X)
  证明: by
  simpa using nhdsSet_prod_le_of_disjoint_cocompact isCompact_singleton hf

Depends on / 依赖: isCompact_singleton, nhdsSet_prod_le_of_disjoint_cocompact
-/
theorem nhds_prod_le_of_disjoint_cocompact {f : Filter Y} (x : X)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝 x ×ˢ f <= 𝓝ˢ ({x} ×ˢ Set.univ) := by
  simpa using nhdsSet_prod_le_of_disjoint_cocompact isCompact_singleton hf

/--
theorem `prod_nhds_le_of_disjoint_cocompact` / 定理 `prod_nhds_le_of_disjoint_cocompact`

English:
theorem prod_nhds_le_of_disjoint_cocompact
  statement: {f : Filter X} (y : Y)
  proof: by
  simpa using prod_nhdsSet_le_of_disjoint_cocompact isCompact_singleton hf

中文:
定理 prod_nhds_le_of_disjoint_cocompact
  结论: {f : 滤子 X} (y : Y)
  证明: by
  simpa using prod_nhdsSet_le_of_disjoint_cocompact isCompact_singleton hf

Depends on / 依赖: isCompact_singleton, prod_nhdsSet_le_of_disjoint_cocompact
-/
theorem prod_nhds_le_of_disjoint_cocompact {f : Filter X} (y : Y)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝 y <= 𝓝ˢ (Set.univ ×ˢ {y}) := by
  simpa using prod_nhdsSet_le_of_disjoint_cocompact isCompact_singleton hf

/--
theorem `generalized_tube_lemma` / 定理 `generalized_tube_lemma`

English:
theorem generalized_tube_lemma
  statement: (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
  proof: by
  rw [← hn.mem_nhdsSet]; rw [hs.nhdsSet_prod_eq ht]; rw [((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩

中文:
定理 generalized_tube_lemma
  结论: (hs : 是紧集 s) {t : 集合 Y} (ht : 是紧集 t)
  证明: by
  rw [← hn.mem_nhdsSet]; rw [hs.nhdsSet_prod_eq ht]; rw [((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩

Depends on / 依赖: hasBasis_nhdsSet, hn.mem_nhdsSet, hs.nhdsSet_prod_eq, mem_iff, mem_nhdsSet, nhdsSet_prod_eq
-/
theorem generalized_tube_lemma (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t subseteq n) :
    exists (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s subseteq u ∧ t subseteq v ∧ u ×ˢ v subseteq n := by
  rw [← hn.mem_nhdsSet]; rw [hs.nhdsSet_prod_eq ht]; rw [((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩

/--
lemma `IsCompact.nhdsSetWithin_prod_eq` / 引理 `IsCompact.nhdsSetWithin_prod_eq`

English:
lemma IsCompact.nhdsSetWithin_prod_eq
  statement: {s s' : Set X} {t t' : Set Y} (hs : IsCompact s)
  proof: by
  simp [nhdsSetWithin, ← prod_inf_prod, hs.nhdsSet_prod_eq ht]

中文:
引理 是紧集.nhdsSetWithin_prod_eq
  结论: {s s' : 集合 X} {t t' : 集合 Y} (hs : 是紧集 s)
  证明: by
  simp [nhdsSetWithin, ← prod_inf_prod, hs.nhdsSet_prod_eq ht]

Depends on / 依赖: hs.nhdsSet_prod_eq, nhdsSetWithin, nhdsSet_prod_eq, prod_inf_prod
-/
lemma IsCompact.nhdsSetWithin_prod_eq {s s' : Set X} {t t' : Set Y} (hs : IsCompact s)
    (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simp [nhdsSetWithin, ← prod_inf_prod, hs.nhdsSet_prod_eq ht]

open Topology Set in
/--
lemma `generalized_tube_lemma'` / 引理 `generalized_tube_lemma'`

English:
lemma generalized_tube_lemma'
  statement: {s s' : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
  proof: by
  rwa [hs.nhdsSetWithin_prod_eq ht, Filter.mem_prod_iff] at hn

中文:
引理 generalized_tube_lemma'
  结论: {s s' : 集合 X} (hs : 是紧集 s) {t t' : 集合 Y} (ht : 是紧集 t)
  证明: by
  rwa [hs.nhdsSetWithin_prod_eq ht, Filter.mem_prod_iff] at hn

Depends on / 依赖: Filter, Filter.mem_prod_iff, hs.nhdsSetWithin_prod_eq, mem_prod_iff, nhdsSetWithin_prod_eq
-/
lemma generalized_tube_lemma' {s s' : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n in 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t)) :
    exists u in 𝓝ˢ[s'] s, exists v in 𝓝ˢ[t'] t, u ×ˢ v subseteq n := by
  rwa [hs.nhdsSetWithin_prod_eq ht, Filter.mem_prod_iff] at hn

open Topology Set in
/--
lemma `generalized_tube_lemma_left` / 引理 `generalized_tube_lemma_left`

English:
lemma generalized_tube_lemma_left
  statement: {s s' : Set X} (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
  proof: by
  rw [hs.nhdsSetWithin_prod_eq ht]; rw [nhdsSetWithin_self]; rw [Filter.mem_prod_principal] at hn
  exact ⟨_, hn, fun x hx => hx.1 _ hx.2⟩

中文:
引理 generalized_tube_lemma_left
  结论: {s s' : 集合 X} (hs : 是紧集 s) {t : 集合 Y} (ht : 是紧集 t)
  证明: by
  rw [hs.nhdsSetWithin_prod_eq ht]; rw [nhdsSetWithin_self]; rw [Filter.mem_prod_principal] at hn
  exact ⟨_, hn, fun x hx => hx.1 _ hx.2⟩

Depends on / 依赖: Filter, Filter.mem_prod_principal, hs.nhdsSetWithin_prod_eq, mem_prod_principal, nhdsSetWithin_prod_eq, nhdsSetWithin_self
-/
lemma generalized_tube_lemma_left {s s' : Set X} (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n in 𝓝ˢ[s' ×ˢ t] (s ×ˢ t)) : exists u in 𝓝ˢ[s'] s, u ×ˢ t subseteq n := by
  rw [hs.nhdsSetWithin_prod_eq ht]; rw [nhdsSetWithin_self]; rw [Filter.mem_prod_principal] at hn
  exact ⟨_, hn, fun x hx => hx.1 _ hx.2⟩

open Topology Set in
/--
lemma `generalized_tube_lemma_right` / 引理 `generalized_tube_lemma_right`

English:
lemma generalized_tube_lemma_right
  statement: {s : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
  proof: by
  rw [hs.nhdsSetWithin_prod_eq ht]; rw [nhdsSetWithin_self]; rw [Filter.mem_prod_iff] at hn
  obtain ⟨s', hs', u, hu, h⟩ := hn
  exact ⟨u, hu, (prod_mono_left hs').trans h⟩

中文:
引理 generalized_tube_lemma_right
  结论: {s : 集合 X} (hs : 是紧集 s) {t t' : 集合 Y} (ht : 是紧集 t)
  证明: by
  rw [hs.nhdsSetWithin_prod_eq ht]; rw [nhdsSetWithin_self]; rw [Filter.mem_prod_iff] at hn
  obtain ⟨s', hs', u, hu, h⟩ := hn
  exact ⟨u, hu, (prod_mono_left hs').trans h⟩

Depends on / 依赖: Filter, Filter.mem_prod_iff, hs.nhdsSetWithin_prod_eq, mem_prod_iff, nhdsSetWithin_prod_eq, nhdsSetWithin_self, prod_mono_left
-/
lemma generalized_tube_lemma_right {s : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n in 𝓝ˢ[s ×ˢ t'] (s ×ˢ t)) : exists u in 𝓝ˢ[t'] t, s ×ˢ u subseteq n := by
  rw [hs.nhdsSetWithin_prod_eq ht]; rw [nhdsSetWithin_self]; rw [Filter.mem_prod_iff] at hn
  obtain ⟨s', hs', u, hu, h⟩ := hn
  exact ⟨u, hu, (prod_mono_left hs').trans h⟩

-- see Note [lower instance priority]
instance (priority := 10) Subsingleton.compactSpace [Subsingleton X] : CompactSpace X :=
  ⟨subsingleton_univ.isCompact⟩

/--
theorem `isCompact_univ_iff` / 定理 `isCompact_univ_iff`

English:
theorem isCompact_univ_iff
  statement: IsCompact (univ : Set X) ↔ CompactSpace X
  proof: ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[compactness ., grind .]

中文:
定理 isCompact_univ_iff
  结论: 是紧集 (univ : 集合 X) ↔ 紧空间 X
  证明: ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[compactness ., grind .]
-/
theorem isCompact_univ_iff : IsCompact (univ : Set X) ↔ CompactSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[compactness ., grind .]
/--
theorem `isCompact_univ` / 定理 `isCompact_univ`

English:
theorem isCompact_univ
  given: [h : CompactSpace X]
  statement: IsCompact (univ : Set X)
  proof: h.isCompact_univ

中文:
定理 isCompact_univ
  条件: [h : 紧空间 X]
  结论: 是紧集 (univ : 集合 X)
  证明: h.isCompact_univ

Depends on / 依赖: h.isCompact_univ, isCompact_univ
-/
theorem isCompact_univ [h : CompactSpace X] : IsCompact (univ : Set X) :=
  h.isCompact_univ

/--
theorem `exists_clusterPt_of_compactSpace` / 定理 `exists_clusterPt_of_compactSpace`

English:
theorem exists_clusterPt_of_compactSpace
  given: [CompactSpace X] (f : Filter X) [NeBot f]
  proof: by
  simpa using isCompact_univ (show f <= 𝓟 univ by simp)

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace X] (F : Ultrafilter X) : ↑F <= 𝓝 F.lim :=
  have ⟨x, _, h⟩ := isCompact_univ.ultrafilter_le_nhds F (by simp)
  le_nhds_lim ⟨x, h⟩

中文:
定理 存在_clusterPt_of_compactSpace
  条件: [紧空间 X] (f : 滤子 X) [NeBot f]
  证明: by
  simpa using isCompact_univ (show f <= 𝓟 univ by simp)

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace X] (F : Ultrafilter X) : ↑F <= 𝓝 F.lim :=
  have ⟨x, _, h⟩ := isCompact_univ.ultrafilter_le_nhds F (by simp)
  le_nhds_lim ⟨x, h⟩

Depends on / 依赖: isCompact_univ
-/
theorem exists_clusterPt_of_compactSpace [CompactSpace X] (f : Filter X) [NeBot f] :
    exists x, ClusterPt x f := by
  simpa using isCompact_univ (show f <= 𝓟 univ by simp)

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace X] (F : Ultrafilter X) : ↑F <= 𝓝 F.lim :=
  have ⟨x, _, h⟩ := isCompact_univ.ultrafilter_le_nhds F (by simp)
  le_nhds_lim ⟨x, h⟩

/--
theorem `CompactSpace.elim_nhds_subcover` / 定理 `CompactSpace.elim_nhds_subcover`

English:
theorem CompactSpace.elim_nhds_subcover
  given: [CompactSpace X] (U : X -> Set X) (hU : forall x, U x in 𝓝 x)
  proof: have ⟨t, _, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  ⟨t, top_unique s⟩

中文:
定理 紧空间.elim_nhds_subcover
  条件: [紧空间 X] (U : X -> 集合 X) (hU : 对任意 x, U x in 𝓝 x)
  证明: have ⟨t, _, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  ⟨t, top_unique s⟩

Depends on / 依赖: IsCompact, IsCompact.elim_nhds_subcover, elim_nhds_subcover, isCompact_univ, top_unique
-/
theorem CompactSpace.elim_nhds_subcover [CompactSpace X] (U : X -> Set X) (hU : forall x, U x in 𝓝 x) :
    exists t : Finset X, ⋃ x in t, U x = ⊤ :=
  have ⟨t, _, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  ⟨t, top_unique s⟩

/--
theorem `compactSpace_of_finite_subfamily_closed` / 定理 `compactSpace_of_finite_subfamily_closed`

English:
theorem compactSpace_of_finite_subfamily_closed
  proof: isCompact_of_finite_subfamily_closed fun t => by simpa using h t

中文:
定理 compactSpace_of_finite_subfamily_closed
  证明: isCompact_of_finite_subfamily_closed fun t => by simpa using h t

Depends on / 依赖: isCompact_of_finite_subfamily_closed
-/
theorem compactSpace_of_finite_subfamily_closed
    (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> ⋂ i, t i = ∅ ->
      exists u : Finset ι, ⋂ i in u, t i = ∅) :
    CompactSpace X where
  isCompact_univ := isCompact_of_finite_subfamily_closed fun t => by simpa using h t

/--
lemma `CompactSpace.iInter_nonempty` / 引理 `CompactSpace.iInter_nonempty`

English:
lemma CompactSpace.iInter_nonempty
  statement: {ι : Type v} [CompactSpace X] {t : ι -> Set X}
  proof: by
  simpa using isCompact_univ.inter_iInter_nonempty t htc (by simpa using hst)

omit [TopologicalSpace X] in

中文:
引理 紧空间.i整数er_nonempty
  结论: {ι : 类型v} [紧空间 X] {t : ι -> 集合 X}
  证明: by
  simpa using isCompact_univ.inter_iInter_nonempty t htc (by simpa using hst)

omit [TopologicalSpace X] in

Depends on / 依赖: inter_iInter_nonempty, isCompact_univ, isCompact_univ.inter_iInter_nonempty
-/
lemma CompactSpace.iInter_nonempty {ι : Type v} [CompactSpace X] {t : ι -> Set X}
    (htc : forall i, IsClosed (t i))
    (hst : forall s : Finset ι, (⋂ i in s, t i).Nonempty) :
    (⋂ i, t i).Nonempty := by
  simpa using isCompact_univ.inter_iInter_nonempty t htc (by simpa using hst)

omit [TopologicalSpace X] in
/--
theorem `compactSpace_generateFrom` / 定理 `compactSpace_generateFrom`

English:
theorem compactSpace_generateFrom
  statement: [T : TopologicalSpace X] {S : Set (Set X)}
  proof: isCompact_univ_iff.mp isCompact_generateFrom hTS by simpa

omit [TopologicalSpace X] in

中文:
定理 compactSpace_generateFrom
  结论: [T : 拓扑空间 X] {S : 集合 (集合 X)}
  证明: isCompact_univ_iff.mp isCompact_generateFrom hTS by simpa

omit [TopologicalSpace X] in

Depends on / 依赖: isCompact_generateFrom, isCompact_univ_iff, isCompact_univ_iff.mp
-/
theorem compactSpace_generateFrom [T : TopologicalSpace X] {S : Set (Set X)}
    (hTS : T = generateFrom S) (h : forall P subseteq S, ⋃₀ P = univ -> exists Q subseteq P, Q.Finite ∧ ⋃₀ Q = univ) :
    CompactSpace X :=
isCompact_univ_iff.mp isCompact_generateFrom hTS by simpa

omit [TopologicalSpace X] in
/--
theorem `compactSpace_generateFrom'` / 定理 `compactSpace_generateFrom'`

English:
theorem compactSpace_generateFrom'
  statement: [T : TopologicalSpace X] {S : Set (Set X)}
  proof: isCompact_univ_iff.mp isCompact_generateFrom' hTS by simpa

omit [TopologicalSpace X] in

中文:
定理 compactSpace_generateFrom'
  结论: [T : 拓扑空间 X] {S : 集合 (集合 X)}
  证明: isCompact_univ_iff.mp isCompact_generateFrom' hTS by simpa

omit [TopologicalSpace X] in

Depends on / 依赖: Finite, J.Finite
-/
theorem compactSpace_generateFrom' [T : TopologicalSpace X] {S : Set (Set X)}
    (hTS : T = generateFrom S)
    (h : forall (ι : Type u) (U : ι -> S),
      ⋃ i, U i = (univ (α := X)) -> exists J : Set ι, J.Finite ∧ ⋃ i in J, U i = (univ (α := X))) :
    CompactSpace X :=
isCompact_univ_iff.mp isCompact_generateFrom' hTS by simpa

omit [TopologicalSpace X] in
/--
lemma `compactSpace_generateFrom_of_compl_mem` / 引理 `compactSpace_generateFrom_of_compl_mem`

English:
lemma compactSpace_generateFrom_of_compl_mem
  statement: [T : TopologicalSpace X]
  proof: by
  refine compactSpace_generateFrom hT fun P hP𝔅 hP => ?_
  contrapose! hP
  simp_rw [← Set.nonempty_compl, Set.compl_sUnion] at hP ⊢
  refine h _ ?_ fun Q hQP hQ => ?_
  · rintro _ ⟨S, hS, rfl⟩
    exact h𝔅 _ (hP𝔅 hS)
  · replace hP : Q subseteq compl '' P -> (compl '' Q).Finite -> (⋂₀ Q).Nonempty := by
      simpa [← compl_involutive.image_eq_preimage_symm] using hP (compl '' Q)
    exact hP hQP (hQ.image _)

中文:
引理 compactSpace_generateFrom_of_compl_mem
  结论: [T : 拓扑空间 X]
  证明: by
  refine compactSpace_generateFrom hT fun P hP𝔅 hP => ?_
  contrapose! hP
  simp_rw [← Set.nonempty_compl, Set.compl_sUnion] at hP ⊢
  refine h _ ?_ fun Q hQP hQ => ?_
  · rintro _ ⟨S, hS, rfl⟩
    exact h𝔅 _ (hP𝔅 hS)
  · replace hP : Q subseteq compl '' P -> (compl '' Q).Finite -> (⋂₀ Q).Nonempty := by
      simpa [← compl_involutive.image_eq_preimage_symm] using hP (compl '' Q)
    exact hP hQP (hQ.image _)

Depends on / 依赖: Finite, Nonempty, Set.compl_sUnion, Set.nonempty_compl, compactSpace_generateFrom, compl_involutive, compl_involutive.image_eq_preimage_symm, compl_sUnion, contrapose, hQ.image, image_eq_preimage_symm, nonempty_compl, replace, simp_rw, subseteq
-/
lemma compactSpace_generateFrom_of_compl_mem [T : TopologicalSpace X]
    (𝔅 : Set (Set X)) (hT : T = TopologicalSpace.generateFrom 𝔅) (h𝔅 : forall s in 𝔅, sᶜ in 𝔅)
    (h : forall P subseteq 𝔅, (forall Q subseteq P, Q.Finite -> (⋂₀ Q).Nonempty) -> (⋂₀ P).Nonempty) :
    CompactSpace X := by
  refine compactSpace_generateFrom hT fun P hP𝔅 hP => ?_
  contrapose! hP
  simp_rw [← Set.nonempty_compl, Set.compl_sUnion] at hP ⊢
  refine h _ ?_ fun Q hQP hQ => ?_
  · rintro _ ⟨S, hS, rfl⟩
    exact h𝔅 _ (hP𝔅 hS)
  · replace hP : Q subseteq compl '' P -> (compl '' Q).Finite -> (⋂₀ Q).Nonempty := by
      simpa [← compl_involutive.image_eq_preimage_symm] using hP (compl '' Q)
    exact hP hQP (hQ.image _)

/--
theorem `IsClosed.isCompact` / 定理 `IsClosed.isCompact`

English:
theorem IsClosed.isCompact
  given: [CompactSpace X] (h : IsClosed s)
  statement: IsCompact s
  proof: isCompact_univ.of_isClosed_subset h (subset_univ _)

中文:
定理 是闭集.isCompact
  条件: [紧空间 X] (h : 是闭集 s)
  结论: 是紧集 s
  证明: isCompact_univ.of_isClosed_subset h (subset_univ _)

Depends on / 依赖: isCompact_univ, isCompact_univ.of_isClosed_subset, of_isClosed_subset, subset_univ
-/
theorem IsClosed.isCompact [CompactSpace X] (h : IsClosed s) : IsCompact s :=
  isCompact_univ.of_isClosed_subset h (subset_univ _)

/--
lemma `le_nhds_of_unique_clusterPt` / 引理 `le_nhds_of_unique_clusterPt`

English:
lemma le_nhds_of_unique_clusterPt
  statement: [CompactSpace X] {l : Filter X} {y : X}
  proof: isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ => h x

中文:
引理 le_nhds_of_unique_clusterPt
  结论: [紧空间 X] {l : 滤子 X} {y : X}
  证明: isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ => h x

Depends on / 依赖: isCompact_univ, isCompact_univ.le_nhds_of_unique_clusterPt, le_nhds_of_unique_clusterPt, univ_mem
-/
lemma le_nhds_of_unique_clusterPt [CompactSpace X] {l : Filter X} {y : X}
    (h : forall x, ClusterPt x l -> x = y) : l <= 𝓝 y :=
  isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ => h x

/--
lemma `tendsto_nhds_of_unique_mapClusterPt` / 引理 `tendsto_nhds_of_unique_mapClusterPt`

English:
lemma tendsto_nhds_of_unique_mapClusterPt
  statement: [CompactSpace X] {Y} {l : Filter Y} {y : X} {f : Y -> X}
  proof: le_nhds_of_unique_clusterPt h

中文:
引理 tendsto_nhds_of_unique_mapClusterPt
  结论: [紧空间 X] {Y} {l : 滤子 Y} {y : X} {f : Y -> X}
  证明: le_nhds_of_unique_clusterPt h

Depends on / 依赖: le_nhds_of_unique_clusterPt
-/
lemma tendsto_nhds_of_unique_mapClusterPt [CompactSpace X] {Y} {l : Filter Y} {y : X} {f : Y -> X}
    (h : forall x, MapClusterPt x l f -> x = y) :
    Tendsto f l (𝓝 y) :=
  le_nhds_of_unique_clusterPt h

/--
lemma `noncompact_univ` / 引理 `noncompact_univ`

English:
lemma noncompact_univ
  given: (X : Type*) [TopologicalSpace X] [NoncompactSpace X]
  proof: NoncompactSpace.noncompact_univ

中文:
引理 noncompact_univ
  条件: (X : 类型) [拓扑空间 X] [Noncompact空间 X]
  证明: NoncompactSpace.noncompact_univ

Depends on / 依赖: NoncompactSpace, NoncompactSpace.noncompact_univ, noncompact_univ
-/
lemma noncompact_univ (X : Type*) [TopologicalSpace X] [NoncompactSpace X] :
    ¬IsCompact (univ : Set X) :=
  NoncompactSpace.noncompact_univ

/--
theorem `IsCompact.ne_univ` / 定理 `IsCompact.ne_univ`

English:
theorem IsCompact.ne_univ
  given: [NoncompactSpace X] (hs : IsCompact s)
  statement: s != univ
  proof: fun h =>
  noncompact_univ X (h ▸ hs)

中文:
定理 是紧集.ne_univ
  条件: [Noncompact空间 X] (hs : 是紧集 s)
  结论: s != univ
  证明: fun h =>
  noncompact_univ X (h ▸ hs)
-/
theorem IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact s) : s != univ := fun h =>
  noncompact_univ X (h ▸ hs)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoncompactSpace
  signature: X] : NeBot (Filter.cocompact X)
  body: by
  refine Filter.hasBasis_cocompact.neBot_iff.2 fun hs => ?_
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ X

@[simp]

中文:
实例 [Noncompact空间
  签名: X] : NeBot (滤子.cocompact X)
  定义体: by
  refine Filter.hasBasis_cocompact.neBot_iff.2 fun hs => ?_
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ X

@[simp]

Depends on / 依赖: Filter, Filter.hasBasis_cocompact.neBot_iff, compl_empty_iff, contrapose, hasBasis_cocompact, neBot_iff, noncompact_univ, not_nonempty_iff_eq_empty
-/
instance [NoncompactSpace X] : NeBot (Filter.cocompact X) := by
  refine Filter.hasBasis_cocompact.neBot_iff.2 fun hs => ?_
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ X

@[simp]
/--
theorem `Filter.cocompact_eq_bot` / 定理 `Filter.cocompact_eq_bot`

English:
theorem Filter.cocompact_eq_bot
  given: [CompactSpace X]
  statement: Filter.cocompact X = ⊥
  proof: Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩

中文:
定理 滤子.cocompact_eq_bot
  条件: [紧空间 X]
  结论: 滤子.cocompact X = ⊥
  证明: Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩

Depends on / 依赖: Filter, Filter.hasBasis_cocompact.eq_bot_iff.mpr, Set.compl_univ, Set.univ, compl_univ, eq_bot_iff, hasBasis_cocompact, isCompact_univ
-/
theorem Filter.cocompact_eq_bot [CompactSpace X] : Filter.cocompact X = ⊥ :=
  Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoncompactSpace
  signature: X] : NeBot (Filter.coclosedCompact X)
  body: neBot_of_le Filter.cocompact_le_coclosedCompact

中文:
实例 [Noncompact空间
  签名: X] : NeBot (滤子.coclosedCompact X)
  定义体: neBot_of_le Filter.cocompact_le_coclosedCompact

Depends on / 依赖: Filter, Filter.cocompact_le_coclosedCompact, cocompact_le_coclosedCompact, neBot_of_le
-/
instance [NoncompactSpace X] : NeBot (Filter.coclosedCompact X) :=
  neBot_of_le Filter.cocompact_le_coclosedCompact

/--
theorem `noncompactSpace_of_neBot` / 定理 `noncompactSpace_of_neBot`

English:
theorem noncompactSpace_of_neBot
  given: (_ : NeBot (Filter.cocompact X))
  statement: NoncompactSpace X
  proof: ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

中文:
定理 noncompactSpace_of_neBot
  条件: (_ : NeBot (滤子.cocompact X))
  结论: Noncompact空间 X
  证明: ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

Depends on / 依赖: Filter, Filter.nonempty_of_mem, compl_mem_cocompact, compl_univ, ne_empty, nonempty_of_mem
-/
theorem noncompactSpace_of_neBot (_ : NeBot (Filter.cocompact X)) : NoncompactSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

/--
theorem `Filter.cocompact_neBot_iff` / 定理 `Filter.cocompact_neBot_iff`

English:
theorem Filter.cocompact_neBot_iff
  statement: NeBot (Filter.cocompact X) ↔ NoncompactSpace X
  proof: ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩

中文:
定理 滤子.cocompact_neBot_iff
  结论: NeBot (滤子.cocompact X) ↔ Noncompact空间 X
  证明: ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩

Depends on / 依赖: noncompactSpace_of_neBot
-/
theorem Filter.cocompact_neBot_iff : NeBot (Filter.cocompact X) ↔ NoncompactSpace X :=
  ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩

/--
theorem `not_compactSpace_iff` / 定理 `not_compactSpace_iff`

English:
theorem not_compactSpace_iff
  statement: ¬CompactSpace X ↔ NoncompactSpace X
  proof: ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

中文:
定理 not_compactSpace_iff
  结论: ¬紧空间 X ↔ Noncompact空间 X
  证明: ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩
-/
theorem not_compactSpace_iff : ¬CompactSpace X ↔ NoncompactSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoncompactSpace Int
  body: noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

中文:
实例 :
  签名: Noncompact空间 整数
  定义体: noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

Depends on / 依赖: Filter, Filter.cocompact_eq_cofinite, Filter.cofinite_neBot, cocompact_eq_cofinite, cofinite_neBot, noncompactSpace_of_neBot
-/
instance : NoncompactSpace Int :=
noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

-- Note: We can't make this into an instance because it loops with `Finite.compactSpace`.
/--
theorem `finite_of_compact_of_discrete` / 定理 `finite_of_compact_of_discrete`

English:
theorem finite_of_compact_of_discrete
  given: [CompactSpace X] [DiscreteTopology X]
  statement: Finite X
  proof: Finite.of_finite_univ isCompact_univ.finite_of_discrete

中文:
定理 finite_of_compact_of_discrete
  条件: [紧空间 X] [离散拓扑 X]
  结论: 有限 X
  证明: Finite.of_finite_univ isCompact_univ.finite_of_discrete

Depends on / 依赖: Finite, Finite.of_finite_univ, finite_of_discrete, isCompact_univ, isCompact_univ.finite_of_discrete, of_finite_univ
-/
theorem finite_of_compact_of_discrete [CompactSpace X] [DiscreteTopology X] : Finite X :=
Finite.of_finite_univ isCompact_univ.finite_of_discrete

/--
lemma `Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact` / 引理 `Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact`

English:
lemma Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact
  proof: (@hK _ hs.cofinite_inf_principal_neBot (inf_le_right.trans <| principal_mono.2 hsub)).imp
    fun x hx => by rwa [accPt_iff_clusterPt, inf_comm, inf_right_comm,
      (finite_singleton _).cofinite_inf_principal_compl]

中文:
引理 集合.无限.存在_accPt_cofinite_inf_principal_of_subset_isCompact
  证明: (@hK _ hs.cofinite_inf_principal_neBot (inf_le_right.trans <| principal_mono.2 hsub)).imp
    fun x hx => by rwa [accPt_iff_clusterPt, inf_comm, inf_right_comm,
      (finite_singleton _).cofinite_inf_principal_compl]

Depends on / 依赖: accPt_iff_clusterPt, cofinite_inf_principal_compl, cofinite_inf_principal_neBot, finite_singleton, hs.cofinite_inf_principal_neBot, inf_comm, inf_le_right, inf_le_right.trans, inf_right_comm, principal_mono
-/
lemma Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact
    {K : Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s subseteq K) :
    exists x in K, AccPt x (cofinite ⊓ 𝓟 s) :=
  (@hK _ hs.cofinite_inf_principal_neBot (inf_le_right.trans <| principal_mono.2 hsub)).imp
    fun x hx => by rwa [accPt_iff_clusterPt, inf_comm, inf_right_comm,
      (finite_singleton _).cofinite_inf_principal_compl]

/--
lemma `Set.Infinite.exists_accPt_of_subset_isCompact` / 引理 `Set.Infinite.exists_accPt_of_subset_isCompact`

English:
lemma Set.Infinite.exists_accPt_of_subset_isCompact
  statement: {K : Set X} (hs : s.Infinite)
  proof: let ⟨x, hxK, hx⟩ := hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact hK hsub
  ⟨x, hxK, hx.mono inf_le_right⟩

中文:
引理 集合.无限.存在_accPt_of_subset_isCompact
  结论: {K : 集合 X} (hs : s.无限)
  证明: let ⟨x, hxK, hx⟩ := hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact hK hsub
  ⟨x, hxK, hx.mono inf_le_right⟩

Depends on / 依赖: exists_accPt_cofinite_inf_principal_of_subset_isCompact, hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact, hx.mono, inf_le_right
-/
lemma Set.Infinite.exists_accPt_of_subset_isCompact {K : Set X} (hs : s.Infinite)
    (hK : IsCompact K) (hsub : s subseteq K) : exists x in K, AccPt x (𝓟 s) :=
  let ⟨x, hxK, hx⟩ := hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact hK hsub
  ⟨x, hxK, hx.mono inf_le_right⟩

/--
lemma `Set.Infinite.exists_accPt_cofinite_inf_principal` / 引理 `Set.Infinite.exists_accPt_cofinite_inf_principal`

English:
lemma Set.Infinite.exists_accPt_cofinite_inf_principal
  given: [CompactSpace X] (hs : s.Infinite)
  proof: by
  simpa only [mem_univ, true_and]
    using hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact isCompact_univ s.subset_univ

中文:
引理 集合.无限.存在_accPt_cofinite_inf_principal
  条件: [紧空间 X] (hs : s.无限)
  证明: by
  simpa only [mem_univ, true_and]
    using hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact isCompact_univ s.subset_univ

Depends on / 依赖: exists_accPt_cofinite_inf_principal_of_subset_isCompact, hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact, isCompact_univ, mem_univ, s.subset_univ, subset_univ, true_and
-/
lemma Set.Infinite.exists_accPt_cofinite_inf_principal [CompactSpace X] (hs : s.Infinite) :
    exists x, AccPt x (cofinite ⊓ 𝓟 s) := by
  simpa only [mem_univ, true_and]
    using hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact isCompact_univ s.subset_univ

/--
lemma `Set.Infinite.exists_accPt_principal` / 引理 `Set.Infinite.exists_accPt_principal`

English:
lemma Set.Infinite.exists_accPt_principal
  given: [CompactSpace X] (hs : s.Infinite)
  statement: exists x, AccPt x (𝓟 s)
  proof: hs.exists_accPt_cofinite_inf_principal.imp fun _x hx => hx.mono inf_le_right

中文:
引理 集合.无限.存在_accPt_principal
  条件: [紧空间 X] (hs : s.无限)
  结论: 存在 x, 聚点 x (𝓟 s)
  证明: hs.exists_accPt_cofinite_inf_principal.imp fun _x hx => hx.mono inf_le_right

Depends on / 依赖: exists_accPt_cofinite_inf_principal, hs.exists_accPt_cofinite_inf_principal.imp, hx.mono, inf_le_right
-/
lemma Set.Infinite.exists_accPt_principal [CompactSpace X] (hs : s.Infinite) : exists x, AccPt x (𝓟 s) :=
  hs.exists_accPt_cofinite_inf_principal.imp fun _x hx => hx.mono inf_le_right

/--
theorem `exists_nhds_ne_neBot` / 定理 `exists_nhds_ne_neBot`

English:
theorem exists_nhds_ne_neBot
  given: (X : Type*) [TopologicalSpace X] [CompactSpace X] [Infinite X]
  proof: by
  simpa [AccPt] using (@infinite_univ X _).exists_accPt_principal

中文:
定理 存在_nhds_ne_neBot
  条件: (X : 类型) [拓扑空间 X] [紧空间 X] [无限 X]
  证明: by
  simpa [AccPt] using (@infinite_univ X _).exists_accPt_principal

Depends on / 依赖: exists_accPt_principal, infinite_univ
-/
theorem exists_nhds_ne_neBot (X : Type*) [TopologicalSpace X] [CompactSpace X] [Infinite X] :
    exists z : X, (𝓝[!=] z).NeBot := by
  simpa [AccPt] using (@infinite_univ X _).exists_accPt_principal

/--
theorem `finite_cover_nhds_interior` / 定理 `finite_cover_nhds_interior`

English:
theorem finite_cover_nhds_interior
  given: [CompactSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x)
  proof: let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩

中文:
定理 finite_cover_nhds_interior
  条件: [紧空间 X] {U : X -> 集合 X} (hU : 对任意 x, U x in 𝓝 x)
  证明: let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩

Depends on / 依赖: elim_finite_subcover, interior, isCompact_univ, isCompact_univ.elim_finite_subcover, isOpen_interior, mem_iUnion, mem_interior_iff_mem_nhds, univ_subset_iff
-/
theorem finite_cover_nhds_interior [CompactSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x) :
    exists t : Finset X, ⋃ x in t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩

/--
theorem `finite_cover_nhds` / 定理 `finite_cover_nhds`

English:
theorem finite_cover_nhds
  given: [CompactSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x)
  proof: let ⟨t, ht⟩ := finite_cover_nhds_interior hU
⟨t, univ_subset_iff.1 ht.symm.subset.trans iUnion₂_mono fun _ _ => interior_subset⟩

中文:
定理 finite_cover_nhds
  条件: [紧空间 X] {U : X -> 集合 X} (hU : 对任意 x, U x in 𝓝 x)
  证明: let ⟨t, ht⟩ := finite_cover_nhds_interior hU
⟨t, univ_subset_iff.1 ht.symm.subset.trans iUnion₂_mono fun _ _ => interior_subset⟩

Depends on / 依赖: finite_cover_nhds_interior, ht.symm.subset.trans, interior_subset, subset, univ_subset_iff
-/
theorem finite_cover_nhds [CompactSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x) :
    exists t : Finset X, ⋃ x in t, U x = univ :=
  let ⟨t, ht⟩ := finite_cover_nhds_interior hU
⟨t, univ_subset_iff.1 ht.symm.subset.trans iUnion₂_mono fun _ _ => interior_subset⟩

/--
theorem `Filter.comap_cocompact_le` / 定理 `Filter.comap_cocompact_le`

English:
theorem Filter.comap_cocompact_le
  given: {f : X -> Y} (hf : Continuous f)
  proof: by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

中文:
定理 滤子.comap_cocompact_le
  条件: {f : X -> Y} (hf : 连续 f)
  证明: by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

Depends on / 依赖: Filter, Filter.hasBasis_cocompact, Filter.hasBasis_cocompact.comap, hasBasis_cocompact, ht.image, le_basis_iff, subset_preimage_image, t.subset_preimage_image
-/
theorem Filter.comap_cocompact_le {f : X -> Y} (hf : Continuous f) :
    (Filter.cocompact Y).comap f <= Filter.cocompact X := by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

/--
theorem `disjoint_map_cocompact` / 定理 `disjoint_map_cocompact`

English:
theorem disjoint_map_cocompact
  statement: {g : X -> Y} {f : Filter X} (hg : Continuous g)
  proof: by
  rw [← Filter.disjoint_comap_iff_map]; rw [disjoint_iff_inf_le]
  calc
    f ⊓ (comap g (cocompact Y))
    _ <= f ⊓ Filter.cocompact X := inf_le_inf_left f (Filter.comap_cocompact_le hg)
    _ = ⊥ := disjoint_iff.mp hf

@[compactness .]

中文:
定理 disjoint_map_cocompact
  结论: {g : X -> Y} {f : 滤子 X} (hg : 连续 g)
  证明: by
  rw [← Filter.disjoint_comap_iff_map]; rw [disjoint_iff_inf_le]
  calc
    f ⊓ (comap g (cocompact Y))
    _ <= f ⊓ Filter.cocompact X := inf_le_inf_left f (Filter.comap_cocompact_le hg)
    _ = ⊥ := disjoint_iff.mp hf

@[compactness .]

Depends on / 依赖: Filter, Filter.cocompact, Filter.comap_cocompact_le, Filter.disjoint_comap_iff_map, cocompact, comap_cocompact_le, disjoint_comap_iff_map, disjoint_iff, disjoint_iff.mp, disjoint_iff_inf_le, inf_le_inf_left
-/
theorem disjoint_map_cocompact {g : X -> Y} {f : Filter X} (hg : Continuous g)
    (hf : Disjoint f (Filter.cocompact X)) : Disjoint (map g f) (Filter.cocompact Y) := by
  rw [← Filter.disjoint_comap_iff_map]; rw [disjoint_iff_inf_le]
  calc
    f ⊓ (comap g (cocompact Y))
    _ <= f ⊓ Filter.cocompact X := inf_le_inf_left f (Filter.comap_cocompact_le hg)
    _ = ⊥ := disjoint_iff.mp hf

@[compactness .]
/--
theorem `isCompact_range` / 定理 `isCompact_range`

English:
theorem isCompact_range
  given: [CompactSpace X] {f : X -> Y} (hf : Continuous f)
  statement: IsCompact (range f)
  proof: by
  rw [← image_univ]; exact isCompact_univ.image hf

中文:
定理 isCompact_range
  条件: [紧空间 X] {f : X -> Y} (hf : 连续 f)
  结论: 是紧集 (range f)
  证明: by
  rw [← image_univ]; exact isCompact_univ.image hf

Depends on / 依赖: image_univ, isCompact_univ, isCompact_univ.image
-/
theorem isCompact_range [CompactSpace X] {f : X -> Y} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ]; exact isCompact_univ.image hf

/--
lemma `Function.Surjective.compactSpace` / 引理 `Function.Surjective.compactSpace`

English:
lemma Function.Surjective.compactSpace
  statement: {f : X -> Y} (hf : Continuous f) [CompactSpace X]
  proof: by
    rw [← hf'.range_eq]
    exact isCompact_range hf

@[compactness .]

中文:
引理 函数.满射.compactSpace
  结论: {f : X -> Y} (hf : 连续 f) [紧空间 X]
  证明: by
    rw [← hf'.range_eq]
    exact isCompact_range hf

@[compactness .]

Depends on / 依赖: isCompact_range, range_eq
-/
lemma Function.Surjective.compactSpace {f : X -> Y} (hf : Continuous f) [CompactSpace X]
    (hf' : f.Surjective) : CompactSpace Y where
  isCompact_univ := by
    rw [← hf'.range_eq]
    exact isCompact_range hf

@[compactness .]
/--
theorem `isCompact_diagonal` / 定理 `isCompact_diagonal`

English:
theorem isCompact_diagonal
  given: [CompactSpace X]
  statement: IsCompact (diagonal X)
  proof: @range_diag X ▸ isCompact_range (continuous_id.prodMk continuous_id)

中文:
定理 isCompact_diagonal
  条件: [紧空间 X]
  结论: 是紧集 (diagonal X)
  证明: @range_diag X ▸ isCompact_range (continuous_id.prodMk continuous_id)

Depends on / 依赖: continuous_id, continuous_id.prodMk, isCompact_range, prodMk, range_diag
-/
theorem isCompact_diagonal [CompactSpace X] : IsCompact (diagonal X) :=
  @range_diag X ▸ isCompact_range (continuous_id.prodMk continuous_id)

/--
theorem `exists_subset_nhds_of_compactSpace` / 定理 `exists_subset_nhds_of_compactSpace`

English:
theorem exists_subset_nhds_of_compactSpace
  statement: [CompactSpace X] [Nonempty ι]
  proof: exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU

中文:
定理 存在_subset_nhds_of_compactSpace
  结论: [紧空间 X] [非空 ι]
  证明: exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU

Depends on / 依赖: exists_subset_nhds_of_isCompact, hV_closed, isCompact
-/
theorem exists_subset_nhds_of_compactSpace [CompactSpace X] [Nonempty ι]
    {V : ι -> Set X} (hV : Directed (· ⊇ ·) V) (hV_closed : forall i, IsClosed (V i)) {U : Set X}
    (hU : forall x in ⋂ i, V i, U in 𝓝 x) : exists i, V i subseteq U :=
  exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU

/--
theorem `Topology.IsInducing.isCompact_iff` / 定理 `Topology.IsInducing.isCompact_iff`

English:
theorem Topology.IsInducing.isCompact_iff
  given: {f : X -> Y} (hf : IsInducing f)
  proof: by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

中文:
定理 拓扑.是Inducing.isCompact_iff
  条件: {f : X -> Y} (hf : 是Inducing f)
  证明: by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

Depends on / 依赖: ClusterPt, F_le, F_ne_bot, continuous, hf.continuous, hf.mapClusterPt_iff, hs.image, mapClusterPt_iff, map_mono, map_principal, trans_eq, x_in
-/
theorem Topology.IsInducing.isCompact_iff {f : X -> Y} (hf : IsInducing f) :
    IsCompact s ↔ IsCompact (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/--
theorem `Topology.IsEmbedding.isCompact_iff` / 定理 `Topology.IsEmbedding.isCompact_iff`

English:
theorem Topology.IsEmbedding.isCompact_iff
  given: {f : X -> Y} (hf : IsEmbedding f)
  proof: hf.isInducing.isCompact_iff

中文:
定理 拓扑.是嵌入.isCompact_iff
  条件: {f : X -> Y} (hf : 是嵌入 f)
  证明: hf.isInducing.isCompact_iff

Depends on / 依赖: hf.isInducing.isCompact_iff, isCompact_iff, isInducing
-/
theorem Topology.IsEmbedding.isCompact_iff {f : X -> Y} (hf : IsEmbedding f) :
    IsCompact s ↔ IsCompact (f '' s) := hf.isInducing.isCompact_iff

/--
theorem `Topology.IsInducing.isCompact_preimage` / 定理 `Topology.IsInducing.isCompact_preimage`

English:
theorem Topology.IsInducing.isCompact_preimage
  statement: (hf : IsInducing f) (hf' : IsClosed (range f))
  proof: by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]

中文:
定理 拓扑.是Inducing.isCompact_preimage
  结论: (hf : 是Inducing f) (hf' : 是闭集 (range f))
  证明: by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]

Depends on / 依赖: hK.inter_right, hf.isCompact_iff, image_preimage_eq_inter_range, inter_right, isCompact_iff, replace
-/
theorem Topology.IsInducing.isCompact_preimage (hf : IsInducing f) (hf' : IsClosed (range f))
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]

/--
lemma `Topology.IsInducing.isCompact_preimage_iff` / 引理 `Topology.IsInducing.isCompact_preimage_iff`

English:
lemma Topology.IsInducing.isCompact_preimage_iff
  statement: {f : X -> Y} (hf : IsInducing f) {K : Set Y}
  proof: by
  rw [hf.isCompact_iff]; rw [image_preimage_eq_of_subset Kf]

中文:
引理 拓扑.是Inducing.isCompact_preimage_iff
  结论: {f : X -> Y} (hf : 是Inducing f) {K : 集合 Y}
  证明: by
  rw [hf.isCompact_iff]; rw [image_preimage_eq_of_subset Kf]

Depends on / 依赖: hf.isCompact_iff, image_preimage_eq_of_subset, isCompact_iff
-/
lemma Topology.IsInducing.isCompact_preimage_iff {f : X -> Y} (hf : IsInducing f) {K : Set Y}
    (Kf : K subseteq range f) : IsCompact (f ⁻¹' K) ↔ IsCompact K := by
  rw [hf.isCompact_iff]; rw [image_preimage_eq_of_subset Kf]

/--
lemma `Topology.IsInducing.isCompact_preimage'` / 引理 `Topology.IsInducing.isCompact_preimage'`

English:
lemma Topology.IsInducing.isCompact_preimage'
  statement: (hf : IsInducing f) {K : Set Y}
  proof: (hf.isCompact_preimage_iff Kf).2 hK

中文:
引理 拓扑.是Inducing.isCompact_preimage'
  结论: (hf : 是Inducing f) {K : 集合 Y}
  证明: (hf.isCompact_preimage_iff Kf).2 hK

Depends on / 依赖: hf.isCompact_preimage_iff, isCompact_preimage_iff
-/
lemma Topology.IsInducing.isCompact_preimage' (hf : IsInducing f) {K : Set Y}
    (hK : IsCompact K) (Kf : K subseteq range f) : IsCompact (f ⁻¹' K) :=
  (hf.isCompact_preimage_iff Kf).2 hK

/--
theorem `Topology.IsClosedEmbedding.isCompact_preimage` / 定理 `Topology.IsClosedEmbedding.isCompact_preimage`

English:
theorem Topology.IsClosedEmbedding.isCompact_preimage
  statement: (hf : IsClosedEmbedding f)
  proof: hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

中文:
定理 拓扑.是闭嵌入.isCompact_preimage
  结论: (hf : 是闭嵌入 f)
  证明: hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

Depends on / 依赖: hf.isClosed_range, hf.isInducing.isCompact_preimage, isClosed_range, isCompact_preimage, isInducing
-/
theorem Topology.IsClosedEmbedding.isCompact_preimage (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

/--
theorem `Topology.IsClosedEmbedding.tendsto_cocompact` / 定理 `Topology.IsClosedEmbedding.tendsto_cocompact`

English:
theorem Topology.IsClosedEmbedding.tendsto_cocompact
  given: (hf : IsClosedEmbedding f)
  proof: Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact

中文:
定理 拓扑.是闭嵌入.tendsto_cocompact
  条件: (hf : 是闭嵌入 f)
  证明: Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact

Depends on / 依赖: Filter, Filter.hasBasis_cocompact.tendsto_right_iff.mpr, compl_mem_cocompact, hasBasis_cocompact, hf.isCompact_preimage, isCompact_preimage, tendsto_right_iff
-/
theorem Topology.IsClosedEmbedding.tendsto_cocompact (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.cocompact X) (Filter.cocompact Y) :=
  Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact

/--
theorem `Subtype.isCompact_iff` / 定理 `Subtype.isCompact_iff`

English:
theorem Subtype.isCompact_iff
  given: {p : X -> Prop} {s : Set { x // p x }}
  proof: IsEmbedding.subtypeVal.isCompact_iff

中文:
定理 子类型.isCompact_iff
  条件: {p : X -> 命题} {s : 集合 { x // p x }}
  证明: IsEmbedding.subtypeVal.isCompact_iff

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isCompact_iff, isCompact_iff, subtypeVal
-/
theorem Subtype.isCompact_iff {p : X -> Prop} {s : Set { x // p x }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isCompact_iff

/--
theorem `isCompact_iff_isCompact_univ` / 定理 `isCompact_iff_isCompact_univ`

English:
theorem isCompact_iff_isCompact_univ
  statement: IsCompact s ↔ IsCompact (univ : Set s)
  proof: by
  rw [Subtype.isCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

中文:
定理 isCompact_iff_isCompact_univ
  结论: 是紧集 s ↔ 是紧集 (univ : 集合 s)
  证明: by
  rw [Subtype.isCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.isCompact_iff, Subtype.range_coe, image_univ, isCompact_iff, range_coe
-/
theorem isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

open scoped Set.Notation in
/--
theorem `IsCompact.elim_finite_subfamily_isClosed_subtype` / 定理 `IsCompact.elim_finite_subfamily_isClosed_subtype`

English:
theorem IsCompact.elim_finite_subfamily_isClosed_subtype
  proof: by
  suffices univ inter ⋂ i, (fun i : I => s ↓inter t i) i = ∅ by
    simpa [eq_empty_iff_forall_notMem] using
      (isCompact_iff_isCompact_univ.mp ks).elim_finite_subfamily_closed
      (fun i : I => s ↓inter t i) (fun i => htc i.val i.prop) this
  simpa [Set.eq_empty_iff_forall_notMem, Subtype.forall] using hst

中文:
定理 是紧集.elim_finite_subfamily_isClosed_subtype
  证明: by
  suffices univ inter ⋂ i, (fun i : I => s ↓inter t i) i = ∅ by
    simpa [eq_empty_iff_forall_notMem] using
      (isCompact_iff_isCompact_univ.mp ks).elim_finite_subfamily_closed
      (fun i : I => s ↓inter t i) (fun i => htc i.val i.prop) this
  simpa [Set.eq_empty_iff_forall_notMem, Subtype.forall] using hst

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, Subtype, Subtype.forall, elim_finite_subfamily_closed, eq_empty_iff_forall_notMem, i.prop, i.val, isCompact_iff_isCompact_univ, isCompact_iff_isCompact_univ.mp
-/
theorem IsCompact.elim_finite_subfamily_isClosed_subtype
    {X : Type*} [TopologicalSpace X] {s : Set X} (ks : IsCompact s)
    {ι : Type*} (t : ι -> Set X) {I : Set ι}
    (htc : forall i in I, IsClosed (s ↓inter (t i) : Set s))
    (hst : s inter ⋂ i in I, t i = ∅) :
    exists u : Finset I, s inter ⋂ i in u, t i = ∅ := by
  suffices univ inter ⋂ i, (fun i : I => s ↓inter t i) i = ∅ by
    simpa [eq_empty_iff_forall_notMem] using
      (isCompact_iff_isCompact_univ.mp ks).elim_finite_subfamily_closed
      (fun i : I => s ↓inter t i) (fun i => htc i.val i.prop) this
  simpa [Set.eq_empty_iff_forall_notMem, Subtype.forall] using hst

/--
theorem `isCompact_iff_compactSpace` / 定理 `isCompact_iff_compactSpace`

English:
theorem isCompact_iff_compactSpace
  statement: IsCompact s ↔ CompactSpace s
  proof: isCompact_iff_isCompact_univ.trans isCompact_univ_iff

中文:
定理 isCompact_iff_compactSpace
  结论: 是紧集 s ↔ 紧空间 s
  证明: isCompact_iff_isCompact_univ.trans isCompact_univ_iff

Depends on / 依赖: isCompact_iff_isCompact_univ, isCompact_iff_isCompact_univ.trans, isCompact_univ_iff
-/
theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s :=
  isCompact_iff_isCompact_univ.trans isCompact_univ_iff

/--
theorem `IsCompact.finite` / 定理 `IsCompact.finite`

English:
theorem IsCompact.finite
  given: (hs : IsCompact s) (hs' : IsDiscrete s)
  statement: s.Finite
  proof: finite_coe_iff.mp (@finite_of_compact_of_discrete _ _
    (isCompact_iff_compactSpace.mp hs) hs'.to_subtype)

中文:
定理 是紧集.finite
  条件: (hs : 是紧集 s) (hs' : 是离散 s)
  结论: s.有限
  证明: finite_coe_iff.mp (@finite_of_compact_of_discrete _ _
    (isCompact_iff_compactSpace.mp hs) hs'.to_subtype)

Depends on / 依赖: finite_coe_iff, finite_coe_iff.mp, finite_of_compact_of_discrete, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, to_subtype
-/
theorem IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete s) : s.Finite :=
  finite_coe_iff.mp (@finite_of_compact_of_discrete _ _
    (isCompact_iff_compactSpace.mp hs) hs'.to_subtype)

/--
theorem `exists_nhds_ne_inf_principal_neBot` / 定理 `exists_nhds_ne_inf_principal_neBot`

English:
theorem exists_nhds_ne_inf_principal_neBot
  given: (hs : IsCompact s) (hs' : s.Infinite)
  proof: hs'.exists_accPt_of_subset_isCompact hs Subset.rfl

中文:
定理 存在_nhds_ne_inf_principal_neBot
  条件: (hs : 是紧集 s) (hs' : s.无限)
  证明: hs'.exists_accPt_of_subset_isCompact hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, exists_accPt_of_subset_isCompact
-/
theorem exists_nhds_ne_inf_principal_neBot (hs : IsCompact s) (hs' : s.Infinite) :
    exists z in s, (𝓝[!=] z ⊓ 𝓟 s).NeBot :=
  hs'.exists_accPt_of_subset_isCompact hs Subset.rfl

/--
theorem `Topology.IsClosedEmbedding.noncompactSpace` / 定理 `Topology.IsClosedEmbedding.noncompactSpace`

English:
theorem Topology.IsClosedEmbedding.noncompactSpace
  statement: [NoncompactSpace X] {f : X -> Y}
  proof: noncompactSpace_of_neBot hf.tendsto_cocompact.neBot

中文:
定理 拓扑.是闭嵌入.noncompactSpace
  结论: [Noncompact空间 X] {f : X -> Y}
  证明: noncompactSpace_of_neBot hf.tendsto_cocompact.neBot
-/
protected theorem Topology.IsClosedEmbedding.noncompactSpace [NoncompactSpace X] {f : X -> Y}
    (hf : IsClosedEmbedding f) : NoncompactSpace Y :=
  noncompactSpace_of_neBot hf.tendsto_cocompact.neBot

/--
theorem `Topology.IsClosedEmbedding.compactSpace` / 定理 `Topology.IsClosedEmbedding.compactSpace`

English:
theorem Topology.IsClosedEmbedding.compactSpace
  statement: [h : CompactSpace Y] {f : X -> Y}
  proof: ⟨by rw [hf.isInducing.isCompact_iff, image_univ]; exact hf.isClosed_range.isCompact⟩

@[compactness .]

中文:
定理 拓扑.是闭嵌入.compactSpace
  结论: [h : 紧空间 Y] {f : X -> Y}
  证明: ⟨by rw [hf.isInducing.isCompact_iff, image_univ]; exact hf.isClosed_range.isCompact⟩

@[compactness .]
-/
protected theorem Topology.IsClosedEmbedding.compactSpace [h : CompactSpace Y] {f : X -> Y}
    (hf : IsClosedEmbedding f) : CompactSpace X :=
  ⟨by rw [hf.isInducing.isCompact_iff, image_univ]; exact hf.isClosed_range.isCompact⟩

@[compactness .]
/--
theorem `IsCompact.prod` / 定理 `IsCompact.prod`

English:
theorem IsCompact.prod
  given: {t : Set Y} (hs : IsCompact s) (ht : IsCompact t)
  proof: by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x in s, hx : map Prod.fst f.1 <= 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y in t, hy : map Prod.snd f.1 <= 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy

中文:
定理 是紧集.乘积
  条件: {t : 集合 Y} (hs : 是紧集 s) (ht : 是紧集 t)
  证明: by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x in s, hx : map Prod.fst f.1 <= 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y in t, hy : map Prod.snd f.1 <= 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy

Depends on / 依赖: And.left, And.right, Prod.fst, Prod.snd, f.map, isCompact_iff_ultrafilter_le_nhds, le_inf, map_le_iff_le_comap, mem_map, mem_of_superset, nhds_prod_eq
-/
theorem IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x in s, hx : map Prod.fst f.1 <= 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y in t, hy : map Prod.snd f.1 <= 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy

/-- Finite topological spaces are compact. -/
instance (priority := 100) Finite.compactSpace [Finite X] : CompactSpace X where
  isCompact_univ := finite_univ.isCompact

/-- The indiscrete topology is compact -/
-- see note [lower instance priority]
instance (priority := 100) instCompactSpace [IndiscreteTopology X] : CompactSpace X where
  isCompact_univ f hf := by simp [clusterPt_of_indiscreteTopology, nonempty_of_neBot f]

/--
Instance `ULift.compactSpace` / 实例 `ULift.compactSpace`

English:
instance ULift.compactSpace
  signature: [CompactSpace X]
  body: IsClosedEmbedding.uliftDown.compactSpace

中文:
实例 类型层提升.compactSpace
  签名: [紧空间 X]
  定义体: IsClosedEmbedding.uliftDown.compactSpace

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.uliftDown.compactSpace, compactSpace, uliftDown
-/
instance ULift.compactSpace [CompactSpace X] : CompactSpace (ULift.{v} X) :=
  IsClosedEmbedding.uliftDown.compactSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] [CompactSpace Y] : CompactSpace (X × Y)
  body: ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

中文:
实例 [紧空间
  签名: X] [紧空间 Y] : 紧空间 (X × Y)
  定义体: ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

Depends on / 依赖: isCompact_univ, isCompact_univ.prod, univ_prod_univ
-/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X × Y) :=
  ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] [CompactSpace Y] : CompactSpace (X oplus Y)
  body: ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩

中文:
实例 [紧空间
  签名: X] [紧空间 Y] : 紧空间 (X oplus Y)
  定义体: ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩

Depends on / 依赖: continuous_inl, continuous_inr, isCompact_range, range_inl_union_range_inr
-/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X oplus Y) :=
  ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩

instance {X : ι -> Type*} [Finite ι] [forall i, TopologicalSpace (X i)] [forall i, CompactSpace (X i)] :
    CompactSpace (Σ i, X i) := by
  refine ⟨?_⟩
  rw [Sigma.univ]
  exact isCompact_iUnion fun i => isCompact_range continuous_sigmaMk

@[compactness .]
/--
lemma `Set.isCompact_sigma` / 引理 `Set.isCompact_sigma`

English:
lemma Set.isCompact_sigma
  statement: {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {s : Set ι}
  proof: by
  rw [Set.sigma_eq_biUnion]
  exact hs.isCompact_biUnion fun i hi => (ht i hi).image continuous_sigmaMk

中文:
引理 集合.isCompact_sigma
  结论: {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)] {s : 集合 ι}
  证明: by
  rw [Set.sigma_eq_biUnion]
  exact hs.isCompact_biUnion fun i hi => (ht i hi).image continuous_sigmaMk

Depends on / 依赖: Set.sigma_eq_biUnion, continuous_sigmaMk, hs.isCompact_biUnion, isCompact_biUnion, sigma_eq_biUnion
-/
lemma Set.isCompact_sigma {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {s : Set ι}
    {t : forall i, Set (X i)} (hs : s.Finite) (ht : forall i in s, IsCompact (t i)) :
    IsCompact (s.sigma t) := by
  rw [Set.sigma_eq_biUnion]
  exact hs.isCompact_biUnion fun i hi => (ht i hi).image continuous_sigmaMk

/--
lemma `IsCompact.sigma_exists_finite_sigma_eq` / 引理 `IsCompact.sigma_exists_finite_sigma_eq`

English:
lemma IsCompact.sigma_exists_finite_sigma_eq
  statement: {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: by
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover (fun i : ι => Sigma.mk i '' Sigma.mk i ⁻¹' Set.univ)
    (fun i => isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk)
    fun x hx => (by simp)
  use s, fun i => Sigma.mk i ⁻¹' u, s.finite_toSet, fun i => ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    simp_all

中文:
引理 是紧集.sigma_存在_finite_sigma_eq
  结论: {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: by
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover (fun i : ι => Sigma.mk i '' Sigma.mk i ⁻¹' Set.univ)
    (fun i => isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk)
    fun x hx => (by simp)
  use s, fun i => Sigma.mk i ⁻¹' u, s.finite_toSet, fun i => ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    simp_all

Depends on / 依赖: Finset, Finset.mem_coe, IsClosedEmbedding, Set.mem_iUnion.mp, Set.mem_preimage, Set.mem_sigma_iff, Set.univ, Sigma.mk, Topology, Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage, and_iff_right_iff_imp, continuous_sigmaMk, elim_finite_subcover, finite_toSet, hu.elim_finite_subcover, isCompact_preimage, isOpenMap_sigmaMk, isOpen_univ, isOpen_univ.preimage, mem_coe
-/
lemma IsCompact.sigma_exists_finite_sigma_eq {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    (u : Set (Σ i, X i)) (hu : IsCompact u) :
    exists (s : Set ι) (t : forall i, Set (X i)), s.Finite ∧ (forall i, IsCompact (t i)) ∧ s.sigma t = u := by
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover (fun i : ι => Sigma.mk i '' Sigma.mk i ⁻¹' Set.univ)
    (fun i => isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk)
    fun x hx => (by simp)
  use s, fun i => Sigma.mk i ⁻¹' u, s.finite_toSet, fun i => ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    simp_all

/--
theorem `Filter.coprod_cocompact` / 定理 `Filter.coprod_cocompact`

English:
theorem Filter.coprod_cocompact
  proof: by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK => ?_
    rw [← univ_prod]; rw [← prod_univ]; rw [← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact

中文:
定理 滤子.coprod_cocompact
  证明: by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK => ?_
    rw [← univ_prod]; rw [← prod_univ]; rw [← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact

Depends on / 依赖: comap_cocompact_le, compl_mem_cocompact, compl_prod_eq_union, continuous_fst, continuous_snd, coprod, ge_iff, hasBasis_cocompact, hasBasis_cocompact.coprod, le_antisymm, prod_univ, sup_le, univ_prod
-/
theorem Filter.coprod_cocompact :
    (Filter.cocompact X).coprod (Filter.cocompact Y) = Filter.cocompact (X × Y) := by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK => ?_
    rw [← univ_prod]; rw [← prod_univ]; rw [← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact

/--
theorem `Prod.noncompactSpace_iff` / 定理 `Prod.noncompactSpace_iff`

English:
theorem Prod.noncompactSpace_iff
  proof: by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]

中文:
定理 积类型.noncompactSpace_iff
  证明: by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]

Depends on / 依赖: Filter, Filter.cocompact_neBot_iff, Filter.coprod_cocompact, Filter.coprod_neBot_iff, cocompact_neBot_iff, coprod_cocompact, coprod_neBot_iff
-/
theorem Prod.noncompactSpace_iff :
    NoncompactSpace (X × Y) ↔ NoncompactSpace X ∧ Nonempty Y ∨ Nonempty X ∧ NoncompactSpace Y := by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]

-- See Note [lower instance priority]
instance (priority := 100) Prod.noncompactSpace_left [NoncompactSpace X] [Nonempty Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

-- See Note [lower instance priority]
instance (priority := 100) Prod.noncompactSpace_right [Nonempty X] [NoncompactSpace Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

section Tychonoff

variable {X : ι -> Type*} [forall i, TopologicalSpace (X i)]

/--
theorem `isCompact_pi_infinite` / 定理 `isCompact_pi_infinite`

English:
theorem isCompact_pi_infinite
  given: {s : forall i, Set (X i)}
  proof: by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, le_pi, le_principal_iff]
  intro h f hfs
  have : forall i : ι, exists x, x in s i ∧ Tendsto (Function.eval i) f (𝓝 x) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose x hx using this
  exact ⟨x, fun i => (hx i).left, fun i => (hx i).right⟩

中文:
定理 isCompact_pi_infinite
  条件: {s : 对任意 i, 集合 (X i)}
  证明: by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, le_pi, le_principal_iff]
  intro h f hfs
  have : forall i : ι, exists x, x in s i ∧ Tendsto (Function.eval i) f (𝓝 x) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose x hx using this
  exact ⟨x, fun i => (hx i).left, fun i => (hx i).right⟩

Depends on / 依赖: Function, Function.eval, Tendsto, f.map, isCompact_iff_ultrafilter_le_nhds, le_pi, le_principal_iff, mem_map, mem_of_superset, nhds_pi
-/
theorem isCompact_pi_infinite {s : forall i, Set (X i)} :
    (forall i, IsCompact (s i)) -> IsCompact { x : forall i, X i | forall i, x i in s i } := by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, le_pi, le_principal_iff]
  intro h f hfs
  have : forall i : ι, exists x, x in s i ∧ Tendsto (Function.eval i) f (𝓝 x) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose x hx using this
  exact ⟨x, fun i => (hx i).left, fun i => (hx i).right⟩

/--
theorem `isCompact_univ_pi` / 定理 `isCompact_univ_pi`

English:
theorem isCompact_univ_pi
  given: {s : forall i, Set (X i)} (h : forall i, IsCompact (s i))
  proof: by
  convert! isCompact_pi_infinite h
  simp only [← mem_univ_pi, ofPred_mem_eq]

中文:
定理 isCompact_univ_pi
  条件: {s : 对任意 i, 集合 (X i)} (h : 对任意 i, 是紧集 (s i))
  证明: by
  convert! isCompact_pi_infinite h
  simp only [← mem_univ_pi, ofPred_mem_eq]

Depends on / 依赖: convert, isCompact_pi_infinite, mem_univ_pi, ofPred_mem_eq
-/
theorem isCompact_univ_pi {s : forall i, Set (X i)} (h : forall i, IsCompact (s i)) :
    IsCompact (pi univ s) := by
  convert! isCompact_pi_infinite h
  simp only [← mem_univ_pi, ofPred_mem_eq]

/--
Instance `Pi.compactSpace` / 实例 `Pi.compactSpace`

English:
instance Pi.compactSpace
  signature: [forall i, CompactSpace (X i)]
  body: ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩

中文:
实例 依赖函数类型.compactSpace
  签名: [对任意 i, 紧空间 (X i)]
  定义体: ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩

Depends on / 依赖: isCompact_univ, isCompact_univ_pi, pi_univ
-/
instance Pi.compactSpace [forall i, CompactSpace (X i)] : CompactSpace (forall i, X i) :=
  ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩

/--
Instance `Function.compactSpace` / 实例 `Function.compactSpace`

English:
instance Function.compactSpace
  signature: [CompactSpace Y]
  body: Pi.compactSpace

中文:
实例 函数.compactSpace
  签名: [紧空间 Y]
  定义体: Pi.compactSpace

Depends on / 依赖: Pi.compactSpace, compactSpace
-/
instance Function.compactSpace [CompactSpace Y] : CompactSpace (ι -> Y) :=
  Pi.compactSpace

/--
lemma `Pi.isCompact_iff_of_isClosed` / 引理 `Pi.isCompact_iff_of_isClosed`

English:
lemma Pi.isCompact_iff_of_isClosed
  given: {s : Set (Π i, X i)} (hs : IsClosed s)
  proof: by
  constructor <;> intro H
· exact fun i => H.image continuous_apply i
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H) hs (subset_pi_eval_image univ s)

中文:
引理 依赖函数类型.isCompact_iff_of_isClosed
  条件: {s : 集合 (Π i, X i)} (hs : 是闭集 s)
  证明: by
  constructor <;> intro H
· exact fun i => H.image continuous_apply i
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H) hs (subset_pi_eval_image univ s)

Depends on / 依赖: H.image, IsCompact, IsCompact.of_isClosed_subset, continuous_apply, isCompact_univ_pi, of_isClosed_subset, subset_pi_eval_image
-/
lemma Pi.isCompact_iff_of_isClosed {s : Set (Π i, X i)} (hs : IsClosed s) :
    IsCompact s ↔ forall i, IsCompact (eval i '' s) := by
  constructor <;> intro H
· exact fun i => H.image continuous_apply i
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H) hs (subset_pi_eval_image univ s)

/--
lemma `Pi.exists_compact_superset_iff` / 引理 `Pi.exists_compact_superset_iff`

English:
lemma Pi.exists_compact_superset_iff
  given: {s : Set (Π i, X i)}
  proof: by
  constructor
  · intro ⟨K, hK, hsK⟩ i
exact ⟨eval i '' K, hK.image continuous_apply i, hsK.trans K.subset_preimage_image _⟩
  · intro H
    choose K hK hsK using H
    exact ⟨pi univ K, isCompact_univ_pi hK, fun _ hx i _ => hsK i hx⟩

中文:
引理 依赖函数类型.存在_compact_superset_iff
  条件: {s : 集合 (Π i, X i)}
  证明: by
  constructor
  · intro ⟨K, hK, hsK⟩ i
exact ⟨eval i '' K, hK.image continuous_apply i, hsK.trans K.subset_preimage_image _⟩
  · intro H
    choose K hK hsK using H
    exact ⟨pi univ K, isCompact_univ_pi hK, fun _ hx i _ => hsK i hx⟩
-/
protected lemma Pi.exists_compact_superset_iff {s : Set (Π i, X i)} :
    (exists K, IsCompact K ∧ s subseteq K) ↔ forall i, exists Ki, IsCompact Ki ∧ s subseteq eval i ⁻¹' Ki := by
  constructor
  · intro ⟨K, hK, hsK⟩ i
exact ⟨eval i '' K, hK.image continuous_apply i, hsK.trans K.subset_preimage_image _⟩
  · intro H
    choose K hK hsK using H
    exact ⟨pi univ K, isCompact_univ_pi hK, fun _ hx i _ => hsK i hx⟩

/--
theorem `Filter.coprodᵢ_cocompact` / 定理 `Filter.coprodᵢ_cocompact`

English:
theorem Filter.coprodᵢ_cocompact
  given: {X : ι -> Type*} [forall d, TopologicalSpace (X d)]
  proof: by
  refine le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) ?_
  refine compl_surjective.forall.2 fun s H => ?_
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩

中文:
定理 滤子.coprodᵢ_cocompact
  条件: {X : ι -> 类型} [对任意 d, 拓扑空间 (X d)]
  证明: by
  refine le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) ?_
  refine compl_surjective.forall.2 fun s H => ?_
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩

Depends on / 依赖: Filter, Filter.comap_cocompact_le, Filter.mem_cocompact, Set.pi, comap_cocompact_le, compl_subset_compl, compl_surjective, compl_surjective.forall, continuous_apply, iSup_le, image_subset_iff, isCompact_univ_pi, le_antisymm, mem_cocompact
-/
theorem Filter.coprodᵢ_cocompact {X : ι -> Type*} [forall d, TopologicalSpace (X d)] :
    (Filter.coprodᵢ fun d => Filter.cocompact (X d)) = Filter.cocompact (forall d, X d) := by
  refine le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) ?_
  refine compl_surjective.forall.2 fun s H => ?_
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩

end Tychonoff

/--
Instance `Quot.compactSpace` / 实例 `Quot.compactSpace`

English:
instance Quot.compactSpace
  signature: {r : X -> X -> Prop} [CompactSpace X]
  body: ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩

中文:
实例 商.compactSpace
  签名: {r : X -> X -> 命题} [紧空间 X]
  定义体: ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩

Depends on / 依赖: continuous_quot_mk, isCompact_range, range_quot_mk
-/
instance Quot.compactSpace {r : X -> X -> Prop} [CompactSpace X] : CompactSpace (Quot r) :=
  ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩

/--
Instance `Quotient.compactSpace` / 实例 `Quotient.compactSpace`

English:
instance Quotient.compactSpace
  signature: {s : Setoid X} [CompactSpace X]
  body: Quot.compactSpace

中文:
实例 商.compactSpace
  签名: {s : 集合等价关系 X} [紧空间 X]
  定义体: Quot.compactSpace

Depends on / 依赖: Quot.compactSpace, compactSpace
-/
instance Quotient.compactSpace {s : Setoid X} [CompactSpace X] : CompactSpace (Quotient s) :=
  Quot.compactSpace

/--
theorem `IsClosed.exists_minimal_nonempty_closed_subset` / 定理 `IsClosed.exists_minimal_nonempty_closed_subset`

English:
theorem IsClosed.exists_minimal_nonempty_closed_subset
  statement: [CompactSpace X] {S : Set X}
  proof: by
  let opens := { U : Set X | Sᶜ subseteq U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        have : Nonempty { U // U in c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine ⟨⟨?_, ?_, ?_⟩, fun U hU _ hx => ⟨U, hU, hx⟩⟩
        · exact fun _ hx => ⟨U₀, hU₀, U₀compl hx⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U in c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, not_and, Set.mem_iInter, Subtype.forall,
              mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, ?_⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  obtain ⟨Uc, Uo, Ucne⟩ := h.prop
  refine ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, ?_⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine h.eq_of_ge ⟨?_, isOpen_compl_iff.mpr V'cls, ?_⟩ (subset_compl_comm.2 V'sub)
    · exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    · simp only [compl_compl, V'ne]
  rw [← this]; rw [compl_compl]

中文:
定理 是闭集.存在_minimal_nonempty_closed_subset
  结论: [紧空间 X] {S : 集合 X}
  证明: by
  let opens := { U : Set X | Sᶜ subseteq U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        have : Nonempty { U // U in c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine ⟨⟨?_, ?_, ?_⟩, fun U hU _ hx => ⟨U, hU, hx⟩⟩
        · exact fun _ hx => ⟨U₀, hU₀, U₀compl hx⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U in c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, not_and, Set.mem_iInter, Subtype.forall,
              mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, ?_⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  obtain ⟨Uc, Uo, Ucne⟩ := h.prop
  refine ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, ?_⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine h.eq_of_ge ⟨?_, isOpen_compl_iff.mpr V'cls, ?_⟩ (subset_compl_comm.2 V'sub)
    · exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    · simp only [compl_compl, V'ne]
  rw [← this]; rw [compl_compl]

Depends on / 依赖: IsOpen, Nonempty, Set.m, c.Nonempty, convert_to, isOpen_sUnion, not_and, not_exists, subseteq, zorn_subset
-/
theorem IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) :
    exists V : Set X, V subseteq S ∧ V.Nonempty ∧ IsClosed V ∧
      forall V' : Set X, V' subseteq V -> V'.Nonempty -> IsClosed V' -> V' = V := by
  let opens := { U : Set X | Sᶜ subseteq U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        have : Nonempty { U // U in c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine ⟨⟨?_, ?_, ?_⟩, fun U hU _ hx => ⟨U, hU, hx⟩⟩
        · exact fun _ hx => ⟨U₀, hU₀, U₀compl hx⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U in c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, not_and, Set.mem_iInter, Subtype.forall,
              mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, ?_⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  obtain ⟨Uc, Uo, Ucne⟩ := h.prop
  refine ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, ?_⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine h.eq_of_ge ⟨?_, isOpen_compl_iff.mpr V'cls, ?_⟩ (subset_compl_comm.2 V'sub)
    · exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    · simp only [compl_compl, V'ne]
  rw [← this]; rw [compl_compl]

end Compact
